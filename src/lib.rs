#![no_std]
#![allow(clippy::partialeq_ne_impl)]

//! [`ThinStr`] is the slimmer sibling of `Box<str>` and `String`. It's a single
//! pointer, and stores it's length inline with the data, in the same
//! allocation.
//!
//! ## Limitations
//!
//! Right now the interface is minimally feature-complete, and relies on
//! `Deref<Target = str>` for most of it, but patches are welcome to flesh it out
//! more.
//!
//! In particular, while it isn't immutable, it might as well be, since it cannot
//! currently be resized after construction. This will probably eventually change.
//!
//! ## Crate features
//!
//! This crate is currently no_std compatible in all configurations, however it
//! uses `extern crate alloc` as you might expect.
//!
//! - `serde_support`: Support serializing and deserializing `ThinStr` using
//!   `serde`. Disabled by default.
extern crate alloc;
use alloc::alloc::{alloc, realloc, dealloc, handle_alloc_error, Layout};

#[doc(hidden)]
pub use core as __core;

use core::{
    mem::{align_of, size_of},
    ptr::{self, NonNull},
};

/// Like a Box<str>, but only a single pointer.
///
/// ```
/// use thin_str::ThinStr;
/// let s = ThinStr::new("abcde");
/// assert_eq!(s.len(), 5);
/// let t: ThinStr = "foo".into();
/// assert_ne!(t, s);
/// let q = s.clone();
/// assert_eq!(s, q);
/// ```
#[repr(transparent)]
pub struct ThinStr(NonNull<ThinHeader>);

#[repr(C)]
struct ThinHeader {
    len: usize,
    // NB: don't actually read from this unless you want to upset miri.
    data: [u8; 0],
}

// All empty strings point at this. Or a similar header -- we want this to be
// usable in a const fn, so we can't use `static` and need to assume two copies
// might be different. This is fine, we just never allocate empty strings, and
// then we can similarly avoid deallocating if `p.len() == 0`.
const EMPTY_HEADER: ThinHeader = ThinHeader { len: 0, data: [] };

// SAFETY: This is just NonNull::from(&T) but const.
const EMPTY: ThinStr = unsafe {
    ThinStr(NonNull::new_unchecked(
        &EMPTY_HEADER as *const ThinHeader as *mut ThinHeader,
    ))
};

unsafe impl Send for ThinStr {}
unsafe impl Sync for ThinStr {}

impl Drop for ThinStr {
    #[inline]
    fn drop(&mut self) {
        let len = self.len();
        if len > 0 {
            let layout = ThinStr::layout_for(len);
            unsafe {
                let ptr: *mut ThinHeader = self.0.as_ptr();
                dealloc(ptr.cast::<u8>(), layout);
            }
        }
    }
}

impl Clone for ThinStr {
    #[inline]
    fn clone(&self) -> Self {
        Self::new(self.as_str())
    }
}

impl ThinStr {
    /// Create a new empty string.
    #[inline]
    pub const fn empty() -> Self {
        EMPTY
    }

    /// SAFETY: `initializer` must initialize the first `len` bytes of the
    /// pointer with UTF-8. The pointer passed in will not be null, and will be
    /// fresh from the allocator.
    #[inline]
    unsafe fn new_init_with(len: usize, initializer: impl FnOnce(*mut u8)) -> Self {
        if len == 0 {
            return EMPTY;
        }
        let layout = Self::layout_for(len);

        let ptr: NonNull<ThinHeader> =
            NonNull::new(alloc(layout).cast()).unwrap_or_else(|| handle_alloc_error(layout));

        let szp = ptr.as_ptr().cast::<usize>();
        ptr::write(szp, len);

        let bufstart = szp.add(1).cast::<u8>();
        initializer(bufstart);

        debug_assert_eq!((*ptr.as_ptr()).data.as_ptr() as usize, bufstart as usize);

        ThinStr(ptr)
    }

    /// Create a new string with the same contents as `s`.
    #[inline]
    pub fn new(s: &str) -> Self {
        // SAFETY: we're required to initialize the first `len` bytes in the
        // callback, and we do with copy_nonoverlapping.
        unsafe {
            let len = s.len();
            Self::new_init_with(len, |buf| {
                ptr::copy_nonoverlapping(s.as_bytes().as_ptr(), buf, len)
            })
        }
    }

    /// Create a new string with all bytes initialized to zero.
    #[inline]
    pub fn new_zeroed(len: usize) -> Self {
        // SAFETY: we're required to initialize the first `len` bytes in the
        // callback, and we do with write_bytes.
        unsafe { Self::new_init_with(len, |buf| buf.write_bytes(0u8, len)) }
    }

    /// Add space for exactly `additional` extra bytes, which will be
    /// initialized by `initializer`.
    ///
    /// SAFETY: `initializer` must must initialize the first `additional_len` of
    /// the pointer it is passed bytes before returning. Note: It may not read from
    /// `self` or any value derived from it (the borrow checker prevents this,
    /// but it's unsound to do it with unsafe code too).
    unsafe fn grow_init_with(&mut self, additional_len: usize, initializer: impl FnOnce(*mut u8)) {
        if additional_len == 0 {
            return;
        }

        let old_len = self.len();

        if old_len == 0 {
            // If we're empty, this is just `new_init_with`.
            *self = Self::new_init_with(additional_len, initializer);
            return;
        }

        let old_layout = Self::layout_for(old_len);
        let new_len = old_len.checked_add(additional_len).unwrap();

        let new_header: NonNull<ThinHeader> = self.reallocate(old_layout, new_len);

        let str_start = new_header.as_ptr().add(1).cast::<u8>();
        let uninit_start = str_start.add(old_len);

        initializer(uninit_start);
        // Now that everything is initialized, go back to being a non-empty string.
        self.0 = new_header;
    }

    unsafe fn shrink_to(&mut self, new_len: usize) {
        debug_assert!(self.as_str().get(..new_len).is_some());

        let layout = Self::layout_for(self.len());

        let realloced: NonNull<ThinHeader> = self.reallocate(layout, new_len);
        self.0 = realloced;
    }

    /// Invoke realloc with our header, `old` and `new_len`. Updates the `len`
    /// of the resulting header and returns it. Aborts if the alloc fails, and
    /// leaves us temproarially empty if not. Unsafe for most of the same
    /// reasons as `realloc`.
    #[inline]
    unsafe fn reallocate(&mut self, old: Layout, new_len: usize) -> NonNull<ThinHeader> {
        debug_assert!(!self.is_empty() && new_len != 0);
        let new = Self::layout_for(new_len);
        let thin_header = self.take_raw();

        let realloced = realloc(thin_header.as_ptr().cast(), old, new.size()).cast();
        let result: NonNull<ThinHeader> = NonNull::new(realloced).unwrap_or_else(|| {
            handle_alloc_error(new)
        });
        (*result.as_ptr()).len = new_len;
        result
    }

    /// Return our header pointer, leaving us EMPTY. Used to defend against
    /// problems in the case of unexpected panics in unsafe code.
    #[inline]
    fn take_raw(&mut self) -> NonNull<ThinHeader> {
        core::mem::replace(self, EMPTY).into_raw()
    }

    #[inline]
    fn into_raw(self) -> NonNull<ThinHeader> {
        let p = self.0;
        core::mem::forget(self);
        p
    }

    #[inline]
    pub fn clear(&mut self) {
        *self = EMPTY;
    }

    #[inline]
    pub fn truncate(&mut self, l: usize) {
        if self.len() <= l {
            return;
        } else if l == 0 {
            self.clear();
            return;
        }
        assert!(self.as_str().get(..l).is_some());
        unsafe {
            self.shrink_to(l);
        }
    }

    // The obvious way of implementing formatting is pretty slow on macos...
    // In principal this shouldn't be that bad though, and we may want it in the future.
    /*
    #[inline]
    pub fn push_str(&mut self, s: &str) {
        unsafe {
            // Safe because we initialize `len` bytes of `buf` and do not read
            // from pointers that came from `self` inside the closure.
            let len = s.len();
            self.grow_init_with(len, |buf| {
                ptr::copy_nonoverlapping(s.as_bytes().as_ptr(), buf, len)
            })
        }
    }*/

    #[inline]
    fn layout_for(len: usize) -> Layout {
        assert!(len != 0);
        let size = size_of::<ThinHeader>().checked_add(len).unwrap();
        Self::raw_size_to_layout(size)
    }

    #[inline]
    fn raw_size_to_layout(size: usize) -> Layout {
        let align = align_of::<ThinHeader>();
        assert!(size.saturating_add(align) < isize::max_value() as usize);
        Layout::from_size_align(size, align).unwrap()
    }

    /// How long is the string, in bytes.
    #[inline]
    pub fn len(&self) -> usize {
        unsafe { (self.0.as_ptr() as *const usize).read() }
    }

    /// Returns true if the len is zero.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// We can't specialize the real to_string, but at least we can help out
    /// people whose muscle memory for <string-like-thing> -> String is 'call
    /// to_string()'
    #[inline]
    #[allow(clippy::inherent_to_string_shadow_display)]
    pub fn to_string(&self) -> alloc::string::String {
        alloc::string::String::from(self.as_str())
    }

    // Note: miri hates it if we get this via `data.as_ptr()` :/
    #[inline]
    fn data_ptr(&self) -> *const u8 {
        unsafe { (self.0.as_ptr() as *const u8).add(size_of::<usize>()) }
    }

    #[inline]
    fn data_ptr_mut(&mut self) -> *mut u8 {
        unsafe { (self.0.as_ptr() as *mut u8).add(size_of::<usize>()) }
    }

    /// Access the string's byte array.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        let len = self.len();
        unsafe { core::slice::from_raw_parts(self.data_ptr(), len) }
    }

    /// Get the underlying byte array mutably. It's unsound to write into this
    /// unless you ensure that it remains valid UTF8 after your writes.
    ///
    /// # Safety
    /// Caller must not write non-utf8 bytes
    #[inline]
    pub unsafe fn as_mut_bytes(&mut self) -> &mut [u8] {
        let len = self.len();
        core::slice::from_raw_parts_mut(self.data_ptr_mut(), len)
    }

    #[inline]
    pub fn as_mut_str(&mut self) -> &mut str {
        unsafe {
            let bytes = self.as_mut_bytes();
            #[cfg(any(test, miri))]
            {
                assert!(core::str::from_utf8(bytes).is_ok());
            }
            core::str::from_utf8_unchecked_mut(bytes)
        }
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        let bytes = self.as_bytes();
        #[cfg(any(test, miri))]
        {
            assert!(core::str::from_utf8(bytes).is_ok());
        }
        unsafe { core::str::from_utf8_unchecked(bytes) }
    }

    #[inline]
    fn append_zeros(&mut self, count: usize) {
        unsafe {
            // Safe because we initialize `count` bytes of `buf` and do not read
            // from pointers that came from `self` (or anything like that)
            // inside the closure.
            self.grow_init_with(count, |buf| buf.write_bytes(0u8, count))
        }
    }
}
#[doc(hidden)]
pub struct WriteHelper<'a> {
    pos: usize,
    buf: &'a mut ThinStr,
}

impl<'a> WriteHelper<'a> {
    #[inline]
    #[doc(hidden)]
    pub fn new(buf: &'a mut ThinStr) -> Self {
        Self { pos: buf.len(), buf }
    }

    fn ensure_cap(&mut self, cap: usize) {
        let grow_to = self.buf.len()
            .max(8)
            .checked_mul(2)
            .unwrap()
            .max(cap);
        let need = grow_to - self.buf.len();
        self.buf.append_zeros(need);
    }

    #[inline]
    fn append(&mut self, s: &str) {
        let need = self.pos + s.len();
        if need > self.buf.len() {
            self.ensure_cap(need);
        }

        debug_assert!(self.buf.is_char_boundary(self.pos) && self.buf.is_char_boundary(need));
        // SAFETY: appending valid utf8 to other valid utf8 still results in
        // valid utf8. Additionally, we know the bytes past `self.pos` are
        // zeroed, which means we cannot create an invalid sequence by
        // overwriting part of a valid one that exists in that area.
        unsafe {
            let buf = &mut self.buf.as_mut_bytes()[self.pos..need];
            buf.copy_from_slice(s.as_bytes());
        }
        self.pos = need;
    }
}

impl<'a> Drop for WriteHelper<'a> {
    #[inline]
    fn drop(&mut self) {
        self.buf.truncate(self.pos);
    }
}

impl<'a> core::fmt::Write for WriteHelper<'a> {
    #[inline]
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.append(s);
        Ok(())
    }
}

impl core::str::FromStr for ThinStr {
    type Err = core::convert::Infallible;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::new(s))
    }
}

impl core::ops::DerefMut for ThinStr {
    #[inline]
    fn deref_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}
impl core::ops::Deref for ThinStr {
    type Target = str;
    #[inline]
    fn deref(&self) -> &str {
        self.as_str()
    }
}
impl AsRef<str> for ThinStr {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}
impl AsMut<str> for ThinStr {
    #[inline]
    fn as_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl From<&str> for ThinStr {
    #[inline]
    fn from(s: &str) -> Self {
        Self::new(s)
    }
}

impl From<alloc::string::String> for ThinStr {
    #[inline]
    fn from(s: alloc::string::String) -> Self {
        Self::new(&s)
    }
}

impl Default for ThinStr {
    #[inline]
    fn default() -> Self {
        Self::empty()
    }
}

impl core::fmt::Debug for ThinStr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Debug::fmt(self.as_str(), f)
    }
}

impl core::fmt::Display for ThinStr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Display::fmt(self.as_str(), f)
    }
}

impl PartialEq for ThinStr {
    #[inline]
    fn eq(&self, o: &ThinStr) -> bool {
        PartialEq::eq(self.as_str(), o.as_str())
    }
    #[inline]
    fn ne(&self, o: &ThinStr) -> bool {
        PartialEq::ne(self.as_str(), o.as_str())
    }
}

impl Eq for ThinStr {}

impl PartialOrd for ThinStr {
    #[inline]
    fn partial_cmp(&self, o: &ThinStr) -> Option<core::cmp::Ordering> {
        Some(Ord::cmp(self.as_str(), o.as_str()))
    }
    #[inline]
    fn lt(&self, o: &ThinStr) -> bool {
        PartialOrd::lt(self.as_str(), o.as_str())
    }
    #[inline]
    fn le(&self, o: &ThinStr) -> bool {
        PartialOrd::le(self.as_str(), o.as_str())
    }
    #[inline]
    fn gt(&self, o: &ThinStr) -> bool {
        PartialOrd::gt(self.as_str(), o.as_str())
    }
    #[inline]
    fn ge(&self, o: &ThinStr) -> bool {
        PartialOrd::ge(self.as_str(), o.as_str())
    }
}

impl Ord for ThinStr {
    #[inline]
    fn cmp(&self, o: &ThinStr) -> core::cmp::Ordering {
        Ord::cmp(self.as_str(), o.as_str())
    }
}

impl core::hash::Hash for ThinStr {
    #[inline]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state)
    }
}

impl core::borrow::Borrow<str> for ThinStr {
    #[inline]
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

macro_rules! impl_index {
    ($($t:ty),+ $(,)?) => {$(
        impl core::ops::Index<$t> for ThinStr {
            type Output = str;
            #[inline]
            fn index(&self, idx: $t) -> &str {
                core::ops::Index::index(self.as_str(), idx)
            }
        }
        impl core::ops::IndexMut<$t> for ThinStr {
            #[inline]
            fn index_mut(&mut self, idx: $t) -> &mut str {
                self.as_mut_str().index_mut(idx)
            }
        }
    )+};
}

impl_index! {
    core::ops::RangeFull,
    core::ops::Range<usize>,
    core::ops::RangeTo<usize>,
    core::ops::RangeFrom<usize>,
    core::ops::RangeInclusive<usize>,
    core::ops::RangeToInclusive<usize>,
}

macro_rules! impl_eq {
    ($lhs:ty, $rhs: ty) => {
        impl<'a, 'b> PartialEq<$rhs> for $lhs {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool {
                PartialEq::eq(&self[..], &other[..])
            }
            #[inline]
            fn ne(&self, other: &$rhs) -> bool {
                PartialEq::ne(&self[..], &other[..])
            }
        }
        impl<'a, 'b> PartialEq<$lhs> for $rhs {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool {
                PartialEq::eq(&self[..], &other[..])
            }
            #[inline]
            fn ne(&self, other: &$lhs) -> bool {
                PartialEq::ne(&self[..], &other[..])
            }
        }
    };
}

impl_eq!(ThinStr, str);
impl_eq!(ThinStr, &'a str);
impl_eq!(&'a ThinStr, str);

impl_eq!(ThinStr, alloc::string::String);
impl_eq!(&'a ThinStr, alloc::string::String);

impl_eq!(ThinStr, &'a alloc::string::String);

#[macro_export]
macro_rules! thin_format {
    ($s:literal $(,)?) => {
        $crate::ThinStr::new($s)
    };
    ($fmt:literal, $($arg:tt)+) => {{
        let mut ts = $crate::ThinStr::empty();
        {
            use $crate::__core::fmt::Write as _;
            let mut writer = $crate::WriteHelper::new(&mut ts);
            $crate::__core::write!(&mut writer, $fmt, $($arg)+).unwrap();
        }
        ts
    }};
}

#[cfg(feature = "serde_support")]
mod serde_support {
    use super::ThinStr;
    use serde::{
        de::{self, Deserialize, Deserializer, Visitor},
        ser::{Serialize, Serializer},
    };

    impl<'de> Deserialize<'de> for ThinStr {
        #[inline]
        fn deserialize<D: Deserializer<'de>>(des: D) -> Result<Self, D::Error> {
            struct TSVisitor;
            impl<'de> Visitor<'de> for TSVisitor {
                type Value = ThinStr;
                fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                    formatter.write_str("a string")
                }
                #[inline]
                fn visit_str<E: de::Error>(self, s: &str) -> Result<Self::Value, E> {
                    Ok(ThinStr::from(s))
                }
            }

            des.deserialize_str(TSVisitor)
        }
    }

    impl Serialize for ThinStr {
        #[inline]
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.serialize_str(self.as_str())
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn test_thinness() {
        assert_eq!(
            core::mem::size_of::<ThinStr>(),
            core::mem::size_of::<usize>()
        );
        assert_eq!(
            core::mem::size_of::<Option<ThinStr>>(),
            core::mem::size_of::<usize>()
        );
    }

    #[test]
    #[allow(clippy::redundant_clone)]
    fn test_create() {
        let xyz = ThinStr::empty();
        let abc = ThinStr::new("foo").clone();
        assert_eq!(xyz.len(), 0);
        assert_eq!(xyz, "");
        assert!(xyz.is_empty());
        assert_eq!(abc.len(), 3);
        assert_eq!(abc, "foo");
        let xyz2 = xyz.clone();
        assert_eq!(xyz2.len(), 0);
        assert_eq!(xyz2, "");
        let s = ThinStr::new("abcde");
        assert_eq!(s.len(), 5);
        let t: ThinStr = "foo".into();
        assert_ne!(t, s);
        let q = s.clone();
        assert_eq!(s, q);

        let z3 = ThinStr::new_zeroed(3);
        assert_eq!(z3, "\0\0\0");

        let z3 = ThinStr::new_zeroed(0);
        assert_eq!(z3, "");
    }

    #[test]
    fn test_ord() {
        let mut v: [ThinStr; 3] = ["foo".into(), "bar".into(), "quux".into()];
        v.sort();
        assert_eq!(v[0], "bar");
        assert_eq!(v[1], "foo");
        assert_eq!(v[2], "quux");
    }

    #[test]
    fn test_indexing() {
        let s = ThinStr::new("abcde");
        assert_eq!(&s[..], "abcde");
        assert_eq!(&s[1..], "bcde");
        assert_eq!(&s[1..3], "bc");
        assert_eq!(&s[1..=3], "bcd");
        assert_eq!(&s[..=3], "abcd");
        let mut y = ThinStr::new("abcde");
        y.as_mut_str().make_ascii_uppercase();
        assert_eq!(y, "ABCDE");

        fn ascii_upper<I>(s: &ThinStr, i: I) -> ThinStr
        where
            ThinStr: core::ops::IndexMut<I, Output = str>,
        {
            let mut s2 = s.clone();
            (&mut s2[i]).make_ascii_uppercase();
            s2
        }

        assert_eq!(ascii_upper(&s, ..), "ABCDE");
        assert_eq!(ascii_upper(&s, 1..), "aBCDE");
        assert_eq!(ascii_upper(&s, 1..3), "aBCde");
        assert_eq!(ascii_upper(&s, 1..=3), "aBCDe");
        assert_eq!(ascii_upper(&s, ..=3), "ABCDe");
        let mut t = ThinStr::empty();
        t.make_ascii_uppercase();
        assert_eq!(t, "");
    }

    #[test]
    fn test_thin_format() {
        assert_eq!(thin_format!("foobar"), "foobar");
        assert_eq!(thin_format!("foobar{}", 123), "foobar123");
        let s = thin_format!("{}, {:?}, {}", 123, "abcdefghijklmnop", 456);
        assert_eq!(s, "123, \"abcdefghijklmnop\", 456");
        let big = thin_format!("{}|{}|{}|{}", s, s, s, s);
        let expected = [s.as_str(), s.as_str(), s.as_str(), s.as_str()].join("|");
        assert_eq!(expected, big);
    }

    #[test]
    fn test_fmt_conv() {
        assert_eq!(ThinStr::from(alloc::string::String::from("abcd")), "abcd");
        assert_eq!(
            alloc::string::String::from("abcd").as_str(),
            ThinStr::from("abcd")
        );
        assert_eq!("1234", alloc::format!("{}", ThinStr::new("1234")));
        assert_eq!("\"1234\"", alloc::format!("{:?}", ThinStr::new("1234")));
    }

    #[test]
    #[cfg(feature = "serde_support")]
    fn test_ser_de() {
        use serde_test::{assert_tokens, Token};
        let s = ThinStr::from("asdffdsa12344321");
        assert_tokens(&s, &[Token::Str("asdffdsa12344321")]);

        let s = ThinStr::from("");
        assert_tokens(&s, &[Token::Str("")]);

        let s = ThinStr::from(alloc::string::String::from("abcd43211234"));
        assert_tokens(&s, &[Token::Str("abcd43211234")]);
    }
}

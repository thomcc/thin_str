# `thin_str`

[`ThinStr`] is the slimmer sibling of `Box<str>` and `String`. It's a single pointer, and stores it's length inline with the data, in the same allocation.

## Limitations

Right now the interface is minimally feature-complete, and relies on `Deref<Target = str>` for most of it, but patches are welcome to flesh it out more.

In particular, while it isn't immutable, it might as well be, since it cannot currently be resized after construction. This will probably eventually change.

## Crate features

This crate is currently no_std compatible in all configurations, however it uses `extern crate alloc` as you might expect.

- `serde_support`: Support serializing and deserializing `ThinStr` using `serde`. Disabled by default.

## License
MIT/Apache2

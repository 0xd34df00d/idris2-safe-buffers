# Safe Buffers for Idris 2

This is a thin wrapper around Idris' native
[`Data.Buffer`](https://github.com/idris-lang/Idris2/blob/main/libs/base/Data/Buffer.idr).
Its sole purpose is to make out-of-bounds access slightly less likely,
by indexing the buffer type (which we'll call `SBuffer`)
with the number of elements and the element type — much like `Data.Vect` does.

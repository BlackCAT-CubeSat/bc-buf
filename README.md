# bc-buf

This Rust crate contains code for a single-writer, multiple-reader circular buffer structure.
Specifically:

* The writer and readers may be on different threads or (for types with a [layout guarantee]) even in different processes.
* The circular buffers are nonblocking.
  The writer may add an item to a buffer at any time.
  As a result, it is possible that readers may miss items if they get too far behind
  the writer.
  (Readers will, with very high probability, recognize if and when this happens.)
* No memory allocations are required after the buffer has been created.
* The writer protocol is simple&mdash;simple enough that it can be easily implemented in FPGA logic.
* Notifying readers when new items are available is beyond the scope of this crate.

The use-case this crate was created for is one
in which event data continuously arrives (with no possiblity of flow control)&mdash;in some cases, from hardware&mdash;and
needs to be communicated to other threads.

See the Rustdocs for details on how to use this crate.

[layout guarantee]: https://github.com/BlackCAT-CubeSat/bc-buf.git
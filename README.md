## A Rust-based Dependently-Typed Lambda Calculus

I follow the [CS 2520R write-up](https://plti.metareflection.club/hw/DependentTypes.pdf) very closely; see `Expr` in `lib.rs` for more details on the language syntax and implementation. In summary, I use names for all variables, a hash-map of arrays for fast `Environment` look-ups, and compare expressions after full $\beta$-reduction and up to $\alpha$-equivalence. Unfortunately, my type-checker is undecidable, but for the purposes of demonstration, I cap normalization to 1000 steps before failure.

In `main.rs`, I include an incomplete proof of the commutativity of addition:
```
cargo run -- release
```

The final three theorems (`plus_right_zero`, `plus_right_suc`, and `plus_comm`) are difficult to translate, and I was unable to produce a valid type. Compared to traditional FP, Rust is unique in allowing us to micro-manage the heap, and I avoid copying and re-allocating where possible. However, this also increased code complexity, and my implementation is quite hard to debug. This was also my first time using Rust, but I definitely learned a lot.
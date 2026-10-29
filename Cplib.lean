-- Utilities
import Cplib.Util.List
import Cplib.Util.Number
import Cplib.IO

-- Typical techniques
import Cplib.Typical

-- Number theory
import Cplib.NumberTheory
import Cplib.String
import Cplib.Convolution

-- Tree algorithms
import Cplib.Tree

-- Graph algorithms
import Cplib.Graph

-- Data structures
import Cplib.Structure.Deque
import Cplib.Structure.RingBuffer
import Cplib.Structure.Heap
import Cplib.Structure.LazySegTree
import Cplib.Structure.SegTree
import Cplib.Structure.FenwickTree
import Cplib.Structure.UnionFind

/-!
# Cplib

A library of algorithms and data structures for competitive programming,
collecting the modules that build under Lean 4.22.0, the version AtCoder uses.

## Module layout

The file layout follows the `Std` and `Batteries` convention:

- `Cplib.<area>.<name>.Basic` — the implementation. Depends only on other
  `Basic` modules and never pulls in `Mathlib`.
- `Cplib.<area>.<name>.Lemmas` — the theorems. Imports `Basic` together with
  whatever the proofs need, `Mathlib` included.
- `Cplib.<area>.<name>` — the aggregate module loading both, which is what this
  root imports.

To use an implementation on its own, for instance when submitting to AtCoder,
import the `...Basic` module directly; it builds without `Lemmas`, and so
without `Mathlib`.

## Naming

Public API specific to this library lives in the `Cplib` namespace. Extensions
to existing types live in that type's namespace instead, as `Nat.midpoint` and
`Array.lowerBound` do.

## Indexing conventions

Ranges are half-open throughout: `[l, r)` includes `l` and excludes `r`, so a
range bound may equal the length while a position may not.

A function that indexes with `Fin` comes with two `Nat`-indexed companions:

- `foo?` returns `none` when the index is out of range;
- `foo!` reports the bad index through `Cplib.unwrap!` and keeps going.

A Lean panic writes to stderr and returns a default rather than stopping the
program, so `foo!` turns a bad index into a loud wrong answer, not a crash.
Reach for `foo?` whenever the caller should handle the out-of-range case.

-/

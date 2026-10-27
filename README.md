# Cplib

A library of algorithms and data structures for competitive programming
(AtCoder and the like), aiming to prove the correctness of whatever can
reasonably be proved in Lean 4 alongside the implementation.

- **Lean**: `v4.22.0` (the version AtCoder uses)
- **Mathlib**: `v4.22.0`
- **Documentation**: [doc-gen4](https://github.com/leanprover/doc-gen4) (`v4.22.0`)

## Principles

- Cover what it actually takes to compete on AtCoder, and cover it well enough
  to rely on.
- Being a library written for pleasure, it weighs elegance, idiomatic Lean and
  ease of proof alongside runtime performance — but never at a large cost in
  performance.  Heaps and segment trees, for instance, are implemented over
  arrays rather than as explicit inductive trees, and the distance between the
  array implementation and the abstract property is bridged by theorems in
  `Lemmas`.
- This is not an academic formalization library, and exposing theorems as an
  external API is not a goal in itself.  The proofs serve as tests: they
  establish statically that an implementation behaves as intended, and they aim
  to cover the principal operations and properties.  So the semantically central
  API is proved, while a trivial convenience wrapper derived from it may be left
  unproved — `Cplib.SegTree.get` has its properties proved, whereas `get!` and
  `get?` may have no theorem of their own.

## Layout

Modules are filed under `Cplib` by area: algorithms, graphs, data structures,
general utilities and so on.  Following the `Std` and `Batteries` convention,
implementation and theorems are separated as in `Std.Data.HashMap.{Basic,Lemmas}`:

- `Cplib.<area>.<name>.Basic` — the implementation.  Depends only on other
  `Basic` modules and **never imports `Mathlib`**.
- `Cplib.<area>.<name>.Lemmas` — the theorems.  Imports `Basic` together with
  whatever the proofs need, `Mathlib` included.
- `Cplib.<area>.<name>` — the aggregate module loading both, which is what
  `Cplib.lean` imports.

Public API specific to this library lives in the `Cplib` namespace.  API defined
as an extension of an existing type lives in that type's namespace instead, as
`Nat.midpoint` and `Array.lowerBound` do.

**To use an implementation on its own, for instance when submitting to AtCoder,
import the `...Basic` module directly.**  It builds without `Lemmas`, and so
without `Mathlib`.  Editing an implementation stays cheap to rebuild for the
same reason.

## Building

```sh
# Resolve dependencies (first time, and after a dependency changes)
lake update

# Fetch Mathlib's build cache (makes the first build much faster)
lake exe cache get

# Build the library
lake build
```

## Bundling a single file for AtCoder

`scripts/bundle.py` expands every `Cplib.*` import reachable from an entry file,
in dependency order.  Imports that AtCoder's judge already provides, such as
`Mathlib` and `Std`, are left at the top.  The generated file carries a
reference URL, as AtCoder's rules on generative AI require, and the full MIT
licence text as a comment.

```sh
python3 scripts/bundle.py path/to/Main.lean -o Submit.lean
```

`--source-url` replaces the reference URL and `--license` the licence file;
`--no-license` embeds no licence notice at all.

Build the generated file as an executable with Lean 4.22.0 to check it before
submitting.

## Generating the documentation locally

The API documentation is generated with
[doc-gen4](https://github.com/leanprover/doc-gen4).  The published copy is at
<https://kowerkoint.github.io/cplib-lean/Cplib.html>.

The bundled script is the easy way:

```sh
./scripts/make-docs.sh
```

It writes to `.lake/build/doc/`.  To open it in a browser:

```sh
xdg-open .lake/build/doc/Cplib.html   # each module is at Cplib/<Name>.html
```

The script points source links at local files and works around a compatibility
problem in a dependency.  The first run also builds doc-gen4 itself, so it takes
a while.

Only the `Cplib` modules are rendered, so links to declarations in `Init`,
`Lean` and `Mathlib` have no page behind them.  `scripts/link-external-docs.py`
redirects those to
[mathlib4_docs](https://leanprover-community.github.io/mathlib4_docs/).  That
site tracks Mathlib master, whose module layout has drifted, so the links are
resolved by declaration name rather than by path.  `--base-url` points them
somewhere else.

## Finding which module a declaration is in

`#whereis` asks **the environment this package pins**, rather than a
documentation site, which module a declaration comes from.  mathlib4_docs is
built from Mathlib master, and measured against v4.22.0, 7.3% of the
declarations that still exist upstream have moved to another module.

```sh
./scripts/whereis.sh Nat.isPowerOfTwo     # Nat.isPowerOfTwo — Init.Data.Nat.Power2
./scripts/whereis.sh -s nextPowerOfTwo    # list every name containing this
```

Each run spends about ten seconds loading Mathlib.  To ask many questions in a
row, open `scripts/WhereIs.lean` in an editor and write the `#whereis` lines at
the end of it instead.

## Licence

[MIT License](LICENSE)

namespace Cplib

/-!
# Util.Unwrap.Basic

Shared implementation of the `!` API variants.

Every function in this library that indexes with `Fin` comes with two
`Nat`-indexed companions:

- `foo? : … → Nat → Option _` returns `none` when the index is out of range.
- `foo! : … → Nat → _` reports the bad index and keeps going.

`foo!` is a thin wrapper around `foo?` written with `unwrap!`.
-/

/-- Unwrap `o`, reporting `name` when it is `none` because an index was out of
range.

**This does not stop the program.** Lean's `panic!` writes a message and a
backtrace to stderr and then returns the `Inhabited` default, so execution
continues with that value and the exit code is unaffected. An out-of-range
index therefore surfaces as a loud wrong answer rather than a crash: visible
when running locally, invisible to a judge that discards stderr. Reach for the
`?` variant whenever the caller should handle the out-of-range case itself.

This matches `Array.get!` and `Array.set!` in the core library, which panic the
same way.

The message is built only in the `none` branch, so the in-range path pays
nothing for it. -/
@[inline] def unwrap! [Inhabited α] (name : String) : Option α → α
  | some x => x
  | none => panic! s!"{name}: index out of bounds"

/-- The out-of-range half of a `!` variant, for the operations that fall back to
the structure they were handed.

Those cannot be written as `unwrap! name (foo? …)`. The `Inhabited` default
holds a second reference to the structure for as long as `foo?` runs, so the
arrays inside it are shared, and an update that should have been in place
copies the whole array instead. Writing the range check out and reaching for
this only on the failing branch leaves the structure uniquely referenced on the
path that does the work:

```lean
def set! (self : SegTree M) (i : Nat) (x : M) : SegTree M :=
  if hi : i < self.sz then self.set ⟨i, hi⟩ x
  else outOfBounds! "SegTree.set!" self
```

The message is the same one `unwrap!` reports. -/
@[inline] def outOfBounds! (name : String) (fallback : α) : α :=
  let _ : Inhabited α := ⟨fallback⟩
  panic! s!"{name}: index out of bounds"

end Cplib

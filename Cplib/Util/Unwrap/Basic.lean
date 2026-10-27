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

end Cplib

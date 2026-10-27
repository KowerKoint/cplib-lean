namespace Cplib

/-!
# Structure.Deque.Basic

A persistent double-ended queue held as two lists, one for each end.

The deque stands for the sequence `front ++ back.reverse`: `front` holds the
elements nearest the front, nearest first, and `back` holds those nearest the
back, nearest first. Pushing at either end is a `cons` onto the matching list,
and `popFront?` takes from `front`, reversing `back` into it once `front` runs
out. That reversal costs `O(n)` but hands `n` elements to later pops, so a run
of operations costs `O(1)` each.

**The amortised bound assumes the deque is used linearly**, each state being
passed on and not reused. The structure is persistent, so popping repeatedly
from one state that is holding a long `back` pays the reversal every time.

**This deque pops only at the front.** That is what 0-1 BFS needs — an edge of
weight 0 goes to the front, one of weight 1 to the back, and the search always
takes from the front — and it is what makes the two-list representation simple:
adding `popBack?` here would reverse `front` into `back`, and alternating the
two pops would then pay `O(n)` every time rather than amortising. For a deque
that pops at both ends, and that indexes, use `Cplib.RingBuffer` — at the cost
of roughly twice the time per push, measured over ten million operations.

Costs, for a deque of `n` elements: `empty`, `isEmpty`, `pushFront` and
`pushBack` are `O(1)`, `popFront?` is `O(1)` amortised and `O(n)` in the worst
case, `front?` is `O(1)` when `front` is non-empty and `O(n)` otherwise, and
`size`, `toList` and `toArray` are `O(n)`.

```lean
let d := (Deque.empty.pushBack 2 |>.pushFront 1).pushBack 3
d.toList              -- [1, 2, 3]
d.popFront?           -- some (1, …)
```
-/

/-- A double-ended queue holding `front ++ back.reverse`. -/
structure Deque (α : Type u) where
  /-- Elements nearest the front, nearest first. -/
  front : List α
  /-- Elements nearest the back, nearest first, so in reverse order. -/
  back : List α

namespace Deque

variable {α : Type u}

/-- The sequence the deque stands for, front to back. `O(n)`. -/
def toList (d : Deque α) : List α := d.front ++ d.back.reverse

/-- The empty deque. `O(1)`. -/
def empty : Deque α := ⟨[], []⟩

instance : EmptyCollection (Deque α) := ⟨empty⟩
instance : Inhabited (Deque α) := ⟨empty⟩

/-- Printed as the sequence it stands for, since the split between `front` and
`back` is an implementation detail that two equal sequences need not share. -/
instance [Repr α] : Repr (Deque α) where
  reprPrec d prec := reprPrec d.toList prec

/-- Whether the deque holds no elements. `O(1)`. -/
@[inline] def isEmpty (d : Deque α) : Bool := d.front.isEmpty && d.back.isEmpty

/-- Number of elements. `O(n)`, since neither list carries its length; reach for
`isEmpty` when that is the question being asked. -/
def size (d : Deque α) : Nat := d.front.length + d.back.length

/-- Add `x` at the front. `O(1)`. -/
@[inline] def pushFront (d : Deque α) (x : α) : Deque α := ⟨x :: d.front, d.back⟩

/-- Add `x` at the back. `O(1)`. -/
@[inline] def pushBack (d : Deque α) (x : α) : Deque α := ⟨d.front, x :: d.back⟩

/-- Remove the front element, returning it and the rest. `O(1)` amortised.

The reversal that refills `front` is what the amortisation pays for; see this
module's documentation. -/
def popFront? (d : Deque α) : Option (α × Deque α) :=
  match d.front with
  | x :: rest => some (x, ⟨rest, d.back⟩)
  | [] =>
      match d.back.reverse with
      | [] => none
      | x :: rest => some (x, ⟨rest, []⟩)

/-- `popFront?` without the emptiness check. Reports a panic on an empty deque
and returns `default` paired with that deque; see `Cplib.unwrap!` on what a
panic does and does not do. `O(1)` amortised. -/
@[inline] def popFront! [Inhabited α] (d : Deque α) : α × Deque α :=
  match d.popFront? with
  | some r => r
  | none => panic! "Deque.popFront!: deque is empty"

/-- The front element. `O(1)` when `front` is non-empty, `O(n)` otherwise. -/
def front? (d : Deque α) : Option α :=
  match d.front with
  | x :: _ => some x
  | [] => d.back.getLast?

/-- The back element. `O(1)` when `back` is non-empty, `O(n)` otherwise. -/
def back? (d : Deque α) : Option α :=
  match d.back with
  | x :: _ => some x
  | [] => d.front.getLast?

/-- The deque holding `xs`, front to back. `O(1)`. -/
def ofList (xs : List α) : Deque α := ⟨xs, []⟩

/-- The deque holding `xs`, front to back. `O(n)`. -/
def ofArray (xs : Array α) : Deque α := ⟨xs.toList, []⟩

/-- The elements, front to back. `O(n)`. -/
def toArray (d : Deque α) : Array α := d.front.toArray ++ d.back.toArray.reverse

end Deque

end Cplib

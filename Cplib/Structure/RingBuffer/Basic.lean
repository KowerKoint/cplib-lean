import Cplib.Util.Unwrap.Basic

namespace Cplib

/-!
# Structure.RingBuffer.Basic

A growable double-ended queue laid out as a ring buffer over a `Vector`.

The elements occupy `sz` slots starting at `head` and wrapping round the end of
`data`, so element `i` lives at `(head + i) % cap`. Both ends therefore move in
`O(1)` without shifting anything, and any element can be read or written by
index. The capacity doubles when the buffer fills, which makes a push `O(1)`
amortised.

Unlike `Cplib.Deque`, this **pops at both ends and indexes**. It is also
ephemeral in the way an array is: an operation on a buffer that is no longer
referenced elsewhere updates `data` in place, while holding on to an older state
forces a copy. `Cplib.Deque` is the one to reach for when a persistent structure
is wanted, or when only 0-1 BFS-style pushes and front pops are — a push here
costs roughly twice what one on `Cplib.Deque` does, measured over ten million
operations, since finding a slot divides.

Slots outside the live range hold whatever was last written there, or a copy of
an element supplied at the growth that created them. They are never read: every
accessor is bounded by `sz`.

Costs, for a buffer of `n` elements: `empty`, `size`, `isEmpty`, `get`, `set`,
`front?`, `back?`, `popFront?` and `popBack?` are `O(1)`, `pushFront` and
`pushBack` are `O(1)` amortised and `O(n)` on the push that grows, and
`ofArray`, `toArray` and `toList` are `O(n)`.

```lean
let b := (RingBuffer.empty.pushBack 2 |>.pushFront 1).pushBack 3
b.toList           -- [1, 2, 3]
b.get! 1           -- 2
b.popBack?         -- some (3, …)
```
-/

/-- A growable deque over a ring buffer: element `i` sits at `(head + i) % cap`. -/
structure RingBuffer (α : Type u) where
  /-- Number of slots in `data`. -/
  cap : Nat
  /-- The slots. Only the `sz` of them starting at `head` hold elements. -/
  data : Vector α cap
  /-- Slot of the front element. -/
  head : Nat
  /-- Number of elements held. -/
  sz : Nat
  /-- The elements fit in the slots. -/
  sz_le : sz ≤ cap

namespace RingBuffer

variable {α : Type u}

/-- Number of elements. `O(1)`. -/
@[inline] def size (b : RingBuffer α) : Nat := b.sz

/-- Whether the buffer holds no elements. `O(1)`. -/
@[inline] def isEmpty (b : RingBuffer α) : Bool := b.sz == 0

/-- Slot holding element `i`. -/
@[inline] def slot (b : RingBuffer α) (i : Nat) : Nat := (b.head + i) % b.cap

theorem slot_lt (b : RingBuffer α) {i : Nat} (h : 0 < b.cap) : b.slot i < b.cap :=
  Nat.mod_lt _ h

theorem cap_pos (b : RingBuffer α) {i : Nat} (h : i < b.sz) : 0 < b.cap :=
  Nat.lt_of_le_of_lt (Nat.zero_le i) (Nat.lt_of_lt_of_le h b.sz_le)

/-- The empty buffer, holding no slots at all. `O(1)`. -/
def empty : RingBuffer α := ⟨0, #v[], 0, 0, Nat.le_refl 0⟩

instance : EmptyCollection (RingBuffer α) := ⟨empty⟩
instance : Inhabited (RingBuffer α) := ⟨empty⟩

/-- Element `i`, counted from the front. `O(1)`. -/
@[inline] def get (b : RingBuffer α) (i : Fin b.sz) : α :=
  b.data[b.slot i.val]'(b.slot_lt (b.cap_pos i.isLt))

/-- `get` for an index that may be out of range. `O(1)`. -/
@[inline] def get? (b : RingBuffer α) (i : Nat) : Option α :=
  if h : i < b.sz then some (b.get ⟨i, h⟩) else none

/-- `get` without the range check. Reports a panic on an out-of-range index and
returns `default`; see `Cplib.unwrap!`. `O(1)`. -/
@[inline] def get! [Inhabited α] (b : RingBuffer α) (i : Nat) : α :=
  unwrap! "RingBuffer.get!" (b.get? i)

/-- Replace element `i`, counted from the front. `O(1)`. -/
@[inline] def set (b : RingBuffer α) (i : Fin b.sz) (x : α) : RingBuffer α :=
  { b with data := b.data.set (b.slot i.val) x (b.slot_lt (b.cap_pos i.isLt)) }

/-- `set` for an index that may be out of range. `O(1)`. -/
@[inline] def set? (b : RingBuffer α) (i : Nat) (x : α) : Option (RingBuffer α) :=
  if h : i < b.sz then some (b.set ⟨i, h⟩ x) else none

/-- `set` without the range check. Reports a panic on an out-of-range index and
returns the buffer unchanged; see `Cplib.unwrap!`. `O(1)`. -/
@[inline] def set! (b : RingBuffer α) (i : Nat) (x : α) : RingBuffer α :=
  let _ : Inhabited (RingBuffer α) := ⟨b⟩
  unwrap! "RingBuffer.set!" (b.set? i x)

namespace Impl

/-- Move the elements into a buffer of twice the capacity, starting at slot `0`.

`pad` fills the slots that hold nothing; it is never read back, and taking it
from the caller is what keeps `RingBuffer` free of an `Inhabited` constraint. -/
def grow (b : RingBuffer α) (pad : α) : RingBuffer α :=
  let ncap := if b.cap = 0 then 1 else b.cap * 2
  have hsz : b.sz ≤ ncap := by
    have := b.sz_le
    dsimp only [ncap]
    split <;> omega
  ⟨ncap, Vector.ofFn (fun i : Fin ncap =>
    if h : i.val < b.sz then b.data[b.slot i.val]'(b.slot_lt (b.cap_pos h)) else pad),
   0, b.sz, hsz⟩

@[simp] theorem grow_sz (b : RingBuffer α) (pad : α) : (grow b pad).sz = b.sz := rfl

@[simp] theorem grow_cap (b : RingBuffer α) (pad : α) :
    (grow b pad).cap = if b.cap = 0 then 1 else b.cap * 2 := rfl

theorem grow_sz_lt_cap (b : RingBuffer α) (pad : α) (h : ¬ b.sz < b.cap) :
    (grow b pad).sz < (grow b pad).cap := by
  have := b.sz_le
  simp only [grow_sz, grow_cap]
  split <;> omega

/-- Write `x` into the slot just past the last element. Needs a free slot. -/
@[inline] def pushBackIn (b : RingBuffer α) (h : b.sz < b.cap) (x : α) : RingBuffer α :=
  ⟨b.cap, b.data.set (b.slot b.sz) x (b.slot_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) h)),
   b.head, b.sz + 1, h⟩

/-- Write `x` into the slot just before the front element. Needs a free slot. -/
@[inline] def pushFrontIn (b : RingBuffer α) (h : b.sz < b.cap) (x : α) : RingBuffer α :=
  have hcap : 0 < b.cap := Nat.lt_of_le_of_lt (Nat.zero_le _) h
  let nhead := (b.head + b.cap - 1) % b.cap
  ⟨b.cap, b.data.set nhead x (Nat.mod_lt _ hcap), nhead, b.sz + 1, h⟩

end Impl

/-- Add `x` at the back. `O(1)` amortised, `O(n)` on the push that grows. -/
def pushBack (b : RingBuffer α) (x : α) : RingBuffer α :=
  if h : b.sz < b.cap then Impl.pushBackIn b h x
  else Impl.pushBackIn (Impl.grow b x) (Impl.grow_sz_lt_cap b x h) x

/-- Add `x` at the front. `O(1)` amortised, `O(n)` on the push that grows. -/
def pushFront (b : RingBuffer α) (x : α) : RingBuffer α :=
  if h : b.sz < b.cap then Impl.pushFrontIn b h x
  else Impl.pushFrontIn (Impl.grow b x) (Impl.grow_sz_lt_cap b x h) x

/-- The front element. `O(1)`. -/
@[inline] def front? (b : RingBuffer α) : Option α := b.get? 0

/-- The back element. `O(1)`. -/
@[inline] def back? (b : RingBuffer α) : Option α := b.get? (b.sz - 1)

/-- Remove the front element, returning it and the rest. `O(1)`. -/
def popFront? (b : RingBuffer α) : Option (α × RingBuffer α) :=
  if h : 0 < b.sz then
    some (b.get ⟨0, h⟩,
      ⟨b.cap, b.data, b.slot 1, b.sz - 1, Nat.le_trans (Nat.sub_le _ _) b.sz_le⟩)
  else none

/-- Remove the back element, returning it and the rest. `O(1)`. -/
def popBack? (b : RingBuffer α) : Option (α × RingBuffer α) :=
  if h : 0 < b.sz then
    some (b.get ⟨b.sz - 1, Nat.sub_lt h Nat.one_pos⟩,
      ⟨b.cap, b.data, b.head, b.sz - 1, Nat.le_trans (Nat.sub_le _ _) b.sz_le⟩)
  else none

/-- `popFront?` without the emptiness check. Reports a panic on an empty buffer
and returns `default` paired with that buffer; see `Cplib.unwrap!`. `O(1)`. -/
@[inline] def popFront! [Inhabited α] (b : RingBuffer α) : α × RingBuffer α :=
  let _ : Inhabited (α × RingBuffer α) := ⟨default, b⟩
  unwrap! "RingBuffer.popFront!" b.popFront?

/-- `popBack?` without the emptiness check. Reports a panic on an empty buffer
and returns `default` paired with that buffer; see `Cplib.unwrap!`. `O(1)`. -/
@[inline] def popBack! [Inhabited α] (b : RingBuffer α) : α × RingBuffer α :=
  let _ : Inhabited (α × RingBuffer α) := ⟨default, b⟩
  unwrap! "RingBuffer.popBack!" b.popBack?

/-- The buffer holding `xs`, front to back. `O(n)`. -/
def ofArray (xs : Array α) : RingBuffer α :=
  ⟨xs.size, xs.toVector, 0, xs.size, Nat.le_refl _⟩

/-- The elements, front to back. `O(n)`. -/
def toArray (b : RingBuffer α) : Array α := Array.ofFn b.get

/-- The elements, front to back. `O(n)`. -/
def toList (b : RingBuffer α) : List α := List.ofFn b.get

/-- Printed as the sequence it stands for, since neither the capacity nor where
the elements start is part of what the buffer means. -/
instance [Repr α] : Repr (RingBuffer α) where
  reprPrec b prec := reprPrec b.toList prec

end RingBuffer

end Cplib

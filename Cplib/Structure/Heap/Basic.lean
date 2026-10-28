
namespace Cplib
/-!
# Structure.Heap.Basic

A `Vector`-backed binary heap, ordered by a comparator carried in the structure.

**This is a min-heap**: `top` is the element that `cmp` reports as smallest, and
repeated `pop` yields elements in non-decreasing order. The default comparator
is `compare`, so `Heap.empty` on an ordered type gives the usual min-heap. For a
max-heap, pass the reversed comparator: `Heap.empty (fun a b => compare b a)`.

`cmp` is expected to be a total preorder. `Heap.LawfulCmp`, in
`Structure.Heap.Lemmas`, states exactly what is assumed, and every order theorem
there takes it as a hypothesis; `compare` on a `LinearOrder` satisfies it.
Nothing enforces this at runtime, and a comparator that violates it simply
produces an unspecified order.

Costs, for a heap of `n` elements: `empty`, `size`, `isEmpty` and `top` are
`O(1)`, `add` and `pop` are `O(log n)`, `ofArray` is `O(n)`, and `drain` is
`O(n log n)`.

```lean
let h := Heap.ofArray #[5, 1, 4, 1, 3]
h.top!            -- 1, the smallest element
(h.pop!).top!     -- 1, the duplicate
h.drain           -- [1, 1, 3, 4, 5]
```
-/

structure Heap (α : Type) where
  n : Nat
  data : Vector α n
  cmp : α → α → Ordering

namespace Heap
variable {α : Type}

namespace Impl
def modifyUp (heap : Heap α) (idx : Fin heap.n) : Heap α :=
  if h : idx.toNat = 0 then heap
  else
    let par : Fin heap.n := ⟨(idx.toNat - 1) / 2, by have : idx.toNat < heap.n := idx.isLt; omega⟩
    if heap.cmp heap.data[par] heap.data[idx] |>.isLE then heap
    else
      let ndata := heap.data.swap par idx
      modifyUp ⟨heap.n, ndata, heap.cmp⟩ par
  termination_by idx.toNat
  decreasing_by show (idx.toNat - 1) / 2 < idx.toNat; omega

def modifyDown (heap : Heap α) (idx : Fin heap.n) : Heap α :=
  let c1 := idx.toNat * 2 + 1
  let c2 := idx.toNat * 2 + 2
  if h : c2 < heap.n then
    let c1 : Fin heap.n := ⟨c1, by omega⟩
    let c2 : Fin heap.n := ⟨c2, by omega⟩
    let cmin := if heap.cmp heap.data[c1] heap.data[c2] |>.isLT then c1 else c2
    if heap.cmp heap.data[idx] heap.data[cmin] |>.isLE then heap
    else
      let ndata := heap.data.swap idx cmin
      modifyDown ⟨heap.n, ndata, heap.cmp⟩ cmin
  else if h : c1 < heap.n then
    let c1 : Fin heap.n := ⟨c1, by omega⟩
    if heap.cmp heap.data[idx] heap.data[c1] |>.isLE then heap
    else
      let ndata := heap.data.swap idx c1
      modifyDown ⟨heap.n, ndata, heap.cmp⟩ c1
  else heap
  termination_by heap.n - idx.toNat
  decreasing_by
    · -- Both children exist: cmin is c1 (= 2i+1) or c2 (= 2i+2), both above idx.
      split
      · show heap.n - (idx.toNat * 2 + 1) < heap.n - idx.toNat; omega
      · show heap.n - (idx.toNat * 2 + 2) < heap.n - idx.toNat; omega
    · -- Only the left child exists: c1 = 2i+1.
      show heap.n - (idx.toNat * 2 + 1) < heap.n - idx.toNat; omega

/-- Sift down at indices `k - 1, k - 2, …, 0`, in that order.

Passing `n / 2` for `k` covers exactly the internal nodes, which restores the
heap property bottom-up in `O(n)` rather than the `O(n log n)` of inserting one
element at a time. -/
def heapifyFrom : Heap α → Nat → Heap α
  | heap, 0 => heap
  | heap, k + 1 =>
      if h : k < heap.n then heapifyFrom (modifyDown heap ⟨k, h⟩) k
      else heapifyFrom heap k

end Impl

/-- The empty heap. `cmp` defaults to `compare`, giving a min-heap. -/
def empty (cmp : α → α → Ordering := by exact compare) : Heap α := ⟨0, Array.empty |>.toVector, cmp⟩

/-- Number of elements. `O(1)`. -/
@[inline] def size (heap : Heap α) : Nat := heap.n

/-- Whether the heap holds no elements. `O(1)`. -/
@[inline] def isEmpty (heap : Heap α) : Bool := heap.n == 0

/-- Insert `x`. `O(log n)`. -/
def add (heap : Heap α) (x : α) : Heap α :=
  let ndata := heap.data.push x
  Impl.modifyUp ⟨heap.n + 1, ndata, heap.cmp⟩ ⟨heap.n, Nat.lt_succ_self _⟩

/-- Build a heap holding every element of `xs`, ordered by `cmp`.

Bottom-up heapification, so `O(n)`; inserting the elements one by one would be
`O(n log n)`. -/
def ofArray (xs : Array α) (cmp : α → α → Ordering := by exact compare) : Heap α :=
  Impl.heapifyFrom ⟨xs.size, xs.toVector, cmp⟩ (xs.size / 2)

/-- The smallest element under `cmp`. `O(1)`. -/
def top (heap : Heap α) (h : 0 < heap.n) := heap.data[0]

/-- `top` for a possibly empty heap. `O(1)`. -/
def top? (heap : Heap α) : Option α := heap.data[0]?

/-- `top` without the emptiness proof. Reports a panic on an empty heap and
returns `default`; see `Cplib.unwrap!` on what a panic does and does not do.
`O(1)`. -/
def top! [Inhabited α] (heap : Heap α) : α := heap.data[0]!

/-- Remove the smallest element. `O(log n)`. -/
def pop (heap : Heap α) (h : 0 < heap.n) : Heap α :=
  let ndata := heap.data.swap 0 (heap.n - 1)
  let ndata := ndata.pop
  if h' : 0 < heap.n - 1 then
    Impl.modifyDown ⟨heap.n - 1, ndata, heap.cmp⟩ ⟨0, h'⟩
  else
    ⟨heap.n - 1, ndata, heap.cmp⟩
/-- `pop` for a possibly empty heap. `O(log n)`. -/
def pop? (heap : Heap α) : Option <| Heap α :=
  if h : 0 < heap.n then some <| heap.pop h
  else none
/-- `pop` without the emptiness proof. Reports a panic on an empty heap and
returns the heap unchanged; see `Cplib.unwrap!`. `O(log n)`. -/
def pop! (heap : Heap α) : Heap α :=
  let _ : Inhabited <| Heap α := ⟨heap⟩
  if h : 0 < heap.n then heap.pop h
  else panic! "Heap.pop! : heap is empty"

namespace Impl

/-- `drain` with an explicit step count, which makes it structurally recursive
and so keeps the termination argument out of this module: that `pop` shortens
the heap is `Heap.pop_n`, which lives with the other proofs. -/
def drainFuel : Nat → Heap α → List α
  | 0, _ => []
  | fuel + 1, heap =>
      if h : 0 < heap.n then heap.top h :: drainFuel fuel (heap.pop h) else []

end Impl

/-- Every element, smallest first, by popping until the heap is empty.
`O(n log n)`.

`heap.n` steps are exactly enough, since each `pop` removes one element.
For a heap in order this list is sorted (`Heap.drain_sorted`), so
`(Heap.ofArray xs).drain` is heapsort.

```lean
(Heap.ofArray #[5, 1, 4, 1, 3]).drain   -- [1, 1, 3, 4, 5]
```
-/
def drain (heap : Heap α) : List α := Impl.drainFuel heap.n heap

end Heap

end Cplib

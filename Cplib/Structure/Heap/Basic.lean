/-!
# Structure.Heap.Basic

`Vector` ベースの二分ヒープ (優先度付きキュー) の実装。比較関数 `cmp` で順序を与える。
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
    · -- 両子がある場合: cmin = c1 (=2i+1) か c2 (=2i+2)。どちらも idx より大きい。
      split
      · show heap.n - (idx.toNat * 2 + 1) < heap.n - idx.toNat; omega
      · show heap.n - (idx.toNat * 2 + 2) < heap.n - idx.toNat; omega
    · -- 左子のみの場合: c1 = 2i+1。
      show heap.n - (idx.toNat * 2 + 1) < heap.n - idx.toNat; omega
end Impl

def empty (cmp : α → α → Ordering := by exact compare) : Heap α := ⟨0, Array.empty |>.toVector, cmp⟩

def add (heap : Heap α) (x : α) : Heap α :=
  let ndata := heap.data.push x
  Impl.modifyUp ⟨heap.n + 1, ndata, heap.cmp⟩ ⟨heap.n, Nat.lt_succ_self _⟩

def top (heap : Heap α) (h : 0 < heap.n) := heap.data[0]
def top? (heap : Heap α) : Option α := heap.data[0]?
def top! [Inhabited α] (heap : Heap α) : α := heap.data[0]!

def pop (heap : Heap α) (h : 0 < heap.n) : Heap α :=
  let ndata := heap.data.swap 0 (heap.n - 1)
  let ndata := ndata.pop
  if h' : 0 < heap.n - 1 then
    Impl.modifyDown ⟨heap.n - 1, ndata, heap.cmp⟩ ⟨0, h'⟩
  else
    ⟨heap.n - 1, ndata, heap.cmp⟩
def pop? (heap : Heap α) : Option <| Heap α :=
  if h : 0 < heap.n then some <| heap.pop h
  else none
def pop! (heap : Heap α) : Heap α :=
  let _ : Inhabited <| Heap α := ⟨heap⟩
  if h : 0 < heap.n then heap.pop h
  else panic! "Heap.pop! : heap is empty"

end Heap

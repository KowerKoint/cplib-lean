/- import Cplib.Util.Number -/
/--/
/- /-! -/
/- # Structure.PersistentSegTree.Basic -/
/--/
/- 永続セグメント木の実装。各更新で新しい木を返し、過去のバージョンを保持する。 -/
/- ノードは区間 `[lid, rid)` を表す `SegTreeNode` の木構造で表現する。 -/
/- -/ -/
/--/
/- inductive SegTreeNode (M : Type) where -/
/-   | leaf (v : M) (lid rid : Nat) : SegTreeNode M -/
/-   | node (v : M) (lid rid : Nat) (l r : SegTreeNode M) (hlr : lid + 1 < rid) : SegTreeNode M -/
/- deriving Inhabited -/
/--/
/- variable {M : Type} [Mul M] [One M] -/
/--/
/- namespace SegTreeNode -/
/- def v : SegTreeNode M → M -/
/-   | leaf v _ _ => v -/
/-   | node v _ _ _ _ _ => v -/
/- def lid : SegTreeNode M → Nat -/
/-   | leaf _ lid _ => lid -/
/-   | node _ lid _ _ _ _ => lid -/
/- def rid : SegTreeNode M → Nat -/
/-   | leaf _ _ rid => rid -/
/-   | node _ _ rid _ _ _ => rid -/
/- end SegTreeNode -/
/--/
/- namespace PersistentSegTree -/
/- namespace Impl -/
/- def init (a : Vector M n) (lid rid : Fin (n + 1)) (hlr : lid.val < rid.val) : SegTreeNode M := -/
/-   if h : lid.val + 1 ≥ rid then .leaf a[lid] lid rid -/
/-   else -/
/-     let mid := midpoint lid rid (by omega) -/
/-     let hmid : mid.v < n + 1 := Nat.lt_trans mid.hvr rid.isLt -/
/-     let mid' : Fin (n + 1) := ⟨mid.v, by omega⟩ -/
/-     let l := init a lid mid' mid.hlv -/
/-     let r := init a mid' rid mid.hvr -/
/-     .node (l.v * r.v) lid rid l r (by omega) -/
/- termination_by (rid.val - lid.val) -/
/- decreasing_by -/
/-   · exact midpoint_decrease_range_left lid.val rid.val (by omega) -/
/-   · exact midpoint_decrease_range_right lid.val rid.val (by omega) -/
/--/
/- def get (self : SegTreeNode M) (i : Nat) : M := -/
/-   let _ : Inhabited M := ⟨1⟩ -/
/-   match self with -/
/-   | .leaf v _ _ => v -/
/-   | .node _ lid rid l r hlr => -/
/-     let mid := midpoint lid rid hlr -/
/-     if i < mid.v then get l i -/
/-     else get r i -/
/--/
/- def set (self : SegTreeNode M) (i : Nat) (x : M) : SegTreeNode M := -/
/-   let _ : Inhabited M := ⟨1⟩ -/
/-   match self with -/
/-   | .leaf _ lid rid => .leaf x lid rid -/
/-   | .node _ lid rid l r hlr => -/
/-     let mid := midpoint lid rid hlr -/
/-     if i < mid.v then -/
/-       let nl := set l i x -/
/-       .node (nl.v * r.v) lid rid nl r hlr -/
/-     else -/
/-       let nr := set r i x -/
/-       .node (l.v * nr.v) lid rid l nr hlr -/
/--/
/- -- lid <= ql < qr <= rid is required -/
/- def prod (self : SegTreeNode M) (ql qr : Nat) : M := -/
/-   match self with -/
/-   | .leaf v _ _ => v -/
/-   | .node v lid rid l r hlr => -/
/-     let mid := midpoint lid rid hlr -/
/-     let m := mid.v -/
/-     if ql ≤ lid ∧ rid ≤ qr then v -/
/-     else if qr ≤ m then prod l ql qr -/
/-     else if m ≤ ql then prod r ql qr -/
/-     else prod l ql m * prod r m qr -/
/- end Impl -/
/--/
/--/
/- def ofArray (a : Array M) : SegTreeNode M := Id.run do -/
/-   let sz := a.size.nextPowerOfTwo -/
/-   let hsz : 0 < sz := Nat.pos_of_isPowerOfTwo (Nat.isPowerOfTwo_nextPowerOfTwo a.size) -/
/-   let a := Vector.ofFn (fun (i : Fin sz) => if h : i < a.size then a[i]'h else 1) -/
/-   Impl.init a 0 ⟨sz, by omega⟩ hsz -/
/--/
/- def replicate (n : Nat) : SegTreeNode M := -/
/-   ofArray <| Array.replicate n 1 -/
/--/
/- end PersistentSegTree -/
/--/
/- namespace SegTreeNode -/
/- def get (self : SegTreeNode M) (i : Nat) : M := -/
/-   let _ : Inhabited M := ⟨1⟩ -/
/-   if i ≥ self.rid then panic! "get: OOB" -/
/-   else PersistentSegTree.Impl.get self i -/
/--/
/- def set (self : SegTreeNode M) (i : Nat) (x : M) : SegTreeNode M := -/
/-   let _ : Inhabited M := ⟨1⟩ -/
/-   if i ≥ self.rid then panic! "set: OOB" -/
/-   else PersistentSegTree.Impl.set self i x -/
/--/
/- def prod (self : SegTreeNode M) (ql qr : Nat) : M := -/
/-   let _ : Inhabited M := ⟨1⟩ -/
/-   if ql > qr ∨ qr > self.rid then panic! "prod : OOB" -/
/-   else if ql == qr then 1 -/
/-   else PersistentSegTree.Impl.prod self ql qr -/
/- end SegTreeNode -/

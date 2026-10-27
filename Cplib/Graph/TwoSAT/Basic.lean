import Cplib.Graph.SCC.Basic
import Cplib.Util.Unwrap.Basic
import Init.Omega

namespace Cplib

/-- A persistent 2-SAT implication graph for `n` Boolean variables. -/
structure TwoSAT (n : Nat) where
  graph : Vector (List Nat) (n * 2)

namespace TwoSAT

def empty (n : Nat) : TwoSAT n := ⟨Vector.replicate (n * 2) []⟩

namespace Impl

def literal (i : Fin n) (value : Bool) : Fin (n * 2) :=
  ⟨i.val * 2 + if value then 1 else 0, by
    have := i.isLt
    split <;> omega⟩

def addImplication {n : Nat} (graph : Vector (List Nat) (n * 2))
    (source target : Fin (n * 2)) : Vector (List Nat) (n * 2) :=
  graph.set source (target.val :: graph[source])

def componentIds (count : Nat) (components : List (List Nat)) : Array Nat :=
  let (_, ids) := components.foldl (fun (id, ids) component =>
    (id + 1, component.foldl (fun ids vertex => ids.set! vertex id) ids))
    (0, Array.replicate count 0)
  ids

end Impl

/-- Add the clause `(xᵢ = iValue) ∨ (xⱼ = jValue)`. -/
def addClause (self : TwoSAT n) (i : Fin n) (iValue : Bool)
    (j : Fin n) (jValue : Bool) : TwoSAT n :=
  let iLit := Impl.literal i iValue
  let notI := Impl.literal i (!iValue)
  let jLit := Impl.literal j jValue
  let notJ := Impl.literal j (!jValue)
  let graph := Impl.addImplication self.graph notI jLit
  ⟨Impl.addImplication graph notJ iLit⟩

/-- `addClause` の範囲外安全版。`i < n` かつ `j < n` でなければ `none`。 -/
def addClause? (self : TwoSAT n) (i : Nat) (iValue : Bool)
    (j : Nat) (jValue : Bool) : Option (TwoSAT n) :=
  if h : i < n ∧ j < n then
    some (self.addClause ⟨i, h.1⟩ iValue ⟨j, h.2⟩ jValue)
  else none

/-- `addClause` の無条件版。`i < n` かつ `j < n` でなければ停止する。 -/
def addClause! (self : TwoSAT n) (i : Nat) (iValue : Bool)
    (j : Nat) (jValue : Bool) : TwoSAT n :=
  let _ : Inhabited (TwoSAT n) := ⟨self⟩
  unwrap! "TwoSAT.addClause!" (self.addClause? i iValue j jValue)

/-- A satisfying assignment, or `none` when the clauses are inconsistent. -/
def solve (self : TwoSAT n) : Option (Vector Bool n) :=
  let components := SCC.scc (n * 2) self.graph.toArray
  let ids := Impl.componentIds (n * 2) components
  -- `∃ i : Fin n, …` の `Decidable` インスタンス (core の `decidableExistsLT`) は
  -- 深さ n の非末尾再帰になりスタックを溢れさせる。`Nat.any` は `@[csimp]` で
  -- 末尾再帰の `Nat.anyTR` に落ちる。
  if Nat.any n (fun i h =>
      ids[(Impl.literal ⟨i, h⟩ false).val]! == ids[(Impl.literal ⟨i, h⟩ true).val]!) then
    none
  else
    some (Vector.ofFn fun i =>
      ids[(Impl.literal i false).val]! < ids[(Impl.literal i true).val]!)

end TwoSAT

end Cplib

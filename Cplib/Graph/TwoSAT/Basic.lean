import Cplib.Graph.SCC.Basic
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

/-- A satisfying assignment, or `none` when the clauses are inconsistent. -/
def solve (self : TwoSAT n) : Option (Vector Bool n) :=
  let components := SCC.scc (n * 2) self.graph.toArray
  let ids := Impl.componentIds (n * 2) components
  if ∃ i : Fin n, ids[(Impl.literal i false).val]! = ids[(Impl.literal i true).val]! then
    none
  else
    some (Vector.ofFn fun i =>
      ids[(Impl.literal i false).val]! < ids[(Impl.literal i true).val]!)

end TwoSAT

end Cplib

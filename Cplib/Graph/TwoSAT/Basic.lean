import Cplib.Graph.SCC.Basic
import Cplib.Util.Unwrap.Basic
import Init.Omega

namespace Cplib

/-!
# Graph.TwoSAT.Basic

2-SAT over `n` Boolean variables, solved by strongly connected components of
the implication graph.

Clauses are added one at a time and `solve` reports a satisfying assignment, or
`none` when the clauses cannot all hold at once. The instance is persistent, so
`addClause` returns a new value.

Costs, with `C` clauses added: `empty` is `O(n)`, `addClause` is `O(1)`, and
`solve` is `O(n + C)`.

```lean
let p := (TwoSAT.empty 2).addClause! 0 true 1 true     -- x₀ ∨ x₁
let p := p.addClause! 0 false 1 false                   -- ¬x₀ ∨ ¬x₁
p.solve    -- some #v[false, true]
```
-/

/-- A persistent 2-SAT implication graph for `n` Boolean variables. -/
structure TwoSAT (n : Nat) where
  graph : Vector (List Nat) (n * 2)

namespace TwoSAT

/-- An instance over `n` variables with no clauses. `O(n)`. -/
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

/-- Add the clause `(xᵢ = iValue) ∨ (xⱼ = jValue)`. `O(1)`. -/
def addClause (self : TwoSAT n) (i : Fin n) (iValue : Bool)
    (j : Fin n) (jValue : Bool) : TwoSAT n :=
  let iLit := Impl.literal i iValue
  let notI := Impl.literal i (!iValue)
  let jLit := Impl.literal j jValue
  let notJ := Impl.literal j (!jValue)
  let graph := Impl.addImplication self.graph notI jLit
  ⟨Impl.addImplication graph notJ iLit⟩

/-- `addClause` for `Nat` variables: `none` unless both `i < n` and `j < n`. -/
def addClause? (self : TwoSAT n) (i : Nat) (iValue : Bool)
    (j : Nat) (jValue : Bool) : Option (TwoSAT n) :=
  if h : i < n ∧ j < n then
    some (self.addClause ⟨i, h.1⟩ iValue ⟨j, h.2⟩ jValue)
  else none

/-- `addClause` for `Nat` variables, reporting a panic unless both `i < n` and
`j < n` and then returning the instance unchanged. See `Cplib.unwrap!`: a panic
does not stop the program. -/
def addClause! (self : TwoSAT n) (i : Nat) (iValue : Bool)
    (j : Nat) (jValue : Bool) : TwoSAT n :=
  if h : i < n ∧ j < n then self.addClause ⟨i, h.1⟩ iValue ⟨j, h.2⟩ jValue
  else outOfBounds! "TwoSAT.addClause!" self

/-- A satisfying assignment, or `none` when the clauses cannot all hold at once.
`O(n + C)` for `C` clauses added. -/
def solve (self : TwoSAT n) : Option (Vector Bool n) :=
  let components := SCC.scc (n * 2) self.graph.toArray
  let ids := Impl.componentIds (n * 2) components
  -- The `Decidable` instance behind `∃ i : Fin n, …` is core's `decidableExistsLT`,
  -- which recurses n deep without a tail call and can exhaust the stack. `Nat.any`
  -- is replaced by the tail-recursive `Nat.anyTR` through `@[csimp]`.
  if Nat.any n (fun i h =>
      ids[(Impl.literal ⟨i, h⟩ false).val]! == ids[(Impl.literal ⟨i, h⟩ true).val]!) then
    none
  else
    some (Vector.ofFn fun i =>
      ids[(Impl.literal i false).val]! < ids[(Impl.literal i true).val]!)

end TwoSAT

end Cplib

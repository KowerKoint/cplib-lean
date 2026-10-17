import Cplib.Graph.MaxFlow.Basic
import Mathlib.Tactic

namespace MaxFlow

@[simp] theorem empty_edges (n : Nat) : (empty n).edges = #[] := rfl

@[simp] theorem addEdge_original_size (self : MaxFlow n) (source target : Fin n) (capacity : Nat) :
    (self.addEdge source target capacity).2.original.size = self.original.size + 1 := by
  simp [addEdge]

@[simp] theorem addEdge_residual_size (self : MaxFlow n) (source target : Fin n) (capacity : Nat) :
    (self.addEdge source target capacity).2.residual.size = self.residual.size + 2 := by
  simp [addEdge]

private def sampleResult : Nat × Vector Bool 4 :=
  let (_, graph) := (empty 4).addEdge 0 1 2
  let (_, graph) := graph.addEdge 0 2 1
  let (_, graph) := graph.addEdge 1 2 1
  let (_, graph) := graph.addEdge 1 3 1
  let (_, graph) := graph.addEdge 2 3 2
  let (value, graph) := graph.flow 0 3
  (value, graph.minCut 0)

example : sampleResult = (3, #v[true, false, false, false]) := by
  native_decide

private def limitedResult : Nat × Nat :=
  let (_, graph) := (empty 2).addEdge 0 1 10
  let (first, graph) := graph.flowUpTo 0 1 4
  let (second, _) := graph.flow 0 1
  (first, second)

example : limitedResult = (4, 6) := by
  native_decide

end MaxFlow

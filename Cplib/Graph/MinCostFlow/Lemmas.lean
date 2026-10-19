import Cplib.Graph.MinCostFlow.Basic
import Mathlib.Tactic

namespace Cplib

namespace MinCostFlow

@[simp] theorem empty_edges (n : Nat) : (empty n).edges = #[] := rfl

@[simp] theorem addEdge_original_size (self : MinCostFlow n) (source target : Fin n)
    (capacity cost : Nat) :
    (self.addEdge source target capacity cost).2.original.size = self.original.size + 1 := by
  simp [addEdge]

@[simp] theorem addEdge_residual_size (self : MinCostFlow n) (source target : Fin n)
    (capacity cost : Nat) :
    (self.addEdge source target capacity cost).2.residual.size = self.residual.size + 2 := by
  simp [addEdge]

private def sampleNetwork : MinCostFlow 4 :=
  let (_, graph) := (empty 4).addEdge 0 1 2 1
  let (_, graph) := graph.addEdge 0 2 1 2
  let (_, graph) := graph.addEdge 1 2 1 0
  let (_, graph) := graph.addEdge 1 3 1 3
  let (_, graph) := graph.addEdge 2 3 2 1
  graph

private def sampleResult : Nat × Int := (sampleNetwork.flow 0 3).1

example : sampleResult = (3, 9) := by native_decide

private def continuationResult : (Nat × Int) × (Nat × Int) :=
  let (first, graph) := sampleNetwork.flowUpTo 0 3 2
  let (second, _) := graph.flow 0 3
  (first, second)

example : continuationResult = ((2, 5), (1, 4)) := by native_decide

end MinCostFlow

end Cplib

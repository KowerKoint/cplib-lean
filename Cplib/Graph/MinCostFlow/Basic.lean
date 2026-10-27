import Cplib.Structure.Heap.Basic
import Cplib.Util.Unwrap.Basic

namespace Cplib

/-!
# Graph.MinCostFlow.Basic

Minimum-cost flow on a directed network over the vertices `0, …, n - 1`, by
successive shortest paths with Johnson potentials and Dijkstra.

**Inserted edge costs must be nonnegative.** The potentials keep the reduced
costs nonnegative so that Dijkstra stays applicable; a negative input cost
breaks that invariant and the result is unspecified.

As in `MaxFlow` the network is persistent, and every edge keeps the stable ID
that `addEdge` handed out so `edge?` and `edges` can report its current flow.
`flow` and `flowUpTo` return `(flow, cost)` together with the updated network.

Costs, with `V = n` vertices, `E` inserted edges and `F` units actually sent:
`addEdge` is `O(1)`, `edges` is `O(E)`, and `flow` is `O(F E log V)`.

```lean
let g := MinCostFlow.empty 3
let (_, g) := g.addEdge! 0 1 2 5       -- capacity 2, cost 5 per unit
let (_, g) := g.addEdge! 1 2 2 3
let ((amount, cost), g) := g.flow! 0 2  -- (2, 16)
```
-/

structure MinCostFlow.ResidualEdge (n : Nat) where
  target : Fin n
  reverse : Nat
  capacity : Nat
  cost : Int

structure MinCostFlow.EdgeInfo (n : Nat) where
  source : Fin n
  target : Fin n
  capacity : Nat
  flow : Nat
  cost : Nat
deriving Repr, BEq, DecidableEq

/-- Persistent min-cost-flow network for nonnegative inserted edge costs. -/
structure MinCostFlow (n : Nat) where
  adjacency : Vector (List Nat) n
  residual : Array (MinCostFlow.ResidualEdge n)
  original : Array (Fin n × Fin n × Nat × Nat)
  potential : Vector Int n

namespace MinCostFlow

/-- A network over `n` vertices with no edges. `O(n)`. -/
def empty (n : Nat) : MinCostFlow n :=
  ⟨Vector.replicate n [], #[], #[], Vector.replicate n 0⟩

/-- Add a directed edge with the given capacity and per-unit cost, and return its
stable ID. `O(1)`. -/
def addEdge (self : MinCostFlow n) (source target : Fin n)
    (capacity cost : Nat) : Nat × MinCostFlow n :=
  let edgeId := self.original.size
  let forwardId := self.residual.size
  let reverseId := forwardId + 1
  let residual := self.residual
    |>.push ⟨target, reverseId, capacity, cost⟩
    |>.push ⟨source, forwardId, 0, -(cost : Int)⟩
  let adjacency := self.adjacency.set source (forwardId :: self.adjacency[source])
  let adjacency := adjacency.set target (reverseId :: adjacency[target])
  (edgeId, { self with
    adjacency, residual
    original := self.original.push (source, target, capacity, cost) })

/-- Current state of the edge with the given ID, or `none` when no such edge was
inserted. `O(1)`. -/
def edge? (self : MinCostFlow n) (edgeId : Nat) : Option (EdgeInfo n) := do
  let (source, target, capacity, cost) ← self.original[edgeId]?
  let residual ← self.residual[edgeId * 2]?
  pure ⟨source, target, capacity, capacity - residual.capacity, cost⟩

/-- Current state of every inserted edge, in insertion order. `O(E)`. -/
def edges (self : MinCostFlow n) : Array (EdgeInfo n) :=
  (Array.range self.original.size).filterMap self.edge?

namespace Impl

abbrev QueueEntry (n : Nat) := Int × Fin n

def queueCompare (x y : QueueEntry n) : Ordering := compare x.1 y.1

def dijkstraLoop (self : MinCostFlow n) : Nat → Heap (QueueEntry n) →
    Array (Option Int) → Array Nat → Array (Option Int) × Array Nat
  | 0, _, distance, previous => (distance, previous)
  | fuel + 1, queue, distance, previous =>
      match queue.top? with
      | none => (distance, previous)
      | some (currentDistance, vertex) =>
          let queue := queue.pop!
          if distance.getD vertex none ≠ some currentDistance then
            dijkstraLoop self fuel queue distance previous
          else
            let (queue, distance, previous) := self.adjacency[vertex].foldl
              (fun (queue, distance, previous) edgeId =>
                match self.residual[edgeId]? with
                | none => (queue, distance, previous)
                | some edge =>
                    if edge.capacity = 0 then (queue, distance, previous)
                    else
                      let reduced := edge.cost + self.potential[vertex] - self.potential[edge.target]
                      let candidate := currentDistance + reduced
                      match distance.getD edge.target none with
                      | some old =>
                          if old ≤ candidate then (queue, distance, previous)
                          else (queue.add (candidate, edge.target),
                            distance.set! edge.target (some candidate), previous.set! edge.target edgeId)
                      | none => (queue.add (candidate, edge.target),
                          distance.set! edge.target (some candidate), previous.set! edge.target edgeId))
              (queue, distance, previous)
            dijkstraLoop self fuel queue distance previous

def dijkstra (self : MinCostFlow n) (source : Fin n) : Array (Option Int) × Array Nat :=
  let queue := (Heap.empty queueCompare).add (0, source)
  let distance := (Array.replicate n none).set! source (some 0)
  dijkstraLoop self (self.residual.size + n + 1) queue distance (Array.replicate n 0)

def updatePotential (self : MinCostFlow n) (distance : Array (Option Int)) : MinCostFlow n :=
  { self with potential := Vector.ofFn fun i =>
      match distance.getD i none with
      | some d => self.potential[i] + d
      | none => self.potential[i] }

def bottleneck (self : MinCostFlow n) (previous : Array Nat)
    (source sink : Fin n) (limit : Nat) : Nat :=
  let rec loop : Nat → Fin n → Nat → Nat
    | 0, _, amount => amount
    | fuel + 1, vertex, amount =>
        if vertex = source then amount
        else
          let edgeId := previous.getD vertex 0
          match self.residual[edgeId]? with
          | none => 0
          | some edge =>
              match self.residual[edge.reverse]? with
              | none => 0
              | some reverse => loop fuel reverse.target (min amount edge.capacity)
  loop n sink limit

def augment (self : MinCostFlow n) (previous : Array Nat) (source sink : Fin n)
    (amount : Nat) : MinCostFlow n :=
  let rec loop : Nat → Fin n → MinCostFlow n → MinCostFlow n
    | 0, _, self => self
    | fuel + 1, vertex, self =>
        if vertex = source then self
        else
          let edgeId := previous.getD vertex 0
          match self.residual[edgeId]? with
          | none => self
          | some edge =>
              match self.residual[edge.reverse]? with
              | none => self
              | some reverse =>
                  let residual := self.residual.set! edgeId
                    { edge with capacity := edge.capacity - amount }
                  let residual := residual.set! edge.reverse
                    { reverse with capacity := reverse.capacity + amount }
                  loop fuel reverse.target { self with residual }
  loop n sink self

end Impl

/-- Sum of inserted capacities, used as a finite upper bound for unrestricted
flow. `O(E)`. -/
def totalCapacity (self : MinCostFlow n) : Nat :=
  self.original.foldl (fun total edge => total + edge.2.2.1) 0

/-- Send at most `limit` further units from `source` to `sink` along cheapest
paths, returning `(flow, cost)` and the updated network. `O(F E log V)` for `F`
units sent. -/
def flowUpTo (self : MinCostFlow n) (source sink : Fin n) (limit : Nat) :
    (Nat × Int) × MinCostFlow n :=
  let rec loop : Nat → Nat → Int → MinCostFlow n → (Nat × Int) × MinCostFlow n
    | 0, flow, cost, self => ((flow, cost), self)
    | fuel + 1, flow, cost, self =>
        if flow = limit then ((flow, cost), self)
        else
          let (distance, previous) := Impl.dijkstra self source
          match distance.getD sink none with
          | none => ((flow, cost), self)
          | some _ =>
              let self := Impl.updatePotential self distance
              let amount := Impl.bottleneck self previous source sink (limit - flow)
              if amount = 0 then ((flow, cost), self)
              else
                let pathCost := self.potential[sink] - self.potential[source]
                let self := Impl.augment self previous source sink amount
                loop fuel (flow + amount) (cost + (amount : Int) * pathCost) self
  if source = sink then ((0, 0), self)
  else loop (self.totalCapacity + 1) 0 0 self

/-- Send as much further flow from `source` to `sink` as the network allows, at
minimum total cost, returning `(flow, cost)` and the updated network. -/
def flow (self : MinCostFlow n) (source sink : Fin n) :
    (Nat × Int) × MinCostFlow n :=
  self.flowUpTo source sink self.totalCapacity

/-- `addEdge` for `Nat` vertices: `none` unless both `source < n` and
`target < n`. -/
def addEdge? (self : MinCostFlow n) (source target : Nat) (capacity cost : Nat) :
    Option (Nat × MinCostFlow n) :=
  if h : source < n ∧ target < n then
    some (self.addEdge ⟨source, h.1⟩ ⟨target, h.2⟩ capacity cost)
  else none

/-- `addEdge` for `Nat` vertices, reporting a panic unless both `source < n` and
`target < n` and then returning `(0, self)`. See `Cplib.unwrap!`: a panic does
not stop the program. -/
def addEdge! (self : MinCostFlow n) (source target : Nat) (capacity cost : Nat) :
    Nat × MinCostFlow n :=
  let _ : Inhabited (Nat × MinCostFlow n) := ⟨(0, self)⟩
  unwrap! "MinCostFlow.addEdge!" (self.addEdge? source target capacity cost)

/-- `flowUpTo` for `Nat` vertices: `none` unless both `source < n` and
`sink < n`. -/
def flowUpTo? (self : MinCostFlow n) (source sink : Nat) (limit : Nat) :
    Option ((Nat × Int) × MinCostFlow n) :=
  if h : source < n ∧ sink < n then
    some (self.flowUpTo ⟨source, h.1⟩ ⟨sink, h.2⟩ limit)
  else none

/-- `flowUpTo` for `Nat` vertices, reporting a panic unless both `source < n` and
`sink < n` and then returning `((0, 0), self)`. See `Cplib.unwrap!`: a panic
does not stop the program. -/
def flowUpTo! (self : MinCostFlow n) (source sink : Nat) (limit : Nat) :
    (Nat × Int) × MinCostFlow n :=
  let _ : Inhabited ((Nat × Int) × MinCostFlow n) := ⟨((0, 0), self)⟩
  unwrap! "MinCostFlow.flowUpTo!" (self.flowUpTo? source sink limit)

/-- `flow` for `Nat` vertices: `none` unless both `source < n` and `sink < n`. -/
def flow? (self : MinCostFlow n) (source sink : Nat) :
    Option ((Nat × Int) × MinCostFlow n) :=
  if h : source < n ∧ sink < n then
    some (self.flow ⟨source, h.1⟩ ⟨sink, h.2⟩)
  else none

/-- `flow` for `Nat` vertices, reporting a panic unless both `source < n` and
`sink < n` and then returning `((0, 0), self)`. See `Cplib.unwrap!`: a panic
does not stop the program. -/
def flow! (self : MinCostFlow n) (source sink : Nat) : (Nat × Int) × MinCostFlow n :=
  let _ : Inhabited ((Nat × Int) × MinCostFlow n) := ⟨((0, 0), self)⟩
  unwrap! "MinCostFlow.flow!" (self.flow? source sink)

end MinCostFlow

end Cplib

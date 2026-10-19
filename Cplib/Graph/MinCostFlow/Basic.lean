import Cplib.Structure.Heap.Basic

namespace Cplib

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

def empty (n : Nat) : MinCostFlow n :=
  ⟨Vector.replicate n [], #[], #[], Vector.replicate n 0⟩

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

def edge? (self : MinCostFlow n) (edgeId : Nat) : Option (EdgeInfo n) := do
  let (source, target, capacity, cost) ← self.original[edgeId]?
  let residual ← self.residual[edgeId * 2]?
  pure ⟨source, target, capacity, capacity - residual.capacity, cost⟩

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

def totalCapacity (self : MinCostFlow n) : Nat :=
  self.original.foldl (fun total edge => total + edge.2.2.1) 0

/-- Send up to `limit` units, returning `(flow, cost)` and the updated network. -/
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

/-- Minimum cost of the maximum additional flow. -/
def flow (self : MinCostFlow n) (source sink : Fin n) :
    (Nat × Int) × MinCostFlow n :=
  self.flowUpTo source sink self.totalCapacity

end MinCostFlow

end Cplib

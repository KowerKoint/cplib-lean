import Cplib.Util.Unwrap.Basic

namespace Cplib

/-!
# Graph.MaxFlow.Basic

Maximum flow on a directed network over the vertices `0, …, n - 1`, by Dinic's
algorithm.

The network is persistent: `addEdge` and the flow routines return a new value
rather than mutating, and every edge keeps the **stable ID** that `addEdge`
handed out, so `edge?` and `edges` can report its current flow afterwards.

Capacities are `Nat`. Running `flow` twice sends the maximum flow once and then
nothing, since the second call works on the already-saturated residual network.

Costs, with `V = n` vertices and `E` inserted edges: `addEdge` is `O(1)`,
`edges` is `O(E)`, `minCut` is `O(V + E)`, and `flow` is `O(V² E)` in general,
improving to `O(E √V)` on unit capacities.

```lean
let g := MaxFlow.empty 4
let (_, g) := g.addEdge! 0 1 2
let (_, g) := g.addEdge! 1 3 2
let (amount, g) := g.flow! 0 3    -- 2
g.minCut! 0                        -- vertices reachable from 0 afterwards
```
-/

/-- A residual edge used internally by Dinic's algorithm. -/
structure MaxFlow.ResidualEdge (n : Nat) where
  target : Fin n
  reverse : Nat
  capacity : Nat

/-- Public information for an inserted edge. -/
structure MaxFlow.EdgeInfo (n : Nat) where
  source : Fin n
  target : Fin n
  capacity : Nat
  flow : Nat
deriving Repr, BEq, DecidableEq

/-- Persistent residual network with stable insertion-order edge IDs. -/
structure MaxFlow (n : Nat) where
  adjacency : Vector (List Nat) n
  residual : Array (MaxFlow.ResidualEdge n)
  original : Array (Fin n × Fin n × Nat)

namespace MaxFlow

def empty (n : Nat) : MaxFlow n := ⟨Vector.replicate n [], #[], #[]⟩

/-- Add a directed edge from `source` to `target` with the given capacity, and
return its stable ID. `O(1)`. -/
def addEdge (self : MaxFlow n) (source target : Fin n) (capacity : Nat) : Nat × MaxFlow n :=
  let edgeId := self.original.size
  let forwardId := self.residual.size
  let reverseId := forwardId + 1
  let residual := self.residual.push ⟨target, reverseId, capacity⟩ |>.push ⟨source, forwardId, 0⟩
  let adjacency := self.adjacency.set source (forwardId :: self.adjacency[source])
  let adjacency := adjacency.set target (reverseId :: adjacency[target])
  (edgeId, ⟨adjacency, residual, self.original.push (source, target, capacity)⟩)

/-- Current state of the edge with the given ID, or `none` when no such edge was
inserted. `O(1)`. -/
def edge? (self : MaxFlow n) (edgeId : Nat) : Option (EdgeInfo n) := do
  let (source, target, capacity) ← self.original[edgeId]?
  let residual ← self.residual[edgeId * 2]?
  pure ⟨source, target, capacity, capacity - residual.capacity⟩

/-- Current state of every inserted edge, in insertion order. `O(E)`. -/
def edges (self : MaxFlow n) : Array (EdgeInfo n) :=
  (Array.range self.original.size).filterMap self.edge?

/-- Replace the capacity and current flow of an inserted edge. `flow` must not
exceed `capacity`. `O(1)`. -/
def changeEdge (self : MaxFlow n) (edgeId : Fin self.original.size)
    (capacity : Nat) (flow : Fin (capacity + 1)) : MaxFlow n :=
  let (source, target, _) := self.original[edgeId]
  let forwardId := edgeId.val * 2
  match self.residual[forwardId]?, self.residual[forwardId + 1]? with
  | some forward, some reverse =>
      { self with
        original := self.original.set edgeId (source, target, capacity)
        residual := self.residual
          |>.set! forwardId { forward with capacity := capacity - flow.val }
          |>.set! (forwardId + 1) { reverse with capacity := flow.val } }
  | _, _ => self

namespace Impl

def bfsLoop (self : MaxFlow n) : Nat → Array Nat → Nat → Array Nat → Array Nat
  | 0, _, _, level => level
  | fuel + 1, queue, head, level =>
      if hhead : head < queue.size then
        let vertex := queue[head]
        let (queue, level) := self.adjacency.getD vertex [] |>.foldl (fun (queue, level) edgeId =>
          match self.residual[edgeId]? with
          | some edge =>
              if edge.capacity = 0 || level.getD edge.target n ≠ n then (queue, level)
              else (queue.push edge.target, level.set! edge.target (level.getD vertex 0 + 1))
          | none => (queue, level)) (queue, level)
        bfsLoop self fuel queue (head + 1) level
      else level

def levels (self : MaxFlow n) (source : Fin n) : Array Nat :=
  bfsLoop self n #[source] 0 ((Array.replicate n n).set! source 0)

def augment (self : MaxFlow n) (edgeId amount : Nat) : MaxFlow n :=
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
          { self with residual }

def dfsFuel (levels : Array Nat) (sink : Fin n) : Nat →
    MaxFlow n → Array Nat → Fin n → Nat → Nat × MaxFlow n × Array Nat
  | 0, self, cursor, _, _ => (0, self, cursor)
  | fuel + 1, self, cursor, vertex, limit =>
      if limit = 0 then (0, self, cursor)
      else if vertex = sink then (limit, self, cursor)
      else
        let rec scan : Nat → MaxFlow n → Array Nat → Nat × MaxFlow n × Array Nat
          | 0, self, cursor => (0, self, cursor)
          | attempts + 1, self, cursor =>
              let position := cursor.getD vertex 0
              match self.adjacency[vertex][position]? with
              | none => (0, self, cursor)
              | some edgeId =>
                  let cursor := cursor.set! vertex (position + 1)
                  match self.residual[edgeId]? with
                  | none => scan attempts self cursor
                  | some edge =>
                      if edge.capacity = 0 || levels.getD edge.target n ≠ levels.getD vertex n + 1 then
                        scan attempts self cursor
                      else
                        let (pushed, self, cursor) :=
                          dfsFuel levels sink fuel self cursor edge.target (min limit edge.capacity)
                        if pushed = 0 then scan attempts self cursor
                        else (pushed, augment self edgeId pushed, cursor)
        scan (self.residual.size + 1) self cursor

def blockingFlow (levels : Array Nat) (source sink : Fin n) (limit : Nat)
    (self : MaxFlow n) : Nat × MaxFlow n :=
  let rec loop : Nat → Nat → MaxFlow n → Array Nat → Nat × MaxFlow n
    | 0, total, self, _ => (total, self)
    | fuel + 1, total, self, cursor =>
        if total = limit then (total, self)
        else
          let dfsFuelAmount := (self.residual.size + n + 1) * (n + 1)
          let (pushed, self, cursor) :=
            dfsFuel levels sink dfsFuelAmount self cursor source (limit - total)
          if pushed = 0 then (total, self)
          else loop fuel (total + pushed) self cursor
  loop (self.residual.size + 1) 0 self (Array.replicate n 0)

end Impl

/-- Sum of inserted capacities, used as a finite upper bound for unrestricted
flow. `O(E)`. -/
def totalCapacity (self : MaxFlow n) : Nat :=
  self.original.foldl (fun total edge => total + edge.2.2) 0

/-- Send at most `limit` further units from `source` to `sink`, returning how
much was sent together with the updated network. `O(V² E)`. -/
def flowUpTo (self : MaxFlow n) (source sink : Fin n) (limit : Nat) :
    Nat × MaxFlow n :=
  let rec loop : Nat → Nat → MaxFlow n → Nat × MaxFlow n
    | 0, total, self => (total, self)
    | phases + 1, total, self =>
        if total = limit then (total, self)
        else
          let levels := Impl.levels self source
          if levels.getD sink n = n then (total, self)
          else
            let (pushed, self) := Impl.blockingFlow levels source sink (limit - total) self
            if pushed = 0 then (total, self)
            else loop phases (total + pushed) self
  if source = sink then (0, self) else loop (n + 1) 0 self

/-- Send as much further flow from `source` to `sink` as the network allows.
`O(V² E)`, improving to `O(E √V)` on unit capacities. -/
def flow (self : MaxFlow n) (source sink : Fin n) : Nat × MaxFlow n :=
  self.flowUpTo source sink self.totalCapacity

/-- Vertices reachable from `source` in the current residual network. After a
saturating `flow`, this is the source side of a minimum cut. `O(V + E)`. -/
def minCut (self : MaxFlow n) (source : Fin n) : Vector Bool n :=
  let levels := Impl.levels self source
  Vector.ofFn fun i => levels.getD i n ≠ n

/-- `addEdge` for `Nat` vertices: `none` unless both `source < n` and
`target < n`. -/
def addEdge? (self : MaxFlow n) (source target : Nat) (capacity : Nat) :
    Option (Nat × MaxFlow n) :=
  if h : source < n ∧ target < n then
    some (self.addEdge ⟨source, h.1⟩ ⟨target, h.2⟩ capacity)
  else none

/-- `addEdge` for `Nat` vertices, reporting a panic unless both `source < n` and
`target < n` and then returning `(0, self)`. See `Cplib.unwrap!`: a panic does
not stop the program. -/
def addEdge! (self : MaxFlow n) (source target : Nat) (capacity : Nat) : Nat × MaxFlow n :=
  if h : source < n ∧ target < n then
    self.addEdge ⟨source, h.1⟩ ⟨target, h.2⟩ capacity
  else outOfBounds! "MaxFlow.addEdge!" (0, self)

/-- `changeEdge` for `Nat` arguments: `none` unless `edgeId` names an inserted
edge and `flow ≤ capacity`. -/
def changeEdge? (self : MaxFlow n) (edgeId : Nat) (capacity flow : Nat) :
    Option (MaxFlow n) :=
  if h : edgeId < self.original.size ∧ flow < capacity + 1 then
    some (self.changeEdge ⟨edgeId, h.1⟩ capacity ⟨flow, h.2⟩)
  else none

/-- `changeEdge` for `Nat` arguments, reporting a panic unless those conditions
hold and then returning the network unchanged. See `Cplib.unwrap!`: a panic does
not stop the program. -/
def changeEdge! (self : MaxFlow n) (edgeId : Nat) (capacity flow : Nat) : MaxFlow n :=
  if h : edgeId < self.original.size ∧ flow < capacity + 1 then
    self.changeEdge ⟨edgeId, h.1⟩ capacity ⟨flow, h.2⟩
  else outOfBounds! "MaxFlow.changeEdge!" self

/-- `flowUpTo` for `Nat` vertices: `none` unless both `source < n` and
`sink < n`. -/
def flowUpTo? (self : MaxFlow n) (source sink : Nat) (limit : Nat) :
    Option (Nat × MaxFlow n) :=
  if h : source < n ∧ sink < n then
    some (self.flowUpTo ⟨source, h.1⟩ ⟨sink, h.2⟩ limit)
  else none

/-- `flowUpTo` for `Nat` vertices, reporting a panic unless both `source < n` and
`sink < n` and then returning `(0, self)`. See `Cplib.unwrap!`: a panic does not
stop the program. -/
def flowUpTo! (self : MaxFlow n) (source sink : Nat) (limit : Nat) : Nat × MaxFlow n :=
  if h : source < n ∧ sink < n then self.flowUpTo ⟨source, h.1⟩ ⟨sink, h.2⟩ limit
  else outOfBounds! "MaxFlow.flowUpTo!" (0, self)

/-- `flow` for `Nat` vertices: `none` unless both `source < n` and `sink < n`. -/
def flow? (self : MaxFlow n) (source sink : Nat) : Option (Nat × MaxFlow n) :=
  if h : source < n ∧ sink < n then
    some (self.flow ⟨source, h.1⟩ ⟨sink, h.2⟩)
  else none

/-- `flow` for `Nat` vertices, reporting a panic unless both `source < n` and
`sink < n` and then returning `(0, self)`. See `Cplib.unwrap!`: a panic does not
stop the program. -/
def flow! (self : MaxFlow n) (source sink : Nat) : Nat × MaxFlow n :=
  if h : source < n ∧ sink < n then self.flow ⟨source, h.1⟩ ⟨sink, h.2⟩
  else outOfBounds! "MaxFlow.flow!" (0, self)

/-- `minCut` for a `Nat` vertex: `none` unless `source < n`. -/
def minCut? (self : MaxFlow n) (source : Nat) : Option (Vector Bool n) :=
  if h : source < n then some (self.minCut ⟨source, h⟩) else none

/-- `minCut` for a `Nat` vertex, reporting a panic unless `source < n` and then
returning an all-`false` vector. See `Cplib.unwrap!`: a panic does not stop the
program. -/
def minCut! (self : MaxFlow n) (source : Nat) : Vector Bool n :=
  let _ : Inhabited (Vector Bool n) := ⟨Vector.replicate n false⟩
  unwrap! "MaxFlow.minCut!" (self.minCut? source)

end MaxFlow

end Cplib

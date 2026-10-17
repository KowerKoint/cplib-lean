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
deriving Repr, BEq

/-- Persistent residual network with stable insertion-order edge IDs. -/
structure MaxFlow (n : Nat) where
  adjacency : Vector (List Nat) n
  residual : Array (MaxFlow.ResidualEdge n)
  original : Array (Fin n × Fin n × Nat)

namespace MaxFlow

def empty (n : Nat) : MaxFlow n := ⟨Vector.replicate n [], #[], #[]⟩

/-- Add a directed edge and return its stable ID. -/
def addEdge (self : MaxFlow n) (source target : Fin n) (capacity : Nat) : Nat × MaxFlow n :=
  let edgeId := self.original.size
  let forwardId := self.residual.size
  let reverseId := forwardId + 1
  let residual := self.residual.push ⟨target, reverseId, capacity⟩ |>.push ⟨source, forwardId, 0⟩
  let adjacency := self.adjacency.set source (forwardId :: self.adjacency[source])
  let adjacency := adjacency.set target (reverseId :: adjacency[target])
  (edgeId, ⟨adjacency, residual, self.original.push (source, target, capacity)⟩)

def edge? (self : MaxFlow n) (edgeId : Nat) : Option (EdgeInfo n) := do
  let (source, target, capacity) ← self.original[edgeId]?
  let residual ← self.residual[edgeId * 2]?
  pure ⟨source, target, capacity, capacity - residual.capacity⟩

def edges (self : MaxFlow n) : Array (EdgeInfo n) :=
  (Array.range self.original.size).filterMap self.edge?

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

/-- Sum of inserted capacities, used as a finite upper bound for unrestricted flow. -/
def totalCapacity (self : MaxFlow n) : Nat :=
  self.original.foldl (fun total edge => total + edge.2.2) 0

/-- Send at most `limit` additional units from `source` to `sink`. -/
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

/-- Send the maximum possible additional flow from `source` to `sink`. -/
def flow (self : MaxFlow n) (source sink : Fin n) : Nat × MaxFlow n :=
  self.flowUpTo source sink self.totalCapacity

/-- Vertices reachable from `source` in the current residual network. -/
def minCut (self : MaxFlow n) (source : Fin n) : Vector Bool n :=
  let levels := Impl.levels self source
  Vector.ofFn fun i => levels.getD i n ≠ n

end MaxFlow

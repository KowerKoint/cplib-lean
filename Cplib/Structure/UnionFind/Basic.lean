/-- Persistent union-find (disjoint-set union) with path compression and union by size. -/
structure UnionFind (n : Nat) where
  parent : Vector (Fin n) n
  componentSize : Vector Nat n

namespace UnionFind

/-- `n` singleton components. -/
def empty (n : Nat) : UnionFind n where
  parent := Vector.ofFn id
  componentSize := Vector.replicate n 1

namespace Impl

/-- Find a representative and compress the traversed path.

The fuel is an operational guard for totality. For states produced by this API,
union by size keeps every path shorter than `n`.
-/
def leaderFuel (fuel : Nat) (self : UnionFind n) (a : Fin n) : Fin n × UnionFind n :=
  match fuel with
  | 0 => (a, self)
  | fuel + 1 =>
      let p := self.parent[a]
      if p = a then (a, self)
      else
        let (root, self) := leaderFuel fuel self p
        (root, { self with parent := self.parent.set a root })

end Impl

/-- Representative of `a`, together with the state after path compression. -/
def leader (self : UnionFind n) (a : Fin n) : Fin n × UnionFind n :=
  Impl.leaderFuel n self a

/-- Whether `a` and `b` are connected, together with the compressed state. -/
def same (self : UnionFind n) (a b : Fin n) : Bool × UnionFind n :=
  let (x, self) := self.leader a
  let (y, self) := self.leader b
  (x == y, self)

/-- Component size of `a`, together with the compressed state. -/
def size (self : UnionFind n) (a : Fin n) : Nat × UnionFind n :=
  let (root, self) := self.leader a
  (self.componentSize[root], self)

/-- Merge the components of `a` and `b` using union by size. -/
def merge (self : UnionFind n) (a b : Fin n) : UnionFind n :=
  let (x, self) := self.leader a
  let (y, self) := self.leader b
  if x = y then self
  else if self.componentSize[x] < self.componentSize[y] then
    { self with
      parent := self.parent.set x y
      componentSize := self.componentSize.set y (self.componentSize[x] + self.componentSize[y]) }
  else
    { self with
      parent := self.parent.set y x
      componentSize := self.componentSize.set x (self.componentSize[x] + self.componentSize[y]) }

namespace Impl

def collectGroups (vertices : List (Fin n)) (self : UnionFind n)
    (groups : Array (Fin n × Array Nat)) : Array (Fin n × Array Nat) × UnionFind n :=
  match vertices with
  | [] => (groups, self)
  | i :: vertices =>
      let (root, self) := self.leader i
      let groups :=
        match groups.findIdx? (fun group => group.1 == root) with
        | some j => groups.modify j (fun group => (group.1, group.2.push i.val))
        | none => groups.push (root, #[i.val])
      collectGroups vertices self groups

end Impl

/-- Components as arrays of vertices, together with the fully compressed state. -/
def groups (self : UnionFind n) : Array (Array Nat) × UnionFind n :=
  let (groups, self) := Impl.collectGroups (List.finRange n) self #[]
  (groups.map (·.2), self)

end UnionFind

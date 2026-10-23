
namespace Cplib
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

/-- Bucket every vertex under its root.

Buckets are indexed by the root itself, so this is `O(n α(n))` overall. `order`
records each root the first time it is seen, which fixes the order of the
returned components. -/
def collectGroups (self : UnionFind n) :
    Array (Fin n) × Vector (Array Nat) n × UnionFind n :=
  Nat.fold n (fun i h (order, buckets, self) =>
    let (root, self) := self.leader ⟨i, h⟩
    if buckets[root].isEmpty then
      (order.push root, buckets.set root #[i], self)
    else
      (order, buckets.set root (buckets[root].push i), self))
    (#[], Vector.replicate n #[], self)

end Impl

/-- Components as arrays of vertices, together with the fully compressed state.

Components appear in order of the first vertex belonging to each, and each
component lists its vertices in increasing order. -/
def groups (self : UnionFind n) : Array (Array Nat) × UnionFind n :=
  let (order, buckets, self) := Impl.collectGroups self
  (order.map (buckets[·]), self)

end UnionFind

end Cplib

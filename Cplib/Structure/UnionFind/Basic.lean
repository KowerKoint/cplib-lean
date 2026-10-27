import Cplib.Util.Unwrap.Basic

namespace Cplib

/-!
# Structure.UnionFind.Basic

A persistent union-find (disjoint-set union) over the vertices `0, …, n - 1`,
with path compression and union by size.

Because path compression rewrites the structure, every query **returns the
updated state alongside its answer** and callers must thread it through:
`let (root, uf) := uf.leader! v`. Discarding the returned state is correct but
throws the compression away, and reusing an older state repeatedly forfeits the
amortised bound.

Costs, used linearly as above: `empty` is `O(n)`, `leader`, `same`, `size` and
`merge` are `O(α(n))` amortised, and `groups` is `O(n α(n))`.

```lean
let uf := (UnionFind.empty 5).merge! 0 1 |>.merge! 3 4
let (connected, uf) := uf.same! 0 1    -- true
let (card, uf) := uf.size! 3           -- 2
uf.groups.1                            -- #[#[0, 1], #[2], #[3, 4]]
```
-/

/-- Persistent union-find (disjoint-set union) with path compression and union by size. -/
structure UnionFind (n : Nat) where
  parent : Vector (Fin n) n
  componentSize : Vector Nat n

namespace UnionFind

/-- `n` singleton components. `O(n)`. -/
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

/-- Representative of `a`, together with the state after path compression.
`O(α(n))` amortised. -/
def leader (self : UnionFind n) (a : Fin n) : Fin n × UnionFind n :=
  Impl.leaderFuel n self a

/-- Whether `a` and `b` lie in the same component, together with the compressed
state. `O(α(n))` amortised. -/
def same (self : UnionFind n) (a b : Fin n) : Bool × UnionFind n :=
  let (x, self) := self.leader a
  let (y, self) := self.leader b
  (x == y, self)

/-- Number of vertices in the component of `a`, together with the compressed
state. `O(α(n))` amortised. -/
def size (self : UnionFind n) (a : Fin n) : Nat × UnionFind n :=
  let (root, self) := self.leader a
  (self.componentSize[root], self)

/-- Merge the components of `a` and `b`, attaching the smaller under the larger.
A no-op when they are already connected. `O(α(n))` amortised. -/
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

/-- `leader` for a `Nat` vertex: `none` unless `a < n`. -/
def leader? (self : UnionFind n) (a : Nat) : Option (Fin n × UnionFind n) :=
  if h : a < n then some (self.leader ⟨a, h⟩) else none

/-- `leader` for a `Nat` vertex, reporting a panic unless `a < n` and then
returning `(0, self)`. See `Cplib.unwrap!`: a panic does not stop the program.

The representative comes back as a `Nat` rather than a `Fin n`, because `Fin n`
has no value to fall back on when `n = 0`. -/
def leader! (self : UnionFind n) (a : Nat) : Nat × UnionFind n :=
  let _ : Inhabited (Nat × UnionFind n) := ⟨(0, self)⟩
  unwrap! "UnionFind.leader!" ((self.leader? a).map (fun (root, self) => (root.val, self)))

/-- `same` for `Nat` vertices: `none` unless both `a < n` and `b < n`. -/
def same? (self : UnionFind n) (a b : Nat) : Option (Bool × UnionFind n) :=
  if h : a < n ∧ b < n then some (self.same ⟨a, h.1⟩ ⟨b, h.2⟩) else none

/-- `same` for `Nat` vertices, reporting a panic unless both `a < n` and `b < n`
and then returning `(false, self)`. See `Cplib.unwrap!`: a panic does not stop
the program. -/
def same! (self : UnionFind n) (a b : Nat) : Bool × UnionFind n :=
  let _ : Inhabited (Bool × UnionFind n) := ⟨(false, self)⟩
  unwrap! "UnionFind.same!" (self.same? a b)

/-- `size` for a `Nat` vertex: `none` unless `a < n`. -/
def size? (self : UnionFind n) (a : Nat) : Option (Nat × UnionFind n) :=
  if h : a < n then some (self.size ⟨a, h⟩) else none

/-- `size` for a `Nat` vertex, reporting a panic unless `a < n` and then returning
`(0, self)`. See `Cplib.unwrap!`: a panic does not stop the program. -/
def size! (self : UnionFind n) (a : Nat) : Nat × UnionFind n :=
  let _ : Inhabited (Nat × UnionFind n) := ⟨(0, self)⟩
  unwrap! "UnionFind.size!" (self.size? a)

/-- `merge` for `Nat` vertices: `none` unless both `a < n` and `b < n`. -/
def merge? (self : UnionFind n) (a b : Nat) : Option (UnionFind n) :=
  if h : a < n ∧ b < n then some (self.merge ⟨a, h.1⟩ ⟨b, h.2⟩) else none

/-- `merge` for `Nat` vertices, reporting a panic unless both `a < n` and `b < n`
and then returning the structure unchanged. See `Cplib.unwrap!`: a panic does
not stop the program. -/
def merge! (self : UnionFind n) (a b : Nat) : UnionFind n :=
  let _ : Inhabited (UnionFind n) := ⟨self⟩
  unwrap! "UnionFind.merge!" (self.merge? a b)

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

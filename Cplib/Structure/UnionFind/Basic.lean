import Cplib.Util.Unwrap.Basic

namespace Cplib

/-!
# Structure.UnionFind.Basic

A union-find (disjoint-set union) over the vertices `0, …, n - 1`, by size.

The operations come in two families, over the same structure, and they agree on
which vertices are connected:

| | compressing | persistent |
|---|---|---|
| representative | `leader` | `persistentLeader` |
| connected? | `same` | `persistentSame` |
| component size | `size` | `persistentSize` |
| merge | `merge` | `persistentMerge` |

**The compressing family rewrites the paths it walks**, so every query returns
the updated state alongside its answer and callers must thread it through:
`let (r, uf) := uf.leader v`. Used that way it is `O(α(n))` amortised.

**The persistent family rewrites nothing**: `uf.persistentLeader v` is a
`Fin n`, not a pair. Union by size alone keeps every path within `O(log n)`,
which is the cost of each operation in this family.

Which to use is a question of how the value is used, not of taste. Compression
pays off when the structure is threaded linearly, each state used once. It
costs when old versions are kept: a query allocates a new `parent` vector, so
structural sharing between versions is lost, and the amortised bound does not
hold for a state that is reused. For those uses take the persistent family.

`empty` is `O(n)` and `groups` is `O(n α(n))`.

```lean
let uf := (UnionFind.empty 5).merge! 0 1 |>.merge! 3 4
let (connected, uf) := uf.same! 0 1    -- true
let (card, uf) := uf.size! 3           -- 2
uf.groups.1                            -- #[#[0, 1], #[2], #[3, 4]]

let uf := (UnionFind.empty 5).persistentMerge! 0 1 |>.persistentMerge! 3 4
uf.persistentSame! 0 1                 -- true, and `uf` is unchanged
uf.persistentSize! 3                   -- 2
```
-/

/-- Union-find (disjoint-set union) by size, with and without path compression. -/
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

/-- Follow parents to a root, rewriting nothing.

The fuel is an operational guard for totality. Union by size makes sizes rise
along every parent edge, so a path cannot visit a vertex twice and `n` steps are
always enough; `UnionFind.parent_persistentLeader` is where that is proved.
-/
def persistentLeaderFuel (fuel : Nat) (self : UnionFind n) (a : Fin n) : Fin n :=
  match fuel with
  | 0 => a
  | fuel + 1 =>
      let p := self.parent[a]
      if p = a then a else persistentLeaderFuel fuel self p

/-- Attach one root under the other, by size, leaving the rest alone.

Both arguments are meant to be roots; `persistentMerge` and `merge` differ only in how
they find the two they pass. -/
def link (self : UnionFind n) (x y : Fin n) : UnionFind n :=
  if x = y then self
  else if self.componentSize[x] < self.componentSize[y] then
    { parent := self.parent.set x y
      componentSize := self.componentSize.set y (self.componentSize[x] + self.componentSize[y]) }
  else
    { parent := self.parent.set y x
      componentSize := self.componentSize.set x (self.componentSize[x] + self.componentSize[y]) }

end Impl

/-- Representative of `a`, together with the state after path compression.
`O(α(n))` amortised. -/
def leader (self : UnionFind n) (a : Fin n) : Fin n × UnionFind n :=
  Impl.leaderFuel n self a

/-- Representative of `a`, leaving the structure untouched. `O(log n)`. -/
def persistentLeader (self : UnionFind n) (a : Fin n) : Fin n :=
  Impl.persistentLeaderFuel n self a

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

/-- Whether `a` and `b` lie in the same component, leaving the structure
untouched. `O(log n)`. -/
def persistentSame (self : UnionFind n) (a b : Fin n) : Bool :=
  self.persistentLeader a == self.persistentLeader b

/-- Number of vertices in the component of `a`, leaving the structure untouched.
`O(log n)`. -/
def persistentSize (self : UnionFind n) (a : Fin n) : Nat :=
  self.componentSize[self.persistentLeader a]

/-- Merge the components of `a` and `b`, attaching the smaller under the larger.
A no-op when they are already connected. Compresses the two paths it walks;
`O(α(n))` amortised. -/
def merge (self : UnionFind n) (a b : Fin n) : UnionFind n :=
  let (x, self) := self.leader a
  let (y, self) := self.leader b
  Impl.link self x y

/-- Merge the components of `a` and `b`, attaching the smaller under the larger,
leaving every other path as it was. A no-op when they are already connected.
`O(log n)`. -/
def persistentMerge (self : UnionFind n) (a b : Fin n) : UnionFind n :=
  Impl.link self (self.persistentLeader a) (self.persistentLeader b)

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

/-- `persistentLeader` for a `Nat` vertex: `none` unless `a < n`. -/
def persistentLeader? (self : UnionFind n) (a : Nat) : Option (Fin n) :=
  if h : a < n then some (self.persistentLeader ⟨a, h⟩) else none

/-- `persistentLeader` for a `Nat` vertex, reporting a panic unless `a < n` and then
returning `0`. See `Cplib.unwrap!`: a panic does not stop the program.

The representative comes back as a `Nat` rather than a `Fin n`, because `Fin n`
has no value to fall back on when `n = 0`. -/
def persistentLeader! (self : UnionFind n) (a : Nat) : Nat :=
  unwrap! "UnionFind.persistentLeader!" ((self.persistentLeader? a).map Fin.val)

/-- `persistentSame` for `Nat` vertices: `none` unless both `a < n` and `b < n`. -/
def persistentSame? (self : UnionFind n) (a b : Nat) : Option Bool :=
  if h : a < n ∧ b < n then some (self.persistentSame ⟨a, h.1⟩ ⟨b, h.2⟩) else none

/-- `persistentSame` for `Nat` vertices, reporting a panic unless both `a < n` and
`b < n` and then returning `false`. See `Cplib.unwrap!`: a panic does not stop
the program. -/
def persistentSame! (self : UnionFind n) (a b : Nat) : Bool :=
  unwrap! "UnionFind.persistentSame!" (self.persistentSame? a b)

/-- `persistentSize` for a `Nat` vertex: `none` unless `a < n`. -/
def persistentSize? (self : UnionFind n) (a : Nat) : Option Nat :=
  if h : a < n then some (self.persistentSize ⟨a, h⟩) else none

/-- `persistentSize` for a `Nat` vertex, reporting a panic unless `a < n` and then
returning `0`. See `Cplib.unwrap!`: a panic does not stop the program. -/
def persistentSize! (self : UnionFind n) (a : Nat) : Nat :=
  unwrap! "UnionFind.persistentSize!" (self.persistentSize? a)

/-- `persistentMerge` for `Nat` vertices: `none` unless both `a < n` and `b < n`. -/
def persistentMerge? (self : UnionFind n) (a b : Nat) : Option (UnionFind n) :=
  if h : a < n ∧ b < n then some (self.persistentMerge ⟨a, h.1⟩ ⟨b, h.2⟩) else none

/-- `persistentMerge` for `Nat` vertices, reporting a panic unless both `a < n` and
`b < n` and then returning the structure unchanged. See `Cplib.unwrap!`: a
panic does not stop the program. -/
def persistentMerge! (self : UnionFind n) (a b : Nat) : UnionFind n :=
  let _ : Inhabited (UnionFind n) := ⟨self⟩
  unwrap! "UnionFind.persistentMerge!" (self.persistentMerge? a b)

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

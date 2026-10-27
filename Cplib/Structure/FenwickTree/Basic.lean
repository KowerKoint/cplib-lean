import Cplib.Util.Unwrap.Basic

namespace Cplib
/-- Array-backed Fenwick tree for prefix sums. -/
structure FenwickTree (α : Type) (n : Nat) where
  data : Vector α n

namespace FenwickTree
variable {α : Type} {n : Nat}

namespace Impl

def addFuel [Add α] (fuel : Nat) (data : Vector α n) (i : Nat) (x : α) : Vector α n :=
  match fuel with
  | 0 => data
  | fuel + 1 =>
      if hi : i < n then
        let data := data.set i (data[i] + x)
        addFuel fuel data (i ||| (i + 1)) x
      else data

def prefixFuel [Add α] [Zero α] (data : Vector α n) : Nat → Nat → α
  | 0, _ => 0
  | _ + 1, 0 => 0
  | fuel + 1, i + 1 =>
      prefixFuel data fuel ((i + 1) &&& i) + data.getD i 0

end Impl

/-- An all-zero Fenwick tree of length `n`. -/
def empty [Zero α] (n : Nat) : FenwickTree α n :=
  ⟨Vector.replicate n 0⟩

/-- Add `x` to position `i`. -/
def add [Add α] (self : FenwickTree α n) (i : Fin n) (x : α) : FenwickTree α n :=
  ⟨Impl.addFuel n self.data i x⟩

/-- Sum of the half-open prefix `[0, i)`. -/
def prefixSum [Add α] [Zero α] (self : FenwickTree α n) (i : Fin (n + 1)) : α :=
  Impl.prefixFuel self.data n i

/-- Sum of the half-open interval `[l, r)`. -/
def sum [Add α] [Sub α] [Zero α] (self : FenwickTree α n)
    (l r : Fin (n + 1)) : α :=
  self.prefixSum r - self.prefixSum l

/-- Recover the value at one position. -/
def get [Add α] [Sub α] [Zero α] (self : FenwickTree α n) (i : Fin n) : α :=
  self.sum ⟨i, by omega⟩ ⟨i + 1, by omega⟩

/-- `add` の範囲外安全版。`i < n` でなければ `none`。 -/
def add? [Add α] (self : FenwickTree α n) (i : Nat) (x : α) : Option (FenwickTree α n) :=
  if h : i < n then some (self.add ⟨i, h⟩ x) else none

/-- `add` の無条件版。`i < n` でなければ停止する。 -/
def add! [Add α] (self : FenwickTree α n) (i : Nat) (x : α) : FenwickTree α n :=
  let _ : Inhabited (FenwickTree α n) := ⟨self⟩
  unwrap! "FenwickTree.add!" (self.add? i x)

/-- `prefixSum` の範囲外安全版。`i ≤ n` でなければ `none`。 -/
def prefixSum? [Add α] [Zero α] (self : FenwickTree α n) (i : Nat) : Option α :=
  if h : i < n + 1 then some (self.prefixSum ⟨i, h⟩) else none

/-- `prefixSum` の無条件版。`i ≤ n` でなければ停止する。 -/
def prefixSum! [Add α] [Zero α] (self : FenwickTree α n) (i : Nat) : α :=
  let _ : Inhabited α := ⟨0⟩
  unwrap! "FenwickTree.prefixSum!" (self.prefixSum? i)

/-- `sum` の範囲外安全版。`l ≤ n` かつ `r ≤ n` でなければ `none`。 -/
def sum? [Add α] [Sub α] [Zero α] (self : FenwickTree α n) (l r : Nat) : Option α :=
  if h : l < n + 1 ∧ r < n + 1 then some (self.sum ⟨l, h.1⟩ ⟨r, h.2⟩) else none

/-- `sum` の無条件版。`l ≤ n` かつ `r ≤ n` でなければ停止する。 -/
def sum! [Add α] [Sub α] [Zero α] (self : FenwickTree α n) (l r : Nat) : α :=
  let _ : Inhabited α := ⟨0⟩
  unwrap! "FenwickTree.sum!" (self.sum? l r)

/-- `get` の範囲外安全版。`i < n` でなければ `none`。 -/
def get? [Add α] [Sub α] [Zero α] (self : FenwickTree α n) (i : Nat) : Option α :=
  if h : i < n then some (self.get ⟨i, h⟩) else none

/-- `get` の無条件版。`i < n` でなければ停止する。 -/
def get! [Add α] [Sub α] [Zero α] (self : FenwickTree α n) (i : Nat) : α :=
  let _ : Inhabited α := ⟨0⟩
  unwrap! "FenwickTree.get!" (self.get? i)

/-- Build a Fenwick tree from point values. -/
def ofArray [Add α] [Zero α] (xs : Array α) : FenwickTree α xs.size :=
  Fin.foldl xs.size (fun tree i => tree.add i xs[i]) (empty xs.size)

end FenwickTree

end Cplib

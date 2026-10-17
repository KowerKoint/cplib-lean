import Init.Omega

/-- `l` と `r` の間 (両端を除く) にある中点を、`l < v < r` の証明込みで保持する。 -/
structure Mid (l r : Nat) where
  v : Nat
  hlv : l < v
  hvr : v < r

namespace Mid

def extendLeft (m : Mid l r) (l' : Nat) (h : l' ≤ l) : Mid l' r :=
  let ⟨v, hlv, hvr⟩ := m
  ⟨v, by omega, hvr⟩

def extendRight (m : Mid l r) (r' : Nat) (h : r ≤ r') : Mid l r' :=
  let ⟨v, hlv, hvr⟩ := m
  ⟨v, hlv, by omega⟩

def shrinkDomainLeft (f : Mid l r → α) (l' : Nat) (h : l ≤ l') (x : Mid l' r) : α :=
  f <| extendLeft x l h

def shrinkDomainRight (f : Mid l r → α) (r' : Nat) (h : r' ≤ r) (x : Mid l r') : α :=
  f <| extendRight x r h

def shrinkDomainLeft_save (f : Mid l r → α) (l' : Nat) (h : l ≤ l') (x : Mid l' r) :
    shrinkDomainLeft f l' h x = f (x.extendLeft l h) := by
  simp [shrinkDomainLeft, extendLeft]

def shrinkDomainRight_save (f : Mid l r → α) (r' : Nat) (h : r' ≤ r) (x : Mid l r') :
    shrinkDomainRight f r' h x = f (x.extendRight r h) := by
  simp [shrinkDomainRight, extendRight]
end Mid

namespace Nat

/-- `nextPowerOfTwo n` は `n` 以上である。 -/
theorem le_nextPowerOfTwo (n : Nat) : n ≤ n.nextPowerOfTwo := by
  apply le_go 1 (by decide)
where
  le_go (power : Nat) (hpower : 0 < power) :
      n ≤ nextPowerOfTwo.go n power hpower := by
    unfold nextPowerOfTwo.go
    split
    · exact le_go (power * 2) (Nat.mul_pos hpower (by decide))
    · omega
  termination_by n - power
  decreasing_by
    simp_wf
    apply nextPowerOfTwo_dec <;> assumption

/-- `l + 1 < r` のとき、オーバーフローしない中点 `l + (r - l) / 2` を返す。 -/
def midpoint(l r : Nat) (hlr : l + 1 < r) : Mid l r :=
  let mid := l + (r - l) / 2
  ⟨mid, by omega, by omega⟩

/-- 左側に再帰したときに区間幅が真に減ることを保証する補題。 -/
def midpoint_decrease_range_left(l r : Nat) (hlr : l + 1 < r) : (midpoint l r hlr).v - l < r - l := by
  let mid := midpoint l r hlr
  have hlm : l ≤ mid.v := Nat.le_of_lt mid.hlv
  exact Nat.sub_lt_sub_right hlm mid.hvr

/-- 右側に再帰したときに区間幅が真に減ることを保証する補題。 -/
def midpoint_decrease_range_right(l r : Nat) (hlr : l + 1 < r) : r - (midpoint l r hlr).v < r - l := by
  let mid := midpoint l r hlr
  have hlr : l < r := by omega
  exact Nat.sub_lt_sub_left hlr mid.hlv

end Nat

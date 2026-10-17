import Init.Omega

namespace Nat

/-- `nextPowerOfTwo n` is at least `n`. -/
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

/-- Overflow-safe midpoint `l + (r - l) / 2`. -/
def midpoint (l r : Nat) : Nat := l + (r - l) / 2

theorem lt_midpoint (hlr : l + 1 < r) : l < midpoint l r := by
  simp [midpoint]
  omega

theorem midpoint_lt (hlr : l + 1 < r) : midpoint l r < r := by
  simp [midpoint]
  omega

theorem midpoint_decrease_range_left (l r : Nat) (hlr : l + 1 < r) :
    midpoint l r - l < r - l := by
  simp [midpoint]
  omega

theorem midpoint_decrease_range_right (l r : Nat) (hlr : l + 1 < r) :
    r - midpoint l r < r - l := by
  simp [midpoint]
  omega

end Nat

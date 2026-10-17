import Init.Omega

namespace NumberTheory

namespace Impl


def powModFuel (modulus : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | _ + 1, _, 0 => 1 % modulus
  | fuel + 1, base, exponent + 1 =>
      let half := powModFuel modulus fuel base ((exponent + 1) / 2)
      let square := half * half % modulus
      if (exponent + 1) % 2 = 0 then square else square * (base % modulus) % modulus

/-- Bézout coefficients and gcd, computed by the extended Euclidean algorithm. -/
def egcd : Nat → Nat → Int × Int × Nat
  | a, 0 => (1, 0, a)
  | a, b + 1 =>
      let (x, y, g) := egcd (b + 1) (a % (b + 1))
      (y, x - (a / (b + 1) : Nat) * y, g)
termination_by _ b => b
decreasing_by exact Nat.mod_lt _ (by omega)

end Impl

/-- `base ^ exponent mod modulus` by binary exponentiation.

As with `Nat.mod`, modulus zero is assigned the totalized result `0`.
-/
def powMod (base exponent modulus : Nat) : Nat :=
  if modulus = 0 then 0 else Impl.powModFuel modulus (exponent + 1) base exponent

/-- Multiplicative inverse modulo `modulus`, when it exists. -/
def invMod? (value modulus : Nat) : Option Nat :=
  if modulus = 0 then none
  else
    let (x, _, g) := Impl.egcd value modulus
    if g = 1 then some (x % (modulus : Int)).toNat else none

namespace Impl

def crtCombine (current : Nat × Nat) (congruence : Int × Nat) : Option (Nat × Nat) :=
  let (r₀, m₀) := current
  let (r₁Int, m₁) := congruence
  if m₀ = 0 || m₁ = 0 then none
  else
    let r₁ := (r₁Int % (m₁ : Int)).toNat
    let g := Nat.gcd m₀ m₁
    let diff : Int := (r₁ : Int) - (r₀ : Int)
    if diff % (g : Int) ≠ 0 then none
    else
      let reduced := m₁ / g
      match invMod? (m₀ / g % reduced) reduced with
      | none => none
      | some inverse =>
          let step := ((diff / (g : Int)) % (reduced : Int)).toNat * inverse % reduced
          let modulus := m₀ * reduced
          some ((r₀ + m₀ * step) % modulus, modulus)

end Impl

/-- Chinese remainder theorem for possibly non-coprime positive moduli.

Returns the least nonnegative solution and the least common multiple modulus,
or `none` when the congruences are inconsistent or contain modulus zero.
-/
def crt (congruences : Array (Int × Nat)) : Option (Nat × Nat) :=
  congruences.foldlM Impl.crtCombine (0, 1)

end NumberTheory

import Cplib.NumberTheory.Modular.Basic

/-!
# NumberTheory.ModInt.Basic

競技プログラミング向けの固定法剰余数型。
-/

namespace Cplib

/-- `modulus` を法とする正規化済みの剰余数。

法は型の一部であり、値は常に `modulus` 未満に保たれる。
-/
structure ModInt (modulus : Nat) where
  val : Nat
  isLt : val < modulus
deriving BEq, DecidableEq, Repr

namespace ModInt

/-- 自然数を法 `modulus` で正規化する。 -/
@[inline] def ofNat [NeZero modulus] (value : Nat) : ModInt modulus :=
  ⟨value % modulus, Nat.mod_lt _ (Nat.pos_of_neZero modulus)⟩

/-- 正規化済みの内部値を取り出す。 -/
@[inline] def toNat (value : ModInt modulus) : Nat := value.val

@[inline] protected def add (a b : ModInt modulus) : ModInt modulus :=
  let sum := a.val + b.val
  if h : sum < modulus then
    ⟨sum, h⟩
  else
    ⟨sum - modulus, by
      have ha := a.isLt
      have hb := b.isLt
      omega⟩

@[inline] protected def sub (a b : ModInt modulus) : ModInt modulus :=
  if h : b.val ≤ a.val then
    ⟨a.val - b.val, by
      have ha := a.isLt
      omega⟩
  else
    ⟨a.val + (modulus - b.val), by
      have ha := a.isLt
      have hb := b.isLt
      omega⟩

@[inline] protected def neg (a : ModInt modulus) : ModInt modulus :=
  if h : a.val = 0 then
    a
  else
    ⟨modulus - a.val, by
      have ha := a.isLt
      omega⟩

@[inline] protected def mul (a b : ModInt modulus) : ModInt modulus :=
  ⟨a.val * b.val % modulus, Nat.mod_lt _ (by
    have ha := a.isLt
    omega)⟩

private def powLoop (base acc : ModInt modulus) : Nat → ModInt modulus
  | 0 => acc
  | exponent + 1 =>
      powLoop (ModInt.mul base base)
        (if (exponent + 1) % 2 = 0 then acc else ModInt.mul acc base)
        ((exponent + 1) / 2)
termination_by exponent => exponent
decreasing_by omega

/-- 二進累乗法で `base ^ exponent` を計算する。 -/
def pow [NeZero modulus] (base : ModInt modulus) (exponent : Nat) : ModInt modulus :=
  powLoop base (ofNat 1) exponent

/-- 乗法逆元が存在するときだけ返す。 -/
def inv? [NeZero modulus] (value : ModInt modulus) : Option (ModInt modulus) :=
  NumberTheory.invMod? value.val modulus |>.map ofNat

/-- 乗法逆元。逆元が存在しない場合は `0` を返す。

存在性を確認したい場合は `inv?` を使う。
-/
def inv [NeZero modulus] (value : ModInt modulus) : ModInt modulus :=
  value.inv?.getD (ofNat 0)

/-- `a / b` を、`b` の乗法逆元が存在するときだけ返す。 -/
def div? [NeZero modulus] (a b : ModInt modulus) : Option (ModInt modulus) :=
  b.inv?.map (ModInt.mul a)

instance (modulus : Nat) : CoeOut (ModInt modulus) Nat := ⟨toNat⟩
instance (modulus : Nat) : ToString (ModInt modulus) := ⟨fun value => toString value.val⟩
instance (modulus : Nat) : Add (ModInt modulus) := ⟨ModInt.add⟩
instance (modulus : Nat) : Sub (ModInt modulus) := ⟨ModInt.sub⟩
instance (modulus : Nat) : Neg (ModInt modulus) := ⟨ModInt.neg⟩
instance (modulus : Nat) : Mul (ModInt modulus) := ⟨ModInt.mul⟩

instance [NeZero modulus] : Zero (ModInt modulus) := ⟨ofNat 0⟩
instance [NeZero modulus] : One (ModInt modulus) := ⟨ofNat 1⟩
instance [NeZero modulus] : Inhabited (ModInt modulus) := ⟨0⟩
instance [NeZero modulus] (n : Nat) : OfNat (ModInt modulus) n := ⟨ofNat n⟩
instance [NeZero modulus] : NatPow (ModInt modulus) := ⟨pow⟩
instance [NeZero modulus] : Inv (ModInt modulus) := ⟨inv⟩
instance [NeZero modulus] : Div (ModInt modulus) := ⟨fun a b => ModInt.mul a b⁻¹⟩

end ModInt

end Cplib

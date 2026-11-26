import Cplib.NumberTheory.ModInt.Basic

namespace Cplib

namespace Convolution

namespace Impl

def nttFuel [NeZero modulus] (primitiveRoot : ModInt modulus) :
    Nat → Array (ModInt modulus) → Array (ModInt modulus)
  | 0, xs => xs
  | fuel + 1, xs =>
      if xs.size ≤ 1 then xs
      else
        let half := xs.size / 2
        let indices := Array.range half
        let even := indices.map (fun i => xs.getD (i * 2) 0)
        let odd := indices.map (fun i => xs.getD (i * 2 + 1) 0)
        let even := nttFuel primitiveRoot fuel even
        let odd := nttFuel primitiveRoot fuel odd
        let step := primitiveRoot ^ ((modulus - 1) / xs.size)
        let (_, left, right) := Nat.fold half (fun i _ (root, left, right) =>
          let term := root * odd.getD i 0
          let a := even.getD i 0 + term
          let b := even.getD i 0 - term
          (root * step, left.push a, right.push b)) (1, #[], #[])
        left ++ right

def padded [NeZero modulus] (size : Nat) (xs : Array (ModInt modulus)) :
    Array (ModInt modulus) :=
  (Array.range size).map fun i => xs.getD i 0

end Impl

/-- NTT convolution for a prime modulus and a supplied primitive root.

The padded transform length must divide `modulus - 1`; otherwise the function
is total but has no convolution specification.
-/
def convolutionMod [NeZero modulus] (primitiveRoot : Nat)
    (xs ys : Array (ModInt modulus)) : Array (ModInt modulus) :=
  if xs.isEmpty || ys.isEmpty || modulus ≤ 1 then #[]
  else
    let resultSize := xs.size + ys.size - 1
    let size := resultSize.nextPowerOfTwo
    let root : ModInt modulus := ModInt.ofNat primitiveRoot
    let sizeMod : ModInt modulus := ModInt.ofNat size
    match root.inv?, sizeMod.inv? with
    | some inverseRoot, some inverseSize =>
        let left := Impl.nttFuel root size (Impl.padded size xs)
        let right := Impl.nttFuel root size (Impl.padded size ys)
        let product := (Array.range size).map fun i =>
          left.getD i 0 * right.getD i 0
        let result := Impl.nttFuel inverseRoot size product
        (result.map fun x => x * inverseSize).extract 0 resultSize
    | _, _ => #[]

/-- Convolution modulo `998244353`, supporting transform lengths up to `2^23`. -/
def convolution (xs ys : Array (ModInt 998244353)) : Array (ModInt 998244353) :=
  convolutionMod 3 xs ys

end Convolution

end Cplib

import Cplib.NumberTheory.Modular.Basic

namespace Cplib

namespace Convolution

namespace Impl

def nttFuel (modulus primitiveRoot : Nat) : Nat → Array Nat → Array Nat
  | 0, xs => xs
  | fuel + 1, xs =>
      if xs.size ≤ 1 then xs
      else
        let half := xs.size / 2
        let indices := Array.range half
        let even := indices.map (fun i => xs.getD (i * 2) 0)
        let odd := indices.map (fun i => xs.getD (i * 2 + 1) 0)
        let even := nttFuel modulus primitiveRoot fuel even
        let odd := nttFuel modulus primitiveRoot fuel odd
        let step := NumberTheory.powMod primitiveRoot ((modulus - 1) / xs.size) modulus
        let (_, left, right) := indices.foldl (fun (root, left, right) i =>
          let term := root * odd.getD i 0 % modulus
          let a := (even.getD i 0 + term) % modulus
          let b := (even.getD i 0 + modulus - term) % modulus
          (root * step % modulus, left.push a, right.push b)) (1, #[], #[])
        left ++ right

def padded (size : Nat) (xs : Array Nat) (modulus : Nat) : Array Nat :=
  (Array.range size).map fun i => xs.getD i 0 % modulus

end Impl

/-- NTT convolution for a prime modulus and a supplied primitive root.

The padded transform length must divide `modulus - 1`; otherwise the function
is total but has no convolution specification.
-/
def convolutionMod (modulus primitiveRoot : Nat) (xs ys : Array Nat) : Array Nat :=
  if xs.isEmpty || ys.isEmpty || modulus ≤ 1 then #[]
  else
    let resultSize := xs.size + ys.size - 1
    let size := resultSize.nextPowerOfTwo
    match NumberTheory.invMod? primitiveRoot modulus,
      NumberTheory.invMod? size modulus with
    | some inverseRoot, some inverseSize =>
        let left := Impl.nttFuel modulus primitiveRoot size (Impl.padded size xs modulus)
        let right := Impl.nttFuel modulus primitiveRoot size (Impl.padded size ys modulus)
        let product := (Array.range size).map fun i =>
          left.getD i 0 * right.getD i 0 % modulus
        let result := Impl.nttFuel modulus inverseRoot size product
        (result.map fun x => x * inverseSize % modulus).extract 0 resultSize
    | _, _ => #[]

/-- Convolution modulo `998244353`, supporting transform lengths up to `2^23`. -/
def convolution (xs ys : Array Nat) : Array Nat :=
  convolutionMod 998244353 3 xs ys

end Convolution

end Cplib

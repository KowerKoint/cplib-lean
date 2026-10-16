import Init.Omega

namespace ZAlgorithm

namespace Impl

def extend [BEq α] (xs : Array α) (i : Nat) : Nat → Nat → Nat
  | 0, k => k
  | fuel + 1, k =>
      if hik : i + k < xs.size then
        if xs[i + k] == xs[k]'(by omega) then extend xs i fuel (k + 1) else k
      else k

def loop [BEq α] (xs : Array α) : Nat → Nat → Nat →
    Vector Nat xs.size → Nat → Vector Nat xs.size
  | 0, _, _, z, _ => z
  | fuel + 1, l, r, z, i =>
      if hi : i < xs.size then
        let k₀ := if i < r then min (z.getD (i - l) 0) (r - i) else 0
        let k := extend xs i xs.size k₀
        let z := z.set i k
        if r < i + k then loop xs fuel i (i + k) z (i + 1)
        else loop xs fuel l r z (i + 1)
      else z

end Impl

/-- Z array: result `i` is the longest common prefix length of `xs` and `xs[i:]`.

Runs in linear time using the usual rightmost matching interval.
-/
def zAlgorithm [BEq α] (xs : Array α) : Array Nat :=
  if h : 0 < xs.size then
    let z := (Vector.replicate xs.size 0).set 0 xs.size (by omega)
    (Impl.loop xs xs.size 0 0 z 1).toArray
  else #[]

end ZAlgorithm

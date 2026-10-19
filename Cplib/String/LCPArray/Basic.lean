import Cplib.String.SuffixArray.Basic

namespace Cplib

namespace LCPArray

namespace Impl

def inverse (n : Nat) (sa : Array Nat) : Array Nat :=
  (List.finRange sa.size).foldl (fun rank (i : Fin sa.size) =>
    let p := sa[i]
    if p < n then rank.setIfInBounds p i.val else rank) (Array.replicate n 0)

def extend [BEq α] (xs : Array α) (i j : Nat) : Nat → Nat → Nat
  | 0, k => k
  | fuel + 1, k =>
      if hi : i + k < xs.size then
        if hj : j + k < xs.size then
          if xs[i + k] == xs[j + k] then extend xs i j fuel (k + 1) else k
        else k
      else k

def loop [BEq α] (xs : Array α) (sa rank : Array Nat) :
    Nat → Nat → Nat → Array Nat → Array Nat
  | 0, _, _, lcp => lcp
  | fuel + 1, i, common, lcp =>
      if hi : i < xs.size then
        let r := rank.getD i 0
        if hr : r + 1 < sa.size then
          let j := sa[r + 1]
          let common := extend xs i j xs.size common
          let lcp := if hl : r < lcp.size then lcp.set r common else lcp
          loop xs sa rank fuel (i + 1) (common - 1) lcp
        else loop xs sa rank fuel (i + 1) 0 lcp
      else lcp

end Impl

/-- LCP lengths of adjacent suffixes in `sa`, computed by Kasai's algorithm.

`sa` is expected to be `suffixArray xs`. Supplying an arbitrary array is total,
but only a genuine suffix permutation has the documented meaning.
-/
def lcpArray [BEq α] (xs : Array α) (sa : Array Nat) : Array Nat :=
  let rank := Impl.inverse xs.size sa
  Impl.loop xs sa rank xs.size 0 0 (Array.replicate (xs.size - 1) 0)

/-- Compute a suffix array and its adjacent LCP array together. -/
def suffixAndLCP [Ord α] [BEq α] (xs : Array α) : Array Nat × Array Nat :=
  let sa := SuffixArray.suffixArray xs
  (sa, lcpArray xs sa)

end LCPArray

end Cplib

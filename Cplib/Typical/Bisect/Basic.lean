import Cplib.Util.Number.Basic

namespace Cplib

/-!
# Typical.Bisect.Basic

Binary search over `Nat`, and the two array positions built on it.

Every function here assumes `p` is **monotone**: it changes truth value at most
once over the searched range. `bisectMax*` expects `p` to go from true to
false, `bisectMin*` from false to true. For a predicate that is not monotone,
the answer is whichever boundary the halving happened to land on; use
`Cplib.findMinBelow` instead.

All of these are `O(log n)` in the width of the range, times the cost of `p`.

```lean
bisectMaxBelow 100 (fun i => i.val * i.val ≤ 50)   -- 7
bisectMinBelow 100 (fun i => 50 ≤ i.val * i.val)   -- 8
#[1, 3, 3, 5].lowerBound 3                          -- 1
#[1, 3, 3, 5].upperBound 3                          -- 3
```
-/

/-- The largest value satisfying `p`, assuming `p` turns from true to false
exactly once between `ok` and `ng`. -/
def bisectMax' (ok ng : Nat) (p : Nat → Bool) : Nat :=
  if _h : ok + 1 < ng then
    let mid := Nat.midpoint ok ng
    if p mid then
      bisectMax' mid ng p
    else
      bisectMax' ok mid p
  else
    ok
termination_by ng - ok
decreasing_by
  · exact Nat.midpoint_decrease_range_right ok ng _h
  · exact Nat.midpoint_decrease_range_left ok ng _h

/-- The largest value satisfying the monotone `p` in the range bounded by `ok`
(where `p` holds) and `ng` (where it does not). `O(log |ng - ok|)`. -/
def bisectMax (ok ng : Nat) (p : Nat → Bool) : Nat :=
  bisectMax' ok ng p

/-- The largest `i < ng` satisfying the monotone `p`, or `ng` when none does.
`O(log ng)`. -/
def bisectMaxBelow (ng : Nat) (p : Fin ng → Bool) : Nat :=
  let p' (x : Nat) : Bool :=
    if x = 0 then true
    else if hx : x.pred < ng then p ⟨x.pred, hx⟩ else false
  bisectMax' 0 ng.succ p' |>.pred

/-- The smallest value satisfying `p`, assuming `p` turns from false to true
exactly once between `ng` and `ok`. -/
def bisectMin' (ng ok : Nat) (p : Nat → Bool) : Nat :=
  (bisectMax' ng ok (fun x => !(p x))).succ

/-- The smallest value satisfying the monotone `p` in the range bounded by `ng`
(where `p` fails) and `ok` (where it holds). `O(log |ok - ng|)`. -/
def bisectMin (ng ok : Nat) (p : Nat → Bool) : Nat :=
  bisectMin' ng ok p

/-- The smallest `i < ok` satisfying the monotone `p`, or `ok` when none does.
`O(log ok)`. -/
def bisectMinBelow (ok : Nat) (p : Fin ok → Bool) : Nat :=
  let p' (x : Nat) : Bool :=
    if x = 0 then false
    else if hx : x.pred < ok then p ⟨x.pred, hx⟩ else true
  bisectMin' 0 ok.succ p' |>.pred

end Cplib

namespace Array

open Cplib

/-- First position of `a` in the sorted array `xs`: the least index whose element
is at least `a`, or `xs.size` when every element is smaller. `O(log xs.size)`. -/
def lowerBound [Ord α] (xs : Array α) (a : α) :=
  bisectMinBelow xs.size (compare xs[·] a != Ordering.lt)

/-- Position just past `a` in the sorted array `xs`: the least index whose element
exceeds `a`, or `xs.size` when none does. The count of elements equal to `a` is
`upperBound a - lowerBound a`. `O(log xs.size)`. -/
def upperBound [Ord α] (xs : Array α) (a : α) :=
  bisectMinBelow xs.size (compare xs[·] a == Ordering.gt)

end Array

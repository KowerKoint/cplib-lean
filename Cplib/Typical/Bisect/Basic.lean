import Cplib.Util.Number.Basic

/-- `p` が単調 (true から false へ一度だけ変化) という前提で、`p` を満たす最大の値を探す。 -/
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

def bisectMax (ok ng : Nat) (p : Nat → Bool) : Nat :=
  bisectMax' ok ng p

def bisectMaxBelow (ng : Nat) (p : Fin ng → Bool) : Nat :=
  let p' (x : Nat) : Bool :=
    if x = 0 then true
    else if hx : x.pred < ng then p ⟨x.pred, hx⟩ else false
  bisectMax' 0 ng.succ p' |>.pred

/-- `p` が単調という前提で、`p` を満たす最小の値を探す。 -/
def bisectMin' (ng ok : Nat) (p : Nat → Bool) : Nat :=
  (bisectMax' ng ok (fun x => !(p x))).succ

def bisectMin (ng ok : Nat) (p : Nat → Bool) : Nat :=
  bisectMin' ng ok p

def bisectMinBelow (ok : Nat) (p : Fin ok → Bool) : Nat :=
  let p' (x : Nat) : Bool :=
    if x = 0 then false
    else if hx : x.pred < ok then p ⟨x.pred, hx⟩ else true
  bisectMin' 0 ok.succ p' |>.pred

namespace Array

/-- ソート済み配列 `xs` における `a` の下限位置 (`a` 以上が現れる最小添字)。 -/
def lowerBound [Ord α] (xs : Array α) (a : α) :=
  bisectMinBelow xs.size (compare xs[·] a != Ordering.lt)

/-- ソート済み配列 `xs` における `a` の上限位置 (`a` 超過が現れる最小添字)。 -/
def upperBound [Ord α] (xs : Array α) (a : α) :=
  bisectMinBelow xs.size (compare xs[·] a == Ordering.gt)

end Array

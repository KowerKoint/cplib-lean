import Lean.Elab.Tactic.Omega

/-!
# Util.Fold.Lemmas

Bridging lemmas that rewrite an index loop back into a `foldl` over a `List`.

Implementations use `Nat.fold` and `Fin.foldl`, which allocate nothing, while
proofs convert back to a list and then run the usual `List.foldl_cons`
induction.

The core library already provides `Fin.foldl_eq_finRange_foldl`,
`Fin.foldr_eq_finRange_foldr`, `Nat.fold_eq_finRange_foldl` and
`Nat.foldRev_eq_finRange_foldr`, so only the link between `Nat.fold` and
`List.range` is missing.
-/

namespace Nat

/-- `Nat.fold` agrees with `foldl` over `List.range`. -/
theorem fold_eq_foldl_range {β : Type u} (n : Nat) (f : β → Nat → β) (init : β) :
    Nat.fold n (fun i _ acc => f acc i) init = (List.range n).foldl f init := by
  induction n generalizing init with
  | zero => rfl
  | succ n ih => rw [Nat.fold_succ, List.range_succ, List.foldl_append, ih]; rfl

end Nat

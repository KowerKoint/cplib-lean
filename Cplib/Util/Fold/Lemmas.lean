import Lean.Elab.Tactic.Omega

/-!
# Util.Fold.Lemmas

添字ループを `List` 上の `foldl` に書き換えるための橋渡し補題。

実装側では確保を伴わない `Nat.fold` / `Fin.foldl` を使い、証明側ではこれらで
`List` 上の `foldl` に戻してから既存の `List.foldl_cons` 流の帰納法を回す。

core には `Fin.foldl_eq_finRange_foldl` / `Fin.foldr_eq_finRange_foldr` /
`Nat.fold_eq_finRange_foldl` / `Nat.foldRev_eq_finRange_foldr` があるので、
ここでは `Nat.fold` と `List.range` を繋ぐものだけを補う。
-/

namespace Nat

/-- `Nat.fold` は `List.range` 上の `foldl` と一致する。 -/
theorem fold_eq_foldl_range {β : Type u} (n : Nat) (f : β → Nat → β) (init : β) :
    Nat.fold n (fun i _ acc => f acc i) init = (List.range n).foldl f init := by
  induction n generalizing init with
  | zero => rfl
  | succ n ih => rw [Nat.fold_succ, List.range_succ, List.foldl_append, ih]; rfl

end Nat

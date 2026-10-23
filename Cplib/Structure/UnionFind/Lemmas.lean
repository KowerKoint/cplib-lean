import Cplib.Structure.UnionFind.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.Vector.Basic
import Mathlib.Tactic

namespace Cplib

namespace UnionFind

theorem Impl.leaderFuel_componentSize (fuel : Nat) (self : UnionFind n) (a : Fin n) :
    (Impl.leaderFuel fuel self a).2.componentSize = self.componentSize := by
  induction fuel generalizing self a with
  | zero => rfl
  | succ fuel ih =>
      rw [Impl.leaderFuel]
      split
      · rfl
      · generalize hresult : Impl.leaderFuel fuel self self.parent[a] = result
        rcases result with ⟨root, next⟩
        have h := ih self self.parent[a]
        rw [hresult] at h
        exact h

theorem leader_componentSize (self : UnionFind n) (a : Fin n) :
    (self.leader a).2.componentSize = self.componentSize :=
  Impl.leaderFuel_componentSize n self a

private theorem leaderFuel_empty {n : Nat} (fuel : Nat) (i : Fin n) :
    Impl.leaderFuel fuel (empty n) i = (i, empty n) := by
  induction fuel generalizing i with
  | zero => rfl
  | succ fuel ih => simp [Impl.leaderFuel, empty]

@[simp] theorem empty_leader {n : Nat} (i : Fin n) :
    (empty n).leader i = (i, empty n) := by
  exact leaderFuel_empty n i

@[simp] theorem empty_size {n : Nat} (i : Fin n) :
    (empty n).size i = (1, empty n) := by
  simp only [size, empty_leader]
  simp [empty]

@[simp] theorem empty_same {n : Nat} (i j : Fin n) :
    (empty n).same i j = (i == j, empty n) := by
  simp [same]

@[simp] theorem empty_merge_self (a : Fin n) :
    (empty n).merge a a = empty n := by
  simp [merge]

/-- 成分は、各根が初めて現れた頂点の順に並び、成分内は頂点番号の昇順。 -/
example :
    let uf := (empty 7).merge 1 3 |>.merge 5 1 |>.merge 4 6
    uf.groups.1 = #[#[0], #[1, 3, 5], #[2], #[4, 6]] := by
  native_decide

example : (empty 4).groups.1 = #[#[0], #[1], #[2], #[3]] := by
  native_decide

/-- 根が成分の最小頂点とは限らない場合も、並びは最小頂点の順になる。 -/
example :
    let uf := (empty 6).merge 5 0 |>.merge 4 1 |>.merge 3 2
    uf.groups.1 = #[#[0, 5], #[1, 4], #[2, 3]] := by
  native_decide

example :
    let uf := (empty 5).merge 0 1 |>.merge 3 4 |>.merge 1 4
    let (connected, uf) := uf.same 0 3
    let (separate, uf) := uf.same 0 2
    let (card, _) := uf.size 4
    connected && !separate && card == 4 := by
  native_decide

end UnionFind

end Cplib

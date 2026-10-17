import Cplib.Structure.LazySegTree.Basic
import Mathlib.Tactic

namespace LazySegTree
variable {M F : Type} [Mul M] [One M] [Mul F] [One F] [SMul F M]

omit [Mul F] [SMul F M] in
@[simp] theorem ofArray_sz (xs : Array M) : (ofArray (F := F) xs).sz = xs.size := rfl

@[simp] theorem applyRange_sz (self : LazySegTree M F) (l r : Fin (self.sz + 1)) (f : F) :
    (self.applyRange l r f).sz = self.sz := rfl

@[simp] theorem applyRange_cap (self : LazySegTree M F) (l r : Fin (self.sz + 1)) (f : F) :
    (self.applyRange l r f).cap = self.cap := rfl

private structure SumLen where
  sum : Nat
  len : Nat
deriving BEq

private instance : Mul SumLen := ⟨fun x y => ⟨x.sum + y.sum, x.len + y.len⟩⟩
private instance : One SumLen := ⟨⟨0, 0⟩⟩

private structure AddTag where
  value : Nat
deriving BEq

private instance : Mul AddTag := ⟨fun f g => ⟨f.value + g.value⟩⟩
private instance : One AddTag := ⟨⟨0⟩⟩
private instance : SMul AddTag SumLen :=
  ⟨fun f x => ⟨x.sum + f.value * x.len, x.len⟩⟩

/-- 区間加算・区間和で、作用の合成順、重なる更新、部分区間問い合わせを確認する。 -/
example :
    let xs : Array SumLen := #[⟨1, 1⟩, ⟨2, 1⟩, ⟨3, 1⟩, ⟨4, 1⟩, ⟨5, 1⟩]
    let tree : LazySegTree SumLen AddTag := ofArray xs
    let tree := tree.applyRange 1 4 ⟨10⟩
    let tree := tree.applyRange 2 5 ⟨3⟩
    tree.prod 0 5 == ⟨54, 5⟩ && tree.prod 2 4 == ⟨33, 2⟩ &&
      tree.get ⟨2, by decide⟩ == ⟨16, 1⟩ && tree.allProd == ⟨54, 5⟩ &&
      tree.maxRight 0 (fun x => x.sum ≤ 30) == 3 &&
      tree.minLeft 5 (fun x => x.sum ≤ 30) == 3 &&
      tree.maxRight 1 (fun x => x.sum ≤ 28) == 3 &&
      tree.minLeft 4 (fun x => x.sum ≤ 33) == 2 := by
  native_decide

end LazySegTree

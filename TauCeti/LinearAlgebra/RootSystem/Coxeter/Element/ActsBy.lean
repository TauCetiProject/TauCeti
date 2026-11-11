/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimpleReflections
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!
# From Weyl-group elements to integer matrices on the simple roots

For a base `b` of a root pairing `P`, an element `w` of the Weyl group *acts by* the integer matrix
`W` (`RootPairing.Base.ActsBy b w W`) if `w • αⱼ = ∑ₖ W k j • αₖ` for every simple root `αⱼ`.
Acting-by is multiplicative, and the simple reflection `sᵢ` acts by `reflMatrix b.cartanMatrix i`.
The action is faithful for a finite anisotropic root pairing over a domain, in particular for a
crystallographic one in characteristic zero (`RootPairing.weylGroup.eq_one_of_forall_smul_root_eq`;
the roots need not span), so the order of `w` is the order of `W`.

## Main results

* `RootPairing.Base.actsBy_wordProd`: a word in the simple reflections acts by the product of the
  corresponding reflection matrices.
* `RootPairing.Base.ActsBy.orderOf_eq`: if `w` acts by `W`, then `orderOf w = orderOf W`.
* `RootPairing.Base.orderOf_wordProd_of_cartanMatrix_eq`: for a base whose Cartan matrix is `A` up
  to a relabelling `e`, the Coxeter element spelled in the order `e` has the order of
  `coxeterElement A`.
-/

public section

open Matrix Submodule TauCeti

namespace RootPairing.Base

variable {ι R M N : Type*} [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}

/-- The Weyl-group element `w` sends the simple root `αⱼ` of `b` to `∑ₖ W k j • αₖ`. -/
def ActsBy (b : P.Base) (w : P.weylGroup) (W : Matrix b.support b.support ℤ) : Prop :=
  ∀ j : b.support, w • P.root j = ∑ k, W k j • P.root k

omit [DecidableEq ι] in
/-- The defining property of `RootPairing.Base.ActsBy`. -/
theorem actsBy_iff {b : P.Base} {w : P.weylGroup} {W : Matrix b.support b.support ℤ} :
    ActsBy b w W ↔ ∀ j : b.support, w • P.root j = ∑ k, W k j • P.root k :=
  Iff.rfl

/-- The identity of the Weyl group acts by the identity matrix. -/
theorem actsBy_one (b : P.Base) : ActsBy b 1 1 := by
  intro j
  simp [Matrix.one_apply, ite_smul]

omit [DecidableEq ι] in
/-- Acting-by is multiplicative. -/
theorem ActsBy.mul {b : P.Base} {v w : P.weylGroup} {V W : Matrix b.support b.support ℤ}
    (hv : ActsBy b v V) (hw : ActsBy b w W) : ActsBy b (v * w) (V * W) := by
  intro j
  calc (v * w) • P.root j = v • (w • P.root j) := mul_smul v w _
    _ = v • ∑ k, W k j • P.root k := by rw [hw j]
    _ = ∑ k, W k j • (v • P.root k) := by
        rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun k _ => smul_comm v _ _
    _ = ∑ k, W k j • ∑ l, V l k • P.root l := Finset.sum_congr rfl fun k _ => by rw [hv k]
    _ = ∑ l, (V * W) l j • P.root l := by
        simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

/-- If `w` acts by `W`, then `w ^ k` acts by `W ^ k`. -/
theorem ActsBy.pow {b : P.Base} {w : P.weylGroup} {W : Matrix b.support b.support ℤ}
    (h : ActsBy b w W) (k : ℕ) : ActsBy b (w ^ k) (W ^ k) := by
  induction k with
  | zero => simpa using actsBy_one b
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

/-- The simple reflection `sᵢ` acts by `reflMatrix b.cartanMatrix i`. -/
theorem actsBy_ofIdx [P.IsCrystallographic] (b : P.Base) (i : b.support) :
    ActsBy b (weylGroup.ofIdx P i) (reflMatrix b.cartanMatrix i) := by
  intro j
  rw [weylGroup.ofIdx_smul, Equiv.reflection_smul, reflection_apply_root]
  simp only [reflMatrix_apply, sub_smul, ite_smul, one_smul, zero_smul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  rw [← Int.cast_smul_eq_zsmul R (b.cartanMatrix j i), ← eq_intCast (algebraMap ℤ R),
    b.algebraMap_cartanMatrixIn_apply (S := ℤ)]

variable [P.IsCrystallographic]

/-- A word in the simple reflections acts by the product of the corresponding reflection
matrices. -/
theorem actsBy_wordProd (b : P.Base) (l : List b.support) :
    ActsBy b (wordProd P b l) (l.map (reflMatrix b.cartanMatrix)).prod := by
  induction l with
  | nil => simpa [wordProd_nil] using actsBy_one b
  | cons i l ih =>
    simpa only [wordProd_cons, List.map_cons, List.prod_cons] using
      (actsBy_ofIdx b i).mul ih

/-- An element acting trivially on the simple roots is trivial. -/
theorem ActsBy.eq_one [Finite ι] [IsDomain R] [CharZero R] {b : P.Base}
    {w : P.weylGroup} (h : ActsBy b w 1) : w = 1 := by
  have := Fintype.ofFinite ι
  have hfix : ∀ j : b.support, w • P.root j = P.root j := fun j => by
    simpa [Matrix.one_apply, ite_smul] using h j
  have hspan : ∀ x ∈ span ℤ (P.root '' b.support), w • x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨j, hj, rfl⟩ := hx; exact hfix ⟨j, hj⟩
    | zero => exact smul_zero w
    | add x y _ _ hx hy => rw [smul_add, hx, hy]
    | smul n x _ hx => rw [smul_comm w n x, hx]
  exact weylGroup.eq_one_of_forall_smul_root_eq fun i => hspan _ (b.root_mem_span_int i)

omit [DecidableEq ι] [P.IsCrystallographic] in
/-- The matrix by which an element acts is unique. -/
theorem ActsBy.unique [CharZero R] {b : P.Base} {w : P.weylGroup}
    {V W : Matrix b.support b.support ℤ} (hV : ActsBy b w V) (hW : ActsBy b w W) : V = W := by
  have hli : LinearIndependent ℤ (fun k : b.support => P.root k) :=
    b.linearIndepOn_root.restrict_scalars' ℤ
  ext k j
  have h0 : ∑ l, (V l j - W l j) • P.root l = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← hV j, ← hW j, sub_self]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h0 k)

/-- If `w` acts by the integer matrix `W`, then `w` and `W` have the same order. -/
theorem ActsBy.orderOf_eq [CharZero R] [Finite ι] [IsDomain R] {b : P.Base}
    {w : P.weylGroup} {W : Matrix b.support b.support ℤ} (h : ActsBy b w W) :
    orderOf w = orderOf W := by
  refine orderOf_eq_orderOf_iff.2 fun k => ⟨fun hk => ?_, fun hk => ?_⟩
  · exact (h.pow k).unique (by simpa [hk] using actsBy_one b)
  · exact ActsBy.eq_one (by simpa [hk] using h.pow k)

/-! ### Relabelling along a Dynkin numbering -/

/-- The product of the simple-reflection matrices of `b`, in the order `e`, is the Coxeter
element of `A`, relabelled. -/
theorem prod_reflMatrix_eq {n : ℕ} (b : P.Base) (A : Matrix (Fin n) (Fin n) ℤ)
    (e : b.support ≃ Fin n) (hA : ∀ i j, b.cartanMatrix i j = A (e i) (e j)) :
    (((List.finRange n).map e.symm).map (reflMatrix b.cartanMatrix)).prod =
      reindexAlgEquiv ℤ ℤ e.symm (coxeterElement A) := by
  have hC : b.cartanMatrix = A.submatrix e e := by ext i j; exact hA i j
  rw [hC, coxeterElement, map_list_prod, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, reflMatrix_submatrix, _root_.Equiv.apply_symm_apply,
    coe_reindexAlgEquiv, reindex_apply, _root_.Equiv.symm_symm]

omit [DecidableEq ι] in
/-- **The Weyl-group Coxeter element has the order of the Coxeter element of its Cartan
matrix.** -/
theorem orderOf_wordProd_of_cartanMatrix_eq [CharZero R] [Finite ι] [IsDomain R] {n : ℕ}
    (b : P.Base)
    (A : Matrix (Fin n) (Fin n) ℤ) (e : b.support ≃ Fin n)
    (hA : ∀ i j, b.cartanMatrix i j = A (e i) (e j)) :
    orderOf (wordProd P b ((List.finRange n).map e.symm)) = orderOf (coxeterElement A) := by
  classical
  rw [(actsBy_wordProd b _).orderOf_eq, prod_reflMatrix_eq b A e hA]
  exact orderOf_injective (reindexAlgEquiv ℤ ℤ e.symm).toRingEquiv.toMulEquiv.toMonoidHom
    (reindexAlgEquiv ℤ ℤ e.symm).injective _

end RootPairing.Base

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Root.Basis

/-!
# Braid relations in the full-weight type-D spin carrier

The pinned words `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` satisfy the commuting and length-three braid
relations over every commutative ring. Their signed action on the spin basis is used,
not merely their permutation of its weights. These equations give braid-move coherence
for transport of numbered root subgroups.

The carrier is not identified with the independently pinned simply connected group
scheme of type D; transfer to that group requires such an identification.

## Main results

* `rootSubgroupPoints_weyl_mul_comm_of_cartan_eq_zero`: the orthogonal-node relation.
* `rootSubgroupPoints_weyl_braid_of_cartan_eq_neg_one`: the adjacent-node relation.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
* The spin-basis normalization is that of
  `TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Root.Basis`.
-/

public section

open scoped Matrix

namespace TauCeti.TypeDSpinCarrier

open Multiplicative

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n)

include hn in
private theorem weight_reflection (i j : Fin n) (a : Fin (dimension n)) :
    basisWeight n (basisReflection n i a) j =
      basisWeight n a j - basisWeight n a i * CartanMatrix.D n i j := by
  simpa only [basisWeight, signSet_basisReflection] using
    DynkinType.typeDSpinWeight_typeDSpinReflection_apply hn i j (signSet n a)

private theorem weight_range (i : Fin n) (a : Fin (dimension n)) :
    basisWeight n a i = -1 ∨ basisWeight n a i = 0 ∨ basisWeight n a i = 1 :=
  DynkinType.typeDSpinWeight_apply_eq_neg_one_or_eq_zero_or_eq_one (signSet n a) i

private theorem basisWeight_injective : Function.Injective (basisWeight n) := by
  intro a b h
  apply (Fintype.equivFin (Finset (Fin n))).symm.injective
  exact DynkinType.typeDSpinWeight_injective h

private theorem root_column (k : Fin n ⊕ Fin n) (a : Fin (dimension n)) :
    (fun r ↦ rootIntMatrix n hn k r a) =
      if basisWeight n a (Sum.elim id id k) = (Sum.elim (fun _ ↦ -1) (fun _ ↦ 1) k : ℤ)
      then Pi.single (basisReflection n (Sum.elim id id k) a) 1 else 0 := by
  classical
  cases k with
  | inl i =>
    dsimp only [Sum.elim, id]
    by_cases h : basisWeight n a i = -1
    · have hc := (polarization n).typeDSpinRep_serreE_exteriorBasis
        (polarizationBasis n) hn i (signSet n a) h
      have he : rep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (serreRootGenerator (CartanMatrix.D n) (.inl i)))
          (latticeBasis n a : ExteriorAlgebra ℚ (polarization n).W) =
          (1 : ℤˣ) • (latticeBasis n (basisReflection n i a) :
            ExteriorAlgebra ℚ (polarization n).W) := by
        simpa only [serreRootGenerator_inl, coe_latticeBasis, signSet_basisReflection,
          one_smul] using hc
      simp only [h, ite_true]
      ext r
      simp only [rootIntMatrix_apply_of_eq n hn (.inl i) he, Units.val_one,
        Pi.single_apply]
    · simp only [h, ite_false]
      ext r
      exact rootIntMatrix_inl_eq_zero_of_ne_basisReflection n hn i (fun ha ↦ (h ha).elim)
  | inr i =>
    dsimp only [Sum.elim, id]
    by_cases h : basisWeight n a i = 1
    · have hc := (polarization n).typeDSpinRep_serreF_exteriorBasis
        (polarizationBasis n) hn i (signSet n a) h
      have he : rep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (serreRootGenerator (CartanMatrix.D n) (.inr i)))
          (latticeBasis n a : ExteriorAlgebra ℚ (polarization n).W) =
          (1 : ℤˣ) • (latticeBasis n (basisReflection n i a) :
            ExteriorAlgebra ℚ (polarization n).W) := by
        simpa only [serreRootGenerator_inr, coe_latticeBasis, signSet_basisReflection,
          one_smul] using hc
      simp only [h, ite_true]
      ext r
      simp only [rootIntMatrix_apply_of_eq n hn (.inr i) he, Units.val_one,
        Pi.single_apply]
    · simp only [h, ite_false]
      ext r
      apply rootIntMatrix_eq_zero_of_weight_ne
      intro hw
      have hi := congrFun hw i
      rw [Pi.sub_apply, TypeDStd.rootGeneratorWeight_inr, CartanMatrix.D_diag] at hi
      have hr := weight_range n i r
      have ha := weight_range n i a
      have hgap : basisWeight n r i - basisWeight n a i ≠ -2 := by omega
      exact hgap hi

private theorem root_mulVec (k : Fin n ⊕ Fin n) (a : Fin (dimension n))
    (A : Type*) [CommRing A] (t : Multiplicative A) :
    ((rootSubgroupPoints n hn k A t :
        Matrix.GeneralLinearGroup (Fin (dimension n)) A) : Matrix _ _ A) *ᵥ
        Pi.single a 1 = Pi.single a 1 +
      if basisWeight n a (Sum.elim id id k) = (Sum.elim (fun _ ↦ -1) (fun _ ↦ 1) k : ℤ)
      then toAdd t • Pi.single (basisReflection n (Sum.elim id id k) a) 1 else 0 := by
  classical
  rw [coe_rootSubgroupPoints_eq_one_add_smul, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.mulVec_single_one]
  have hc := root_column n hn k a
  split_ifs with h
  · rw [ite_eq_left h] at hc
    congr 1
    congr 1
    ext r
    simpa [Pi.single_apply] using congrArg (fun f ↦ (f r : A)) hc
  · rw [ite_eq_right h] at hc
    congr 1
    ext r
    have hr := congrFun hc r
    simp only [Pi.zero_apply] at hr
    simp only [Pi.smul_apply, Matrix.col_apply, Matrix.map_apply, hr, Int.cast_zero,
      smul_eq_mul, mul_zero, Pi.zero_apply]

private def word (i : Fin n) (A : Type*) [CommRing A] :=
  rootSubgroupPoints n hn (.inl i) A (ofAdd 1) *
    rootSubgroupPoints n hn (.inr i) A (ofAdd (-1)) *
    rootSubgroupPoints n hn (.inl i) A (ofAdd 1)

private theorem word_mulVec (i : Fin n) (a : Fin (dimension n))
    (A : Type*) [CommRing A] :
    ((word n hn i A : Matrix.GeneralLinearGroup (Fin (dimension n)) A) : Matrix _ _ A) *ᵥ
        Pi.single a 1 =
      (if basisWeight n a i = 1 then (-1 : A) else 1) •
        Pi.single (basisReflection n i a) 1 := by
  classical
  have hr := weight_reflection n hn i i a
  rw [CartanMatrix.D_diag] at hr
  have hrr := basisReflection_involutive n i a
  have hzero := (basisReflection_eq_self_iff n i a).2
  simp only [word, Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
  rcases weight_range n i a with h | h | h
  all_goals
    simp only [h] at hr
    norm_num only at hr
    simp only [root_mulVec, Sum.elim_inl, Sum.elim_inr, id_eq, h, hr, hrr,
      toAdd_ofAdd, Matrix.mulVec_add, ite_true, one_smul, neg_one_smul, Matrix.mulVec_neg]
    norm_num only
    simp only [ite_false, one_smul, Matrix.mulVec_zero, add_zero]
    first
    | exact (congrArg (fun b ↦ Pi.single b (1 : A)) (hzero h)).symm
    | abel

include hn in
private theorem reflection_comm (i j : Fin n) (hij : CartanMatrix.D n i j = 0)
    (a : Fin (dimension n)) :
    basisReflection n i (basisReflection n j a) =
      basisReflection n j (basisReflection n i a) := by
  have hji : CartanMatrix.D n j i = 0 := (CartanMatrix.D_isSymm n).apply i j |>.trans hij
  apply basisWeight_injective n
  funext k
  simp only [weight_reflection n hn, hij, hji, mul_zero, sub_zero]
  rw [sub_sub, sub_sub, add_comm]

private theorem braid_coordinate (x y z p q : ℤ) :
    z - x * p - (y - x * (-1)) * q -
        (x - x * 2 - (y - x * (-1)) * (-1)) * p =
      z - y * q - (x - y * (-1)) * p -
        (y - y * 2 - (x - y * (-1)) * (-1)) * q := by
  ring

include hn in
private theorem reflection_braid (i j : Fin n) (hij : CartanMatrix.D n i j = -1)
    (a : Fin (dimension n)) :
    basisReflection n i (basisReflection n j (basisReflection n i a)) =
      basisReflection n j (basisReflection n i (basisReflection n j a)) := by
  have hji : CartanMatrix.D n j i = -1 := (CartanMatrix.D_isSymm n).apply i j |>.trans hij
  apply basisWeight_injective n
  funext k
  simp only [weight_reflection n hn, hij, hji, CartanMatrix.D_diag]
  exact braid_coordinate _ _ _ _ _

include hn in
private theorem weight_reflection_reflection (i j : Fin n)
    (hij : CartanMatrix.D n i j = -1) (a : Fin (dimension n)) :
    basisWeight n (basisReflection n j (basisReflection n i a)) i = basisWeight n a j := by
  have hji : CartanMatrix.D n j i = -1 := (CartanMatrix.D_isSymm n).apply i j |>.trans hij
  have hcoordinate (x y : ℤ) : x - x * 2 - (y - x * (-1)) * (-1) = y := by ring
  simp only [weight_reflection n hn, hij, hji, CartanMatrix.D_diag]
  exact hcoordinate _ _

/-- Pinned simple Weyl words at orthogonal nodes commute, over every commutative ring. -/
theorem rootSubgroupPoints_weyl_mul_comm_of_cartan_eq_zero
    (i j : Fin n) (hij : CartanMatrix.D n i j = 0) (A : Type*) [CommRing A] :
    let w := fun k ↦ rootSubgroupPoints n hn (.inl k) A (ofAdd 1) *
      rootSubgroupPoints n hn (.inr k) A (ofAdd (-1)) *
      rootSubgroupPoints n hn (.inl k) A (ofAdd 1)
    w i * w j = w j * w i := by
  classical
  -- The displayed local word is exactly the private definition used for the column calculation.
  change word n hn i A * word n hn j A = word n hn j A * word n hn i A
  have hji : CartanMatrix.D n j i = 0 := (CartanMatrix.D_isSymm n).apply i j |>.trans hij
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro a
  simp only [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
    word_mulVec, Matrix.mulVec_smul, weight_reflection n hn, hij, hji, mul_zero, sub_zero,
    reflection_comm n hn i j hij, smul_smul]
  congr 1
  exact mul_comm _ _

/-- Pinned simple Weyl words at adjacent type-D nodes satisfy the length-three braid relation,
including the edges meeting the fork, over every commutative ring. -/
theorem rootSubgroupPoints_weyl_braid_of_cartan_eq_neg_one
    (i j : Fin n) (hij : CartanMatrix.D n i j = -1) (A : Type*) [CommRing A] :
    let w := fun k ↦ rootSubgroupPoints n hn (.inl k) A (ofAdd 1) *
      rootSubgroupPoints n hn (.inr k) A (ofAdd (-1)) *
      rootSubgroupPoints n hn (.inl k) A (ofAdd 1)
    w i * w j * w i = w j * w i * w j := by
  classical
  -- Both sides use the literal pinned root words, with no choice of normalizer representatives.
  change word n hn i A * word n hn j A * word n hn i A =
    word n hn j A * word n hn i A * word n hn j A
  have hji : CartanMatrix.D n j i = -1 := (CartanMatrix.D_isSymm n).apply i j |>.trans hij
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro a
  have hleft := weight_reflection_reflection n hn i j hij a
  have hright := weight_reflection_reflection n hn j i hji a
  simp only [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
    word_mulVec, Matrix.mulVec_smul, hleft, hright, reflection_braid n hn i j hij,
    weight_reflection n hn, hij, hji, mul_neg_one, sub_neg_eq_add, smul_smul]
  congr 1
  ac_rfl

end

end TauCeti.TypeDSpinCarrier

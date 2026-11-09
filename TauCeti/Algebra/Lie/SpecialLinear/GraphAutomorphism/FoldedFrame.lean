/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Lie.Matrix.Single
public import TauCeti.Algebra.Lie.SpecialLinear.GraphAutomorphism.SkewAdjoint
public import TauCeti.Algebra.Lie.SpecialLinear.GraphAutomorphism.Symplectic
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Basic
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# The symplectic frame in the type-A fixed Lie algebra

The paired-coordinate equivalence identifies the fixed algebra of the pinned reversal of
`sl_(2k+2)` with `sp_(2k+2)`. This file computes the inverse images of its numbered simple
raising, lowering and Cartan generators. A noncentral node gives the sum over its two-element
reversal orbit. The middle node occurs only once, and its raising and lowering vectors acquire
the sign `(-1)^k` from the specified change of coordinates. This sign must be retained when
comparing pinned frames, even though it cancels in the opposite-root bracket.

The form equivalence is Robert Boyer's construction in
`TauCeti.Algebra.Lie.SpecialLinear.GraphAutomorphism.Symplectic`; the rational frame is the
existing `TauCeti.SpStd` frame. No root basis or generation theorem is assumed here.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §7.9.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate III.
-/

public section

open Matrix LieAlgebra.SpecialLinear

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : ℕ) (A : Type*) [CommRing A] [Invertible (2 : A)]

/-- The fixed trace-zero algebra of the pinned type-A reversal in native symplectic coordinates. -/
noncomputable def typeASpecialLinearFixedSymplecticEquiv :
    (typeASpecialLinearGraphAutomorphism (2 * k + 1) A).toLieHom.fixedSubalgebra ≃ₗ⁅A⁆
      LieAlgebra.Symplectic.sp (Fin (k + 1)) A :=
  (typeASpecialLinearFixedSkewAdjointEquiv (2 * k + 1) A).trans
    (typeAGraphSkewAdjointSymplecticEquiv k A)

/-- The forward coordinate map on matrices. -/
@[simp]
theorem typeASpecialLinearFixedSymplecticEquiv_val
    (X : (typeASpecialLinearGraphAutomorphism (2 * k + 1) A).toLieHom.fixedSubalgebra) :
    (typeASpecialLinearFixedSymplecticEquiv k A X).val =
      typeASymplecticDiagonal k A *
        reindex (typeASymplecticIndex k).symm (typeASymplecticIndex k).symm X.val.val *
          typeASymplecticDiagonal k A := by
  simp [typeASpecialLinearFixedSymplecticEquiv]

/-- The inverse coordinate map on matrices. This is left explicit so that simplification
uses the simple-generator formulas below rather than expanding their coordinate changes. -/
theorem typeASpecialLinearFixedSymplecticEquiv_symm_val
    (Y : LieAlgebra.Symplectic.sp (Fin (k + 1)) A) :
    ((typeASpecialLinearFixedSymplecticEquiv k A).symm Y).val.val =
      reindex (typeASymplecticIndex k) (typeASymplecticIndex k)
        (typeASymplecticDiagonal k A * Y.val * typeASymplecticDiagonal k A) := by
  simp [typeASpecialLinearFixedSymplecticEquiv]

omit [Invertible (2 : A)] in
private theorem paired_single (a b : Fin (k + 1) ⊕ Fin (k + 1)) (c : A) :
    reindex (typeASymplecticIndex k) (typeASymplecticIndex k)
        (typeASymplecticDiagonal k A * single a b c * typeASymplecticDiagonal k A) =
      single (typeASymplecticIndex k a) (typeASymplecticIndex k b)
        (Sum.elim (fun _ : Fin (k + 1) ↦ 1)
          (fun i : Fin (k + 1) ↦ (-1 : A) ^ i.val) a * c *
          Sum.elim (fun _ : Fin (k + 1) ↦ 1)
            (fun i : Fin (k + 1) ↦ (-1 : A) ^ i.val) b) := by
  rw [typeASymplecticDiagonal_def, diagonal_mul_single_mul_diagonal]
  ext x y
  simp [reindex_apply, submatrix_apply, single_apply, Equiv.eq_symm_apply]

variable {A}

private theorem paired_short_indices (i : Fin k) :
    typeASymplecticIndex k (.inl i.castSucc) =
        (⟨i.val, by omega⟩ : Fin (2 * k + 1)).castSucc ∧
    typeASymplecticIndex k (.inl i.succ) =
        (⟨i.val, by omega⟩ : Fin (2 * k + 1)).succ := by
  constructor <;> apply Fin.ext <;> simp

variable (A)

omit [Invertible (2 : A)] in
private theorem paired_short_sign (i : Fin k) :
    (-1 : A) ^ (i.succ : Fin (k + 1)).val * (-1 : A) ^ i.castSucc.val = -1 := by
  rw [← pow_add]
  exact Odd.neg_one_pow ⟨i.val, by simp; omega⟩

/-- A noncentral raising generator becomes the sum of the two pinned type-A raising vectors. -/
@[simp]
theorem typeASpecialLinearFixedSymplecticEquiv_symm_rootGenerator_inl
    (i : Fin k) :
    let j : Fin (2 * k + 1) := ⟨i.val, by omega⟩
    ((typeASpecialLinearFixedSymplecticEquiv k ℚ).symm
      (SpStd.rootGenerator k (.inl i.castSucc))).val.val =
        single j.castSucc j.succ 1 + single j.rev.castSucc j.rev.succ 1 := by
  dsimp only
  rw [typeASpecialLinearFixedSymplecticEquiv_symm_val, SpStd.val_rootGenerator_inl,
    SpStd.positiveRootMatrix_of_ne_last k i.castSucc (by simp), mul_sub, sub_mul,
    ← coe_reindexLinearEquiv ℚ ℚ, map_sub]
  simp only [coe_reindexLinearEquiv, paired_single]
  have hs : Order.succ i.castSucc = i.succ := by simp
  rw [hs]
  simp only [Sum.elim_inl, Sum.elim_inr, mul_one, paired_short_sign]
  simp only [← rev_typeASymplecticIndex_inl, (paired_short_indices k i).1,
    (paired_short_indices k i).2, Fin.rev_succ, Fin.rev_castSucc, ← single_neg,
    sub_neg_eq_add]

/-- The middle raising generator is a single pinned vector with the coordinate-change sign. -/
@[simp]
theorem typeASpecialLinearFixedSymplecticEquiv_symm_rootGenerator_inl_last :
    ((typeASpecialLinearFixedSymplecticEquiv k ℚ).symm
      (SpStd.rootGenerator k (.inl (Fin.last k)))).val.val =
        single (⟨k, by omega⟩ : Fin (2 * k + 2)) ⟨k + 1, by omega⟩ ((-1 : ℚ) ^ k) := by
  rw [typeASpecialLinearFixedSymplecticEquiv_symm_val, SpStd.val_rootGenerator_inl,
    SpStd.positiveRootMatrix_last, paired_single]
  have h₁ : typeASymplecticIndex k (.inl (Fin.last k)) =
      (⟨k, by omega⟩ : Fin (2 * k + 2)) := by apply Fin.ext; simp
  have h₂ : typeASymplecticIndex k (.inr (Fin.last k)) =
      (⟨k + 1, by omega⟩ : Fin (2 * k + 2)) := by apply Fin.ext; simp; omega
  simp [h₁, h₂]

/-- A noncentral lowering generator becomes the sum of the two pinned type-A lowering vectors. -/
@[simp]
theorem typeASpecialLinearFixedSymplecticEquiv_symm_rootGenerator_inr
    (i : Fin k) :
    let j : Fin (2 * k + 1) := ⟨i.val, by omega⟩
    ((typeASpecialLinearFixedSymplecticEquiv k ℚ).symm
      (SpStd.rootGenerator k (.inr i.castSucc))).val.val =
        single j.succ j.castSucc 1 + single j.rev.succ j.rev.castSucc 1 := by
  dsimp only
  rw [typeASpecialLinearFixedSymplecticEquiv_symm_val, SpStd.val_rootGenerator_inr,
    SpStd.negativeRootMatrix_of_ne_last k i.castSucc (by simp), mul_sub, sub_mul,
    ← coe_reindexLinearEquiv ℚ ℚ, map_sub]
  simp only [coe_reindexLinearEquiv, paired_single]
  have hs : Order.succ i.castSucc = i.succ := by simp
  rw [hs]
  simp only [Sum.elim_inl, Sum.elim_inr, mul_one]
  rw [mul_comm ((-1 : ℚ) ^ i.castSucc.val), paired_short_sign]
  simp only [← rev_typeASymplecticIndex_inl, (paired_short_indices k i).1,
    (paired_short_indices k i).2, Fin.rev_succ, Fin.rev_castSucc, ← single_neg,
    sub_neg_eq_add]

/-- The middle lowering generator has the same coordinate-change sign as the raising generator. -/
@[simp]
theorem typeASpecialLinearFixedSymplecticEquiv_symm_rootGenerator_inr_last :
    ((typeASpecialLinearFixedSymplecticEquiv k ℚ).symm
      (SpStd.rootGenerator k (.inr (Fin.last k)))).val.val =
        single (⟨k + 1, by omega⟩ : Fin (2 * k + 2)) ⟨k, by omega⟩ ((-1 : ℚ) ^ k) := by
  rw [typeASpecialLinearFixedSymplecticEquiv_symm_val, SpStd.val_rootGenerator_inr,
    SpStd.negativeRootMatrix_last, paired_single]
  have h₁ : typeASymplecticIndex k (.inl (Fin.last k)) =
      (⟨k, by omega⟩ : Fin (2 * k + 2)) := by apply Fin.ext; simp
  have h₂ : typeASymplecticIndex k (.inr (Fin.last k)) =
      (⟨k + 1, by omega⟩ : Fin (2 * k + 2)) := by apply Fin.ext; simp; omega
  simp [h₁, h₂]

/-- A noncentral simple coroot becomes the sum over its two-element reversal orbit. -/
@[simp]
theorem typeASpecialLinearFixedSymplecticEquiv_symm_cartanGenerator
    (i : Fin k) :
    let j : Fin (2 * k + 1) := ⟨i.val, by omega⟩
    ((typeASpecialLinearFixedSymplecticEquiv k ℚ).symm
      (SpStd.cartanGenerator k i.castSucc)).val.val =
        (single j.castSucc j.castSucc 1 - single j.succ j.succ 1) +
          (single j.rev.castSucc j.rev.castSucc 1 - single j.rev.succ j.rev.succ 1) := by
  dsimp only
  rw [← (SpStd.isSl2Triple_rootGenerator k i.castSucc).lie_e_f, LieEquiv.map_lie]
  simp only [LieSubalgebra.coe_bracket]
  rw [typeASpecialLinearFixedSymplecticEquiv_symm_rootGenerator_inl,
    typeASpecialLinearFixedSymplecticEquiv_symm_rootGenerator_inr]
  simp only [add_lie, lie_add, Matrix.lie_single_single]
  simp only [Fin.ext_iff, Fin.val_rev, Fin.val_castSucc, Fin.val_succ, ite_true, mul_one]
  split_ifs <;> first | omega | simp

/-- The middle simple coroot occurs once; the two coordinate-change signs cancel. -/
@[simp]
theorem typeASpecialLinearFixedSymplecticEquiv_symm_cartanGenerator_last :
    ((typeASpecialLinearFixedSymplecticEquiv k ℚ).symm
      (SpStd.cartanGenerator k (Fin.last k))).val.val =
        single (⟨k, by omega⟩ : Fin (2 * k + 2)) ⟨k, by omega⟩ 1 -
          single (⟨k + 1, by omega⟩ : Fin (2 * k + 2)) ⟨k + 1, by omega⟩ 1 := by
  rw [← (SpStd.isSl2Triple_rootGenerator k (Fin.last k)).lie_e_f, LieEquiv.map_lie]
  simp only [LieSubalgebra.coe_bracket]
  rw [typeASpecialLinearFixedSymplecticEquiv_symm_rootGenerator_inl_last,
    typeASpecialLinearFixedSymplecticEquiv_symm_rootGenerator_inr_last,
    Matrix.lie_single_single]
  simp [← pow_add, ← two_mul, pow_mul]

end TauCeti

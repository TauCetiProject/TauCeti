/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Congruence
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Rank

/-!
# Congruence images of bounded-rank positive-semidefinite cones

Congruence by a possibly singular rectangular matrix sends the positive-semidefinite cone of
rank at most `r` to a closed set. Given an inner inverse `N` of the congruence matrix `M`, its
image consists of the positive-semidefinite matrices of rank at most `r` fixed by congruence
with `M * N`. This describes singular Gaussian-Gram supports without a closure operation.
-/

public section

open Set TauCeti

namespace Matrix

variable {p q : ℕ}

/-- With an inner inverse `N` satisfying `M * N * M = M`, the congruence image of the
positive-semidefinite rank-at-most-`r` cone consists exactly of the matrices in that cone
fixed by congruence with `M * N`. -/
theorem image_symmetricCongruenceLinearMap_setOf_posSemidef_rank_le
    (M : Matrix (Fin q) (Fin p) ℝ) (N : Matrix (Fin p) (Fin q) ℝ)
    (hMNM : M * N * M = M) (r : ℕ) :
    symmetricCongruenceLinearMap M ''
        {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (A : Matrix (Fin p) (Fin p) ℝ).PosSemidef ∧
            (A : Matrix (Fin p) (Fin p) ℝ).rank ≤ r} =
      {A : selfAdjoint.submodule ℝ (Matrix (Fin q) (Fin q) ℝ) |
        (A : Matrix (Fin q) (Fin q) ℝ).PosSemidef ∧
          (A : Matrix (Fin q) (Fin q) ℝ).rank ≤ r ∧
          symmetricCongruenceLinearMap (M * N) A = A} := by
  ext A
  constructor
  · rintro ⟨B, ⟨hB, hr⟩, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [coe_symmetricCongruenceLinearMap_apply]
      exact (conjTranspose_eq_transpose_of_trivial M) ▸ hB.mul_mul_conjTranspose_same M
    · rw [coe_symmetricCongruenceLinearMap_apply]
      exact ((rank_mul_le_left (M * (B : Matrix (Fin p) (Fin p) ℝ)) Mᵀ).trans
        (rank_mul_le_right M (B : Matrix (Fin p) (Fin p) ℝ))).trans hr
    · rw [← LinearMap.comp_apply, ← symmetricCongruenceLinearMap_mul, hMNM]
  · rintro ⟨hA, hr, hfix⟩
    refine ⟨symmetricCongruenceLinearMap N A, ⟨?_, ?_⟩, ?_⟩
    · rw [coe_symmetricCongruenceLinearMap_apply]
      exact (conjTranspose_eq_transpose_of_trivial N) ▸ hA.mul_mul_conjTranspose_same N
    · rw [coe_symmetricCongruenceLinearMap_apply]
      exact ((rank_mul_le_left (N * (A : Matrix (Fin q) (Fin q) ℝ)) Nᵀ).trans
        (rank_mul_le_right N (A : Matrix (Fin q) (Fin q) ℝ))).trans hr
    · rw [← LinearMap.comp_apply, ← symmetricCongruenceLinearMap_mul, hfix]

/-- Congruence with a matrix admitting an inner inverse has closed image on every
positive-semidefinite cone with a rank bound, even when the congruence is singular. -/
theorem isClosed_image_symmetricCongruenceLinearMap_setOf_posSemidef_rank_le
    (M : Matrix (Fin q) (Fin p) ℝ) (N : Matrix (Fin p) (Fin q) ℝ)
    (hMNM : M * N * M = M) (r : ℕ) :
    IsClosed (symmetricCongruenceLinearMap M ''
      {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosSemidef ∧
          (A : Matrix (Fin p) (Fin p) ℝ).rank ≤ r}) := by
  rw [image_symmetricCongruenceLinearMap_setOf_posSemidef_rank_le M N hMNM]
  exact (isClosed_setOfPred_posSemidef.preimage continuous_subtype_val).inter
    ((TauCeti.isClosed_setOfPred_rank_le r).inter
      (isClosed_eq (LinearMap.continuous_of_finiteDimensional _) continuous_id))

end Matrix

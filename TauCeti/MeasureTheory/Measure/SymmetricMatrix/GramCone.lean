/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Congruence
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Rank
import TauCeti.LinearAlgebra.LinearMap.PseudoInverse

/-!
# Congruence images of bounded-rank positive-semidefinite cones

Congruence by a possibly singular rectangular matrix sends the positive-semidefinite cone of
rank at most `r` to a closed set. Given an inner inverse `N` of the congruence matrix `M`, its
image consists of the positive-semidefinite matrices of rank at most `r` fixed by congruence
with `M * N`. This describes singular Gaussian-Gram supports without a closure operation.
-/

public section

open Set TauCeti

variable {p q : ℕ}

namespace TauCeti

/-- The positive-semidefinite cone with a fixed upper rank bound is closed in the
space of self-adjoint matrices. -/
theorem isClosed_setOf_posSemidef_rank_le (r : ℕ) :
    IsClosed {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).PosSemidef ∧
        (A : Matrix (Fin p) (Fin p) ℝ).rank ≤ r} :=
  (isClosed_setOfPred_posSemidef.preimage continuous_subtype_val).inter
    (isClosed_setOfPred_rank_le r)

end TauCeti

namespace Matrix

/-- Rectangular congruence preserves positive semidefiniteness and an upper rank bound. -/
theorem mapsTo_symmetricCongruenceLinearMap_setOf_posSemidef_rank_le
    (M : Matrix (Fin q) (Fin p) ℝ) (r : ℕ) :
    MapsTo (symmetricCongruenceLinearMap M)
      {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosSemidef ∧
          (A : Matrix (Fin p) (Fin p) ℝ).rank ≤ r}
      {A : selfAdjoint.submodule ℝ (Matrix (Fin q) (Fin q) ℝ) |
        (A : Matrix (Fin q) (Fin q) ℝ).PosSemidef ∧
          (A : Matrix (Fin q) (Fin q) ℝ).rank ≤ r} := by
  rintro A ⟨hA, hr⟩
  constructor
  · rw [coe_symmetricCongruenceLinearMap_apply]
    exact (conjTranspose_eq_transpose_of_trivial M) ▸ hA.mul_mul_conjTranspose_same M
  · rw [coe_symmetricCongruenceLinearMap_apply]
    exact ((rank_mul_le_left (M * (A : Matrix (Fin p) (Fin p) ℝ)) Mᵀ).trans
      (rank_mul_le_right M (A : Matrix (Fin p) (Fin p) ℝ))).trans hr

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
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨hpos, hr⟩ := mapsTo_symmetricCongruenceLinearMap_setOf_posSemidef_rank_le M r hB
    refine ⟨hpos, hr, ?_⟩
    rw [← LinearMap.comp_apply, ← symmetricCongruenceLinearMap_mul, hMNM]
  · rintro ⟨hA, hr, hfix⟩
    refine ⟨symmetricCongruenceLinearMap N A,
      mapsTo_symmetricCongruenceLinearMap_setOf_posSemidef_rank_le N r ⟨hA, hr⟩, ?_⟩
    rw [← LinearMap.comp_apply, ← symmetricCongruenceLinearMap_mul, hfix]

/-- Rectangular congruence has closed image on every positive-semidefinite cone with a
rank bound, even when the congruence is singular. -/
theorem isClosed_image_symmetricCongruenceLinearMap_setOf_posSemidef_rank_le
    (M : Matrix (Fin q) (Fin p) ℝ) (r : ℕ) :
    IsClosed (symmetricCongruenceLinearMap M ''
      {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosSemidef ∧
          (A : Matrix (Fin p) (Fin p) ℝ).rank ≤ r}) := by
  obtain ⟨f, hf⟩ := M.toLin'.exists_comp_comp_eq_self
  let N := LinearMap.toMatrix' f
  have hMNM : M * N * M = M := Matrix.toLin'.injective (by
    simpa [Matrix.toLin'_mul, LinearMap.comp_assoc, N] using hf)
  rw [image_symmetricCongruenceLinearMap_setOf_posSemidef_rank_le M N hMNM]
  simpa only [← Set.ofPred_and, id_eq, and_assoc] using
    (isClosed_setOf_posSemidef_rank_le r).inter
    (isClosed_eq (LinearMap.continuous_of_finiteDimensional
      (symmetricCongruenceLinearMap (M * N))) continuous_id)

end Matrix

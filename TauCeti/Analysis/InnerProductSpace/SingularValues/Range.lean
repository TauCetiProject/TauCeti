/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SingularValues

/-!
# Lower bounds for the adjoint on the range

The nonzero singular values control the action of the adjoint on the range even when
the map has a kernel or fails to be surjective. This is the spectral estimate behind
gradient domination for least squares.
-/

public section

open Module

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- A lower bound on the squared stretch of the adjoint on the range is precisely a
lower bound on all nonzero squared singular values. -/
theorem mul_norm_sq_le_norm_adjoint_sq_iff (A : E →ₗ[𝕜] F) {μ : ℝ} :
    (∀ y ∈ A.range, μ * ‖y‖ ^ 2 ≤ ‖A.adjoint y‖ ^ 2) ↔
      ∀ i, A.singularValues i ≠ 0 → μ ≤ A.singularValues i ^ 2 := by
  constructor
  · intro h i hi
    have hdim : i < finrank 𝕜 E := lt_of_not_ge fun h ↦ hi (A.singularValues_of_finrank_le h)
    let j : Fin (finrank 𝕜 E) := ⟨i, hdim⟩
    have hj := h _ (A.mem_range_self (A.rightSingularBasis j))
    rw [← comp_apply, A.adjoint_comp_self_rightSingularBasis, norm_smul,
      OrthonormalBasis.norm_eq_one, mul_one, RCLike.norm_ofReal,
      abs_of_nonneg (sq_nonneg _), A.norm_apply_rightSingularBasis] at hj
    exact le_of_mul_le_mul_right (by simpa only [pow_two] using hj) (sq_pos_of_ne_zero hi)
  · intro h y hy
    let s := {i : Fin (finrank 𝕜 F) | A.adjoint.singularValues i ≠ 0}
    have hs : y ∈ A.adjoint.rightSingularBasis.spanIndices s := by
      obtain ⟨x, rfl⟩ := hy
      refine A.adjoint.rightSingularBasis.mem_spanIndices_iff.mpr fun i hi ↦ ?_
      have hz := A.adjoint.apply_rightSingularBasis_eq_zero_iff.mpr (not_not.mp hi)
      rw [OrthonormalBasis.repr_apply_apply, ← A.adjoint_inner_left, hz, inner_zero_left]
    have hbound (i : Fin (finrank 𝕜 F)) (hi : i ∈ s) : μ ≤ A.adjoint.singularValues i ^ 2 := by
      simpa only [singularValues_adjoint] using h i (by simpa only [s, Set.mem_ofPred_eq,
        singularValues_adjoint] using hi)
    have hq := le_re_inner_of_eigenbasis _ A.adjoint.rightSingularBasis
      A.adjoint.adjoint_comp_self_rightSingularBasis hbound hs
    rwa [comp_apply, A.adjoint.adjoint_inner_left, inner_self_eq_norm_sq] at hq

end LinearMap

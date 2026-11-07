/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Orthogonal families from orthogonal vectors

The spans of pairwise orthogonal vectors form an `OrthogonalFamily`. This construction allows
orthogonal-series results for subspaces to apply directly to a vector family, including one with
zero terms: the span of a zero vector is the zero subspace. In particular, the Pythagorean
identity `OrthogonalFamily.norm_sum` gives `‖∑ i ∈ s, v i‖² = ∑ i ∈ s, ‖v i‖²` for pairwise
orthogonal vectors, and passing to the limit gives the same identity for a convergent series of
pairwise orthogonal vectors. Normalizing the nonzero vectors of a pairwise orthogonal family gives
an orthonormal family.

Orthogonality also gives linear independence: a nonzero vector followed by a linearly independent
family of vectors orthogonal to it is linearly independent
(`LinearIndependent.finCons_of_inner_eq_zero`), as for an outward normal followed by a basis of a
tangent space.
-/

public section

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Pairwise orthogonal vectors determine an orthogonal family of their cyclic spans. Zero
vectors contribute the zero subspace, so no nonzero hypothesis is needed. -/
theorem orthogonalFamily_span_singleton {v : ι → E}
    (hv : Pairwise fun i j ↦ ⟪v i, v j⟫_𝕜 = 0) :
    OrthogonalFamily 𝕜 (fun i ↦ 𝕜 ∙ v i) (fun i ↦ (𝕜 ∙ v i).subtypeₗᵢ) := by
  apply OrthogonalFamily.of_pairwise
  intro i j hij
  simpa only [Function.onFun, Submodule.isOrtho_span, Set.mem_singleton_iff, forall_eq]
    using hv hij

/-- **Pythagoras for pairwise orthogonal vectors.** The squared norm of a finite sum of pairwise
orthogonal vectors is the sum of their squared norms. -/
theorem norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero {v : ι → E}
    (hv : Pairwise fun i j ↦ ⟪v i, v j⟫_𝕜 = 0) (s : Finset ι) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 :=
  (orthogonalFamily_span_singleton hv).norm_sum
    (fun i ↦ ⟨v i, Submodule.mem_span_singleton_self (v i)⟩) s

/-- **Pythagoras for an orthogonal series.** If pairwise orthogonal vectors sum to `y`, then
their squared norms sum to `‖y‖²`. -/
theorem hasSum_norm_sq_of_pairwise_inner_eq_zero {v : ι → E}
    (hv : Pairwise fun i j ↦ ⟪v i, v j⟫_𝕜 = 0) {y : E} (hy : HasSum v y) :
    HasSum (fun i ↦ ‖v i‖ ^ 2) (‖y‖ ^ 2) :=
  ((Filter.Tendsto.norm hy).pow 2).congr fun s ↦
    norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero hv s

/-- **Normalizing an orthogonal family.** If the vectors `vᵢ` are pairwise orthogonal, then the
normalized nonzero vectors `‖vᵢ‖⁻¹ vᵢ` are orthonormal. -/
theorem orthonormal_inv_norm_smul_of_pairwise_inner_eq_zero {v : ι → E}
    (hv : Pairwise fun i j ↦ ⟪v i, v j⟫_𝕜 = 0) :
    Orthonormal 𝕜 fun i : {i // v i ≠ 0} ↦ ((‖v i‖⁻¹ : ℝ) : 𝕜) • v i := by
  refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
  · simp [norm_smul, i.2]
  · simp [inner_smul_left, inner_smul_right, hv (Subtype.coe_ne_coe.mpr hij)]

end TauCeti

namespace LinearIndependent

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A nonzero vector followed by a linearly independent family of vectors orthogonal to it is
linearly independent. -/
theorem finCons_of_inner_eq_zero {n : ℕ} {p : E} (hp : p ≠ 0) {v : Fin n → E}
    (hv : LinearIndependent 𝕜 v) (horth : ∀ i, inner 𝕜 p (v i) = 0) :
    LinearIndependent 𝕜 (Fin.cons p v : Fin (n + 1) → E) := by
  refine hv.finCons fun hmem ↦ hp ?_
  have hle : Submodule.span 𝕜 (Set.range v) ≤ (𝕜 ∙ p)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.2 (horth i)
  exact inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hmem))

end LinearIndependent

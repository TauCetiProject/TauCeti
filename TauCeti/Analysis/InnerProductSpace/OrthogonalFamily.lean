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
orthogonal vectors. Applied to the images of an orthonormal basis under a linear map `T`, it gives
`‖T x‖² = ∑ᵢ ‖⟪eᵢ, x⟫‖² ‖T eᵢ‖²` whenever these images are pairwise orthogonal.
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

end TauCeti

namespace LinearMap

open scoped InnerProductSpace

variable {𝕜 E F ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [Fintype ι]

/-- **Pythagoras for a diagonal map.** If `T` sends an orthonormal basis `(eᵢ)` to pairwise
orthogonal vectors, then `‖T x‖² = ∑ᵢ ‖⟪eᵢ, x⟫‖² ‖T eᵢ‖²`. -/
theorem norm_apply_sq_eq_sum_of_pairwise_inner_eq_zero (T : E →ₗ[𝕜] F)
    (e : OrthonormalBasis ι 𝕜 E) (hT : Pairwise fun i j ↦ ⟪T (e i), T (e j)⟫_𝕜 = 0) (x : E) :
    ‖T x‖ ^ 2 = ∑ i, ‖⟪e i, x⟫_𝕜‖ ^ 2 * ‖T (e i)‖ ^ 2 := by
  have hv : Pairwise fun i j ↦ ⟪⟪e i, x⟫_𝕜 • T (e i), ⟪e j, x⟫_𝕜 • T (e j)⟫_𝕜 = 0 :=
    fun i j hij ↦ by simp [inner_smul_left, inner_smul_right, hT hij]
  conv_lhs => rw [← e.sum_repr' x, map_sum]
  simp only [map_smul]
  rw [TauCeti.norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero hv]
  simp [norm_smul, mul_pow]

end LinearMap

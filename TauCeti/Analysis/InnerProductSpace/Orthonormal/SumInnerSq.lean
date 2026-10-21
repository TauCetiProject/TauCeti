/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The bilinear square sum of the coordinates in an orthonormal basis

For an orthonormal basis `b` of an inner product space, the sum `∑ⱼ ⟪b j, v⟫²` of the squared
coordinates of `v` is a bilinear, not sesquilinear, quadratic form in `v`. Unlike
`∑ⱼ ‖⟪b j, v⟫‖² = ‖v‖²` (`OrthonormalBasis.sum_sq_norm_inner_right`), it is not determined by the
norm, but it is bounded by it: `‖∑ⱼ ⟪b j, v⟫²‖ ≤ ‖v‖²`.

Over `ℂ`, the bound is attained on the real span of a rotated basis `ζ • b j`, for a unit complex
number `ζ`: there `∑ⱼ ⟪b j, v⟫² = ζ² ‖v‖²`. This real span has real dimension the complex
dimension (`Module.Basis.finrank_span_smul`).

## Main results

* `OrthonormalBasis.norm_sum_inner_sq_le`: `‖∑ⱼ ⟪b j, v⟫²‖ ≤ ‖v‖²`.
* `OrthonormalBasis.sum_inner_sq_eq_of_mem_span_smul`: on the real span of `ζ • b j`, `‖ζ‖ = 1`,
  `∑ⱼ ⟪b j, v⟫² = ζ² ‖v‖²`.
-/

public section

open scoped InnerProductSpace

namespace OrthonormalBasis

variable {ι : Type*} [Fintype ι]

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The bilinear square sum of the coordinates in an orthonormal basis is bounded by the squared
norm: `‖∑ⱼ ⟪b j, v⟫²‖ ≤ ‖v‖²`. -/
theorem norm_sum_inner_sq_le (b : OrthonormalBasis ι 𝕜 E) (v : E) :
    ‖∑ j, ⟪b j, v⟫_𝕜 ^ 2‖ ≤ ‖v‖ ^ 2 := by
  rw [← b.sum_sq_norm_inner_right]
  exact (norm_sum_le _ _).trans_eq (by simp)

end RCLike

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- On the real span of a rotated orthonormal basis `ζ • b j`, for a unit complex number `ζ`, the
bilinear square sum of the coordinates is `∑ⱼ ⟪b j, v⟫² = ζ² ‖v‖²`. -/
theorem sum_inner_sq_eq_of_mem_span_smul (b : OrthonormalBasis ι ℂ E) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    {v : E} (hv : v ∈ Submodule.span ℝ (Set.range fun j ↦ ζ • b j)) :
    ∑ j, ⟪b j, v⟫_ℂ ^ 2 = ζ ^ 2 * ‖v‖ ^ 2 := by
  obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
  have hk (k : ι) : ⟪b k, ∑ j, t j • ζ • b j⟫_ℂ = ζ * t k := by
    have h : ∑ j, t j • ζ • b j = ∑ j, (ζ * t j) • b j := by
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← Complex.coe_smul, smul_smul, mul_comm]
    rw [h, b.orthonormal.inner_right_fintype]
  rw [← Complex.ofReal_pow, ← b.sum_sq_norm_inner_right]
  simp only [hk, norm_mul, hζ, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
    ← Finset.mul_sum]
  push_cast
  ring

end OrthonormalBasis

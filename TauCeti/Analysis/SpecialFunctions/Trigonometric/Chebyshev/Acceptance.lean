module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Measure

/-!
# Low-degree Chebyshev `T` acceptance checks

This file records the explicit degree-zero and degree-one consequences of the normalized
Chebyshev `T` mode API.  The `OrthogonalL2Bases` roadmap asks the Chebyshev basis construction
to expose the acceptance checks
`⟨T₀,T₀⟩ = π`, `⟨T₁,T₁⟩ = π / 2`, and `⟨T₀,T₁⟩ = 0`; the lemmas here package those checks, together
with their normalized `L²(measureT)` consumer forms.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial.Chebyshev

/-! ## Explicit low-degree normalized modes -/

/-- The zeroth normalized Chebyshev `T` mode is the constant `1 / √π`. -/
@[simp]
lemma normalizedChebyshevT_zero_apply (x : ℝ) :
    normalizedChebyshevT 0 x = (Real.sqrt Real.pi)⁻¹ := by
  rw [normalizedChebyshevT_def, chebyshevTNormSq_zero]
  simp

/-- The first normalized Chebyshev `T` mode is `x / √(π / 2)`. -/
@[simp]
lemma normalizedChebyshevT_one_apply (x : ℝ) :
    normalizedChebyshevT 1 x = x / Real.sqrt (Real.pi / 2) := by
  rw [normalizedChebyshevT_def, chebyshevTNormSq_of_ne_zero (by norm_num)]
  simp

/-- The `L²(measureT)` representative of the zeroth normalized Chebyshev mode is
the constant scalar `1 / √π`. -/
lemma coeFn_normalizedChebyshevTLp_zero {𝕜 : Type*} [RCLike 𝕜] :
    ⇑(normalizedChebyshevTLp 𝕜 0) =ᵐ[Polynomial.Chebyshev.measureT]
      fun _ : ℝ => (algebraMap ℝ 𝕜) ((Real.sqrt Real.pi)⁻¹) := by
  filter_upwards [coeFn_normalizedChebyshevTLp (𝕜 := 𝕜) 0] with x hx
  rw [hx, normalizedChebyshevT_zero_apply]

/-- The `L²(measureT)` representative of the first normalized Chebyshev mode is
the scalar-cast function `x / √(π / 2)`. -/
lemma coeFn_normalizedChebyshevTLp_one {𝕜 : Type*} [RCLike 𝕜] :
    ⇑(normalizedChebyshevTLp 𝕜 1) =ᵐ[Polynomial.Chebyshev.measureT]
      fun x : ℝ => (algebraMap ℝ 𝕜) (x / Real.sqrt (Real.pi / 2)) := by
  filter_upwards [coeFn_normalizedChebyshevTLp (𝕜 := 𝕜) 1] with x hx
  rw [hx, normalizedChebyshevT_one_apply]

/-! ## Unnormalized roadmap acceptance checks -/

/-- The zeroth Chebyshev `T` polynomial has squared `L²(measureT)` norm `π`. -/
lemma integral_eval_T_real_zero_mul_self_measureT :
    ∫ x, (T ℝ 0).eval x * (T ℝ 0).eval x ∂Polynomial.Chebyshev.measureT = Real.pi := by
  simpa using integral_eval_T_real_mul_self_measureT 0

/-- The first Chebyshev `T` polynomial has squared `L²(measureT)` norm `π / 2`. -/
lemma integral_eval_T_real_one_mul_self_measureT :
    ∫ x, (T ℝ 1).eval x * (T ℝ 1).eval x ∂Polynomial.Chebyshev.measureT =
      Real.pi / 2 := by
  simpa [chebyshevTNormSq_of_ne_zero (by norm_num : (1 : ℕ) ≠ 0)] using
    integral_eval_T_real_mul_self_measureT 1

/-- The zeroth and first Chebyshev `T` polynomials are orthogonal in `L²(measureT)`. -/
lemma integral_eval_T_real_zero_mul_one_measureT :
    ∫ x, (T ℝ 0).eval x * (T ℝ 1).eval x ∂Polynomial.Chebyshev.measureT = 0 := by
  simpa using integral_eval_T_real_mul_eval_T_real_measureT_of_ne
    (by norm_num : (0 : ℕ) ≠ 1)

/-- The first and zeroth Chebyshev `T` polynomials are orthogonal in `L²(measureT)`. -/
lemma integral_eval_T_real_one_mul_zero_measureT :
    ∫ x, (T ℝ 1).eval x * (T ℝ 0).eval x ∂Polynomial.Chebyshev.measureT = 0 := by
  simpa using integral_eval_T_real_mul_eval_T_real_measureT_of_ne
    (by norm_num : (1 : ℕ) ≠ 0)

/-! ## Normalized roadmap acceptance checks -/

/-- The zeroth normalized Chebyshev mode has squared integral one. -/
lemma integral_normalizedChebyshevT_zero_mul_self_measureT :
    ∫ x, normalizedChebyshevT 0 x * normalizedChebyshevT 0 x
        ∂Polynomial.Chebyshev.measureT = 1 := by
  simpa using integral_normalizedChebyshevT_mul_normalizedChebyshevT_measureT_eq_ite 0 0

/-- The first normalized Chebyshev mode has squared integral one. -/
lemma integral_normalizedChebyshevT_one_mul_self_measureT :
    ∫ x, normalizedChebyshevT 1 x * normalizedChebyshevT 1 x
        ∂Polynomial.Chebyshev.measureT = 1 := by
  simpa using integral_normalizedChebyshevT_mul_normalizedChebyshevT_measureT_eq_ite 1 1

/-- The zeroth and first normalized Chebyshev modes are orthogonal. -/
lemma integral_normalizedChebyshevT_zero_mul_one_measureT :
    ∫ x, normalizedChebyshevT 0 x * normalizedChebyshevT 1 x
        ∂Polynomial.Chebyshev.measureT = 0 := by
  simpa using integral_normalizedChebyshevT_mul_normalizedChebyshevT_measureT_eq_ite 0 1

/-- The first and zeroth normalized Chebyshev modes are orthogonal. -/
lemma integral_normalizedChebyshevT_one_mul_zero_measureT :
    ∫ x, normalizedChebyshevT 1 x * normalizedChebyshevT 0 x
        ∂Polynomial.Chebyshev.measureT = 0 := by
  simpa using integral_normalizedChebyshevT_mul_normalizedChebyshevT_measureT_eq_ite 1 0

/-- The zeroth normalized Chebyshev `L²(measureT)` vector has norm one. -/
@[simp]
lemma norm_normalizedChebyshevTLp_zero {𝕜 : Type*} [RCLike 𝕜] :
    ‖normalizedChebyshevTLp 𝕜 0‖ = 1 :=
  (orthonormal_normalizedChebyshevTLp (𝕜 := 𝕜)).norm_eq_one 0

/-- The first normalized Chebyshev `L²(measureT)` vector has norm one. -/
@[simp]
lemma norm_normalizedChebyshevTLp_one {𝕜 : Type*} [RCLike 𝕜] :
    ‖normalizedChebyshevTLp 𝕜 1‖ = 1 :=
  (orthonormal_normalizedChebyshevTLp (𝕜 := 𝕜)).norm_eq_one 1

/-- The zeroth normalized Chebyshev `L²(measureT)` vector has inner product one with itself. -/
@[simp]
lemma inner_normalizedChebyshevTLp_zero_self {𝕜 : Type*} [RCLike 𝕜] :
    inner 𝕜 (normalizedChebyshevTLp 𝕜 0) (normalizedChebyshevTLp 𝕜 0) = 1 := by
  simp

/-- The first normalized Chebyshev `L²(measureT)` vector has inner product one with itself. -/
@[simp]
lemma inner_normalizedChebyshevTLp_one_self {𝕜 : Type*} [RCLike 𝕜] :
    inner 𝕜 (normalizedChebyshevTLp 𝕜 1) (normalizedChebyshevTLp 𝕜 1) = 1 := by
  simp

/-- The zeroth and first normalized Chebyshev `L²(measureT)` vectors are orthogonal. -/
@[simp]
lemma inner_normalizedChebyshevTLp_zero_one {𝕜 : Type*} [RCLike 𝕜] :
    inner 𝕜 (normalizedChebyshevTLp 𝕜 0) (normalizedChebyshevTLp 𝕜 1) = 0 := by
  simp

/-- The first and zeroth normalized Chebyshev `L²(measureT)` vectors are orthogonal. -/
@[simp]
lemma inner_normalizedChebyshevTLp_one_zero {𝕜 : Type*} [RCLike 𝕜] :
    inner 𝕜 (normalizedChebyshevTLp 𝕜 1) (normalizedChebyshevTLp 𝕜 0) = 0 := by
  simp

end TauCeti

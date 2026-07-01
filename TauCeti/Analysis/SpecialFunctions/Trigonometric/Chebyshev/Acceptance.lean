module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Measure

/-!
# Low-degree normalized Chebyshev `T` modes

This file records explicit degree-zero and degree-one formulas for the normalized Chebyshev `T`
mode API. The general orthogonality theorems in the measure file supply the indexed acceptance
checks; the lemmas here expose the corresponding normalized modes to consumers.
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

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# Test functions on an interval against primitives

For a test function `φ` on an open interval `(x₀, x₁)`, the derivative `φ'` has integral zero, and
the primitive `Φ(t) = ∫_{x₀}^t f` of a function `f` integrable on `(x₀, x₁)` satisfies
`∫ φ' Φ = -∫ φ f`. So `Φ` has distributional derivative `f` on `(x₀, x₁)`, although it need not be
differentiable anywhere. The second identity is integration by parts
(`TauCeti.intervalIntegral.integral_deriv_smul_primitive_eq_sub_of_le`), using that `φ` vanishes
at the endpoints.

## Main results

* `TestFunction.integral_Ioo_deriv_eq_zero`: `∫_{(x₀, x₁)} φ' = 0`.
* `TestFunction.integral_Ioo_deriv_smul_primitive`: `∫_{(x₀, x₁)} φ' Φ = -∫_{(x₀, x₁)} φ f`.
-/

public section

open MeasureTheory Set
open scoped Distributions

namespace TestFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x₀ x₁ : ℝ}

/-- The derivative of a test function on an open interval has integral zero over the interval. -/
theorem integral_Ioo_deriv_eq_zero (φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, E)) :
    ∫ t in Ioo x₀ x₁, deriv φ t = 0 := by
  rcases le_or_gt x₁ x₀ with hx | hx
  · simp [Ioo_eq_empty_of_le hx]
  by_cases hE : CompleteSpace E
  swap
  · exact integral_of_not_completeSpace hE
  have hdφ : Continuous (deriv φ) := φ.contDiff.continuous_deriv (by simp)
  have hφ0 : φ x₀ = 0 := φ.zero_on_compl (by simp)
  have hφ1 : φ x₁ = 0 := φ.zero_on_compl (by simp)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.le,
    intervalIntegral.integral_deriv_eq_sub
      (fun t _ => (φ.contDiff.differentiable (by simp)) t) (hdφ.intervalIntegrable _ _),
    hφ0, hφ1, sub_zero]

/-- Against a test function `φ` on `(x₀, x₁)`, the primitive `t ↦ ∫_{x₀}^t f` of a function
integrable on `(x₀, x₁)` has distributional derivative `f`:
`∫_{(x₀, x₁)} φ' (∫_{x₀}^t f) = -∫_{(x₀, x₁)} φ f`. -/
theorem integral_Ioo_deriv_smul_primitive (φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ)) {f : ℝ → E}
    (hf : IntegrableOn f (Ioo x₀ x₁)) :
    ∫ t in Ioo x₀ x₁, deriv φ t • ∫ s in x₀..t, f s = -∫ t in Ioo x₀ x₁, φ t • f t := by
  rcases le_or_gt x₁ x₀ with hx | hx
  · simp [Ioo_eq_empty_of_le hx]
  have h := TauCeti.intervalIntegral.integral_deriv_smul_primitive_eq_sub_of_le hx.le
    (φ.contDiff.of_le (by exact_mod_cast le_top))
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hx.le).2 hf)
  have hφ1 : φ x₁ = 0 := φ.zero_on_compl (by simp)
  simpa only [hφ1, zero_smul, zero_sub,
    intervalIntegral.integral_of_le hx.le, integral_Ioc_eq_integral_Ioo] using h

end TestFunction

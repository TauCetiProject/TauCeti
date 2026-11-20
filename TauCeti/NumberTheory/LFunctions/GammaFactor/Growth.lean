/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Reciprocal.Order
public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta
public import TauCeti.NumberTheory.LFunctions.GammaFactor.Basic

/-!
# The order of the reciprocal gamma factor

The analytic reciprocal `invGammaFactor d` of the gamma factor of an analytic L-function record
is a finite product of shifted reciprocals `1/Γ_ℝ` and `1/Γ_ℂ`, so it has order at most one by
the bounds of `TauCeti.Analysis.SpecialFunctions.Gamma.Reciprocal.Order`. For the `ζ` record it is
`1/Γ_ℝ`, whose order is exactly one.

## Main results

* `TauCeti.LFunctions.AnalyticLFunctionData.orderLE_invGammaFactor`: the analytic reciprocal of
  the gamma factor of every record has order at most one.
* `TauCeti.LFunctions.riemannZetaData_invGammaFactor`: for the `ζ` record it is `1/Γ_ℝ`.
* `TauCeti.LFunctions.orderLE_invGammaFactor_riemannZetaData_iff`: for the `ζ` record the
  order is exactly one.

## References

* H. Davenport, *Multiplicative Number Theory*, §11.
-/

public section

open Complex

namespace TauCeti.LFunctions

namespace AnalyticLFunctionData

variable (d : AnalyticLFunctionData)

/-- The analytic reciprocal of the gamma factor of a record has order at most one. -/
theorem orderLE_invGammaFactor : OrderLE d.invGammaFactor 1 := by
  rw [funext d.invGammaFactor_eq_prod]
  refine (OrderLE.multisetProd fun μ _ ↦ ?_).mul (OrderLE.multisetProd fun ν _ ↦ ?_)
  · simpa using orderLE_inv_Gammaℝ.comp_mul_add 1 μ
  · simpa using orderLE_inv_Gammaℂ.comp_mul_add 1 ν

end AnalyticLFunctionData

/-- The analytic reciprocal of the gamma factor of the `ζ` record is `1/Γ_ℝ`. -/
@[simp]
theorem riemannZetaData_invGammaFactor (s : ℂ) :
    riemannZetaData.invGammaFactor s = (Gammaℝ s)⁻¹ := by
  rw [AnalyticLFunctionData.invGammaFactor_def, riemannZetaData_gammaFactor]

/-- For the `ζ` record the analytic reciprocal of the gamma factor has order exactly one: order
at most `A` holds exactly when `1 ≤ A`. -/
theorem orderLE_invGammaFactor_riemannZetaData_iff {A : ℝ} :
    OrderLE riemannZetaData.invGammaFactor A ↔ 1 ≤ A := by
  rw [funext riemannZetaData_invGammaFactor, orderLE_inv_Gammaℝ_iff]

end TauCeti.LFunctions

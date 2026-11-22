/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.RingTheory.PowerSeries.Exp
public import TauCeti.Analysis.Analytic.TaylorSeries

/-!
# Formal Taylor series for the exponential function

Identities evaluating `TauCeti.taylorSeries` at `0` for `z ↦ NormedSpace.exp (a * z)`,
`NormedSpace.exp`, and `z ↦ NormedSpace.exp z - 1` over any `[RCLike 𝕜]`.

## Main results

* `NormedSpace.taylorSeries_exp_const_mul_at_zero`:
  `TauCeti.taylorSeries (fun z ↦ NormedSpace.exp (a * z)) 0 =`
  `PowerSeries.rescale a (PowerSeries.exp 𝕜)`.
* `NormedSpace.taylorSeries_exp_at_zero`:
  `TauCeti.taylorSeries (NormedSpace.exp : 𝕜 → 𝕜) 0 = PowerSeries.exp 𝕜`.
* `NormedSpace.taylorSeries_exp_sub_one_at_zero`:
  `TauCeti.taylorSeries (fun z ↦ NormedSpace.exp z - 1) 0 = PowerSeries.exp 𝕜 - 1`.
-/

public section

noncomputable section

namespace NormedSpace

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The formal Taylor series at `0` of `z ↦ NormedSpace.exp (a * z)` is
`PowerSeries.rescale a (PowerSeries.exp 𝕜)`. -/
theorem taylorSeries_exp_const_mul_at_zero (a : 𝕜) :
    TauCeti.taylorSeries (fun z : 𝕜 => NormedSpace.exp (a * z)) 0 =
      PowerSeries.rescale a (PowerSeries.exp 𝕜) := by
  have hexp : HasFPowerSeriesAt (fun z : 𝕜 => NormedSpace.exp (a * z))
      ((expSeries 𝕜 𝕜).compContinuousLinearMap (a • ContinuousLinearMap.id 𝕜 𝕜)) 0 := by
    have h0 : HasFPowerSeriesAt (NormedSpace.exp : 𝕜 → 𝕜) (expSeries 𝕜 𝕜)
        ((a • ContinuousLinearMap.id 𝕜 𝕜) 0) := by
      simpa using hasFPowerSeriesAt_exp_zero_of_radius_pos (expSeries_radius_pos 𝕜 𝕜)
    simpa [Function.comp_def, smul_eq_mul] using h0.compContinuousLinearMap
  ext n
  rw [hexp.coeff_taylorSeries n, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
    FormalMultilinearSeries.coeff]
  simp only [FormalMultilinearSeries.compContinuousLinearMap,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, Pi.one_apply, mul_one, expSeries_apply_eq,
    one_div, map_inv₀, map_natCast, mul_comm]

/-- The formal Taylor series at `0` of `NormedSpace.exp` is `PowerSeries.exp 𝕜`. -/
theorem taylorSeries_exp_at_zero :
    TauCeti.taylorSeries (NormedSpace.exp : 𝕜 → 𝕜) 0 = PowerSeries.exp 𝕜 := by
  simpa using taylorSeries_exp_const_mul_at_zero (1 : 𝕜)

/-- The formal Taylor series at `0` of `z ↦ NormedSpace.exp z - 1` is
`PowerSeries.exp 𝕜 - 1`. -/
theorem taylorSeries_exp_sub_one_at_zero :
    TauCeti.taylorSeries (fun z : 𝕜 => NormedSpace.exp z - 1) 0 = PowerSeries.exp 𝕜 - 1 := by
  have hfn : (fun z : 𝕜 => NormedSpace.exp z - 1) =
      (NormedSpace.exp : 𝕜 → 𝕜) - fun _ : 𝕜 => (1 : 𝕜) := rfl
  have hexp : AnalyticAt 𝕜 (NormedSpace.exp : 𝕜 → 𝕜) 0 :=
    (hasFPowerSeriesAt_exp_zero_of_radius_pos (expSeries_radius_pos 𝕜 𝕜)).analyticAt
  rw [hfn, TauCeti.taylorSeries_sub hexp analyticAt_const,
    taylorSeries_exp_at_zero, TauCeti.taylorSeries_const, map_one]

end NormedSpace

end

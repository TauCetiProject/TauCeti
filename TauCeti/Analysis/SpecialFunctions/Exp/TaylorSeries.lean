/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.RingTheory.PowerSeries.Exp
public import TauCeti.Analysis.Analytic.TaylorSeries
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv

/-!
# Formal Taylor series for the complex exponential function

Identities evaluating `TauCeti.taylorSeries` at `0` for `z ↦ Complex.exp (a * z)`,
`Complex.exp`, and `z ↦ Complex.exp z - 1`.

## Main results

* `Complex.taylorSeries_exp_const_mul_at_zero`:
  `TauCeti.taylorSeries (fun z ↦ Complex.exp (a * z)) 0 =`
  `PowerSeries.rescale a (PowerSeries.exp ℂ)`.
* `Complex.taylorSeries_exp_at_zero`: `TauCeti.taylorSeries Complex.exp 0 = PowerSeries.exp ℂ`.
* `Complex.taylorSeries_exp_sub_one_at_zero`:
  `TauCeti.taylorSeries (fun z ↦ Complex.exp z - 1) 0 = PowerSeries.exp ℂ - 1`.
-/

public section

noncomputable section

namespace Complex

/-- The formal Taylor series at `0` of `z ↦ Complex.exp (a * z)` is
`PowerSeries.rescale a (PowerSeries.exp ℂ)`. -/
theorem taylorSeries_exp_const_mul_at_zero (a : ℂ) :
    TauCeti.taylorSeries (fun z : ℂ => Complex.exp (a * z)) 0 =
      PowerSeries.rescale a (PowerSeries.exp ℂ) := by
  have hexp : AnalyticAt ℂ (fun z : ℂ => Complex.exp (a * z)) 0 := by fun_prop
  ext n
  rw [hexp.coeff_taylorSeries_eq_inv_factorial_smul_iteratedDeriv n,
    PowerSeries.coeff_rescale, PowerSeries.coeff_exp, _root_.iteratedDeriv_cexp_const_mul]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The formal Taylor series at `0` of `Complex.exp` is `PowerSeries.exp ℂ`. -/
theorem taylorSeries_exp_at_zero :
    TauCeti.taylorSeries Complex.exp 0 = PowerSeries.exp ℂ := by
  simpa using taylorSeries_exp_const_mul_at_zero (1 : ℂ)

/-- The formal Taylor series at `0` of `z ↦ Complex.exp z - 1` is `PowerSeries.exp ℂ - 1`. -/
theorem taylorSeries_exp_sub_one_at_zero :
    TauCeti.taylorSeries (fun z : ℂ => Complex.exp z - 1) 0 = PowerSeries.exp ℂ - 1 := by
  have hfn : (fun z : ℂ => Complex.exp z - 1) = Complex.exp - fun _ : ℂ => (1 : ℂ) := by
    ext z
    exact (Pi.sub_apply Complex.exp (fun _ : ℂ => (1 : ℂ)) z).symm
  rw [hfn, TauCeti.taylorSeries_sub (by fun_prop) (by fun_prop), taylorSeries_exp_at_zero,
    TauCeti.taylorSeries_const, map_one]

end Complex

end

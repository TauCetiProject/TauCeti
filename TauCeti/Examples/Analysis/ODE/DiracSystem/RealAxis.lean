/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.RealAxis
import TauCeti.Examples.Analysis.ODE.DiracSystem.HermiteBiehler

/-!
# Checks for the bounds of the Hermite–Biehler functions on the real axis

For a real constant potential `c` at `z = 0`, `E(t, 0) = e^{ct}` and `E~(t, 0) = -i e^{-ct}`.
When `ct ≥ 0`, the absolute integral of the potential norm equals `ct`, so `E` attains the
upper bound and `E~` the lower bound
(`TauCeti.Examples.DiracSystem.norm_diracHermiteBiehler_ofReal_const_spectralParam_zero`,
`TauCeti.Examples.DiracSystem.norm_diracHermiteBiehlerDirichlet_ofReal_const_spectralParam_zero`).
-/

public section

open MeasureTheory Set Matrix Complex

namespace TauCeti.Examples.DiracSystem

/-- The absolute integral of the norm of a real constant potential is `ct` when `ct ≥ 0`. -/
private theorem abs_integral_norm_const {c t : ℝ} (hct : 0 ≤ c * t) :
    |∫ _ in (0 : ℝ)..t, ‖(c : ℂ)‖| = c * t := by
  simpa [intervalIntegral.integral_const, smul_eq_mul, Complex.norm_real, abs_mul, mul_comm]
    using abs_of_nonneg hct

/-- At zero frequency, a real constant potential with `ct ≥ 0` attains the upper bound for
`|E(t, 0)|`. -/
theorem norm_diracHermiteBiehler_ofReal_const_spectralParam_zero {c t : ℝ} (hct : 0 ≤ c * t) :
    ‖diracHermiteBiehler (fun _ ↦ (c : ℂ)) t 0‖ =
      Real.exp |∫ _ in (0 : ℝ)..t, ‖(c : ℂ)‖| := by
  rw [abs_integral_norm_const hct, diracHermiteBiehler_ofReal_const_spectralParam_zero]
  exact Complex.norm_of_nonneg (Real.exp_pos _).le

/-- At zero frequency, a real constant potential with `ct ≥ 0` attains the lower bound for
`|E~(t, 0)|`. -/
theorem norm_diracHermiteBiehlerDirichlet_ofReal_const_spectralParam_zero {c t : ℝ}
    (hct : 0 ≤ c * t) :
    ‖diracHermiteBiehlerDirichlet (fun _ ↦ (c : ℂ)) t 0‖ =
      Real.exp (-|∫ _ in (0 : ℝ)..t, ‖(c : ℂ)‖|) := by
  rw [abs_integral_norm_const hct, diracHermiteBiehlerDirichlet_ofReal_const_spectralParam_zero,
    norm_mul, norm_neg, norm_I, one_mul]
  exact Complex.norm_of_nonneg (Real.exp_pos _).le

/-- The upper bound of `TauCeti.norm_diracHermiteBiehler_ofReal_le` at this potential. -/
example {c t : ℝ} :
    ‖diracHermiteBiehler (fun _ ↦ (c : ℂ)) t 0‖ ≤ Real.exp |∫ _ in (0 : ℝ)..t, ‖(c : ℂ)‖| :=
  norm_diracHermiteBiehler_ofReal_le
    (integrableOn_const isCompact_uIcc.measure_lt_top.ne) 0

end TauCeti.Examples.DiracSystem

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import TauCeti.NumberTheory.LSeries.GaussianTheta
import TauCeti.NumberTheory.ArithmeticFunction.Moebius

/-!
# Gaussian theta tail for quadratic twists

The joint tail integrates the norms of the normalized theta series of the given coefficients
and their Möbius twist. It is nonnegative and is integrable above a positive cutoff for
unit-bounded coefficients.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
PBC), commit `72fead102f663d5c7a407964a13dc0cf9d977207`, specifically `New.thetaTailIntegral`
in `grh/src/Lib/Analytic/QuadraticTwist.lean`.
-/

public section

noncomputable section

open MeasureTheory Real Set
open scoped ArithmeticFunction.Moebius

namespace TauCeti

/-- The joint theta tail used in quadratic-twist nonvanishing arguments. It integrates the
norms of the normalized theta series of `c` and its Möbius twist against `du / u` above `1 / T`. -/
def quadraticTwistGaussianThetaTailIntegral (j : Fin 2) (c : ℕ → ℂ) (T : ℝ) : ℝ :=
  ∫ u in Ioi T⁻¹, (‖gaussianThetaSeries j c u‖ +
    ‖gaussianThetaSeries j (fun n ↦ c n * μ n) u‖) / u

/-- Expand the joint quadratic-twist tail as a set integral. -/
theorem quadraticTwistGaussianThetaTailIntegral_def (j : Fin 2) (c : ℕ → ℂ) (T : ℝ) :
    quadraticTwistGaussianThetaTailIntegral j c T =
      ∫ u in Ioi T⁻¹, (‖gaussianThetaSeries j c u‖ +
        ‖gaussianThetaSeries j (fun n ↦ c n * μ n) u‖) / u := by
  unfold quadraticTwistGaussianThetaTailIntegral
  rfl

variable {j : Fin 2} {c : ℕ → ℂ}

/-- The full quadratic-twist theta tail integrand is integrable for positive `T` and
unit-bounded coefficients. -/
theorem integrableOn_quadraticTwistGaussianThetaTailIntegrand (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1)
    {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun u ↦ (‖gaussianThetaSeries j c u‖ +
      ‖gaussianThetaSeries j (fun n ↦ c n * μ n) u‖) / u) (Ioi T⁻¹) := by
  have hμ (n : ℕ+) : ‖c n * (μ n : ℂ)‖ ≤ 1 := by
    rw [mul_comm, ← zsmul_eq_mul]
    exact (ArithmeticFunction.norm_moebius_smul_le n (c n)).trans (hc n)
  have h := (integrableOn_norm_gaussianThetaSeries_div (j := j) hc (inv_pos.mpr hT)).add
    (integrableOn_norm_gaussianThetaSeries_div (j := j) (c := fun n ↦ c n * μ n)
      hμ (inv_pos.mpr hT))
  refine h.congr_fun (fun u _ ↦ ?_) measurableSet_Ioi
  exact (add_div ..).symm

/-- The quadratic-twist theta tail integral is nonnegative. -/
theorem quadraticTwistGaussianThetaTailIntegral_nonneg (T : ℝ) :
    0 ≤ quadraticTwistGaussianThetaTailIntegral j c T := by
  rw [quadraticTwistGaussianThetaTailIntegral_def]
  refine integral_nonneg fun u ↦ ?_
  obtain hu | hu := le_or_gt u 0
  · simp [gaussianThetaSeries_def, sqrt_eq_zero_of_nonpos hu]
  · positivity

end TauCeti

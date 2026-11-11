/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Divergence of power-weighted sine integrals at zero

For an exponent at most `-2`, the integral of `x ^ a * sin x` over `(ε, ∞)` diverges
to positive infinity as `ε` tends to zero from above. Each cutoff integral is absolutely
convergent. The divergent contribution comes from the origin, where the integrand
dominates a positive multiple of `1 / x`; the oscillating tail is absolutely integrable.

This distinguishes the unbounded sine centering from the convergent compensated kernels
used in constructing stable distributions.
-/

public section

open MeasureTheory Real Set Filter
open scoped Topology

namespace TauCeti

/-- Power-weighted sine integrals with exponent at most `-2` diverge to positive infinity
as the positive lower cutoff tends to zero, including the logarithmic boundary exponent. -/
theorem tendsto_integral_rpow_mul_sin_Ioi_nhdsGT_zero {a : ℝ} (ha : a ≤ -2) :
    Tendsto (fun ε : ℝ ↦ ∫ x in Ioi ε, x ^ a * sin x) (𝓝[>] 0) atTop := by
  have hint {ε : ℝ} (hε : 0 < ε) :
      IntegrableOn (fun x : ℝ ↦ x ^ a * sin x) (Ioi ε) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : a < -1) hε).mul_bdd
      (by fun_prop) (ae_of_all _ fun x ↦ by simpa using abs_sin_le_one x)
  -- The tail beyond one is fixed; a logarithmic lower bound on the initial segment suffices.
  have hlog : Tendsto (fun ε : ℝ ↦ -(log ε) / 2 +
      ∫ x in Ioi (1 : ℝ), x ^ a * sin x) (𝓝[>] 0) atTop :=
    (Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2)
      (tendsto_neg_atTop_iff.mpr tendsto_log_nhdsGT_zero)).atTop_add tendsto_const_nhds
  refine tendsto_atTop_mono' _ ?_ hlog
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with ε hε hε1
  have hε : 0 < ε := hε
  have hpow : IntervalIntegrable (fun x : ℝ ↦ x ^ a * sin x) volume ε 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hε1.le).mpr
      ((hint hε).mono_set Ioc_subset_Ioi_self)
  have hinv : IntervalIntegrable (fun x : ℝ ↦ x⁻¹ / 2) volume ε 1 :=
    (ContinuousOn.intervalIntegrable (u := fun x : ℝ ↦ x⁻¹) (fun x hx ↦
      (continuousAt_inv₀ (by
        rw [uIcc_of_le hε1.le] at hx
        exact (hε.trans_le hx.1).ne')).continuousWithinAt)).div_const 2
  have hle : -(log ε) / 2 ≤ ∫ x in ε..1, x ^ a * sin x := by
    have h := intervalIntegral.integral_mono_on hε1.le hinv hpow (fun x hx ↦ ?_)
    · simpa [intervalIntegral.integral_div, integral_inv_of_pos hε zero_lt_one,
        Real.log_inv] using h
    · have hx0 : 0 < x := hε.trans_le hx.1
      have hsin : x / 2 ≤ sin x := by
        have hcube : x ^ 3 ≤ x := pow_le_of_le_one hx0.le hx.2 (by norm_num)
        linarith [sin_ge_sub_cube hx0.le]
      have hp : x ^ (-2 : ℝ) ≤ x ^ a :=
        rpow_le_rpow_of_exponent_ge hx0 hx.2 ha
      calc
        x⁻¹ / 2 = x ^ (-2 : ℝ) * (x / 2) := by
          rw [rpow_neg hx0.le, rpow_two]
          field_simp
        _ ≤ x ^ a * sin x := mul_le_mul hp hsin (by positivity) (by positivity)
  rw [← intervalIntegral.integral_interval_add_Ioi (hint hε) (hint zero_lt_one)]
  linarith

end TauCeti

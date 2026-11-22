/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Growth
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical
import TauCeti.Analysis.SpecialFunctions.Log.GrowthScale

/-!
# Elementary Gamma majorants on the right half-plane

Comparison with real Gamma gives a power bound depending only on the real part when
`1 ≤ Re z`. One recurrence extends this to the closed right half-plane, retaining the
reciprocal norm factor which accounts for growth near zero. Both estimates hold at every
height. The closed-half-plane bound includes Mathlib's totalized value `Gamma 0 = 0`.

A nonnegative real dilation of Gamma consequently has logarithmic-exponential growth outside
the unit disk. This includes the half-scale Gamma function in the real archimedean factor,
without omitting the annulus where its argument has norm between one half and one.

## References

* NIST Digital Library of Mathematical Functions, [5.6.6](https://dlmf.nist.gov/5.6.E6).
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, §5.1.
* Matteo Cipollina, PNT+,
  `PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Gamma/StripBounds.lean`,
  especially `norm_bound_re_ge_one`, `stirling_bound_re_ge_zero`, and `half_bound_re_ge_zero`.
  These motivate the polynomial and dilation bounds here.
-/

public section

open Real Set

namespace Complex

/-- On `Re z ≥ 1`, Gamma is bounded by a power of the real part, uniformly in the height. -/
theorem norm_Gamma_le_re_add_one_rpow {z : ℂ} (hz : 1 ≤ z.re) :
    ‖Gamma z‖ ≤ (z.re + 1) ^ (z.re + 1) := by
  refine (norm_Gamma_le_Gamma_re (by linarith)).trans ?_
  by_cases hz2 : 2 ≤ z.re
  · exact Real.Gamma_le_add_one_rpow hz2
  · have hmem : z.re ∈ Icc 1 2 := ⟨hz, (lt_of_not_ge hz2).le⟩
    have hseg : z.re ∈ segment ℝ (1 : ℝ) 2 := by
      simpa only [segment_eq_Icc (by norm_num : (1 : ℝ) ≤ 2)] using hmem
    have hΓ : Real.Gamma z.re ≤ 1 := by
      simpa only [Real.Gamma_one, Real.Gamma_two, max_self] using
        Real.convexOn_Gamma.le_on_segment (by norm_num) (by norm_num) hseg
    exact hΓ.trans (Real.one_le_rpow (by linarith) (by linarith))

/-- A pointwise bound on the closed right half-plane, retaining the reciprocal norm factor
near zero. At zero both sides are zero, using Mathlib's totalized Gamma function. -/
theorem norm_Gamma_le_re_add_two_rpow_div {z : ℂ} (hz : 0 ≤ z.re) :
    ‖Gamma z‖ ≤ (z.re + 2) ^ (z.re + 2) / ‖z‖ := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp [Gamma_zero]
  have h := norm_Gamma_le_re_add_one_rpow (z := z + 1) (by simp; linarith)
  rw [Gamma_add_one z hz0, norm_mul] at h
  apply (le_div_iff₀ (norm_pos_iff.mpr hz0)).mpr
  simpa only [add_re, one_re, add_assoc, one_add_one_eq_two, mul_comm] using h

/-- Every nonnegative real dilation of Gamma has logarithmic-exponential growth on the closed
right half-plane outside the unit disk. The constant may depend on the dilation. -/
theorem exists_norm_Gamma_mul_le_exp_mul_log {c : ℝ} (hc : 0 ≤ c) :
    ∃ C > 0, ∀ z : ℂ, 0 ≤ z.re → 1 ≤ ‖z‖ →
      ‖Gamma (c * z)‖ ≤ Real.exp (C * ‖z‖ * Real.log (1 + ‖z‖)) := by
  rcases eq_or_lt_of_le hc with hc0 | hc
  · subst c
    exact ⟨1, zero_lt_one, fun z _ _ ↦ by
      simp only [ofReal_zero, zero_mul, Gamma_zero, norm_zero]; positivity⟩
  let D := (c + 2) * (2 * Real.log (c + 2) + 1)
  have hlog : 0 < Real.log (c + 2) := Real.log_pos (by linarith)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D + 2 / c, add_pos hD (by positivity), fun z hz hr ↦ ?_⟩
  have hy : 0 < c * z.re + 2 := by positivity
  have hprod : (c * z.re + 2) * Real.log (c * z.re + 2) ≤
      D * ‖z‖ * Real.log (1 + ‖z‖) := by
    have hle : c * z.re + 2 ≤ c * ‖z‖ + 2 := by nlinarith [re_le_norm z]
    exact (mul_le_mul hle (Real.log_le_log hy hle)
      (Real.log_nonneg (by nlinarith : 1 ≤ c * z.re + 2))
      (by positivity : 0 ≤ c * ‖z‖ + 2)).trans (Real.mul_add_two_mul_log_le hc.le hr)
  have hΓ := norm_Gamma_le_re_add_two_rpow_div (z := c * z) (by simpa using mul_nonneg hc.le hz)
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, norm_mul, norm_real,
    Real.norm_of_nonneg hc.le] at hΓ
  rw [Real.rpow_def_of_pos hy] at hΓ
  calc
    ‖Gamma (c * z)‖ ≤ Real.exp (D * ‖z‖ * Real.log (1 + ‖z‖)) / c :=
      hΓ.trans (div_le_div₀ (by positivity) (Real.exp_le_exp.mpr (by nlinarith)) hc
        (by nlinarith))
    _ ≤ Real.exp ((D + 2 / c) * ‖z‖ * Real.log (1 + ‖z‖)) := by
      have hfirst : 1 + (‖z‖ - 1) = ‖z‖ := by ring
      have hsecond : 2 + (‖z‖ - 1) = 1 + ‖z‖ := by ring
      simpa only [hfirst, hsecond, div_eq_mul_inv, mul_comm] using
        Real.mul_exp_mul_one_add_mul_log_two_add_le (C := D) (D := c⁻¹) (r := ‖z‖ - 1)
          (inv_nonneg.mpr hc.le) (by linarith)

end Complex

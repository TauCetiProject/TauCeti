/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Decay on the left edge of a subtracted Perron contour

When shifting a finite-height contour for a difference of two Perron sums, the left edge can
be taken to `−∞` along a sequence of lines avoiding poles. On these lines the denominator
of `(b ^ s - a ^ s) / s` absorbs the growth of the logarithmic derivative, and both powers decay
uniformly in the ordinate. The statements use the interval-integral parameterization `s = c + it`,
so the contour factor `I` is not included.

For the contour method see D. Koukoulopoulos, *The Distribution of Prime Numbers*, Chapter 8,
proof of Theorem 5.1.
-/

public section

open Complex Filter
open scoped Interval Real Topology

namespace TauCeti

/-- On a vertical segment, a bound on the norm of the multiplier divided by `s` bounds the
subtracted Perron integral by the sum of the two real powers times the segment length. -/
theorem norm_integral_subtractedPerron_vertical_le {g : ℂ → ℂ} {a b c u v B : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hg : ∀ t ∈ Ι u v, ‖g ((c : ℂ) + t * I) / ((c : ℂ) + t * I)‖ ≤ B) :
    ‖∫ t in u..v, g ((c : ℂ) + t * I) *
        (((b : ℂ) ^ ((c : ℂ) + t * I) - (a : ℂ) ^ ((c : ℂ) + t * I)) /
          ((c : ℂ) + t * I))‖ ≤ B * (b ^ c + a ^ c) * |v - u| := by
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ ?_
  let z : ℂ := (c : ℂ) + t * I
  have hz : z.re = c := by simp [z]
  have hpow (x : ℝ) (hx : 0 ≤ x) : ‖(x : ℂ) ^ z‖ ≤ x ^ c := by
    simpa [arg_ofReal_of_nonneg hx, norm_real, abs_of_nonneg hx, hz] using
      norm_cpow_le (x : ℂ) z
  have hdiff := (norm_sub_le ((b : ℂ) ^ z) ((a : ℂ) ^ z)).trans
    (add_le_add (hpow b hb) (hpow a ha))
  have h := mul_le_mul (hg t ht) hdiff (norm_nonneg _) ((norm_nonneg _).trans (hg t ht))
  simpa only [z, ← norm_mul, div_mul_eq_mul_div, ← mul_div_assoc] using h

/-- A logarithmic bound for the multiplier on a family of vertical lines suffices to discard the
left edge as their abscissae tend to `−∞`. The bound is only needed on those lines, not between
them, so it can be used with the half-integer edges in a contour shift past trivial zeros. -/
theorem tendsto_integral_subtractedPerron_vertical_of_log_bound {ι : Type*} {l : Filter ι}
    {c : ι → ℝ} {g : ℂ → ℂ} {a b u v C q : ℝ} (ha : 1 < a) (hb : 1 < b)
    (hc : Tendsto c l atBot)
    (hg : ∀ᶠ i in l, ∀ t ∈ Ι u v,
      ‖g ((c i : ℂ) + t * I)‖ ≤ C * Real.log (q * (‖(c i : ℂ) + t * I‖ + 2))) :
    Tendsto (fun i ↦ ∫ t in u..v, g ((c i : ℂ) + t * I) *
      (((b : ℂ) ^ ((c i : ℂ) + t * I) - (a : ℂ) ^ ((c i : ℂ) + t * I)) /
        ((c i : ℂ) + t * I))) l (𝓝 0) := by
  have hquot : ∀ᶠ i in l, ∀ t ∈ Ι u v,
      ‖g ((c i : ℂ) + t * I) / ((c i : ℂ) + t * I)‖ ≤ 3 * |C| * |q| := by
    by_cases hq : q = 0
    · filter_upwards [hg] with i hi t ht
      have hzero : g ((c i : ℂ) + t * I) = 0 := by simpa [hq] using hi t ht
      simp [hzero, hq]
    have hthreshold := hc.eventually_le_atBot (min (-1) (-|q|⁻¹))
    filter_upwards [hg, hthreshold] with i hi hci t ht
    let z : ℂ := (c i : ℂ) + t * I
    have hzr : z.re = c i := by simp [z]
    have hcz : -c i ≤ ‖z‖ := by simpa only [hzr] using (neg_le_abs z.re).trans (abs_re_le_norm z)
    have h₁ : 1 ≤ ‖z‖ := by linarith [hci.trans (min_le_left _ _)]
    have h₂ : |q|⁻¹ ≤ ‖z‖ := by linarith [hci.trans (min_le_right _ _)]
    have hqpos : 0 < |q| := abs_pos.mpr hq
    have hlogarg : 1 ≤ |q| * (‖z‖ + 2) := by
      calc
        1 = |q| * |q|⁻¹ := (mul_inv_cancel₀ hqpos.ne').symm
        _ ≤ _ := by gcongr; linarith
    have hlog : Real.log (q * (‖z‖ + 2)) = Real.log (|q| * (‖z‖ + 2)) := by
      rw [← Real.log_abs (q * _), abs_mul, abs_of_pos (by positivity : 0 < ‖z‖ + 2)]
    have hmajor : ‖g z‖ ≤ 3 * |C| * |q| * ‖z‖ := calc
      _ ≤ C * Real.log (q * (‖z‖ + 2)) := hi t ht
      _ ≤ |C| * Real.log (|q| * (‖z‖ + 2)) := by
        rw [hlog]
        exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.log_nonneg hlogarg)
      _ ≤ |C| * (|q| * (‖z‖ + 2)) := by gcongr; exact Real.log_le_self (by positivity)
      _ ≤ 3 * |C| * |q| * ‖z‖ := by
        calc
          _ ≤ |C| * (|q| * (3 * ‖z‖)) := by gcongr; linarith
          _ = _ := by ring
    simpa only [norm_div] using (div_le_iff₀ (by linarith : 0 < ‖z‖)).mpr hmajor
  have hlim : Tendsto (fun i ↦ (3 * |C| * |q|) * (b ^ c i + a ^ c i) * |v - u|) l (𝓝 0) := by
    have hsum := ((tendsto_rpow_atBot_of_base_gt_one b hb).comp hc).add
      ((tendsto_rpow_atBot_of_base_gt_one a ha).comp hc)
    simpa using (hsum.const_mul (3 * |C| * |q|)).mul_const |v - u|
  refine tendsto_zero_iff_norm_tendsto_zero.mpr <|
    squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [hquot] with i hi using
    norm_integral_subtractedPerron_vertical_le
      (zero_le_one.trans ha.le) (zero_le_one.trans hb.le) hi

end TauCeti

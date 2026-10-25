/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.MeanInequalities

/-!
# The one-dimensional energy estimate for traces

A `C¹` function with values in a real inner product space has both endpoint norms controlled
by its value and derivative energies on a finite interval, with an explicit width-dependent
constant. No compact support is needed for this finite-interval estimate.

For `1 ≤ r`, a compactly supported `C¹` real function has the `r`-th power of its value at the
endpoint of a half-line bounded by the integral of `(r - 1) |g|ʳ + |g'|ʳ` on that half-line
(`TauCeti.abs_rpow_le_integral_Ioi`); for `r = 2` this is the `H¹` energy. Integrating this
estimate over the transverse variables supplies the flat-boundary `W^{1,p}` trace inequality.
The energy density `(r - 1) |u|ʳ + ‖Du‖ʳ` of a compactly supported `C¹` function on any normed
space is continuous with compact support (`TauCeti.continuous_rpow_energy`,
`TauCeti.hasCompactSupport_rpow_energy`), and `TauCeti.le_rpow_inv_mul_of_rpow_le` turns an
inequality `xʳ ≤ (r - 1) yʳ + zʳ` into the linear bound `x ≤ r ^ (1 / r) n` for `y, z ≤ n`.

The estimate follows the fundamental-theorem-of-calculus proof of the trace theorem in
L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.5.
-/

public section

namespace TauCeti

open MeasureTheory Set

/-- Both endpoint norms of a curve that is `C¹` near a closed interval are controlled by
its energy on that interval.
The coefficient of the value energy depends on the interval width; no compact support or
integrability outside the interval is required. -/
theorem norm_sq_add_norm_sq_le_integral_norm_sq_add_norm_deriv_sq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {g : ℝ → F} {a b : ℝ} (hg : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 g t)
    (hab : a < b) :
    ‖g a‖ ^ 2 + ‖g b‖ ^ 2 ≤
      ∫ t in a..b, (2 / (b - a) + 1) * ‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2 := by
  -- A signed affine weight gives the sum of both endpoint energies in one FTC identity.
  let q : ℝ → ℝ := fun t ↦ (2 * t - a - b) / (b - a)
  have hgc : ContinuousOn g (Icc a b) :=
    fun t ht ↦ (hg t ht).continuousAt.continuousWithinAt
  have hdc : ContinuousOn (deriv g) (Icc a b) :=
    fun t ht ↦ ((hg t ht).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hd (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt (fun t ↦ q t * ‖g t‖ ^ 2)
      (2 / (b - a) * ‖g t‖ ^ 2 + q t * (2 * inner ℝ (g t) (deriv g t))) t := by
    simpa only [q, mul_one, id_eq] using!
      ((((hasDerivAt_id t).const_mul 2).sub_const a |>.sub_const b).div_const
        (b - a)).mul ((hg t ht).differentiableAt one_ne_zero).hasDerivAt.norm_sq
  have hcq : Continuous q := by fun_prop
  have hleft := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hd t ((uIcc_of_le hab.le) ▸ ht))
    (ContinuousOn.intervalIntegrable_of_Icc hab.le
      ((continuousOn_const.mul (hgc.norm.pow 2)).add
        (hcq.continuousOn.mul (continuousOn_const.mul (hgc.inner hdc)))))
  have hqa : q a = -1 := by dsimp [q]; field_simp [sub_ne_zero.mpr hab.ne']; ring
  have hqb : q b = 1 := by dsimp [q]; field_simp [sub_ne_zero.mpr hab.ne']; ring
  rw [hqa, hqb] at hleft
  -- The weight has absolute value at most one; use Cauchy–Schwarz and Young's inequality.
  have hbound (t : ℝ) (ht : t ∈ Icc a b) :
      2 / (b - a) * ‖g t‖ ^ 2 + q t * (2 * inner ℝ (g t) (deriv g t)) ≤
        (2 / (b - a) + 1) * ‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2 := by
    have hq : |q t| ≤ 1 := by
      rw [abs_le]
      dsimp [q]
      constructor
      · rw [le_div_iff₀ (sub_pos.mpr hab)]; linarith [ht.1]
      · rw [div_le_iff₀ (sub_pos.mpr hab)]; linarith [ht.2]
    have hi := abs_real_inner_le_norm (g t) (deriv g t)
    have hmul : q t * inner ℝ (g t) (deriv g t) ≤ ‖g t‖ * ‖deriv g t‖ := by
      calc
        _ ≤ |q t * inner ℝ (g t) (deriv g t)| := le_abs_self _
        _ = |q t| * |inner ℝ (g t) (deriv g t)| := abs_mul _ _
        _ ≤ 1 * (‖g t‖ * ‖deriv g t‖) :=
          mul_le_mul hq hi (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    nlinarith [sq_nonneg (‖g t‖ - ‖deriv g t‖)]
  -- Integrate the pointwise estimate and substitute the endpoint identity.
  have hmono : (∫ t in a..b,
      2 / (b - a) * ‖g t‖ ^ 2 + q t * (2 * inner ℝ (g t) (deriv g t))) ≤
      ∫ t in a..b, (2 / (b - a) + 1) * ‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2 :=
    intervalIntegral.integral_mono_on hab.le
    (ContinuousOn.intervalIntegrable_of_Icc hab.le
      ((continuousOn_const.mul (hgc.norm.pow 2)).add
        (hcq.continuousOn.mul (continuousOn_const.mul (hgc.inner hdc)))))
    (((continuousOn_const.mul (hgc.norm.pow 2)).add
      (hdc.norm.pow 2)).intervalIntegrable_of_Icc hab.le) hbound
  rw [hleft] at hmono
  nlinarith

section Energy

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For `1 ≤ r`, the `Lʳ` energy density `(r - 1) |u|ʳ + ‖Du‖ʳ` of a `C¹` function is
continuous. -/
theorem continuous_rpow_energy {u : F → ℝ} (hu : ContDiff ℝ 1 u) {r : ℝ} (hr : 1 ≤ r) :
    Continuous fun x ↦ (r - 1) * |u x| ^ r + ‖fderiv ℝ u x‖ ^ r :=
  (continuous_const.mul (hu.continuous.abs.rpow_const fun _ ↦ Or.inr (zero_le_one.trans hr))).add
    ((hu.continuous_fderiv one_ne_zero).norm.rpow_const fun _ ↦ Or.inr (zero_le_one.trans hr))

/-- For `1 ≤ r`, the `Lʳ` energy density `(r - 1) |u|ʳ + ‖Du‖ʳ` of a compactly supported
function has compact support. -/
theorem hasCompactSupport_rpow_energy {u : F → ℝ} (hsupp : HasCompactSupport u) {r : ℝ}
    (hr : 1 ≤ r) : HasCompactSupport fun x ↦ (r - 1) * |u x| ^ r + ‖fderiv ℝ u x‖ ^ r := by
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le hr).ne'
  exact (hsupp.mono fun x hx hz ↦ hx (by simp [hz, hr0])).add
    ((hsupp.fderiv ℝ).mono fun x hx hz ↦ hx (by
      simp only [hz, norm_zero (E := F →L[ℝ] ℝ), Real.zero_rpow hr0]))

end Energy

private theorem integrable_rpow_energy {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hs : HasCompactSupport g) {r : ℝ} (hr : 1 ≤ r) :
    Integrable (fun t ↦ (r - 1) * |g t| ^ r + |deriv g t| ^ r) volume := by
  simpa only [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs] using
    (continuous_rpow_energy hg hr).integrable_of_hasCompactSupport
      (hasCompactSupport_rpow_energy hs hr)

/-- If `x ^ r ≤ (r - 1) y ^ r + z ^ r` for `1 ≤ r` and nonnegative `x`, `y`, `z`, with `y` and `z`
at most `n`, then `x ≤ r ^ (1 / r) n`. This turns the `Lʳ` trace inequality into a bound with
constant `r ^ (1 / r)` by the Sobolev norm. -/
theorem le_rpow_inv_mul_of_rpow_le {r x y z n : ℝ} (hr : 1 ≤ r) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hyn : y ≤ n) (hzn : z ≤ n) (h : x ^ r ≤ (r - 1) * y ^ r + z ^ r) :
    x ≤ r ^ r⁻¹ * n := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hn : 0 ≤ n := hy.trans hyn
  have h1 : y ^ r ≤ n ^ r := Real.rpow_le_rpow hy hyn hr0.le
  have h2 : z ^ r ≤ n ^ r := Real.rpow_le_rpow hz hzn hr0.le
  rw [← Real.rpow_le_rpow_iff hx (by positivity) hr0, Real.mul_rpow (by positivity) hn,
    ← Real.rpow_mul hr0.le, inv_mul_cancel₀ hr0.ne', Real.rpow_one]
  nlinarith [sub_nonneg.2 hr]

/-- **The one-dimensional `Lᵖ` trace estimate.** For `1 ≤ r`, the `r`-th power of the value at
the endpoint of a half-line of a compactly supported `C¹` function is controlled by
`(r - 1) |g|ʳ + |g'|ʳ` on that half-line. For `r = 2` the right side is the `H¹` energy. -/
theorem abs_rpow_le_integral_Ioi {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g)
    (a : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    |g a| ^ r ≤ ∫ t in Ioi a, (r - 1) * |g t| ^ r + |deriv g t| ^ r := by
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le hr).ne'
  have hint := integrable_rpow_energy hg hs hr
  rcases hr.eq_or_lt with rfl | hr1
  · -- For `r = 1`, the fundamental theorem of calculus on `[a, ∞)`.
    have hi := hs.integral_Ioi_deriv_eq hg a
    simp only [Real.rpow_one, sub_self, zero_mul, zero_add] at hint ⊢
    calc |g a| = |∫ t in Ioi a, deriv g t| := by rw [hi, abs_neg]
      _ ≤ ∫ t in Ioi a, |deriv g t| := abs_integral_le_integral_abs
  · -- For `r > 1`, the same argument for the `C¹` function `|g|ʳ`, whose derivative
    -- `r |g|ʳ⁻¹ g'` is bounded by Young's inequality.
    have hv : ContDiff ℝ 1 (fun t ↦ ‖g t‖ ^ r) := hg.norm_rpow hr1
    have hvs : HasCompactSupport (fun t ↦ ‖g t‖ ^ r) :=
      hs.mono fun t ht hzero ↦ ht (by simp [hzero, hr0])
    have hi := hvs.integral_Ioi_deriv_eq hv a
    have hdv : Integrable (fun t ↦ deriv (fun t ↦ ‖g t‖ ^ r) t) volume :=
      (hv.continuous_deriv le_rfl).integrable_of_hasCompactSupport hvs.deriv
    have hyoung : ∀ t, |deriv (fun t ↦ ‖g t‖ ^ r) t| ≤ (r - 1) * |g t| ^ r + |deriv g t| ^ r := by
      intro t
      have hd := norm_fderiv_norm_rpow_le (hg.differentiable one_ne_zero) (x := t) hr1
      rw [← norm_deriv_eq_norm_fderiv, ← norm_deriv_eq_norm_fderiv] at hd
      simp only [Real.norm_eq_abs] at hd
      refine hd.trans ?_
      -- Weighted AM-GM with weights `(r - 1) / r` and `1 / r`.
      have hw := Real.geom_mean_le_arith_mean2_weighted
        (div_nonneg (sub_nonneg.2 hr) (zero_le_one.trans hr))
        (one_div_nonneg.2 (zero_le_one.trans hr))
        (Real.rpow_nonneg (abs_nonneg (g t)) r) (Real.rpow_nonneg (abs_nonneg (deriv g t)) r)
        (by field_simp; ring)
      rw [← Real.rpow_mul (abs_nonneg _), ← Real.rpow_mul (abs_nonneg _),
        show r * ((r - 1) / r) = r - 1 by field_simp, show r * (1 / r) = 1 by field_simp,
        Real.rpow_one] at hw
      have hr' : 0 < r := zero_lt_one.trans hr1
      calc r * |g t| ^ (r - 1) * |deriv g t| = r * (|g t| ^ (r - 1) * |deriv g t|) := by ring
        _ ≤ r * ((r - 1) / r * |g t| ^ r + 1 / r * |deriv g t| ^ r) := by gcongr
        _ = (r - 1) * |g t| ^ r + |deriv g t| ^ r := by field_simp
    calc |g a| ^ r = ∫ t in Ioi a, -deriv (fun t ↦ ‖g t‖ ^ r) t := by
          rw [integral_neg, hi, neg_neg, Real.norm_eq_abs]
      _ ≤ ∫ t in Ioi a, (r - 1) * |g t| ^ r + |deriv g t| ^ r :=
          integral_mono hdv.neg.integrableOn hint.integrableOn fun t ↦
            (neg_le_abs _).trans (hyoung t)

/-- For `1 ≤ r`, the `r`-th power of a point value of a compactly supported `C¹` function is
controlled by `(r - 1) |g|ʳ + |g'|ʳ` on the whole line. -/
theorem abs_rpow_le_integral {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g)
    (a : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    |g a| ^ r ≤ ∫ t, (r - 1) * |g t| ^ r + |deriv g t| ^ r := by
  refine (abs_rpow_le_integral_Ioi hg hs a hr).trans
    (setIntegral_le_integral (integrable_rpow_energy hg hs hr)
      (Filter.Eventually.of_forall fun t ↦ ?_))
  have := Real.rpow_nonneg (abs_nonneg (g t)) r
  have := Real.rpow_nonneg (abs_nonneg (deriv g t)) r
  have := sub_nonneg.2 hr
  positivity

end TauCeti

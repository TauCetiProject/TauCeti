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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

/-!
# The one-dimensional energy estimate for traces

A `C¹` function with values in a real inner product space has both endpoint norms controlled
by its value and derivative energies on a finite interval, with an explicit width-dependent
constant. No compact support is needed for this finite-interval estimate.

For `1 ≤ r`, a compactly supported `C¹` curve in a real inner product space has the `r`-th power
of the norm of its value at the endpoint of a half-line bounded by the integral of
`(r - 1) ‖g‖ʳ + ‖g'‖ʳ` on that half-line (`TauCeti.norm_rpow_le_integral_Ioi`); for `r = 2` this
is the `H¹` energy. Integrating this estimate over the transverse variables supplies the
flat-boundary `W^{1,p}` trace inequality. The energy density `(r - 1) ‖u‖ʳ + ‖Du‖ʳ` of a
compactly supported `C¹` function between normed spaces is continuous with compact support
(`TauCeti.continuous_rpow_energy`, `TauCeti.hasCompactSupport_rpow_energy`), and
`TauCeti.le_rpow_inv_mul_of_rpow_le` turns an inequality `xʳ ≤ (r - 1) yʳ + zʳ` into the linear
bound `x ≤ r ^ r⁻¹ n` for `0 ≤ y, z ≤ n`.

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
  have hint : IntervalIntegrable
      (fun t ↦ 2 / (b - a) * ‖g t‖ ^ 2 + q t * (2 * inner ℝ (g t) (deriv g t))) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab.le
      ((continuousOn_const.mul (hgc.norm.pow 2)).add
        (hcq.continuousOn.mul (continuousOn_const.mul (hgc.inner hdc))))
  have hleft := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hd t ((uIcc_of_le hab.le) ▸ ht)) hint
  have hqa : q a = -1 := by dsimp [q]; field_simp [sub_ne_zero.mpr hab.ne']; ring
  have hqb : q b = 1 := by dsimp [q]; field_simp [sub_ne_zero.mpr hab.ne']; ring
  rw [hqa, hqb] at hleft
  -- The weight has absolute value at most one; use Cauchy–Schwarz and Young's inequality.
  have hbound (t : ℝ) (ht : t ∈ Icc a b) :
      2 / (b - a) * ‖g t‖ ^ 2 + q t * (2 * inner ℝ (g t) (deriv g t)) ≤
        (2 / (b - a) + 1) * ‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2 := by
    have hq : |q t| ≤ 1 := by
      dsimp only [q]
      rw [abs_div, abs_of_pos (sub_pos.2 hab), div_le_one (sub_pos.2 hab), abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hmul : q t * inner ℝ (g t) (deriv g t) ≤ ‖g t‖ * ‖deriv g t‖ :=
      (le_abs_self _).trans <| (abs_mul _ _).trans_le <|
        (mul_le_of_le_one_left (abs_nonneg _) hq).trans (abs_real_inner_le_norm _ _)
    nlinarith [sq_nonneg (‖g t‖ - ‖deriv g t‖)]
  -- Integrate the pointwise estimate and substitute the endpoint identity.
  calc ‖g a‖ ^ 2 + ‖g b‖ ^ 2 = ∫ t in a..b,
        2 / (b - a) * ‖g t‖ ^ 2 + q t * (2 * inner ℝ (g t) (deriv g t)) := by
        rw [hleft]; ring
    _ ≤ _ := intervalIntegral.integral_mono_on hab.le hint
      (((continuousOn_const.mul (hgc.norm.pow 2)).add
        (hdc.norm.pow 2)).intervalIntegrable_of_Icc hab.le) hbound

section Energy

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- For `1 ≤ r`, the `Lʳ` energy density `(r - 1) ‖u‖ʳ + ‖Du‖ʳ` of a `C¹` function is
continuous. -/
theorem continuous_rpow_energy {u : F → G} (hu : ContDiff ℝ 1 u) {r : ℝ} (hr : 1 ≤ r) :
    Continuous fun x ↦ (r - 1) * ‖u x‖ ^ r + ‖fderiv ℝ u x‖ ^ r :=
  (continuous_const.mul (hu.continuous.norm.rpow_const fun _ ↦ Or.inr (zero_le_one.trans hr))).add
    ((hu.continuous_fderiv one_ne_zero).norm.rpow_const fun _ ↦ Or.inr (zero_le_one.trans hr))

/-- For `1 ≤ r`, the `Lʳ` energy density `(r - 1) ‖u‖ʳ + ‖Du‖ʳ` of a compactly supported
function has compact support. -/
theorem hasCompactSupport_rpow_energy {u : F → G} (hsupp : HasCompactSupport u) {r : ℝ}
    (hr : 1 ≤ r) : HasCompactSupport fun x ↦ (r - 1) * ‖u x‖ ^ r + ‖fderiv ℝ u x‖ ^ r := by
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le hr).ne'
  exact (hsupp.mono fun x hx hz ↦ hx (by simp [hz, hr0])).add
    ((hsupp.fderiv ℝ).mono fun x hx hz ↦ hx (by simp [hz, hr0]))

/-- The energy density of a compactly supported `C¹` curve is integrable. -/
private theorem integrable_rpow_energy {g : ℝ → G} (hg : ContDiff ℝ 1 g)
    (hs : HasCompactSupport g) {r : ℝ} (hr : 1 ≤ r) :
    Integrable (fun t ↦ (r - 1) * ‖g t‖ ^ r + ‖deriv g t‖ ^ r) volume := by
  simpa only [← norm_deriv_eq_norm_fderiv] using
    (continuous_rpow_energy hg hr).integrable_of_hasCompactSupport
      (hasCompactSupport_rpow_energy hs hr)

end Energy

/-- If `x ^ r ≤ (r - 1) y ^ r + z ^ r` for `1 ≤ r` and nonnegative `y`, `z`, both at most `n`,
then `x ≤ r ^ r⁻¹ n`. This turns the `Lʳ` trace inequality into a bound with constant
`r ^ r⁻¹` by the Sobolev norm. -/
theorem le_rpow_inv_mul_of_rpow_le {r x y z n : ℝ} (hr : 1 ≤ r) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hyn : y ≤ n) (hzn : z ≤ n) (h : x ^ r ≤ (r - 1) * y ^ r + z ^ r) :
    x ≤ r ^ r⁻¹ * n := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hn : 0 ≤ n := hy.trans hyn
  -- A negative `x` is below the nonnegative right side.
  rcases lt_or_ge x 0 with hx | hx
  · exact hx.le.trans (by positivity)
  have h1 : y ^ r ≤ n ^ r := Real.rpow_le_rpow hy hyn hr0.le
  have h2 : z ^ r ≤ n ^ r := Real.rpow_le_rpow hz hzn hr0.le
  rw [← Real.rpow_le_rpow_iff hx (by positivity) hr0, Real.mul_rpow (by positivity) hn,
    ← Real.rpow_mul hr0.le, inv_mul_cancel₀ hr0.ne', Real.rpow_one]
  nlinarith [sub_nonneg.2 hr]

section Curve

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The one-dimensional `Lᵖ` trace estimate.** For `1 ≤ r`, the `r`-th power of the norm of the
value at the endpoint of a half-line of a compactly supported `C¹` curve in a real inner product
space is controlled by `(r - 1) ‖g‖ʳ + ‖g'‖ʳ` on that half-line. For `r = 2` the right side is
the `H¹` energy. -/
theorem norm_rpow_le_integral_Ioi {g : ℝ → E} (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g)
    (a : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    ‖g a‖ ^ r ≤ ∫ t in Ioi a, (r - 1) * ‖g t‖ ^ r + ‖deriv g t‖ ^ r := by
  rcases hr.eq_or_lt with rfl | hr1
  · -- For `r = 1`, the displacement from `a` to a point `c` beyond the support is at most the
    -- integral of the speed.
    have hint := integrable_rpow_energy hg hs le_rfl
    simp only [Real.rpow_one, sub_self, zero_mul, zero_add] at hint ⊢
    obtain ⟨b, hb⟩ := hs.isCompact.bddAbove
    set c := max a b + 1
    have hac : a ≤ c := by linarith [le_max_left a b]
    have hc : g c = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ by
      linarith [hb h, le_max_right a b]
    calc ‖g a‖ = ‖g c - g a‖ := by rw [hc, zero_sub, norm_neg]
      _ ≤ ∫ t in a..c, ‖deriv g t‖ :=
        norm_sub_le_integral_of_norm_deriv_le_of_le hac hg.continuous.continuousOn
          (hg.differentiable one_ne_zero).differentiableOn (.of_forall fun _ _ ↦ le_rfl)
          hint.intervalIntegrable
      _ ≤ ∫ t in Ioi a, ‖deriv g t‖ := by
        rw [intervalIntegral.integral_of_le hac]
        exact setIntegral_mono_set hint.integrableOn (.of_forall fun _ ↦ norm_nonneg _)
          (.of_forall fun _ h ↦ Ioc_subset_Ioi_self h)
  · -- For `r > 1`, the same argument for the `C¹` function `‖g‖ʳ`, whose derivative
    -- is bounded by `r ‖g‖ʳ⁻¹ ‖g'‖` and then by Young's inequality.
    have hr0 : r ≠ 0 := (zero_lt_one.trans hr1).ne'
    have hv : ContDiff ℝ 1 (fun t ↦ ‖g t‖ ^ r) := hg.norm_rpow hr1
    have hvs : HasCompactSupport (fun t ↦ ‖g t‖ ^ r) :=
      hs.mono fun t ht hzero ↦ ht (by simp [hzero, hr0])
    have hi := hvs.integral_Ioi_deriv_eq hv a
    have hdv : Integrable (fun t ↦ deriv (fun t ↦ ‖g t‖ ^ r) t) volume :=
      (hv.continuous_deriv le_rfl).integrable_of_hasCompactSupport hvs.deriv
    have hyoung : ∀ t, |deriv (fun t ↦ ‖g t‖ ^ r) t| ≤ (r - 1) * ‖g t‖ ^ r + ‖deriv g t‖ ^ r := by
      intro t
      have hd := norm_fderiv_norm_rpow_le (hg.differentiable one_ne_zero) (x := t) hr1
      rw [← norm_deriv_eq_norm_fderiv, ← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs] at hd
      refine hd.trans ?_
      -- Young's inequality with the conjugate exponents `r / (r - 1)` and `r`.
      have hw := Real.young_inequality_of_nonneg (Real.rpow_nonneg (norm_nonneg (g t)) (r - 1))
        (norm_nonneg (deriv g t)) (Real.HolderConjugate.conjExponent hr1).symm
      rw [← Real.rpow_mul (norm_nonneg _), Real.conjExponent,
        mul_div_cancel₀ _ (sub_ne_zero.2 hr1.ne')] at hw
      calc r * ‖g t‖ ^ (r - 1) * ‖deriv g t‖ = r * (‖g t‖ ^ (r - 1) * ‖deriv g t‖) := by ring
        _ ≤ r * (‖g t‖ ^ r / (r / (r - 1)) + ‖deriv g t‖ ^ r / r) := by gcongr
        _ = (r - 1) * ‖g t‖ ^ r + ‖deriv g t‖ ^ r := by field_simp
    calc ‖g a‖ ^ r = ∫ t in Ioi a, -deriv (fun t ↦ ‖g t‖ ^ r) t := by
          rw [integral_neg, hi, neg_neg]
      _ ≤ ∫ t in Ioi a, (r - 1) * ‖g t‖ ^ r + ‖deriv g t‖ ^ r :=
          integral_mono hdv.neg.integrableOn (integrable_rpow_energy hg hs hr).integrableOn
            fun t ↦ (neg_le_abs _).trans (hyoung t)

/-- For `1 ≤ r`, the `r`-th power of the norm of a point value of a compactly supported `C¹`
curve in a real inner product space is controlled by `(r - 1) ‖g‖ʳ + ‖g'‖ʳ` on the whole line. -/
theorem norm_rpow_le_integral {g : ℝ → E} (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g)
    (a : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    ‖g a‖ ^ r ≤ ∫ t, (r - 1) * ‖g t‖ ^ r + ‖deriv g t‖ ^ r :=
  (norm_rpow_le_integral_Ioi hg hs a hr).trans
    (setIntegral_le_integral (integrable_rpow_energy hg hs hr)
      (.of_forall fun t ↦ by have := sub_nonneg.2 hr; positivity))

end Curve

end TauCeti

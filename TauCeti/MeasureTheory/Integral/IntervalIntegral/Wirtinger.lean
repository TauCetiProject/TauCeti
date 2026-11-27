/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Wirtinger's inequality with one vanishing endpoint

An absolutely continuous function `f` on `[a, b]` with square-integrable derivative and vanishing
at one endpoint satisfies

`(π / (2 (b - a)))² ∫_a^b f² ≤ ∫_a^b f'²`,

with equality for `sin (π (t - a) / (2 (b - a)))` when `f(a) = 0` and for
`cos (π (t - a) / (2 (b - a)))` when `f(b) = 0`. This is the one-dimensional sharp
Poincaré–Friedrichs inequality: in Sobolev form it says that the first eigenvalue of `-u''` on
`(a, b)` with a Dirichlet condition at one endpoint and a Neumann condition at the other is
`(π / (2 (b - a)))²`.

## The argument

The proof is a Riccati identity, with no eigenfunction expansion
(`AbsolutelyContinuousOnInterval.sq_mul_integral_sq_le_integral_deriv_sq_of_hasDerivAt`). If `c`
is absolutely continuous on `[a, b]` with `c' = -(k² + c²)`, then almost everywhere

`f'² - k² f² = (f' - c f)² + (c f²)'`,

so `k² ∫ f² ≤ ∫ f'²` as soon as the boundary term `[c f²]_a^b` vanishes. The functions
`c(t) = k cot (k (t - p))` solve the Riccati equation. When `f(a) = 0`, take
`k = π / (2 (b - a + δ))` with `δ > 0` and `p = a - δ`: then `c` is smooth on `[a, b]` and
vanishes at `b`, and letting `δ → 0` gives the constant `π / (2 (b - a))`. The shift `δ` keeps the
pole of the cotangent outside `[a, b]`. When `f(b) = 0`, take `p = b + δ` instead, so that `c`
vanishes at `a`.

## Main declarations

* `AbsolutelyContinuousOnInterval.sq_mul_integral_sq_le_integral_deriv_sq_of_hasDerivAt`: the
  inequality `k² ∫ f² ≤ ∫ f'²` from a solution of the Riccati equation `c' = -(k² + c²)` with
  vanishing boundary term.
* `AbsolutelyContinuousOnInterval.mul_integral_sq_le_integral_deriv_sq_of_eq_zero_left` and
  `AbsolutelyContinuousOnInterval.mul_integral_sq_le_integral_deriv_sq_of_eq_zero_right`:
  Wirtinger's inequality for a function vanishing at `a`, respectively at `b`.

## References

* G. H. Hardy, J. E. Littlewood, G. Pólya, *Inequalities*, 2nd ed., Cambridge University Press,
  1952, Chapter VII (Wirtinger's inequality, and its proof through the identity
  `y'² - y² = (y' - y cot x)² + (y² cot x)'`).
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace AbsolutelyContinuousOnInterval

variable {a b : ℝ} {f : ℝ → ℝ}

/-- **The Riccati inequality.** Let `f` be absolutely continuous on `[a, b]` with `f'²`
integrable, and let `c` be absolutely continuous on `[a, b]`, with `c' = -(k² + c²)` on `(a, b)`
and with `c f²` taking the same value at both endpoints. Then `k² ∫_a^b f² ≤ ∫_a^b f'²`. -/
theorem sq_mul_integral_sq_le_integral_deriv_sq_of_hasDerivAt
    (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b)
    (hdf : IntervalIntegrable (fun t ↦ deriv f t ^ 2) volume a b) {c : ℝ → ℝ} {k : ℝ}
    (hc : AbsolutelyContinuousOnInterval c a b)
    (hc' : ∀ t ∈ Ioo a b, HasDerivAt c (-(k ^ 2 + c t ^ 2)) t)
    (hcf : c b * f b ^ 2 = c a * f a ^ 2) :
    k ^ 2 * ∫ t in a..b, f t ^ 2 ≤ ∫ t in a..b, deriv f t ^ 2 := by
  have hF := hc.fun_mul (hf.fun_mul hf)
  -- The derivative of `c f²` is below `f'² - k² f²` almost everywhere.
  have hle : (fun t ↦ deriv (fun t ↦ c t * (f t * f t)) t) ≤ᵐ[volume.restrict (Icc a b)]
      fun t ↦ deriv f t ^ 2 - k ^ 2 * f t ^ 2 := by
    have hIoo : ∀ᵐ t ∂volume.restrict (Icc a b), t ∈ Ioo a b := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hIoo, ae_restrict_of_ae hf.ae_differentiableAt] with t ht hdiff
    have hd := hdiff (Icc_subset_uIcc (Ioo_subset_Icc_self ht))
    have hD : HasDerivAt (fun t ↦ c t * (f t * f t))
        (-(k ^ 2 + c t ^ 2) * (f t * f t) + c t * (deriv f t * f t + f t * deriv f t)) t :=
      (hc' t ht).mul (hd.hasDerivAt.mul hd.hasDerivAt)
    rw [hD.deriv]
    nlinarith [sq_nonneg (deriv f t - c t * f t)]
  have hsq := (hf.continuousOn.pow 2).intervalIntegrable (μ := volume)
  have hmono := intervalIntegral.integral_mono_ae_restrict hab hF.intervalIntegrable_deriv
    (hdf.sub (hsq.const_mul (k ^ 2))) hle
  -- The boundary term `c f²` vanishes by `hcf`.
  have hbd : c b * (f b * f b) - c a * (f a * f a) = 0 := by linear_combination hcf
  rw [hF.integral_deriv_eq_sub, hbd, intervalIntegral.integral_sub hdf (hsq.const_mul _),
    intervalIntegral.integral_const_mul] at hmono
  simp only [Pi.pow_apply] at hmono
  linarith

/-- The Riccati inequality for the solution `c(t) = k cot (k (t - p))` of `c' = -(k² + c²)`, when
its pole stays off `[a, b]` and the boundary term `c f²` vanishes at both endpoints. -/
private theorem sq_mul_integral_sq_le_integral_deriv_sq_of_sin_ne_zero
    (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b)
    (hdf : IntervalIntegrable (fun t ↦ deriv f t ^ 2) volume a b) {k p : ℝ}
    (hsin : ∀ t ∈ uIcc a b, Real.sin (k * (t - p)) ≠ 0)
    (ha : Real.cos (k * (a - p)) * f a = 0) (hb : Real.cos (k * (b - p)) * f b = 0) :
    k ^ 2 * ∫ t in a..b, f t ^ 2 ≤ ∫ t in a..b, deriv f t ^ 2 := by
  have hθ (t : ℝ) : HasDerivAt (fun t ↦ k * (t - p)) k t := by
    simpa using ((hasDerivAt_id t).sub_const p).const_mul k
  refine sq_mul_integral_sq_le_integral_deriv_sq_of_hasDerivAt hf hab hdf
    (c := fun t ↦ k * Real.cos (k * (t - p)) / Real.sin (k * (t - p))) ?_ (fun t ht ↦ ?_) ?_
  · exact (((contDiff_const.mul (Real.contDiff_cos.comp (by fun_prop))).contDiffOn).div
      (Real.contDiff_sin.comp (by fun_prop)).contDiffOn hsin).absolutelyContinuousOnInterval
  · have hs := hsin t (Icc_subset_uIcc (Ioo_subset_Icc_self ht))
    refine ((((Real.hasDerivAt_cos _).comp t (hθ t)).const_mul k).div
      ((Real.hasDerivAt_sin _).comp t (hθ t)) hs).congr_deriv ?_
    simp only [Function.comp_apply]
    field_simp
    ring
  · have key (x : ℝ) : k * Real.cos (k * (x - p)) / Real.sin (k * (x - p)) * f x ^ 2 =
        k / Real.sin (k * (x - p)) * (Real.cos (k * (x - p)) * f x) * f x := by ring
    simp only [key, ha, hb, mul_zero, zero_mul]

/-- The inequality with the constant `π / (2 (b - a + δ))`, `δ > 0`, for `f` vanishing at `a`,
from the Riccati solution `k cot (k (t - a + δ))`, which is smooth on `[a, b]` and vanishes at
`b`. -/
private theorem mul_integral_sq_le_integral_deriv_sq_of_eq_zero_left_of_pos
    (hf : AbsolutelyContinuousOnInterval f a b) (hab : a < b) (hfa : f a = 0)
    (hdf : IntervalIntegrable (fun t ↦ deriv f t ^ 2) volume a b) {δ : ℝ} (hδ : 0 < δ) :
    (π / (2 * (b - a + δ))) ^ 2 * ∫ t in a..b, f t ^ 2 ≤ ∫ t in a..b, deriv f t ^ 2 := by
  have hk0 : 0 < π / (2 * (b - a + δ)) := div_pos Real.pi_pos (by linarith)
  have hkb : π / (2 * (b - a + δ)) * (b - (a - δ)) = π / 2 := by
    field_simp
    ring
  refine sq_mul_integral_sq_le_integral_deriv_sq_of_sin_ne_zero hf hab.le hdf (p := a - δ)
    (fun t ht ↦ ?_) (by simp [hfa]) (by simp [hkb])
  rw [uIcc_of_le hab.le] at ht
  refine (Real.sin_pos_of_pos_of_lt_pi (mul_pos hk0 (by linarith [ht.1])) ?_).ne'
  nlinarith [ht.2, Real.pi_pos]

/-- The inequality with the constant `π / (2 (b - a + δ))`, `δ > 0`, for `f` vanishing at `b`,
from the Riccati solution `k cot (k (t - b - δ))`, which is smooth on `[a, b]` and vanishes at
`a`. -/
private theorem mul_integral_sq_le_integral_deriv_sq_of_eq_zero_right_of_pos
    (hf : AbsolutelyContinuousOnInterval f a b) (hab : a < b) (hfb : f b = 0)
    (hdf : IntervalIntegrable (fun t ↦ deriv f t ^ 2) volume a b) {δ : ℝ} (hδ : 0 < δ) :
    (π / (2 * (b - a + δ))) ^ 2 * ∫ t in a..b, f t ^ 2 ≤ ∫ t in a..b, deriv f t ^ 2 := by
  have hk0 : 0 < π / (2 * (b - a + δ)) := div_pos Real.pi_pos (by linarith)
  have hka : π / (2 * (b - a + δ)) * (a - (b + δ)) = -(π / 2) := by
    field_simp
    ring
  refine sq_mul_integral_sq_le_integral_deriv_sq_of_sin_ne_zero hf hab.le hdf (p := b + δ)
    (fun t ht ↦ ?_) (by simp [hka]) (by simp [hfb])
  rw [uIcc_of_le hab.le] at ht
  refine (Real.sin_neg_of_neg_of_neg_pi_lt (mul_neg_of_pos_of_neg hk0 (by linarith [ht.2])) ?_).ne
  nlinarith [ht.1, Real.pi_pos]

/-- Passing to the limit `δ → 0` in an inequality with the constant `π / (2 (b - a + δ))`. -/
private theorem mul_integral_sq_le_of_forall_pos {g h : ℝ → ℝ} (hab : a < b)
    (H : ∀ δ : ℝ, 0 < δ →
      (π / (2 * (b - a + δ))) ^ 2 * ∫ t in a..b, g t ≤ ∫ t in a..b, h t) :
    (π / (2 * (b - a))) ^ 2 * ∫ t in a..b, g t ≤ ∫ t in a..b, h t := by
  have hcont : ContinuousAt
      (fun δ : ℝ ↦ (π / (2 * (b - a + δ))) ^ 2 * ∫ t in a..b, g t) 0 :=
    ((continuousAt_const.div (continuousAt_const.mul (continuousAt_const.add continuousAt_id))
      (by simp [(sub_pos.2 hab).ne'])).pow 2).mul continuousAt_const
  refine le_of_tendsto (x := 𝓝[>] (0 : ℝ)) ?_ (eventually_nhdsWithin_of_forall H)
  simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- **Wirtinger's inequality with one Dirichlet endpoint, at `a`.** An absolutely continuous
function on `[a, b]` vanishing at `a`, with square-integrable derivative, satisfies
`(π / (2 (b - a)))² ∫_a^b f² ≤ ∫_a^b f'²`. The constant is attained by
`sin (π (t - a) / (2 (b - a)))`. -/
theorem mul_integral_sq_le_integral_deriv_sq_of_eq_zero_left
    (hf : AbsolutelyContinuousOnInterval f a b) (hab : a < b) (hfa : f a = 0)
    (hdf : IntervalIntegrable (fun t ↦ deriv f t ^ 2) volume a b) :
    (π / (2 * (b - a))) ^ 2 * ∫ t in a..b, f t ^ 2 ≤ ∫ t in a..b, deriv f t ^ 2 :=
  mul_integral_sq_le_of_forall_pos hab fun _ hδ ↦
    mul_integral_sq_le_integral_deriv_sq_of_eq_zero_left_of_pos hf hab hfa hdf hδ

/-- **Wirtinger's inequality with one Dirichlet endpoint, at `b`.** An absolutely continuous
function on `[a, b]` vanishing at `b`, with square-integrable derivative, satisfies
`(π / (2 (b - a)))² ∫_a^b f² ≤ ∫_a^b f'²`. The constant is attained by
`cos (π (t - a) / (2 (b - a)))`. -/
theorem mul_integral_sq_le_integral_deriv_sq_of_eq_zero_right
    (hf : AbsolutelyContinuousOnInterval f a b) (hab : a < b) (hfb : f b = 0)
    (hdf : IntervalIntegrable (fun t ↦ deriv f t ^ 2) volume a b) :
    (π / (2 * (b - a))) ^ 2 * ∫ t in a..b, f t ^ 2 ≤ ∫ t in a..b, deriv f t ^ 2 :=
  mul_integral_sq_le_of_forall_pos hab fun _ hδ ↦
    mul_integral_sq_le_integral_deriv_sq_of_eq_zero_right_of_pos hf hab hfb hdf hδ

end AbsolutelyContinuousOnInterval

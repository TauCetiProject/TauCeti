/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Analytic.OfScalars

/-!
# Profiles of the standard cap

The surgery step of Ricci flow on three-manifolds glues in a fixed rotationally symmetric metric on
`ℝ³`, the *standard cap* (Perelman's standard initial metric). In polar coordinates it is
`dr² + f(r)² g_(S²)` for a radial *profile* `f`, and `TauCeti.IsStandardCapProfile f` records the
conditions placed on `f`:

* `f` is smooth and odd on `ℝ`: this is the odd smooth extension of `f` across the tip `r = 0`;
* `f` is concave on `[0, ∞)`;
* near the tip, `f(r) = 2 sin (r / 2)`, the profile of a ball in the round sphere of radius `2`,
  of sectional curvature `1 / 4`;
* beyond a finite radius, `f = √2`, the profile of the round cylinder `S²(√2) × ℝ`, of scalar
  curvature one.

From these conditions we derive the remaining normalizations of the profile on `[0, ∞)`: `f(0) = 0`
and `f'(0) = 1`, `0 ≤ f' ≤ 1`, `f'' ≤ 0`, monotonicity, positivity away from the tip, the upper
bound `f ≤ √2`, the secant bounds `0 < f(r) / r ≤ 1`, and smoothness in `s = r²` of the radial
quotients `(f(r) / r)²` and `(1 - (f(r) / r)²) / r²` across the tip. The radial and tangential
sectional curvatures of `dr² + f(r)² g_(S²)` are `-f'' / f` and `(1 - f'²) / f²`, which these
inequalities make nonnegative; this is the source of the nonnegative curvature of the standard cap.
Finally, the class of standard cap profiles is nonempty (`TauCeti.exists_isStandardCapProfile`), so
the standard cap can be chosen.

## Main definitions

* `TauCeti.IsStandardCapProfile`: the profile of a standard cap metric.
* `TauCeti.capAngularQuot`, `TauCeti.capRadialQuot`: the smooth radial-square profile quotients
  extending `(f(r) / r)²` and `(1 - (f(r) / r)²) / r²` across `s = r² = 0`.

## Main results

* `TauCeti.IsStandardCapProfile.eventuallyEq_two_mul_sin`: near the tip, on both sides, the profile
  is `2 sin (r / 2)`.
* `TauCeti.IsStandardCapProfile.apply_zero`, `TauCeti.IsStandardCapProfile.deriv_zero`: `f(0) = 0`
  and `f'(0) = 1`.
* `TauCeti.IsStandardCapProfile.deriv_nonneg`, `TauCeti.IsStandardCapProfile.deriv_le_one`,
  `TauCeti.IsStandardCapProfile.deriv_deriv_nonpos`: `0 ≤ f' ≤ 1` and `f'' ≤ 0` on `[0, ∞)`.
* `TauCeti.IsStandardCapProfile.apply_pos`, `TauCeti.IsStandardCapProfile.apply_le_sqrt_two`:
  `0 < f(r) ≤ √2` for `r > 0`.
* `TauCeti.IsStandardCapProfile.apply_le_self`,
  `TauCeti.IsStandardCapProfile.antitoneOn_div_self`,
  `TauCeti.IsStandardCapProfile.div_self_pos`, `TauCeti.IsStandardCapProfile.div_self_le_one`:
  secant bounds `0 < f(r) / r ≤ 1` and antitonicity of `r ↦ f(r) / r` on `(0, ∞)`.
* `TauCeti.IsStandardCapProfile.contDiff_capAngularQuot`,
  `TauCeti.IsStandardCapProfile.contDiff_capRadialQuot`: smoothness of `capAngularQuot f` and
  `capRadialQuot f` on `ℝ`.
* `TauCeti.exists_isStandardCapProfile`: standard cap profiles exist.

## Implementation notes

The witness profile is `2 sin (θ / 2)` for an odd angle function `θ` which is the identity near
`0`, nondecreasing and concave on `[0, ∞)`, and equal to `π / 2` beyond a finite radius. The angle
`θ` is a rescaled primitive of a smooth even cutoff; rescaling fixes its final value without
changing it near `0`. Building a profile as the primitive of a `smoothTransition` cutoff follows
`TauCeti.torpedoProfile` in `TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Torpedo`.
That profile has a fixed cap-to-cylinder ratio, so here the primitive is additionally rescaled to
reach the prescribed final angle `π / 2` while remaining the identity near the tip.

## References

* J. Morgan, G. Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Mathematics Monographs 3
  (2007), Definition 12.1.
* G. Perelman, *Ricci flow with surgery on three-manifolds*, arXiv:math/0303109 (2003), §2.
-/

public section

noncomputable section

open Real Set Filter
open scoped ContDiff Topology

namespace TauCeti

/-- A *standard cap profile*: a function `f` for which `dr² + f(r)² g_(S²)` is the standard cap
metric on `ℝ³`. It is smooth and odd on `ℝ` (the odd smooth extension across the tip), concave on
`[0, ∞)`, equal to `2 sin (r / 2)` on some interval `[0, r₀)` (a round tip of sectional curvature
`1 / 4`), and equal to `√2` beyond some radius (a round cylinder of scalar curvature one). -/
structure IsStandardCapProfile (f : ℝ → ℝ) : Prop where
  /-- The profile is smooth. -/
  contDiff : ContDiff ℝ ∞ f
  /-- The profile is odd, so that it is the odd extension of its restriction to `[0, ∞)`. -/
  odd : Function.Odd f
  /-- The profile is concave on `[0, ∞)`. -/
  concaveOn : ConcaveOn ℝ (Ici 0) f
  /-- Near the tip the profile is that of the round sphere of radius `2`. -/
  exists_eq_two_mul_sin : ∃ r₀ > 0, ∀ r ∈ Ico 0 r₀, f r = 2 * sin (r / 2)
  /-- Beyond a finite radius the profile is that of the round cylinder of radius `√2`. -/
  exists_eq_sqrt_two : ∃ R, ∀ r, R ≤ r → f r = √2

namespace IsStandardCapProfile

variable {f : ℝ → ℝ} (hf : IsStandardCapProfile f)
include hf

/-- A standard cap profile is differentiable. -/
theorem differentiable : Differentiable ℝ f :=
  hf.contDiff.differentiable (by simp)

/-- Near the tip, on both sides, a standard cap profile is `2 sin (r / 2)`. -/
theorem eventuallyEq_two_mul_sin : f =ᶠ[𝓝 0] fun r ↦ 2 * sin (r / 2) := by
  obtain ⟨r₀, hr₀, h⟩ := hf.exists_eq_two_mul_sin
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.2 hr₀) hr₀] with r hr
  rcases le_or_gt 0 r with h0 | h0
  · exact h r ⟨h0, hr.2⟩
  · have hodd := hf.odd (-r)
    rw [neg_neg] at hodd
    rw [hodd, h (-r) ⟨by linarith, by linarith [hr.1]⟩, neg_div, sin_neg]
    ring

/-- A standard cap profile vanishes at the tip. -/
theorem apply_zero : f 0 = 0 := by
  simpa using hf.eventuallyEq_two_mul_sin.eq_of_nhds

/-- A standard cap profile has unit slope at the tip. -/
@[simp]
theorem deriv_zero : deriv f 0 = 1 := by
  have h : HasDerivAt (fun r : ℝ ↦ 2 * sin (r / 2)) (2 * (cos (0 / 2) * (1 / 2))) 0 :=
    ((hasDerivAt_id' 0).div_const 2).sin.const_mul 2
  rw [hf.eventuallyEq_two_mul_sin.deriv_eq, h.deriv]
  simp

/-- The derivative of a standard cap profile is antitone on `[0, ∞)`. -/
theorem antitoneOn_deriv : AntitoneOn (deriv f) (Ici 0) :=
  hf.concaveOn.antitoneOn_deriv fun x _ ↦ hf.differentiable x

/-- Beyond a finite radius a standard cap profile is stationary. -/
theorem exists_deriv_eq_zero : ∃ R, ∀ r, R < r → deriv f r = 0 := by
  obtain ⟨R, hR⟩ := hf.exists_eq_sqrt_two
  refine ⟨R, fun r hr ↦ ?_⟩
  have h : f =ᶠ[𝓝 r] fun _ ↦ √2 := by
    filter_upwards [Ioi_mem_nhds hr] with s hs using hR s hs.le
  rw [h.deriv_eq, deriv_const]

/-- A standard cap profile is nondecreasing: `0 ≤ f'` on `[0, ∞)`. -/
theorem deriv_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ deriv f r := by
  obtain ⟨R, hR⟩ := hf.exists_deriv_eq_zero
  have h := hf.antitoneOn_deriv (mem_Ici.2 hr) (mem_Ici.2 (by linarith [le_max_left r R]))
    ((le_max_left r R).trans (le_add_of_nonneg_right zero_le_one))
  rwa [hR _ (by linarith [le_max_right r R])] at h

/-- The slope of a standard cap profile is at most one on `[0, ∞)`. -/
theorem deriv_le_one {r : ℝ} (hr : 0 ≤ r) : deriv f r ≤ 1 :=
  hf.deriv_zero ▸ hf.antitoneOn_deriv (mem_Ici.2 le_rfl) (mem_Ici.2 hr) hr

/-- The second derivative of a standard cap profile is nonpositive on `[0, ∞)`. -/
theorem deriv_deriv_nonpos {r : ℝ} (hr : 0 ≤ r) : deriv (deriv f) r ≤ 0 := by
  rw [← (((contDiff_infty_iff_deriv.1 hf.contDiff).2.differentiable (by simp)) r).derivWithin
    (uniqueDiffOn_Ici 0 r (mem_Ici.2 hr))]
  exact hf.antitoneOn_deriv.derivWithin_nonpos

/-- A standard cap profile is monotone on `[0, ∞)`. -/
theorem monotoneOn : MonotoneOn f (Ici 0) :=
  monotoneOn_of_deriv_nonneg (convex_Ici 0) hf.contDiff.continuous.continuousOn
    hf.differentiable.differentiableOn fun _ hx ↦ hf.deriv_nonneg (interior_subset hx)

/-- A standard cap profile is positive away from the tip. -/
theorem apply_pos {r : ℝ} (hr : 0 < r) : 0 < f r := by
  obtain ⟨r₀, hr₀, h⟩ := hf.exists_eq_two_mul_sin
  set s := min r (min (r₀ / 2) 1)
  have hs : 0 < s := lt_min hr (lt_min (half_pos hr₀) one_pos)
  have hsr₀ : s < r₀ := (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hr₀))
  have hs1 : s ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  calc 0 < 2 * sin (s / 2) :=
        mul_pos two_pos (sin_pos_of_pos_of_lt_pi (half_pos hs) (by linarith [two_le_pi]))
    _ = f s := (h s ⟨hs.le, hsr₀⟩).symm
    _ ≤ f r := hf.monotoneOn (mem_Ici.2 hs.le) (mem_Ici.2 hr.le) (min_le_left _ _)

/-- A standard cap profile is nonnegative on `[0, ∞)`. -/
theorem apply_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ f r :=
  hr.eq_or_lt.elim (fun h ↦ h ▸ hf.apply_zero.ge) fun h ↦ (hf.apply_pos h).le

/-- A standard cap profile is at most `√2` on `[0, ∞)`. -/
theorem apply_le_sqrt_two {r : ℝ} (hr : 0 ≤ r) : f r ≤ √2 := by
  obtain ⟨R, hR⟩ := hf.exists_eq_sqrt_two
  calc f r ≤ f (max r R) :=
        hf.monotoneOn (mem_Ici.2 hr) (mem_Ici.2 (hr.trans (le_max_left r R))) (le_max_left r R)
    _ = √2 := hR _ (le_max_right r R)

/-- Because `f(0) = 0` and `f' ≤ 1` on `[0, ∞)`, a standard cap profile satisfies `f(r) ≤ r` for
`r ≥ 0`. -/
theorem apply_le_self {r : ℝ} (hr : 0 ≤ r) : f r ≤ r := by
  have hmono : MonotoneOn (id - f) (Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (continuous_id.sub hf.contDiff.continuous).continuousOn
      (differentiable_id.sub hf.differentiable).differentiableOn fun s hs ↦ by
        rw [deriv_sub differentiableAt_id (hf.differentiable s), deriv_id]
        linarith [hf.deriv_le_one (interior_subset hs)]
  have h0 := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hr) hr
  simp only [Pi.sub_apply, id_eq, hf.apply_zero, sub_self] at h0
  linarith

/-- Concavity of `f` on `[0, ∞)` and `f(0) = 0` make the secant ratio `r ↦ f(r) / r` antitone on
`(0, ∞)`. -/
theorem antitoneOn_div_self : AntitoneOn (fun r ↦ f r / r) (Ioi 0) := fun a ha b hb hab ↦ by
  have hsec := hf.concaveOn.neg.secant_mono (a := 0) (x := a) (y := b) (mem_Ici.2 le_rfl)
    (mem_Ici.2 ha.le) (mem_Ici.2 hb.le) ha.ne' hb.ne' hab
  simp only [Pi.neg_apply, hf.apply_zero, neg_zero, sub_zero, neg_div] at hsec
  linarith

private theorem div_self_neg (r : ℝ) : f (-r) / -r = f r / r := by
  rw [hf.odd r, neg_div_neg_eq]

/-- Away from `0`, the secant ratio `f(r) / r` is positive. -/
theorem div_self_pos {r : ℝ} (hr : r ≠ 0) : 0 < f r / r := by
  rcases lt_or_gt_of_ne hr with hlt | hgt
  · rw [← hf.div_self_neg]
    exact div_pos (hf.apply_pos (neg_pos.2 hlt)) (neg_pos.2 hlt)
  · exact div_pos (hf.apply_pos hgt) hgt

/-- Everywhere on `ℝ`, the secant ratio `f(r) / r` is at most one. -/
theorem div_self_le_one (r : ℝ) : f r / r ≤ 1 := by
  rcases lt_trichotomy r 0 with hlt | rfl | hgt
  · rw [← hf.div_self_neg]
    exact (div_le_one (neg_pos.2 hlt)).2 (hf.apply_le_self (neg_pos.2 hlt).le)
  · simp
  · exact (div_le_one hgt).2 (hf.apply_le_self hgt.le)

/-- Everywhere on `ℝ`, the squared secant ratio `(f(r) / r)²` is at most one. -/
theorem sq_div_self_le_one (r : ℝ) : (f r / r) ^ 2 ≤ 1 := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · nlinarith [hf.div_self_pos hr, hf.div_self_le_one r]

end IsStandardCapProfile

/-! ### Smooth radial-square profile quotients -/

/-- The formal power series `∑ (-1)^k s^k / (2k)!`, whose sum at `r²` is `cos r`. -/
private def evenCosSeries : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ fun k ↦ (-1 : ℝ) ^ k / (2 * k).factorial

private theorem evenCosSeries_radius : evenCosSeries.radius = ⊤ := by
  refine evenCosSeries.radius_eq_top_of_summable_norm fun r ↦
    (hasSum_cosh √(r : ℝ)).summable.congr fun k ↦ ?_
  rw [evenCosSeries, FormalMultilinearSeries.ofScalars_norm, norm_div, norm_pow, norm_neg,
    norm_one, one_pow, Real.norm_natCast, pow_mul, sq_sqrt r.coe_nonneg]
  ring

private theorem analyticOnNhd_evenCosSeries_sum : AnalyticOnNhd ℝ evenCosSeries.sum univ := by
  simpa [evenCosSeries_radius] using evenCosSeries.analyticOnNhd

private theorem evenCosSeries_sum_sq (r : ℝ) : evenCosSeries.sum (r ^ 2) = cos r := by
  change FormalMultilinearSeries.ofScalarsSum _ (r ^ 2) = cos r
  rw [FormalMultilinearSeries.ofScalars_sum_eq, cos_eq_tsum r]
  exact tsum_congr fun k ↦ by rw [smul_eq_mul, ← pow_mul]; ring

private def evenSinSqQuot : ℝ → ℝ :=
  dslope (fun s : ℝ ↦ 2 * (1 - evenCosSeries.sum s)) 0

private theorem analyticOnNhd_evenSinSqQuot : AnalyticOnNhd ℝ evenSinSqQuot univ :=
  (analyticOnNhd_const.mul (analyticOnNhd_const.sub analyticOnNhd_evenCosSeries_sum)).dslope 0

private theorem evenSinSqQuot_sq_of_ne_zero {r : ℝ} (hr : r ≠ 0) :
    evenSinSqQuot (r ^ 2) = (2 * sin (r / 2) / r) ^ 2 := by
  have h0 : evenCosSeries.sum 0 = 1 := by simpa using evenCosSeries_sum_sq 0
  have htrig : 2 * (1 - cos r) = (2 * sin (r / 2)) ^ 2 := by
    rw [show cos r = cos (2 * (r / 2)) by ring_nf, cos_two_mul', cos_sq']; ring
  rw [evenSinSqQuot, dslope_of_ne _ (pow_ne_zero 2 hr), slope_def_field, h0, sub_self, mul_zero,
    sub_zero, sub_zero, evenCosSeries_sum_sq, htrig, div_pow]

private theorem evenSinSqQuot_zero : evenSinSqQuot 0 = 1 := by
  have hd : deriv evenCosSeries.sum 0 = -(1 / 2) := by
    have h := FormalMultilinearSeries.iteratedDeriv_ofScalarsSum_zero
      (fun k ↦ (-1 : ℝ) ^ k / (2 * k).factorial)
      (by rw [← evenCosSeries, evenCosSeries_radius]; exact ENNReal.zero_lt_top) 1
    rw [iteratedDeriv_one] at h
    change deriv evenCosSeries.sum 0 = _ at h
    norm_num [Nat.factorial] at h
    exact h
  have hdiff := (analyticOnNhd_evenCosSeries_sum 0 trivial).differentiableAt
  have h2 : HasDerivAt (fun s : ℝ ↦ 2 * (1 - evenCosSeries.sum s))
      (2 * (0 - deriv evenCosSeries.sum 0)) 0 :=
    ((hasDerivAt_const 0 (1 : ℝ)).sub hdiff.hasDerivAt).const_mul 2
  rw [evenSinSqQuot, dslope_same, h2.deriv, hd]
  ring

private def evenRadialQuot : ℝ → ℝ :=
  dslope (fun s : ℝ ↦ 1 - evenSinSqQuot s) 0

private theorem analyticOnNhd_evenRadialQuot : AnalyticOnNhd ℝ evenRadialQuot univ :=
  (analyticOnNhd_const.sub analyticOnNhd_evenSinSqQuot).dslope 0

private theorem evenRadialQuot_sq_of_ne_zero {r : ℝ} (hr : r ≠ 0) :
    evenRadialQuot (r ^ 2) = (1 - (2 * sin (r / 2) / r) ^ 2) / r ^ 2 := by
  rw [evenRadialQuot, dslope_of_ne _ (pow_ne_zero 2 hr), slope_def_field, evenSinSqQuot_zero,
    sub_self, sub_zero, sub_zero, evenSinSqQuot_sq_of_ne_zero hr]

open Classical in
/-- Radial-square angular quotient of a profile `f`: equals `1` at `s = 0` and `(f r / r)²` at
`s = r²` (`r > 0`), and is smooth on `ℝ` when `f` is a standard cap profile. -/
def capAngularQuot (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  if s ≤ 0 then evenSinSqQuot s else (f √s / √s) ^ 2

open Classical in
/-- Radial-square radial quotient of a profile `f`: equals `(1 - (f r / r)²) / r²` at `s = r²`
(`r > 0`), and is smooth on `ℝ` when `f` is a standard cap profile. -/
def capRadialQuot (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  if s ≤ 0 then evenRadialQuot s else (1 - (f √s / √s) ^ 2) / s

@[simp]
theorem capAngularQuot_zero (f : ℝ → ℝ) : capAngularQuot f 0 = 1 := by
  simp [capAngularQuot, evenSinSqQuot_zero]

theorem capAngularQuot_sq_of_pos (f : ℝ → ℝ) {r : ℝ} (hr : 0 < r) :
    capAngularQuot f (r ^ 2) = (f r / r) ^ 2 := by
  simp [capAngularQuot, not_le.2 (sq_pos_of_pos hr), sqrt_sq hr.le]

theorem capRadialQuot_sq_of_pos (f : ℝ → ℝ) {r : ℝ} (hr : 0 < r) :
    capRadialQuot f (r ^ 2) = (1 - (f r / r) ^ 2) / r ^ 2 := by
  simp [capRadialQuot, not_le.2 (sq_pos_of_pos hr), sqrt_sq hr.le]

namespace IsStandardCapProfile

/-- For a standard cap profile `f`, `capAngularQuot f` is smooth on `ℝ`. -/
theorem contDiff_capAngularQuot {f : ℝ → ℝ} (hf : IsStandardCapProfile f) :
    ContDiff ℝ ∞ (capAngularQuot f) := by
  rw [contDiff_iff_contDiffAt]
  obtain ⟨r₀, hr₀, hsin⟩ := hf.exists_eq_two_mul_sin
  intro s
  rcases lt_or_ge s (r₀ ^ 2) with hs | hs
  · refine (analyticOnNhd_evenSinSqQuot s trivial).contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hs] with t ht
    rcases le_or_gt t 0 with ht0 | ht0
    · simp [capAngularQuot, ht0]
    · have hsqrt : √t < r₀ := (sqrt_lt_sqrt ht0.le ht).trans_eq (sqrt_sq hr₀.le)
      simp only [capAngularQuot, not_le.2 ht0, ↓reduceIte]
      rw [hsin √t ⟨sqrt_nonneg t, hsqrt⟩, ← evenSinSqQuot_sq_of_ne_zero (sqrt_ne_zero'.2 ht0),
        sq_sqrt ht0.le]
  · have hs0 : 0 < s := (sq_pos_of_pos hr₀).trans_le hs
    have hev : capAngularQuot f =ᶠ[𝓝 s] fun t ↦ (f √t / √t) ^ 2 := by
      filter_upwards [Ioi_mem_nhds hs0] with t ht using by simp [capAngularQuot, not_le.2 ht]
    have hsq : ContDiffAt ℝ ∞ (√·) s := contDiffAt_sqrt hs0.ne'
    exact (((hf.contDiff.contDiffAt.comp s hsq).div hsq (sqrt_ne_zero'.2 hs0)).pow
      2).congr_of_eventuallyEq hev

/-- For a standard cap profile `f`, `capRadialQuot f` is smooth on `ℝ`. -/
theorem contDiff_capRadialQuot {f : ℝ → ℝ} (hf : IsStandardCapProfile f) :
    ContDiff ℝ ∞ (capRadialQuot f) := by
  rw [contDiff_iff_contDiffAt]
  obtain ⟨r₀, hr₀, hsin⟩ := hf.exists_eq_two_mul_sin
  intro s
  rcases lt_or_ge s (r₀ ^ 2) with hs | hs
  · refine (analyticOnNhd_evenRadialQuot s trivial).contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hs] with t ht
    rcases le_or_gt t 0 with ht0 | ht0
    · simp [capRadialQuot, ht0]
    · have hsqrt : √t < r₀ := (sqrt_lt_sqrt ht0.le ht).trans_eq (sqrt_sq hr₀.le)
      have hr := evenRadialQuot_sq_of_ne_zero (sqrt_ne_zero'.2 ht0)
      rw [sq_sqrt ht0.le] at hr
      simp only [capRadialQuot, not_le.2 ht0, ↓reduceIte]
      rw [hsin √t ⟨sqrt_nonneg t, hsqrt⟩, hr]
  · have hs0 : 0 < s := (sq_pos_of_pos hr₀).trans_le hs
    have hev : capRadialQuot f =ᶠ[𝓝 s] fun t ↦ (1 - capAngularQuot f t) / t := by
      filter_upwards [Ioi_mem_nhds hs0] with t ht
      simp [capRadialQuot, capAngularQuot, not_le.2 ht]
    exact ((contDiffAt_const.sub hf.contDiff_capAngularQuot.contDiffAt).div contDiffAt_id
      hs0.ne').congr_of_eventuallyEq hev

end IsStandardCapProfile

/-! ### Existence of standard cap profiles -/

/-- An even cutoff, equal to `1` on `[-1, 1]`, to `0` outside `(-2, 2)`, and antitone on
`[0, ∞)`. -/
private def capCutoff (s : ℝ) : ℝ :=
  1 - smoothTransition (s ^ 2 - 1)

private theorem contDiff_capCutoff : ContDiff ℝ ∞ capCutoff :=
  contDiff_const.sub (smoothTransition.contDiff.comp ((contDiff_id.pow 2).sub contDiff_const))

private theorem capCutoff_of_abs_le_one {s : ℝ} (hs : |s| ≤ 1) : capCutoff s = 1 := by
  have := (sq_le_one_iff_abs_le_one s).2 hs
  rw [capCutoff, smoothTransition.zero_of_nonpos (by linarith), sub_zero]

private theorem capCutoff_of_two_le {s : ℝ} (hs : 2 ≤ s) : capCutoff s = 0 := by
  rw [capCutoff, smoothTransition.one_of_one_le (by nlinarith), sub_self]

private theorem capCutoff_nonneg (s : ℝ) : 0 ≤ capCutoff s :=
  sub_nonneg.2 (smoothTransition.le_one _)

private theorem capCutoff_neg (s : ℝ) : capCutoff (-s) = capCutoff s := by
  rw [capCutoff, capCutoff, neg_sq]

private theorem antitoneOn_capCutoff : AntitoneOn capCutoff (Ici 0) := by
  intro a ha b _ hab
  have ha := mem_Ici.1 ha
  exact sub_le_sub_left (smoothTransition.monotone (by nlinarith)) _

/-- The primitive of `capCutoff` vanishing at `0`: the identity on `[-1, 1]`, odd, nondecreasing
and constant on `[2, ∞)`. -/
private def capRamp (r : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..r, capCutoff s

private theorem hasDerivAt_capRamp (r : ℝ) : HasDerivAt capRamp (capCutoff r) r :=
  (contDiff_capCutoff.continuous.integral_hasStrictDerivAt 0 r).hasDerivAt

private theorem contDiff_capRamp : ContDiff ℝ ∞ capRamp :=
  contDiff_infty_iff_deriv.2 ⟨fun r ↦ (hasDerivAt_capRamp r).differentiableAt,
    (funext fun r ↦ (hasDerivAt_capRamp r).deriv) ▸ contDiff_capCutoff⟩

private theorem monotone_capRamp : Monotone capRamp :=
  monotone_of_deriv_nonneg (fun r ↦ (hasDerivAt_capRamp r).differentiableAt) fun r ↦
    (hasDerivAt_capRamp r).deriv ▸ capCutoff_nonneg r

private theorem capRamp_of_abs_le_one {r : ℝ} (hr : |r| ≤ 1) : capRamp r = r := by
  rw [capRamp, intervalIntegral.integral_congr (g := fun _ ↦ (1 : ℝ)),
    intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  intro s hs
  rw [mem_uIcc] at hs
  rw [abs_le] at hr
  exact capCutoff_of_abs_le_one (abs_le.2 (by rcases hs with h | h <;> constructor <;> linarith))

private theorem capRamp_neg (r : ℝ) : capRamp (-r) = -capRamp r := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := r) capCutoff
  simp only [capCutoff_neg, neg_zero] at h
  rw [capRamp, capRamp, h, intervalIntegral.integral_symm]

private theorem capRamp_of_two_le {r : ℝ} (hr : 2 ≤ r) : capRamp r = capRamp 2 := by
  have hi (a b : ℝ) : IntervalIntegrable capCutoff MeasureTheory.volume a b :=
    contDiff_capCutoff.continuous.intervalIntegrable a b
  rw [capRamp, capRamp, ← intervalIntegral.integral_add_adjacent_intervals (hi 0 2) (hi 2 r),
    intervalIntegral.integral_congr (a := 2) (b := r) (g := fun _ ↦ (0 : ℝ)),
    intervalIntegral.integral_zero, add_zero]
  intro s hs
  rw [uIcc_of_le hr] at hs
  exact capCutoff_of_two_le hs.1

private theorem one_le_capRamp_two : 1 ≤ capRamp 2 := by
  have h : capRamp 1 ≤ capRamp 2 := monotone_capRamp (by norm_num)
  rwa [capRamp_of_abs_le_one (by norm_num)] at h

/-- The scale `k` for which `k · capRamp (r / k)` is `π / 2` on `[2 k, ∞)`. -/
private def capScale : ℝ :=
  π / (2 * capRamp 2)

private theorem capScale_pos : 0 < capScale :=
  div_pos pi_pos (by linarith [one_le_capRamp_two])

/-- The angle function `θ(r) = k · capRamp (r / k)`: the identity on `[-k, k]`, odd,
nondecreasing, concave on `[0, ∞)` and equal to `π / 2` on `[2 k, ∞)`. -/
private def capAngle (r : ℝ) : ℝ :=
  capScale * capRamp (r / capScale)

private theorem hasDerivAt_capAngle (r : ℝ) :
    HasDerivAt capAngle (capCutoff (r / capScale)) r := by
  have h := ((hasDerivAt_capRamp (r / capScale)).comp r
    ((hasDerivAt_id' r).div_const capScale)).const_mul capScale
  unfold capAngle
  convert h using 1
  · simp only [Function.comp_def]
  · field_simp [capScale_pos.ne']

private theorem contDiff_capAngle : ContDiff ℝ ∞ capAngle :=
  contDiff_const.mul (contDiff_capRamp.comp (contDiff_id.div_const _))

private theorem monotone_capAngle : Monotone capAngle := fun _ _ hab ↦
  mul_le_mul_of_nonneg_left
    (monotone_capRamp (div_le_div_of_nonneg_right hab capScale_pos.le)) capScale_pos.le

private theorem capAngle_of_abs_le {r : ℝ} (hr : |r| ≤ capScale) : capAngle r = r := by
  rw [capAngle, capRamp_of_abs_le_one, mul_div_cancel₀ _ capScale_pos.ne']
  rwa [abs_div, abs_of_pos capScale_pos, div_le_one capScale_pos]

private theorem capAngle_of_le {r : ℝ} (hr : 2 * capScale ≤ r) : capAngle r = π / 2 := by
  rw [capAngle, capRamp_of_two_le ((le_div_iff₀ capScale_pos).2 hr), capScale]
  field_simp [(one_pos.trans_le one_le_capRamp_two).ne']

private theorem capAngle_neg (r : ℝ) : capAngle (-r) = -capAngle r := by
  rw [capAngle, capAngle, neg_div, capRamp_neg, mul_neg]

private theorem capAngle_mem_Icc {r : ℝ} (hr : 0 ≤ r) : capAngle r ∈ Icc 0 (π / 2) := by
  constructor
  · have h := monotone_capAngle hr
    rwa [capAngle_of_abs_le (by simpa using capScale_pos.le)] at h
  · have h := monotone_capAngle (le_max_left r (2 * capScale))
    rwa [capAngle_of_le (le_max_right r _)] at h

/-- The witness profile `2 sin (θ / 2)`. -/
private def capProfile (r : ℝ) : ℝ :=
  2 * sin (capAngle r / 2)

private theorem hasDerivAt_capProfile (r : ℝ) :
    HasDerivAt capProfile (cos (capAngle r / 2) * capCutoff (r / capScale)) r := by
  have h : HasDerivAt capProfile (2 * (cos (capAngle r / 2) * (capCutoff (r / capScale) / 2))) r :=
    ((hasDerivAt_capAngle r).div_const 2).sin.const_mul 2
  convert h using 1
  ring

private theorem antitoneOn_deriv_capProfile : AntitoneOn (deriv capProfile) (Ici 0) := by
  intro a ha b hb hab
  rw [mem_Ici] at ha hb
  rw [(hasDerivAt_capProfile a).deriv, (hasDerivAt_capProfile b).deriv]
  have hθa := capAngle_mem_Icc ha
  have hθb := capAngle_mem_Icc hb
  refine mul_le_mul ?_ (antitoneOn_capCutoff (mem_Ici.2 (div_nonneg ha capScale_pos.le))
    (mem_Ici.2 (div_nonneg hb capScale_pos.le)) (div_le_div_of_nonneg_right hab capScale_pos.le))
    (capCutoff_nonneg _)
    (cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos, hθa.1], by linarith [hθa.2, pi_pos]⟩)
  exact cos_le_cos_of_nonneg_of_le_pi (by linarith [hθa.1]) (by linarith [hθb.2, pi_pos])
    (by linarith [monotone_capAngle hab])

private theorem isStandardCapProfile_capProfile : IsStandardCapProfile capProfile where
  contDiff := contDiff_const.mul (contDiff_sin.comp (contDiff_capAngle.div_const 2))
  odd r := by rw [capProfile, capProfile, capAngle_neg, neg_div, sin_neg, mul_neg]
  concaveOn := antitoneOn_deriv_capProfile.mono interior_subset |>.concaveOn_of_deriv
    (convex_Ici 0) (fun r _ ↦ (hasDerivAt_capProfile r).continuousAt.continuousWithinAt)
    fun r _ ↦ (hasDerivAt_capProfile r).differentiableAt.differentiableWithinAt
  exists_eq_two_mul_sin := ⟨capScale, capScale_pos, fun r hr ↦ by
    rw [capProfile, capAngle_of_abs_le (by rw [abs_of_nonneg hr.1]; exact hr.2.le)]⟩
  exists_eq_sqrt_two := ⟨2 * capScale, fun r hr ↦ by
    have hπ : π / 2 / 2 = π / 4 := by ring
    rw [capProfile, capAngle_of_le hr, hπ, sin_pi_div_four]
    ring⟩

/-- Standard cap profiles exist. -/
theorem exists_isStandardCapProfile : ∃ f, IsStandardCapProfile f :=
  ⟨capProfile, isStandardCapProfile_capProfile⟩

end TauCeti

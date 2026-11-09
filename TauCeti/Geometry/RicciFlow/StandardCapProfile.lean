/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Standard cap profiles

The standard initial metric of Ricci flow with surgery is a rotationally symmetric metric
`dr² + f(r)² g_(S²)` on `ℝ³`, written in polar coordinates about the tip. Its *profile* `f` is
that of the round sphere of radius `2`, `f(r) = 2 sin (r / 2)`, near the tip, it is concave, and
it is the constant `√2` beyond a finite radius, where the metric is the round cylinder of scalar
curvature one. The radial and tangential sectional curvatures of such a metric are `-f''/f` and
`(1 - f'²)/f²`, so concavity together with `0 ≤ f' ≤ 1` makes them nonnegative.

`TauCeti.IsStandardCapProfile f` records these conditions for a smooth odd function
`f : ℝ → ℝ`; oddness says that `f` is the odd smooth extension across the tip of its
restriction to `[0, ∞)`. The further conditions `f(0) = 0`, `f'(0) = 1`, `f > 0` on `(0, ∞)`,
`0 ≤ f' ≤ 1` and `f ≤ √2` on `[0, ∞)` are consequences, proved here.

The main result, `TauCeti.exists_isStandardCapProfile`, shows that the class is nonempty. The
witness integrates `cos (r / 2)` multiplied by a smooth cutoff: on `[0, ∞)` this slope is
antitone, so its primitive is concave, and the position of the cutoff is chosen by the
intermediate value theorem so that the primitive levels off exactly at `√2`.

## Main definitions

* `TauCeti.IsStandardCapProfile`: the profiles of standard cap metrics.

## Main results

* `TauCeti.IsStandardCapProfile.pos`, `TauCeti.IsStandardCapProfile.deriv_nonneg`,
  `TauCeti.IsStandardCapProfile.deriv_le_one`, `TauCeti.IsStandardCapProfile.le_sqrt_two`:
  the derived bounds on `[0, ∞)`.
* `TauCeti.exists_isStandardCapProfile`: standard cap profiles exist.

## References

* J. Morgan, G. Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Mathematics Monographs 3
  (2007), Definition 12.1 (the standard initial metric).
-/

public section

open Real Set Filter
open scoped ContDiff Topology

namespace TauCeti

/-- A *standard cap profile* is a smooth odd function `f : ℝ → ℝ` which agrees with
`2 sin (r / 2)` near `0`, is concave on `[0, ∞)`, and is eventually equal to `√2`. It is the
profile of the rotationally symmetric metric `dr² + f(r)² g_(S²)` on `ℝ³` with a round tip of
radius `2` and a round cylindrical end of radius `√2`. -/
structure IsStandardCapProfile (f : ℝ → ℝ) : Prop where
  /-- The profile is smooth. -/
  contDiff : ContDiff ℝ ∞ f
  /-- The profile is odd: it is the odd smooth extension of its restriction to `[0, ∞)`. -/
  odd : Function.Odd f
  /-- Near the tip the profile is that of the round sphere of radius `2`. -/
  eventuallyEq_nhds_zero : f =ᶠ[𝓝 0] fun r ↦ 2 * sin (r / 2)
  /-- The profile is concave on `[0, ∞)`. -/
  deriv2_nonpos : ∀ ⦃r⦄, 0 ≤ r → deriv^[2] f r ≤ 0
  /-- Beyond a finite radius the profile is that of the cylinder of scalar curvature one. -/
  eventually_eq_sqrt_two : ∀ᶠ r in atTop, f r = √2

namespace IsStandardCapProfile

variable {f : ℝ → ℝ} (hf : IsStandardCapProfile f)
include hf

/-- A standard cap profile vanishes at the tip. -/
theorem apply_zero : f 0 = 0 := by
  simpa using hf.eventuallyEq_nhds_zero.eq_of_nhds

/-- A standard cap profile has unit slope at the tip. -/
theorem deriv_zero : deriv f 0 = 1 := by
  have h : HasDerivAt (fun r ↦ 2 * sin (r / 2)) (2 * (cos (0 / 2) * (1 / 2))) 0 :=
    (((hasDerivAt_id 0).div_const 2).sin).const_mul 2
  rw [hf.eventuallyEq_nhds_zero.deriv_eq, h.deriv]
  simp

/-- A standard cap profile is differentiable. -/
theorem differentiable : Differentiable ℝ f :=
  hf.contDiff.differentiable (by simp)

/-- The slope of a standard cap profile is differentiable. -/
theorem differentiable_deriv : Differentiable ℝ (deriv f) :=
  (contDiff_infty_iff_deriv.1 hf.contDiff).2.differentiable (by simp)

/-- The slope of a standard cap profile decreases on `[0, ∞)`. -/
theorem antitoneOn_deriv : AntitoneOn (deriv f) (Ici 0) :=
  antitoneOn_of_deriv_nonpos (convex_Ici 0) hf.differentiable_deriv.continuous.continuousOn
    hf.differentiable_deriv.differentiableOn fun _ hr ↦
      hf.deriv2_nonpos (interior_subset hr : _ ∈ Ici (0 : ℝ))

/-- A standard cap profile is concave on `[0, ∞)`. -/
theorem concaveOn : ConcaveOn ℝ (Ici 0) f :=
  concaveOn_of_deriv2_nonpos (convex_Ici 0) hf.differentiable.continuous.continuousOn
    hf.differentiable.differentiableOn hf.differentiable_deriv.differentiableOn fun _ hr ↦
      hf.deriv2_nonpos (interior_subset hr : _ ∈ Ici (0 : ℝ))

/-- The slope of a standard cap profile is at most one on `[0, ∞)`. -/
theorem deriv_le_one {r : ℝ} (hr : 0 ≤ r) : deriv f r ≤ 1 :=
  hf.deriv_zero ▸ hf.antitoneOn_deriv (mem_Ici.2 le_rfl) hr hr

/-- The slope of a standard cap profile is nonnegative on `[0, ∞)`. -/
theorem deriv_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ deriv f r := by
  obtain ⟨R, hR⟩ := eventually_atTop.1 hf.eventually_eq_sqrt_two
  have hx : deriv f (max r R + 1) = 0 := by
    have h : f =ᶠ[𝓝 (max r R + 1)] fun _ ↦ √2 :=
      eventually_of_mem (Ioi_mem_nhds (by linarith [le_max_right r R]))
        fun y hy ↦ hR y (le_of_lt hy)
    rw [h.deriv_eq, deriv_const]
  rw [← hx]
  exact hf.antitoneOn_deriv hr (by simp only [mem_Ici]; linarith [le_max_left r R])
    (by linarith [le_max_left r R])

/-- A standard cap profile is monotone on `[0, ∞)`. -/
theorem monotoneOn : MonotoneOn f (Ici 0) :=
  monotoneOn_of_deriv_nonneg (convex_Ici 0) hf.differentiable.continuous.continuousOn
    hf.differentiable.differentiableOn fun _ hr ↦
      hf.deriv_nonneg (interior_subset hr : _ ∈ Ici (0 : ℝ))

/-- A standard cap profile is positive away from the tip. -/
theorem pos {r : ℝ} (hr : 0 < r) : 0 < f r := by
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 hf.eventuallyEq_nhds_zero
  set t := min r (min (ε / 2) 1)
  have ht : 0 < t := lt_min hr (lt_min (by positivity) one_pos)
  have htε : t < ε := (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have ht1 : t ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hft : f t = 2 * sin (t / 2) := h (by rwa [Real.dist_eq, sub_zero, abs_of_pos ht])
  have hsin : 0 < sin (t / 2) := sin_pos_of_pos_of_lt_pi (by positivity)
    (by linarith [pi_gt_three])
  calc 0 < f t := by rw [hft]; positivity
    _ ≤ f r := hf.monotoneOn ht.le hr.le (min_le_left _ _)

/-- A standard cap profile is at most `√2` on `[0, ∞)`. -/
theorem le_sqrt_two {r : ℝ} (hr : 0 ≤ r) : f r ≤ √2 := by
  obtain ⟨R, hR⟩ := eventually_atTop.1 hf.eventually_eq_sqrt_two
  rw [← hR (max r R) (le_max_right r R)]
  exact hf.monotoneOn hr (hr.trans (le_max_left r R)) (le_max_left r R)

end IsStandardCapProfile

/-! ### Existence -/

/-- A smooth cutoff, equal to one on `(-∞, 0]` and to zero on `[1, ∞)`. -/
private noncomputable def capCutoff (x : ℝ) : ℝ := smoothTransition (1 - x)

private theorem capCutoff_of_nonpos {x : ℝ} (hx : x ≤ 0) : capCutoff x = 1 :=
  smoothTransition.one_of_one_le (by linarith)

private theorem capCutoff_of_one_le {x : ℝ} (hx : 1 ≤ x) : capCutoff x = 0 :=
  smoothTransition.zero_of_nonpos (by linarith)

private theorem capCutoff_nonneg (x : ℝ) : 0 ≤ capCutoff x := smoothTransition.nonneg _

private theorem capCutoff_le_one (x : ℝ) : capCutoff x ≤ 1 := smoothTransition.le_one _

private theorem antitone_capCutoff : Antitone capCutoff :=
  fun _ _ h ↦ smoothTransition.monotone (by linarith)

private theorem contDiff_capCutoff : ContDiff ℝ ∞ capCutoff :=
  smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

/-- The slope of the witness profile: `cos (x / 2)` cut off outside `[-(s + 1), s + 1]`, and
left unchanged on `[-s, s]`. -/
private noncomputable def capSlope (s x : ℝ) : ℝ :=
  cos (x / 2) * capCutoff (x - s) * capCutoff (-x - s)

/-- The witness profile, the primitive of `capSlope s` vanishing at `0`. -/
private noncomputable def capProfile (s r : ℝ) : ℝ := ∫ x in 0..r, capSlope s x

private theorem continuous_uncurry_capSlope : Continuous (Function.uncurry capSlope) := by
  have := contDiff_capCutoff.continuous
  unfold capSlope Function.uncurry
  fun_prop

private theorem continuous_capSlope (s : ℝ) : Continuous (capSlope s) :=
  continuous_uncurry_capSlope.comp (.prodMk_right s)

private theorem contDiff_capSlope (s : ℝ) : ContDiff ℝ ∞ (capSlope s) :=
  ((contDiff_cos.comp (contDiff_id.div_const 2)).mul
    (contDiff_capCutoff.comp (contDiff_id.sub contDiff_const))).mul
    (contDiff_capCutoff.comp (contDiff_id.neg.sub contDiff_const))

private theorem capSlope_neg (s x : ℝ) : capSlope s (-x) = capSlope s x := by
  simp only [capSlope, neg_div, cos_neg, neg_neg]
  ring

private theorem capSlope_of_abs_le {s x : ℝ} (hx : |x| ≤ s) : capSlope s x = cos (x / 2) := by
  rw [capSlope, capCutoff_of_nonpos (by linarith [le_abs_self x]),
    capCutoff_of_nonpos (by linarith [neg_le_abs x]), mul_one, mul_one]

private theorem capSlope_of_nonneg {s x : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) :
    capSlope s x = cos (x / 2) * capCutoff (x - s) := by
  rw [capSlope, capCutoff_of_nonpos (x := -x - s) (by linarith), mul_one]

private theorem capSlope_of_le {s x : ℝ} (hs : 0 ≤ s) (hx : s + 1 ≤ x) :
    capSlope s x = 0 := by
  rw [capSlope_of_nonneg hs (by linarith), capCutoff_of_one_le (by linarith), mul_zero]

private theorem cos_half_nonneg {x : ℝ} (hx : 0 ≤ x) (hxπ : x ≤ π) : 0 ≤ cos (x / 2) :=
  cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith⟩

private theorem capSlope_nonneg {s x : ℝ} (hs : 0 ≤ s) (hsπ : s + 1 ≤ π) (hx : 0 ≤ x) :
    0 ≤ capSlope s x := by
  rcases le_total x (s + 1) with h | h
  · rw [capSlope_of_nonneg hs hx]
    exact mul_nonneg (cos_half_nonneg hx (by linarith)) (capCutoff_nonneg _)
  · rw [capSlope_of_le hs h]

private theorem capSlope_le_cos {s x : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) (hxπ : x ≤ π) :
    capSlope s x ≤ cos (x / 2) := by
  rw [capSlope_of_nonneg hs hx]
  exact mul_le_of_le_one_right (cos_half_nonneg hx hxπ) (capCutoff_le_one _)

private theorem antitoneOn_capSlope {s : ℝ} (hs : 0 ≤ s) (hsπ : s + 1 ≤ π) :
    AntitoneOn (capSlope s) (Ici 0) := by
  intro x hx y hy hxy
  rcases le_total (s + 1) y with h | h
  · rw [capSlope_of_le hs h]
    exact capSlope_nonneg hs hsπ hx
  · rw [capSlope_of_nonneg hs hx, capSlope_of_nonneg hs hy]
    exact mul_le_mul (cos_le_cos_of_nonneg_of_le_pi (by linarith [mem_Ici.1 hx])
        (by linarith) (by linarith)) (antitone_capCutoff (by linarith)) (capCutoff_nonneg _)
      (cos_half_nonneg (mem_Ici.1 hx) (by linarith))

private theorem hasDerivAt_capProfile (s r : ℝ) :
    HasDerivAt (capProfile s) (capSlope s r) r :=
  ((continuous_capSlope s).integral_hasStrictDerivAt 0 r).hasDerivAt

private theorem deriv_capProfile (s : ℝ) : deriv (capProfile s) = capSlope s :=
  funext fun r ↦ (hasDerivAt_capProfile s r).deriv

private theorem capProfile_of_abs_le {s r : ℝ} (hr : |r| ≤ s) :
    capProfile s r = 2 * sin (r / 2) := by
  rw [capProfile, show 2 * sin (r / 2) = ∫ x in 0..r, cos (x / 2) by simp]
  refine intervalIntegral.integral_congr fun x hx ↦ capSlope_of_abs_le ?_
  obtain ⟨h₁, h₂⟩ := abs_le.1 hr
  rcases mem_uIcc.1 hx with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩ <;> exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem capProfile_of_le {s r : ℝ} (hs : 0 ≤ s) (hr : s + 1 ≤ r) :
    capProfile s r = capProfile s (s + 1) := by
  rw [capProfile, capProfile, ← intervalIntegral.integral_add_adjacent_intervals
    ((continuous_capSlope s).intervalIntegrable 0 (s + 1))
    ((continuous_capSlope s).intervalIntegrable (s + 1) r)]
  have h : ∫ x in (s + 1)..r, capSlope s x = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun x hx ↦
      capSlope_of_le hs (by rw [uIcc_of_le hr] at hx; exact hx.1)]
    simp
  rw [h, add_zero]

private theorem capProfile_odd (s : ℝ) : Function.Odd (capProfile s) := by
  intro r
  simp only [capProfile]
  rw [← intervalIntegral.integral_symm, ← neg_zero, ← intervalIntegral.integral_comp_neg]
  simp only [capSlope_neg, neg_zero]

private theorem monotoneOn_capProfile {s : ℝ} (hs : 0 ≤ s) (hsπ : s + 1 ≤ π) :
    MonotoneOn (capProfile s) (Ici 0) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (fun r _ ↦ (hasDerivAt_capProfile s r).continuousAt.continuousWithinAt)
    (fun r _ ↦ (hasDerivAt_capProfile s r).hasDerivWithinAt)
    fun _ hr ↦ capSlope_nonneg hs hsπ (interior_subset hr)

/-- The value at `π` of the witness profile lies between `2 sin (s / 2)` and
`2 sin ((s + 1) / 2)`. -/
private theorem capProfile_pi_mem_Icc {s : ℝ} (hs : 0 ≤ s) (hsπ : s + 1 ≤ π) :
    capProfile s π ∈ Icc (2 * sin (s / 2)) (2 * sin ((s + 1) / 2)) := by
  constructor
  · rw [← capProfile_of_abs_le (abs_of_nonneg hs).le]
    exact monotoneOn_capProfile hs hsπ hs (by simp only [mem_Ici]; linarith) (by linarith)
  · rw [capProfile_of_le hs hsπ, capProfile,
      show 2 * sin ((s + 1) / 2) = ∫ x in 0..(s + 1), cos (x / 2) by simp]
    exact intervalIntegral.integral_mono_on (by linarith)
      ((continuous_capSlope s).intervalIntegrable _ _)
      ((continuous_cos.comp (continuous_id.div_const 2)).intervalIntegrable _ _)
      fun x hx ↦ capSlope_le_cos hs hx.1 (hx.2.trans hsπ)

private theorem isStandardCapProfile_capProfile {s : ℝ} (hs : 0 < s) (hsπ : s + 1 ≤ π)
    (hπ : capProfile s π = √2) : IsStandardCapProfile (capProfile s) where
  contDiff := contDiff_infty_iff_deriv.2
    ⟨fun r ↦ (hasDerivAt_capProfile s r).differentiableAt,
      deriv_capProfile s ▸ contDiff_capSlope s⟩
  odd := capProfile_odd s
  eventuallyEq_nhds_zero := by
    filter_upwards [Metric.ball_mem_nhds 0 hs] with r hr
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hr
    exact capProfile_of_abs_le hr.le
  deriv2_nonpos r hr := by
    rw [Function.iterate_succ_apply, Function.iterate_one, deriv_capProfile,
      ← ((contDiff_capSlope s).differentiable (by simp) r).derivWithin
        (uniqueDiffOn_Ici 0 r hr)]
    exact (antitoneOn_capSlope hs.le hsπ).derivWithin_nonpos
  eventually_eq_sqrt_two := by
    filter_upwards [eventually_ge_atTop π] with r hr
    rw [← hπ, capProfile_of_le hs.le (hsπ.trans hr), capProfile_of_le hs.le hsπ]

/-- **Existence of standard cap profiles.** There is a smooth odd function, concave on
`[0, ∞)`, equal to `2 sin (r / 2)` near `0` and to `√2` beyond a finite radius. -/
theorem exists_isStandardCapProfile : ∃ f, IsStandardCapProfile f := by
  have hcont : Continuous fun s ↦ capProfile s π :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      continuous_uncurry_capSlope 0 π
  have hπ := pi_gt_three
  have hsin : 2 * sin (π / 4) = √2 := by rw [sin_pi_div_four]; ring
  have h₀ := (capProfile_pi_mem_Icc (s := π / 2 - 1) (by linarith) (by linarith)).2
  have h₁ := (capProfile_pi_mem_Icc (s := π / 2) (by linarith) (by linarith)).1
  rw [show (π / 2 - 1 + 1) / 2 = π / 4 by ring, hsin] at h₀
  rw [show π / 2 / 2 = π / 4 by ring, hsin] at h₁
  obtain ⟨s, ⟨hs₀, hs₁⟩, hs⟩ :=
    intermediate_value_Icc (by linarith) hcont.continuousOn ⟨h₀, h₁⟩
  exact ⟨_, isStandardCapProfile_capProfile (by linarith) (by linarith) hs⟩

end TauCeti

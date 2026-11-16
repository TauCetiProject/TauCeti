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
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

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
bound `f ≤ √2`, the secant bounds `0 < f(r) / r ≤ 1`, and the round-tip curvature identities
`-f''(r) / f(r) = 1 / 4` and `(1 - f'(r)²) / f(r)² = 1 / 4` for `0 < |r| < r₀`. The radial and
tangential sectional curvatures of `dr² + f(r)² g_(S²)` are `-f'' / f` and `(1 - f'²) / f²`, which
these inequalities make nonnegative; this is the source of the nonnegative curvature of the
standard cap. Finally, the class of standard cap profiles is nonempty
(`TauCeti.exists_isStandardCapProfile`), so the standard cap can be chosen.

## Main definitions

* `TauCeti.IsStandardCapProfile`: the profile of a standard cap metric.

## Main results

* `TauCeti.IsStandardCapProfile.eventuallyEq_two_mul_sin`: near the tip, on both sides, the profile
  is `2 sin (r / 2)`.
* `TauCeti.IsStandardCapProfile.exists_neg_deriv_deriv_div_eq_and_one_sub_deriv_sq_div_sq_eq`: near
  the punctured tip (`0 < |r| < r₀`), both `-f''(r) / f(r)` and `(1 - f'(r)²) / f(r)²` equal
  `1 / 4`.
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

/-- Near the tip, on `(-r₀, r₀)`, a standard cap profile and its first two derivatives agree with
`2 sin (r / 2)`, `cos (r / 2)`, and `-sin (r / 2) / 2`. -/
theorem exists_eq_two_mul_sin_and_deriv :
    ∃ r₀ > 0, ∀ r, |r| < r₀ →
      f r = 2 * sin (r / 2) ∧ deriv f r = cos (r / 2) ∧
        deriv (deriv f) r = -sin (r / 2) / 2 := by
  obtain ⟨r₀, hr₀, h⟩ := hf.exists_eq_two_mul_sin
  have hIoo : ∀ s ∈ Ioo (-r₀) r₀, f s = 2 * sin (s / 2) := fun s hs ↦ by
    rcases le_or_gt 0 s with h0 | h0
    · exact h s ⟨h0, hs.2⟩
    · have hodd := hf.odd (-s)
      rw [neg_neg] at hodd
      rw [hodd, h (-s) ⟨by linarith, by linarith [hs.1]⟩, neg_div, sin_neg]
      ring
  refine ⟨r₀, hr₀, fun r hr ↦ ?_⟩
  have hmem : r ∈ Ioo (-r₀) r₀ := abs_lt.1 hr
  have heq : f =ᶠ[𝓝 r] fun s ↦ 2 * sin (s / 2) :=
    eventuallyEq_iff_exists_mem.2 ⟨Ioo (-r₀) r₀, isOpen_Ioo.mem_nhds hmem, hIoo⟩
  have hd : deriv f =ᶠ[𝓝 r] fun s ↦ cos (s / 2) := by
    filter_upwards [heq.deriv] with s hs
    rw [hs, (((hasDerivAt_id' s).div_const 2).sin.const_mul 2).deriv]; ring
  refine ⟨hIoo r hmem, hd.eq_of_nhds, ?_⟩
  rw [hd.deriv_eq, (((hasDerivAt_id' r).div_const 2).cos).deriv]; ring

/-- Near the tip, on both sides, a standard cap profile is `2 sin (r / 2)`. -/
theorem eventuallyEq_two_mul_sin : f =ᶠ[𝓝 0] fun r ↦ 2 * sin (r / 2) := by
  obtain ⟨r₀, hr₀, h⟩ := hf.exists_eq_two_mul_sin_and_deriv
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.2 hr₀) hr₀] with r hr using (h r (abs_lt.2 hr)).1

/-- A standard cap profile vanishes at the tip. -/
theorem apply_zero : f 0 = 0 := by
  simpa using hf.eventuallyEq_two_mul_sin.eq_of_nhds

/-- A standard cap profile has unit slope at the tip. -/
@[simp]
theorem deriv_zero : deriv f 0 = 1 := by
  obtain ⟨r₀, hr₀, h⟩ := hf.exists_eq_two_mul_sin_and_deriv
  simpa using (h 0 (by simpa using hr₀)).2.1

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
  simpa [hf.apply_zero] using
    (convex_Ici (0 : ℝ)).image_sub_le_mul_sub_of_deriv_le hf.contDiff.continuous.continuousOn
      hf.differentiable.differentiableOn (fun s hs ↦ hf.deriv_le_one (interior_subset hs))
      0 (mem_Ici.2 le_rfl) r (mem_Ici.2 hr) hr

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

/-- Near the punctured tip (`0 < |r| < r₀`), both `-f''(r) / f(r)` and `(1 - f'(r)²) / f(r)²`
equal `1 / 4`, the sectional curvature of the round sphere of radius `2`. -/
theorem exists_neg_deriv_deriv_div_eq_and_one_sub_deriv_sq_div_sq_eq :
    ∃ r₀ > 0, ∀ r, r ≠ 0 → |r| < r₀ →
      -deriv (deriv f) r / f r = 1 / 4 ∧ (1 - deriv f r ^ 2) / f r ^ 2 = 1 / 4 := by
  obtain ⟨r₀, hr₀, h⟩ := hf.exists_eq_two_mul_sin_and_deriv
  refine ⟨r₀, hr₀, fun r hr0 hr ↦ ?_⟩
  obtain ⟨hf0, hd, hdd⟩ := h r hr
  have hpos : f r ≠ 0 := fun h0 ↦ by
    rcases lt_or_gt_of_ne hr0 with hlt | hgt
    · exact (hf.apply_pos (neg_pos.2 hlt)).ne' (by rw [hf.odd, h0, neg_zero])
    · exact (hf.apply_pos hgt).ne' h0
  have hsin : sin (r / 2) ≠ 0 := fun hs ↦ hpos (by rw [hf0, hs, mul_zero])
  refine ⟨?_, ?_⟩
  · rw [hf0, hdd]; field_simp; ring
  · rw [hf0, hd, ← sin_sq]; field_simp; ring

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

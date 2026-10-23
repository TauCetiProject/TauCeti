/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Convex
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import TauCeti.Analysis.Contour.DslopeFTC
public import TauCeti.Analysis.Contour.LogDerivFTC
public import TauCeti.Analysis.Contour.Primitive

/-!
# The left detour in Newman's contour argument

Newman's Tauberian theorem integrates a function `g` holomorphic on an open set `Ω` containing
the closed half-plane `0 ≤ re z` against `dz / z` over a closed contour around `0`: the right
semicircle of radius `R`, parametrized counterclockwise from `-R * I` to `R * I` by
`circleMap 0 R` on `[-π/2, π/2]`, followed by a detour back to `-R * I` through the left
half-plane, close enough to the imaginary axis to stay inside `Ω`.

The detour used here is the parabolic arc `newmanDetour R δ`, parametrized on `[-1, 1]` by
`s ↦ -δ (1 - s²) - R s I`. It runs from `R * I` to `-R * I`; for `R ≥ 0` and `δ > 0` it lies in
the strip `-δ ≤ re z ≤ 0`, `|im z| ≤ R`, and meets the imaginary axis only at its endpoints. This
file proves:

* `exists_convex_newmanDetour_subset`: by compactness of the segment `[-R * I, R * I]`, for some
  `δ > 0` the right semicircle and the detour lie in an open convex subset of `Ω`;
* `integral_right_semicircle_add_integral_newmanDetour`: Cauchy's integral formula for the
  closed contour formed by the right semicircle and the detour, for `g` holomorphic on such a
  convex set: the two integrals of `g z / z` add up to `2πi g 0`;
* `integral_left_semicircle_eq_integral_newmanDetour`: the detour may replace the left semicircle
  in the integral of `g z / z`, for `g` holomorphic on a convex set containing both;
* `tendsto_integral_newmanDetour_mul_cexp`, `tendsto_integral_newmanDetour_mul_kernel`: for `G`
  continuous on the detour, the detour integral
  of `G` against Newman's kernel `exp (T z) (1 + z² / R²) / z` tends to `0` as `T → ∞`, by
  dominated convergence: `exp (T z) → 0` on the interior of the detour, where `re z < 0`, and
  the endpoints have measure zero.

The deformation identities split `g z / z` into the removable-singularity quotient
`dslope g 0`, which has a primitive on the convex set, and the polar part `g 0 / z`, whose
integral over each of the three arcs is `g 0 * π i`, since `dz / z` integrates to `π i` there
(the general splitting is
`TauCeti.Contour.integral_mul_div_eq_of_hasDerivAt_dslope`).

## References

* D. J. Newman, *Simple analytic proof of the prime number theorem*, Amer. Math. Monthly 87
  (1980), 693–696.
* D. Zagier, *Newman's short proof of the prime number theorem*, Amer. Math. Monthly 104
  (1997), 705–708.
-/

public section

open Filter MeasureTheory Set Metric Complex
open scoped Topology Real Interval

namespace TauCeti.LSeries

variable {R δ : ℝ}

/-- **Newman's left detour.** The parabolic arc `s ↦ -δ (1 - s²) - R s I`, which on `[-1, 1]`
runs from `R * I` to `-R * I`; for `R, δ ≥ 0` it stays in the strip `-δ ≤ re z ≤ 0`,
`|im z| ≤ R`. -/
noncomputable def newmanDetour (R δ s : ℝ) : ℂ :=
  -((δ : ℂ) * (1 - (s : ℂ) ^ 2)) - R * s * I

/-- The real part of the detour, `-δ (1 - s²)`. -/
@[simp]
theorem newmanDetour_re (R δ s : ℝ) : (newmanDetour R δ s).re = -(δ * (1 - s ^ 2)) := by
  simp [newmanDetour, ← ofReal_pow]

/-- The imaginary part of the detour, `-R s`. -/
@[simp]
theorem newmanDetour_im (R δ s : ℝ) : (newmanDetour R δ s).im = -(R * s) := by
  simp [newmanDetour, ← ofReal_pow]

/-- The detour starts at `R * I`. -/
@[simp]
theorem newmanDetour_neg_one (R δ : ℝ) : newmanDetour R δ (-1) = R * I := by
  simp [newmanDetour]

/-- The detour ends at `-R * I`. -/
@[simp]
theorem newmanDetour_one (R δ : ℝ) : newmanDetour R δ 1 = -(R * I) := by
  simp [newmanDetour]

/-- The velocity of the detour is `2 δ s - R I`. -/
theorem hasDerivAt_newmanDetour (R δ s : ℝ) :
    HasDerivAt (newmanDetour R δ) (2 * δ * s - R * I) s := by
  have h : HasDerivAt (fun w : ℂ ↦ -((δ : ℂ) * (1 - w ^ 2)) - R * w * I)
      (2 * δ * s - R * I) (s : ℂ) := by
    have := (((hasDerivAt_pow 2 (s : ℂ)).const_sub 1).const_mul (δ : ℂ)).neg.sub
      (((hasDerivAt_id (s : ℂ)).const_mul (R : ℂ)).mul_const I)
    convert this using 1
    · funext w
      simp only [Pi.sub_apply, Pi.neg_apply, id]
    · simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
      ring
  exact h.comp_ofReal

/-- The velocity of the detour is `2 δ s - R I`. -/
@[simp]
theorem deriv_newmanDetour (R δ s : ℝ) : deriv (newmanDetour R δ) s = 2 * δ * s - R * I :=
  (hasDerivAt_newmanDetour R δ s).deriv

/-- The detour is continuous. -/
@[fun_prop]
theorem continuous_newmanDetour (R δ : ℝ) : Continuous (newmanDetour R δ) := by
  unfold newmanDetour
  fun_prop

/-- For `R ≠ 0` and `δ ≠ 0` the detour avoids `0`. -/
theorem newmanDetour_ne_zero (hR : R ≠ 0) (hδ : δ ≠ 0) (s : ℝ) : newmanDetour R δ s ≠ 0 := by
  intro h
  have hre := congrArg re h
  have him := congrArg im h
  simp only [newmanDetour_re, newmanDetour_im, zero_re, zero_im, neg_eq_zero, mul_eq_zero,
    hR, hδ, false_or] at hre him
  simp [him] at hre

/-- The detour stays in the closed left half-plane on `[-1, 1]`. -/
theorem newmanDetour_re_nonpos (hδ : 0 ≤ δ) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    (newmanDetour R δ s).re ≤ 0 := by
  have : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  rw [newmanDetour_re, neg_nonpos]
  positivity

/-- Strictly inside `[-1, 1]` the detour lies in the open left half-plane. -/
theorem newmanDetour_re_neg (hδ : 0 < δ) {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    (newmanDetour R δ s).re < 0 := by
  have : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  rw [newmanDetour_re, neg_neg_iff_pos]
  positivity

/-- **The detour inside the continuation domain.** If `Ω` is open and contains the closed
half-plane `0 ≤ re z`, then for some `δ > 0` the right semicircle of radius `R` and the detour
`newmanDetour R δ` lie in a common open convex subset of `Ω`. -/
theorem exists_convex_newmanDetour_subset {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hcover : {z : ℂ | 0 ≤ z.re} ⊆ Ω) (hR : 0 ≤ R) :
    ∃ δ > 0, ∃ U ⊆ Ω, IsOpen U ∧ Convex ℝ U ∧
      (∀ θ ∈ Icc (-π / 2) (π / 2), circleMap 0 R θ ∈ U) ∧
      ∀ s ∈ Icc (-1 : ℝ) 1, newmanDetour R δ s ∈ U := by
  -- A thickening of the compact segment `{re z = 0, ‖z‖ ≤ R + 1}` lies in `Ω`.
  set K : Set ℂ := {z | z.re = 0} ∩ closedBall 0 (R + 1)
  have hK : IsCompact K :=
    (isCompact_closedBall 0 (R + 1)).inter_left (isClosed_eq continuous_re continuous_const)
  obtain ⟨r, hr, hrΩ⟩ := hK.exists_thickening_subset_open hΩ
    fun z hz ↦ hcover (le_of_eq hz.1.symm)
  set η := min r 1
  have hη : 0 < η := lt_min hr one_pos
  have hηr : η ≤ r := min_le_left r 1
  have hη1 : η ≤ 1 := min_le_right r 1
  set U : Set ℂ := {z | -η < z.re} ∩ ({z | -(R + η) < z.im} ∩ {z | z.im < R + η})
  refine ⟨η / 2, half_pos hη, U, fun z hz ↦ ?_, ?_, ?_, fun θ hθ ↦ ?_, fun s hs ↦ ?_⟩
  · obtain ⟨hz1, hz2, hz3⟩ := hz
    rcases le_or_gt 0 z.re with h0 | h0
    · exact hcover h0
    refine hrΩ (mem_thickening_iff.mpr ⟨z.im * I, ⟨by simp, ?_⟩, ?_⟩)
    · rw [mem_closedBall, dist_zero_right, norm_mul, norm_I, mul_one, norm_real,
        Real.norm_eq_abs, abs_le]
      constructor <;> simp only [mem_ofPred_eq] at hz2 hz3 <;> linarith
    · have he : z - z.im * I = z.re := by
        nth_rewrite 1 [← re_add_im z]
        ring
      rw [dist_eq_norm, he, norm_real, Real.norm_eq_abs, abs_of_neg h0]
      simp only [mem_ofPred_eq] at hz1
      linarith
  · exact (isOpen_lt continuous_const continuous_re).inter
      ((isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const))
  · exact (convex_halfSpace_re_gt _).inter
      ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _))
  · have hc := circleMap_mem_closedBall (0 : ℂ) hR θ
    rw [mem_closedBall, dist_zero_right] at hc
    have him := abs_le.mp ((abs_im_le_norm _).trans hc)
    have hre : 0 ≤ (circleMap 0 R θ).re := by
      rw [circleMap_zero_re]
      exact mul_nonneg hR (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2⟩)
    refine ⟨?_, ?_, ?_⟩ <;> simp only [mem_ofPred_eq] <;> linarith [him.1, him.2]
  · have hs2 : 1 - s ^ 2 ≤ 1 := by nlinarith
    have hs2' : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
    have hRs : |R * s| ≤ R := by
      rw [abs_mul, abs_of_nonneg hR]
      exact mul_le_of_le_one_right hR (abs_le.mpr hs)
    refine ⟨?_, ?_, ?_⟩ <;> simp only [mem_ofPred_eq, newmanDetour_re, newmanDetour_im]
    · nlinarith
    · linarith [neg_abs_le (R * s), le_abs_self (R * s)]
    · linarith [neg_abs_le (R * s), le_abs_self (R * s)]

/-- The polar part over the detour: it integrates `dz / z` to `π i`, a primitive along it being
`log (-z)`. -/
private theorem integral_deriv_newmanDetour_div (hR : 0 < R) (hδ : 0 < δ) :
    ∫ s in (-1 : ℝ)..1, deriv (newmanDetour R δ) s / newmanDetour R δ s = π * I := by
  have hmem : ∀ s ∈ [[(-1 : ℝ), 1]], -newmanDetour R δ s ∈ slitPlane := by
    intro s hs
    rw [uIcc_of_le (by norm_num)] at hs
    rw [mem_slitPlane_iff, neg_re, neg_im, newmanDetour_re, newmanDetour_im, neg_neg, neg_neg]
    rcases eq_or_ne s 0 with rfl | h
    · left
      simpa using hδ
    · right
      exact mul_ne_zero hR.ne' h
  have hcont : ContinuousOn (fun s ↦ deriv (newmanDetour R δ) s / newmanDetour R δ s)
      [[(-1 : ℝ), 1]] := by
    simp only [deriv_newmanDetour]
    exact (by fun_prop : Continuous fun s : ℝ ↦ 2 * δ * (s : ℂ) - R * I).continuousOn.div
      (continuous_newmanDetour R δ).continuousOn
      fun s _ ↦ newmanDetour_ne_zero hR.ne' hδ.ne' s
  have h := Contour.integral_deriv_div_eq_log_sub_log (f := fun s ↦ -newmanDetour R δ s)
    (f' := fun s ↦ -deriv (newmanDetour R δ) s) countable_empty
    (continuous_newmanDetour R δ).neg.continuousOn
    (fun s _ ↦ (hasDerivAt_newmanDetour R δ s).differentiableAt.hasDerivAt.neg) hmem
    (by simpa only [neg_div_neg_eq] using hcont.intervalIntegrable)
  simp only [neg_div_neg_eq] at h
  rw [h, newmanDetour_one, newmanDetour_neg_one, neg_neg, ← mul_neg,
    log_ofReal_mul hR I_ne_zero, log_ofReal_mul hR (neg_ne_zero.mpr I_ne_zero), log_I, log_neg_I]
  ring

/-- The detour integral of `g z / z`, through a primitive `H` of `dslope g 0`. -/
private theorem integral_newmanDetour_mul_div_eq {U : Set ℂ} {g H : ℂ → ℂ} (hR : 0 < R)
    (hδ : 0 < δ) (hU : U ∈ 𝓝 (0 : ℂ)) (hg : DifferentiableOn ℂ g U)
    (hH : ∀ z ∈ U, HasDerivAt H (dslope g 0 z) z)
    (hdet : ∀ s ∈ Icc (-1 : ℝ) 1, newmanDetour R δ s ∈ U) :
    ∫ s in (-1 : ℝ)..1, deriv (newmanDetour R δ) s *
        (g (newmanDetour R δ s) / newmanDetour R δ s) =
      H (-(R * I)) - H (R * I) + g 0 * (π * I) := by
  have hI : [[(-1 : ℝ), 1]] = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hc : ContinuousOn (deriv (newmanDetour R δ)) [[(-1 : ℝ), 1]] :=
    (by fun_prop : Continuous fun s : ℝ ↦ 2 * δ * (s : ℂ) - R * I).continuousOn.congr
      fun s _ ↦ deriv_newmanDetour R δ s
  rw [Contour.integral_mul_div_eq_of_hasDerivAt_dslope hU hg hH
    (fun s _ ↦ (hasDerivAt_newmanDetour R δ s).differentiableAt.hasDerivAt) hc (hI ▸ hdet)
    (fun s _ ↦ newmanDetour_ne_zero hR.ne' hδ.ne' s), integral_deriv_newmanDetour_div hR hδ,
    newmanDetour_one, newmanDetour_neg_one]

/-- A convex set containing the endpoints `±R * I` of the detour contains `0`, and on it
`dslope g 0` has a primitive when `g` is holomorphic there. -/
private theorem exists_primitive_dslope {U : Set ℂ} {g : ℂ → ℂ} (hU : IsOpen U)
    (hconv : Convex ℝ U) (hg : DifferentiableOn ℂ g U)
    (hdet : ∀ s ∈ Icc (-1 : ℝ) 1, newmanDetour R δ s ∈ U) :
    U ∈ 𝓝 (0 : ℂ) ∧ ∃ H : ℂ → ℂ, ∀ z ∈ U, HasDerivAt H (dslope g 0 z) z := by
  have h0 : (0 : ℂ) ∈ U := by
    have h := hconv (hdet (-1) ⟨le_rfl, by norm_num⟩) (hdet 1 ⟨by norm_num, le_rfl⟩)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    rwa [newmanDetour_neg_one, newmanDetour_one, smul_neg, add_neg_cancel] at h
  exact ⟨hU.mem_nhds h0, Contour.isExactOn_of_starConvex hU (hconv.starConvex h0)
    ((differentiableOn_dslope (hU.mem_nhds h0)).mpr hg)⟩

/-- **Cauchy's formula for Newman's contour.** Let `g` be holomorphic on an open convex set `U`
containing the right semicircle of radius `R > 0` and the detour `newmanDetour R δ` with
`δ > 0`. Then the integral of `g z / z` over the right semicircle, counterclockwise from
`-R * I` to `R * I`, plus its integral over the detour, back from `R * I` to `-R * I` through the
left half-plane, is `2πi g 0`. Both integrals include the velocity of their parametrization. -/
theorem integral_right_semicircle_add_integral_newmanDetour {U : Set ℂ} {g : ℂ → ℂ}
    (hR : 0 < R) (hδ : 0 < δ) (hU : IsOpen U) (hconv : Convex ℝ U)
    (hg : DifferentiableOn ℂ g U) (hcirc : ∀ θ ∈ Icc (-π / 2) (π / 2), circleMap 0 R θ ∈ U)
    (hdet : ∀ s ∈ Icc (-1 : ℝ) 1, newmanDetour R δ s ∈ U) :
    (∫ θ in (-π / 2)..(π / 2), circleMap 0 R θ * I *
        (g (circleMap 0 R θ) / circleMap 0 R θ)) +
      ∫ s in (-1 : ℝ)..1, deriv (newmanDetour R δ) s *
        (g (newmanDetour R δ s) / newmanDetour R δ s) = 2 * π * I * g 0 := by
  obtain ⟨h0, H, hH⟩ := exists_primitive_dslope hU hconv hg hdet
  rw [Contour.integral_circleMap_mul_div_eq_of_hasDerivAt_dslope hR.ne' h0 hg hH
      (by rwa [uIcc_of_le (by linarith [Real.pi_pos])]),
    integral_newmanDetour_mul_div_eq hR hδ h0 hg hH hdet,
    circleMap_pi_div_two, circleMap_neg_pi_div_two]
  simp only [zero_add, zero_sub]
  push_cast
  ring

/-- **The detour replaces the left semicircle.** If `g` is holomorphic on an open convex set `U`
containing the left semicircle of radius `R > 0` and the detour `newmanDetour R δ` with `δ > 0`,
then the integrals of `g z / z` over the left semicircle, counterclockwise from `R * I` to
`-R * I`, and over the detour, which has the same endpoints, agree. -/
theorem integral_left_semicircle_eq_integral_newmanDetour {U : Set ℂ} {g : ℂ → ℂ}
    (hR : 0 < R) (hδ : 0 < δ) (hU : IsOpen U) (hconv : Convex ℝ U)
    (hg : DifferentiableOn ℂ g U)
    (hcirc : ∀ θ ∈ Icc (π / 2) (3 * π / 2), circleMap 0 R θ ∈ U)
    (hdet : ∀ s ∈ Icc (-1 : ℝ) 1, newmanDetour R δ s ∈ U) :
    (∫ θ in (π / 2)..(3 * π / 2), circleMap 0 R θ * I *
        (g (circleMap 0 R θ) / circleMap 0 R θ)) =
      ∫ s in (-1 : ℝ)..1, deriv (newmanDetour R δ) s *
        (g (newmanDetour R δ s) / newmanDetour R δ s) := by
  obtain ⟨h0, H, hH⟩ := exists_primitive_dslope hU hconv hg hdet
  -- The left semicircle ends at `-R * I`, a full turn after the right semicircle starts there.
  have he : 3 * π / 2 = -π / 2 + 2 * π := by ring
  have hc : circleMap 0 R (3 * π / 2) = -(R * I) := by
    rw [he, periodic_circleMap, circleMap_neg_pi_div_two, zero_sub]
  rw [Contour.integral_circleMap_mul_div_eq_of_hasDerivAt_dslope hR.ne' h0 hg hH
      (by rwa [uIcc_of_le (by linarith [Real.pi_pos])]),
    integral_newmanDetour_mul_div_eq hR hδ h0 hg hH hdet, hc, circleMap_pi_div_two, zero_add]
  push_cast
  ring

/-- **The detour contribution vanishes in the limit.** If `w` is continuous on the detour
`newmanDetour R δ` with `δ > 0`, then `∫ w(z) exp (T z) dz` over the detour tends to `0` as
`T → ∞`: the integrand is dominated by `|w(z) dz|`, and `exp (T z) → 0` wherever `re z < 0`,
which holds except at the two endpoints. -/
theorem tendsto_integral_newmanDetour_mul_cexp {w : ℂ → ℂ} (hδ : 0 < δ)
    (hw : ContinuousOn w (newmanDetour R δ '' Icc (-1) 1)) :
    Tendsto (fun T : ℝ ↦ ∫ s in (-1 : ℝ)..1, deriv (newmanDetour R δ) s *
      (w (newmanDetour R δ s) * cexp (T * newmanDetour R δ s))) atTop (𝓝 0) := by
  set γ := newmanDetour R δ
  have hI : [[(-1 : ℝ), 1]] = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hc : ContinuousOn (fun s ↦ deriv γ s * w (γ s)) [[(-1 : ℝ), 1]] := by
    rw [hI]
    simp only [γ, deriv_newmanDetour]
    exact (by fun_prop : Continuous fun s : ℝ ↦ 2 * δ * (s : ℂ) - R * I).continuousOn.mul
      (hw.comp (continuous_newmanDetour R δ).continuousOn (mapsTo_image _ _))
  have hF (T : ℝ) : ContinuousOn (fun s ↦ deriv γ s * (w (γ s) * cexp (T * γ s)))
      [[(-1 : ℝ), 1]] := by
    have := hc.mul ((by fun_prop : Continuous fun s : ℝ ↦ cexp (T * newmanDetour R δ s))
      |>.continuousOn (s := [[(-1 : ℝ), 1]]))
    exact this.congr fun s _ ↦ (mul_assoc _ _ _).symm
  have hnorm (T s : ℝ) : ‖deriv γ s * (w (γ s) * cexp (T * γ s))‖ =
      ‖deriv γ s * w (γ s)‖ * Real.exp (T * (γ s).re) := by
    rw [← mul_assoc, norm_mul, norm_exp, re_ofReal_mul]
  have hlim := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (l := atTop) (μ := volume) (a := -1) (b := 1)
    (F := fun (T : ℝ) s ↦ deriv γ s * (w (γ s) * cexp (T * γ s)))
    (f := fun _ ↦ 0) (fun s ↦ ‖deriv γ s * w (γ s)‖)
    (.of_forall fun T ↦ ((hF T).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc)
    ((eventually_ge_atTop 0).mono fun T hT ↦ .of_forall fun s hs ↦ by
      rw [hnorm]
      have hs' : s ∈ Icc (-1 : ℝ) 1 := hI ▸ uIoc_subset_uIcc hs
      refine mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr ?_)
      exact mul_nonpos_of_nonneg_of_nonpos hT (newmanDetour_re_nonpos hδ.le hs'))
    hc.norm.intervalIntegrable ?_
  · simpa using hlim
  · filter_upwards [Measure.ae_ne volume 1] with s hs1 hs
    rw [uIoc_of_le (by norm_num)] at hs
    have hre := newmanDetour_re_neg (R := R) hδ ⟨hs.1, lt_of_le_of_ne hs.2 hs1⟩
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [hnorm]
    have h := (Real.tendsto_exp_atBot.comp
      (tendsto_id.atTop_mul_const_of_neg hre)).const_mul ‖deriv γ s * w (γ s)‖
    rw [mul_zero] at h
    exact h

/-- **The detour contribution in Newman's argument vanishes in the limit.** If `G` is continuous
on the detour `newmanDetour R δ` with `R, δ > 0`, then the detour integral of `G` against Newman's
kernel `exp (T z) (1 + z² / R²) / z` tends to `0` as `T → ∞`. -/
theorem tendsto_integral_newmanDetour_mul_kernel {G : ℂ → ℂ} (hR : 0 < R) (hδ : 0 < δ)
    (hG : ContinuousOn G (newmanDetour R δ '' Icc (-1) 1)) :
    Tendsto (fun T : ℝ ↦ ∫ s in (-1 : ℝ)..1, deriv (newmanDetour R δ) s *
      (G (newmanDetour R δ s) * cexp (T * newmanDetour R δ s) *
        (1 + newmanDetour R δ s ^ 2 / (R : ℂ) ^ 2) / newmanDetour R δ s)) atTop (𝓝 0) := by
  have hw : ContinuousOn (fun z ↦ G z * (1 + z ^ 2 / (R : ℂ) ^ 2) / z)
      (newmanDetour R δ '' Icc (-1) 1) := by
    refine (hG.mul (by fun_prop)).div continuousOn_id ?_
    rintro _ ⟨s, -, rfl⟩
    exact newmanDetour_ne_zero hR.ne' hδ.ne' s
  refine (tendsto_integral_newmanDetour_mul_cexp hδ hw).congr fun T ↦
    intervalIntegral.integral_congr fun s _ ↦ ?_
  ring

end TauCeti.LSeries

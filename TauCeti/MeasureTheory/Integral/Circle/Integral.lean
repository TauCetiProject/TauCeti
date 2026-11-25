/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Circle integrals: linear maps, the angle interval and the radius

This file records that continuous linear maps commute with Mathlib's circle integrals
`∮ z in C(c, R), f z`, the circle-integral analogue of
`ContinuousLinearMap.intervalIntegral_comp_comm`. It also writes a circle integral over the angle
interval `[-π, π]` instead of `[0, 2π]`, and shows that for `f` continuous on a closed disc the
circle integrals over the concentric circles depend continuously on the radius up to the
boundary circle. By periodicity of `circleMap` a circle integral may also be computed over
any parameter interval `[a, a + 2π]`.

## Main results

* `ContinuousLinearMap.circleIntegral_comp_comm`: continuous linear maps commute with circle
  integrals.
* `circleIntegral.integral_of_not_completeSpace`: in an incomplete codomain every circle integral
  is `0`.
* `TauCeti.circleIntegral_eq_intervalIntegral_add_two_pi`: a circle integral may be computed over
  any parameter interval of length `2π`.
* `TauCeti.integral_neg_pi_pi_eq_circleIntegral`: a circle integral as an integral over
  `[-π, π]`.
* `ContinuousOn.continuousOn_circleIntegral`: for `f` continuous on the closed disc
  `|z - c| ≤ R`, the map `r ↦ ∮ z in C(c, r), f z` is continuous on `[0, R]`.
* `TauCeti.norm_circleIntegral_sub_inv_smul_sub_le` and
  `TauCeti.norm_circleIntegral_sub_inv_smul_sub_le_sSup`: quantitative bounds on
  `‖(∮ z in C(c, R), (z - c)⁻¹ • f z) - (2 * π * I) • y‖` in terms of `‖f z - y‖` on the circle.
* `Filter.Tendsto.tendsto_circleIntegral_sub_inv_smul_nhdsGT`,
  `ContinuousAt.tendsto_circleIntegral_sub_inv_smul_nhdsGT`, and
  `ContinuousOn.tendsto_circleIntegral_sub_inv_smul_nhdsGT`: for maps into a complete space, as
  `R → 0⁺`, `∮ z in C(c, R), (z - c)⁻¹ • f z` tends to `(2 * π * I) • y` from a punctured limit
  `f z → y` along `𝓝[≠] c` (or continuity at `c`) together with eventual circle-integrability on
  small positive circles (automatic for `ContinuousOn` on a neighborhood of `c`).
-/

public section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Continuous linear maps commute with circle integrals. -/
theorem ContinuousLinearMap.circleIntegral_comp_comm [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℂ] F) {f : ℂ → E} {c : ℂ} {R : ℝ} (hf : CircleIntegrable f c R) :
    ∮ z in C(c, R), L (f z) = L (∮ z in C(c, R), f z) := by
  rw [circleIntegral, circleIntegral, ← L.intervalIntegral_comp_comm hf.out]
  simp only [map_smul]

/-- In an incomplete codomain every circle integral is `0`. -/
theorem circleIntegral.integral_of_not_completeSpace (hE : ¬CompleteSpace E) (f : ℂ → E) (c : ℂ)
    (R : ℝ) : ∮ z in C(c, R), f z = 0 := by
  rw [circleIntegral, intervalIntegral.integral_of_not_completeSpace hE]

open Complex Filter Metric Set
open scoped Real Topology

/-- By periodicity of `circleMap`, a circle integral may be computed over any parameter interval
`[a, a + 2π]` instead of `[0, 2π]`. -/
theorem TauCeti.circleIntegral_eq_intervalIntegral_add_two_pi (f : ℂ → E) (c : ℂ) (R a : ℝ) :
    (∮ z in C(c, R), f z) = ∫ θ in a..a + 2 * π, deriv (circleMap c R) θ • f (circleMap c R θ) := by
  have hper : Function.Periodic
      (fun θ ↦ deriv (circleMap c R) θ • f (circleMap c R θ)) (2 * π) := fun θ ↦ by
    simp only [deriv_circleMap, periodic_circleMap 0 R θ, periodic_circleMap c R θ]
  simpa [circleIntegral] using hper.intervalIntegral_add_eq 0 a

/-- A circle integral written over the angle interval `[-π, π]`. -/
theorem TauCeti.integral_neg_pi_pi_eq_circleIntegral (f : ℂ → E) (c : ℂ) (R : ℝ) :
    (∫ θ in -π..π, (circleMap 0 R θ * I) • f (circleMap c R θ)) = ∮ z in C(c, R), f z := by
  rw [TauCeti.circleIntegral_eq_intervalIntegral_add_two_pi f c R (-π),
    show -π + 2 * π = π by ring]
  simp only [deriv_circleMap]

/-- For `f` continuous on the closed disc `|z - c| ≤ R`, the circle integrals
`r ↦ ∮ z in C(c, r), f z` over the concentric circles are continuous in the radius on `[0, R]`,
including at the boundary circle. -/
theorem ContinuousOn.continuousOn_circleIntegral {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : ContinuousOn f (closedBall c R)) :
    ContinuousOn (fun r ↦ ∮ z in C(c, r), f z) (Icc 0 R) := by
  rcases lt_or_ge R 0 with hR | hR
  · simp [Icc_eq_empty_of_lt hR]
  -- Clamp the radius to `[0, R]`, so that the circles stay in the closed disc.
  set ρ : ℝ → ℝ := fun r ↦ max 0 (min r R) with hρ
  have hmem (r θ : ℝ) : circleMap c (ρ r) θ ∈ closedBall c R := by
    rw [mem_closedBall, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
      abs_of_nonneg (le_max_left _ _)]
    exact max_le hR (min_le_right _ _)
  have hG : Continuous fun p : ℝ × ℝ ↦
      deriv (circleMap c (ρ p.1)) p.2 • f (circleMap c (ρ p.1) p.2) := by
    simp only [deriv_circleMap]
    have hcm : Continuous fun p : ℝ × ℝ ↦ circleMap c (ρ p.1) p.2 := by
      unfold circleMap
      fun_prop
    have hcm0 : Continuous fun p : ℝ × ℝ ↦ circleMap 0 (ρ p.1) p.2 := by
      unfold circleMap
      fun_prop
    exact (hcm0.mul continuous_const).smul (hf.comp_continuous hcm fun p ↦ hmem p.1 p.2)
  have hcont : Continuous fun r ↦ ∮ z in C(c, ρ r), f z :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG 0 (2 * π)
  refine hcont.continuousOn.congr fun r hr ↦ ?_
  simp [hρ, hr.1, hr.2]

/-- **Oscillation bound for the Cauchy integral over a circle.** For `R > 0`, if `f` is
circle-integrable on `|z - c| = R` and `‖f z - y‖ ≤ M` on that circle, then
`∮ z in C(c, R), (z - c)⁻¹ • f z` differs from `(2 * π * I) • y` by at most `2 * π * M`. No
differentiability of `f` is assumed. -/
theorem TauCeti.norm_circleIntegral_sub_inv_smul_sub_le [CompleteSpace E] {f : ℂ → E} {c : ℂ}
    {y : E} {R M : ℝ} (hR : 0 < R) (hf : CircleIntegrable f c R)
    (hM : ∀ z ∈ sphere c R, ‖f z - y‖ ≤ M) :
    ‖(∮ z in C(c, R), (z - c)⁻¹ • f z) - (2 * π * I : ℂ) • y‖ ≤ 2 * π * M := by
  have hint : ∮ z in C(c, R), (z - c)⁻¹ • f z = (2 * π * I : ℂ) • Real.circleAverage f c R :=
    (inv_smul_eq_iff₀ Complex.two_pi_I_ne_zero).mp
      (Real.circleAverage_eq_circleIntegral hR.ne').symm
  have hconst : CircleIntegrable (fun _ ↦ y) c R := circleIntegrable_const y c R
  rw [hint, ← Real.circleAverage_const y c R, ← smul_sub, ← Real.circleAverage_sub hf hconst,
    norm_smul, norm_mul, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg
      Real.pi_pos.le, Complex.norm_I, mul_one]
  refine mul_le_mul_of_nonneg_left
    (Real.norm_circleAverage_le_circleAverage_norm.trans ?_) (by positivity)
  refine Real.circleAverage_mono_on_of_le_circle (hf.sub hconst).norm fun z hz ↦ ?_
  rw [abs_of_pos hR] at hz
  exact hM z hz

/-- **Supremum oscillation bound for the Cauchy integral over a circle.** For `R > 0` and `f`
continuous on `sphere c R`, `‖(∮ z in C(c, R), (z - c)⁻¹ • f z) - (2 * π * I) • y‖` is bounded
by `2 * π` times the supremum of `‖f z - y‖` over `sphere c R`. -/
theorem TauCeti.norm_circleIntegral_sub_inv_smul_sub_le_sSup [CompleteSpace E] {f : ℂ → E}
    {c : ℂ} {y : E} {R : ℝ} (hR : 0 < R) (hf : ContinuousOn f (sphere c R)) :
    ‖(∮ z in C(c, R), (z - c)⁻¹ • f z) - (2 * π * I : ℂ) • y‖ ≤
      2 * π * sSup ((fun z ↦ ‖f z - y‖) '' sphere c R) := by
  have hbdd : BddAbove ((fun z ↦ ‖f z - y‖) '' sphere c R) :=
    ((isCompact_sphere c R).image_of_continuousOn (hf.sub continuousOn_const).norm).bddAbove
  exact TauCeti.norm_circleIntegral_sub_inv_smul_sub_le hR (hf.circleIntegrable hR.le)
    fun z hz ↦ le_csSup hbdd (mem_image_of_mem _ hz)

/-- **Small-circle limit of the Cauchy integral from a punctured limit.** If `f z → y` along the
punctured neighborhood `𝓝[≠] c` and `f` is circle-integrable on small positive circles centered at
`c`, then `∮ z in C(c, R), (z - c)⁻¹ • f z → (2 * π * I) • y` as `R → 0⁺`. -/
theorem Filter.Tendsto.tendsto_circleIntegral_sub_inv_smul_nhdsGT [CompleteSpace E] {f : ℂ → E}
    {c : ℂ} {y : E} (hf : Tendsto f (𝓝[≠] c) (𝓝 y))
    (hint : ∀ᶠ R in 𝓝[>] 0, CircleIntegrable f c R) :
    Tendsto (fun R ↦ ∮ z in C(c, R), (z - c)⁻¹ • f z) (𝓝[>] 0)
      (𝓝 ((2 * π * I : ℂ) • y)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε' : 0 < ε / (4 * π) := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hdist⟩ := Metric.mem_nhdsWithin_iff.mp (hf (Metric.ball_mem_nhds y hε'))
  filter_upwards [Ioo_mem_nhdsGT hδ, hint] with R hR hintR
  rw [dist_eq_norm]
  calc
    ‖(∮ z in C(c, R), (z - c)⁻¹ • f z) - (2 * π * I : ℂ) • y‖
        ≤ 2 * π * (ε / (4 * π)) :=
          TauCeti.norm_circleIntegral_sub_inv_smul_sub_le hR.1 hintR fun z hz ↦ by
            rw [← dist_eq_norm]
            have hzne : z ≠ c := fun h ↦ hR.1.ne (by simpa [h] using mem_sphere.mp hz)
            exact (mem_ball.mp (hdist ⟨mem_ball.mpr (by rw [mem_sphere.mp hz]; exact hR.2),
              hzne⟩)).le
    _ = ε / 2 := by
          have hpi : π ≠ 0 := Real.pi_ne_zero
          field_simp
          ring
    _ < ε := half_lt_self hε

/-- **Small-circle limit of the Cauchy integral at a point of continuity.** If `f` is continuous
at `c` and circle-integrable on small positive circles centered at `c`, then
`∮ z in C(c, R), (z - c)⁻¹ • f z → (2 * π * I) • f c` as `R → 0⁺`. -/
theorem ContinuousAt.tendsto_circleIntegral_sub_inv_smul_nhdsGT [CompleteSpace E] {f : ℂ → E}
    {c : ℂ} (hf : ContinuousAt f c) (hint : ∀ᶠ R in 𝓝[>] 0, CircleIntegrable f c R) :
    Tendsto (fun R ↦ ∮ z in C(c, R), (z - c)⁻¹ • f z) (𝓝[>] 0)
      (𝓝 ((2 * π * I : ℂ) • f c)) :=
  (hf.tendsto.mono_left nhdsWithin_le_nhds).tendsto_circleIntegral_sub_inv_smul_nhdsGT hint

/-- **Small-circle limit of the Cauchy integral for a map continuous near the center.** If `f` is
continuous on a neighborhood of `c`, then `∮ z in C(c, R), (z - c)⁻¹ • f z → (2 * π * I) • f c`
as `R → 0⁺`. -/
theorem ContinuousOn.tendsto_circleIntegral_sub_inv_smul_nhdsGT [CompleteSpace E] {f : ℂ → E}
    {s : Set ℂ} {c : ℂ} (hf : ContinuousOn f s) (hs : s ∈ 𝓝 c) :
    Tendsto (fun R ↦ ∮ z in C(c, R), (z - c)⁻¹ • f z) (𝓝[>] 0)
      (𝓝 ((2 * π * I : ℂ) • f c)) := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hs
  refine (hf.continuousAt hs).tendsto_circleIntegral_sub_inv_smul_nhdsGT ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with R hR
  exact (hf.mono ((sphere_subset_ball hR.2).trans hsub)).circleIntegrable hR.1.le

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Convex.Integral
import TauCeti.Analysis.BoundedVariation.Ball
import TauCeti.Analysis.BoundedVariation.Poincare
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The reduced boundary of a ball

Let `μ` be an additive Haar measure on a finite-dimensional real inner product space `E`. For
`r > 0`, the ball `ball c r` has reduced boundary the sphere `sphere c r` in the whole space, with
outer normal `ν(x) = (x - c) / r` (`TauCeti.reducedBoundary_ball`, `TauCeti.outerNormal_ball`). Its
exterior `(closedBall c r)ᶜ`, a set of infinite volume, has the same reduced boundary and the
opposite normal (`TauCeti.reducedBoundary_compl_closedBall`,
`TauCeti.outerNormal_compl_closedBall`).

The reduced boundary lies in the frontier, the sphere, and the perimeter measure `|Dχ|` is
concentrated on it. The proof identifies the normal, then shows every point of the sphere is in
the reduced boundary.

* *The normal.* For the field `φ(x) = θ(x) (x - c) / r`, with a bump `θ` equal to one on the
  closed ball, the Gauss–Green formula gives `∫ ⟪φ, ν⟫ d|Dχ| = ∫_B div φ = (n / r) μ(B)`, which is
  the perimeter `|Dχ|(E)` (`TauCeti.perimeter_ball_eq_ofReal_div_mul`). On the sphere `φ` is the
  unit vector `(x - c) / r`, so `1 - ⟪φ, ν⟫ ≥ 0` there and integrates to zero: `ν = (x - c) / r`
  at `|Dχ|`-almost every point.
* *The support.* Every ball `ball x ρ` around a point `x` of the sphere meets both the ball and the
  exterior of the closed ball in open sets of positive measure, so by the Poincaré inequality on
  `ball x ρ` the perimeter of the ball in `ball x ρ` is positive, and hence so is
  `|Dχ| (closedBall x ρ)`.
* *The limit.* The averages of the polar density `-ν` over `closedBall x ρ` against `|Dχ|` are
  averages of the continuous field `-(y - c) / r` over sets of positive finite measure, so they
  converge to `-(x - c) / r` as `ρ → 0`.

## Main results

* `TauCeti.reducedBoundary_ball`: `∂*(ball c r) = sphere c r` for `r > 0`.
* `TauCeti.outerNormal_ball`: the outer normal at `x ∈ sphere c r` is `r⁻¹ • (x - c)`.
* `TauCeti.reducedBoundary_compl_closedBall`, `TauCeti.outerNormal_compl_closedBall`: the
  exterior of the closed ball has the same reduced boundary and the opposite normal.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 15.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Module Set Filter TopologicalSpace
open scoped ENNReal Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {c x : E} {r : ℝ}

/-- The indicator of a ball is locally integrable. -/
private theorem locallyIntegrableOn_indicator_ball :
    LocallyIntegrableOn ((ball c r).indicator (1 : E → ℝ)) (⊤ : Opens E) μ :=
  locallyIntegrableOn_indicator_const measurableSet_ball.nullMeasurableSet 1

/-- A ball has finite perimeter in the whole space. -/
private theorem forall_exists_totalVariationOn_indicator_ball_ne_top :
    ∀ K, IsCompact K → K ⊆ (⊤ : Opens E) → ∃ U : Opens E, K ⊆ (U : Set E) ∧
      totalVariationOn μ U ((ball c r).indicator 1) ≠ ∞ := fun K _ _ => by
  refine ⟨⊤, by simp, ?_⟩
  rw [← perimeter_def, perimeter_ball_eq_ofReal_div_mul]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne

/-- The perimeter measure of a ball is concentrated on the sphere. -/
private theorem ae_mem_sphere (hr : 0 < r) :
    ∀ᵐ y : (⊤ : Opens E) ∂variationMeasure μ ⊤ ((ball c r).indicator 1),
      (y : E) ∈ reducedBoundary μ ⊤ (ball c r) ∧ (y : E) ∈ sphere c r := by
  filter_upwards [ae_mem_reducedBoundary] with y hy
  exact ⟨hy, frontier_ball c hr.ne' ▸ reducedBoundary_subset_frontier hy⟩

/-- The perimeter measure of a ball has total mass `(n / r) μ (ball c r)`. -/
private theorem variationMeasure_ball_univ :
    variationMeasure μ ⊤ ((ball c r).indicator 1) univ =
      ENNReal.ofReal (finrank ℝ E / r) * μ (ball c r) := by
  rw [variationMeasure_univ locallyIntegrableOn_indicator_ball
    forall_exists_totalVariationOn_indicator_ball_ne_top, ← perimeter_def,
    perimeter_ball_eq_ofReal_div_mul]

/-- The perimeter measure of a ball is finite. -/
private theorem isFiniteMeasure_variationMeasure_ball :
    IsFiniteMeasure (variationMeasure μ ⊤ ((ball c r).indicator 1)) :=
  ⟨by
    rw [variationMeasure_ball_univ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- On the sphere, `(y - c) / r` is a unit vector. -/
private theorem norm_inv_smul_sub_eq_one (hr : 0 < r) {y : E} (hy : y ∈ sphere c r) :
    ‖r⁻¹ • (y - c)‖ = 1 := by
  rw [norm_smul, ← dist_eq_norm, mem_sphere.1 hy, Real.norm_of_nonneg (inv_nonneg.2 hr.le),
    inv_mul_cancel₀ hr.ne']

/-- **Gauss–Green for the ball against the radial field.** For a continuous field `φ` equal to
`(y - c) / r` on the sphere, `∫ ⟪φ, ν⟫ d|Dχ| = |Dχ| (E)`: the divergence of the radial field
is `n / r` on the ball, and `(n / r) μ (ball c r)` is the perimeter. -/
private theorem exists_integral_inner_outerNormal_ball_eq (hr : 0 < r) :
    ∃ φ : E → E, Continuous φ ∧ (∀ y ∈ sphere c r, φ y = r⁻¹ • (y - c)) ∧
      ∫ y, ⟪φ y, outerNormal μ ⊤ (ball c r) y⟫ ∂variationMeasure μ ⊤ ((ball c r).indicator 1) =
        (variationMeasure μ ⊤ ((ball c r).indicator 1)).real univ := by
  -- The field `θ (y - c) / r`, with a bump `θ` equal to one on the closed ball.
  let θ : ContDiffBump c := ⟨r, 2 * r, hr, by linarith⟩
  set φ : E → E := fun y => (r⁻¹ * θ y) • (y - c)
  have hφd : ContDiff ℝ 1 φ := (contDiff_const.mul θ.contDiff).smul (contDiff_id.sub contDiff_const)
  have hdiv (y : E) (hy : y ∈ ball c r) :
      LinearMap.trace ℝ E (fderiv ℝ φ y : E →ₗ[ℝ] E) = finrank ℝ E / r := by
    have hloc : φ =ᶠ[𝓝 y] fun z => r⁻¹ • (z - c) := by
      filter_upwards [isOpen_ball.mem_nhds hy] with z hz
      simp only [φ]
      rw [θ.one_of_mem_closedBall (ball_subset_closedBall hz), mul_one]
    have hd : HasFDerivAt (fun z => r⁻¹ • (z - c)) (r⁻¹ • ContinuousLinearMap.id ℝ E) y :=
      ((hasFDerivAt_id y).sub_const c).const_smul _
    rw [hloc.fderiv_eq, hd.fderiv]
    simp [div_eq_inv_mul]
  refine ⟨φ, hφd.continuous, fun y hy => ?_, ?_⟩
  · simp only [φ]
    rw [θ.one_of_mem_closedBall (sphere_subset_closedBall hy), mul_one]
  rw [← integral_trace_fderiv_mul_indicator_eq_integral_inner_outerNormal
    locallyIntegrableOn_indicator_ball forall_exists_totalVariationOn_indicator_ball_ne_top hφd
    θ.hasCompactSupport.mul_left.smul_right (by simp), measureReal_def,
    variationMeasure_ball_univ, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ← measureReal_def]
  have hind (y : E) : LinearMap.trace ℝ E (fderiv ℝ φ y : E →ₗ[ℝ] E) *
      (ball c r).indicator 1 y =
        (ball c r).indicator (fun y => LinearMap.trace ℝ E (fderiv ℝ φ y : E →ₗ[ℝ] E)) y := by
    by_cases hy : y ∈ ball c r <;> simp [hy]
  simp_rw [hind]
  rw [integral_indicator measurableSet_ball, setIntegral_congr_fun measurableSet_ball hdiv,
    setIntegral_const, smul_eq_mul, mul_comm]

/-- **The outer normal of a ball**, almost everywhere: at `|Dχ|`-almost every point, the outer
normal of `ball c r` is `r⁻¹ • (y - c)`. -/
private theorem ae_outerNormal_ball_eq (hr : 0 < r) :
    ∀ᵐ y : (⊤ : Opens E) ∂variationMeasure μ ⊤ ((ball c r).indicator 1),
      outerNormal μ ⊤ (ball c r) y = r⁻¹ • ((y : E) - c) := by
  set V := variationMeasure μ ⊤ ((ball c r).indicator 1)
  have := isFiniteMeasure_variationMeasure_ball (μ := μ) (c := c) (r := r)
  obtain ⟨φ, hφc, hφs, hGG⟩ := exists_integral_inner_outerNormal_ball_eq (μ := μ) hr
  -- On the sphere, `φ` and `ν` are unit vectors, so `⟪φ, ν⟫ ≤ 1`.
  have hle (y : (⊤ : Opens E)) (hy : (y : E) ∈ reducedBoundary μ ⊤ (ball c r) ∧
      (y : E) ∈ sphere c r) : ‖⟪φ y, outerNormal μ ⊤ (ball c r) y⟫‖ ≤ 1 := by
    rw [hφs _ hy.2]
    exact (norm_inner_le_norm _ _).trans_eq (by
      rw [norm_inv_smul_sub_eq_one hr hy.2, norm_outerNormal hy.1, one_mul])
  have hint : Integrable (fun y : (⊤ : Opens E) => ⟪φ y, outerNormal μ ⊤ (ball c r) y⟫) V :=
    (integrable_const (1 : ℝ)).mono'
      (Measurable.inner (hφc.comp continuous_subtypeVal).measurable
        (measurable_outerNormal.comp measurable_subtypeVal)).aestronglyMeasurable
      ((ae_mem_sphere hr).mono hle)
  -- Hence `1 - ⟪φ, ν⟫`, nonnegative almost everywhere, integrates to zero.
  have hzero := (integral_eq_zero_iff_of_nonneg_ae (μ := V)
    (f := fun y : (⊤ : Opens E) => 1 - ⟪φ y, outerNormal μ ⊤ (ball c r) y⟫)
    ((ae_mem_sphere hr).mono fun y hy => sub_nonneg.2 ((le_abs_self _).trans (hle y hy)))
    ((integrable_const 1).sub hint)).1 (by
      rw [integral_sub (integrable_const 1) hint, hGG, integral_const, smul_eq_mul, mul_one,
        sub_self])
  filter_upwards [hzero, ae_mem_sphere hr] with y hy hys
  have h1 : ⟪r⁻¹ • ((y : E) - c), outerNormal μ ⊤ (ball c r) y⟫ = 1 := by
    rw [← hφs _ hys.2]
    have h := hy
    simp only [Pi.zero_apply] at h
    linarith
  have h2 := inner_eq_norm_mul_iff_real.1 (by
    rw [h1, norm_inv_smul_sub_eq_one hr hys.2, norm_outerNormal hys.1, one_mul])
  rwa [norm_inv_smul_sub_eq_one hr hys.2, norm_outerNormal hys.1, one_smul, one_smul,
    eq_comm] at h2

/-- Every closed ball around a point of the sphere has positive perimeter measure for the ball:
the ball and the exterior of the closed ball both charge `ball x ρ`, so by the Poincaré
inequality the perimeter of the ball in `ball x ρ` is positive. -/
private theorem variationMeasure_closedBall_ne_zero (hr : 0 < r) (hx : x ∈ sphere c r) {ρ : ℝ}
    (hρ : 0 < ρ) :
    variationMeasure μ ⊤ ((ball c r).indicator 1) (((↑) : (⊤ : Opens E) → E) ⁻¹'
      closedBall x ρ) ≠ 0 := by
  have hu := locallyIntegrableOn_indicator_ball (μ := μ) (c := c) (r := r)
  refine fun h0 => ?_
  have hP := (perimeter_ball_le_variationMeasure_closedBall (x := x) (r := ρ) hu
    forall_exists_totalVariationOn_indicator_ball_ne_top (by simp)).trans_eq h0
  -- By the Poincaré inequality the indicator is almost everywhere constant on `ball x ρ`.
  set a := ⨍ y in ball x ρ, (ball c r).indicator (1 : E → ℝ) y ∂μ
  have hP0 := setLIntegral_enorm_sub_setAverage_le_mul_totalVariationOn_of_convex
    (Ω := ⟨ball x ρ, isOpen_ball⟩) (μ := μ) (convex_ball x ρ) isBounded_ball
    (hu.mono_set (subset_univ _)) subset_rfl (measure_ball_pos μ x hρ).ne'
  rw [← perimeter_def, nonpos_iff_eq_zero.1 hP, mul_zero, nonpos_iff_eq_zero,
    lintegral_eq_zero_iff'
    ((measurable_one.indicator measurableSet_ball).sub_const _).eNorm.aemeasurable] at hP0
  have hconst (U : Set E) (hU : IsOpen U) (hUx : U ⊆ ball x ρ) (hne : U.Nonempty) (b : ℝ)
      (hb : ∀ y ∈ U, (ball c r).indicator (1 : E → ℝ) y = b) : b = a := by
    have : (ae (μ.restrict U)).NeBot := ae_restrict_neBot.2 (hU.measure_ne_zero μ hne)
    obtain ⟨y, hy, hyU⟩ := ((ae_restrict_of_ae_restrict_of_subset hUx hP0).and
      (ae_restrict_mem hU.measurableSet)).exists
    exact (hb y hyU).symm.trans (sub_eq_zero.1 (eNorm_eq_zero.1 hy))
  -- Points `c + (1 ± t) (x - c)` near `x`, inside the ball and outside the closed ball.
  have hxc : ‖x - c‖ = r := by rw [← dist_eq_norm, mem_sphere.1 hx]
  set t := min (1 / 2) (ρ / (2 * r))
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have htρ : t * r < ρ := by
    calc t * r ≤ ρ / (2 * r) * r := by gcongr; exact min_le_right _ _
      _ = ρ / 2 := by field_simp
      _ < ρ := half_lt_self hρ
  have hdist (s : ℝ) : dist (c + s • (x - c)) x = |s - 1| * r ∧
      dist (c + s • (x - c)) c = |s| * r := by
    refine ⟨?_, ?_⟩
    · rw [dist_eq_norm, show c + s • (x - c) - x = (s - 1) • (x - c) by
        rw [sub_smul, one_smul]; abel, norm_smul, Real.norm_eq_abs, hxc]
    · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hxc]
  have h1 : (1 : ℝ) = a := by
    refine hconst (ball x ρ ∩ ball c r) (isOpen_ball.inter isOpen_ball) inter_subset_left
      ⟨c + (1 - t) • (x - c), ?_, ?_⟩ 1 fun y hy => by simp [hy.2]
    · rw [mem_ball, (hdist _).1, show 1 - t - 1 = -t by ring, abs_neg, abs_of_pos ht]
      exact htρ
    · rw [mem_ball, (hdist _).2, abs_of_pos (by linarith [min_le_left (1 / 2 : ℝ) (ρ / (2 * r))])]
      nlinarith
  have h0 : (0 : ℝ) = a := by
    refine hconst (ball x ρ ∩ (closedBall c r)ᶜ)
      (isOpen_ball.inter isClosed_closedBall.isOpen_compl) inter_subset_left
      ⟨c + (1 + t) • (x - c), ?_, ?_⟩ 0 fun y hy => by
        simp [show y ∉ ball c r from fun h => hy.2 (ball_subset_closedBall h)]
    · rw [mem_ball, (hdist _).1, show 1 + t - 1 = t by ring, abs_of_pos ht]
      exact htρ
    · rw [mem_compl_iff, mem_closedBall, not_le, (hdist _).2, abs_of_pos (by linarith)]
      nlinarith
  exact one_ne_zero (h1.trans h0.symm)

/-- The polar density of the ball is `-(y - c) / r` at `|Dχ|`-almost every point, and its averages
over closed balls around a point `x` of the sphere converge to `-(x - c) / r`. -/
private theorem tendsto_setAverage_polarDensity_ball (hr : 0 < r) (hx : x ∈ sphere c r) :
    Tendsto (fun ρ => ⨍ y in ((↑) : (⊤ : Opens E) → E) ⁻¹' closedBall x ρ,
      polarDensity μ ⊤ ((ball c r).indicator 1) y ∂variationMeasure μ ⊤ ((ball c r).indicator 1))
      (𝓝[>] 0) (𝓝 (-(r⁻¹ • (x - c)))) := by
  set V := variationMeasure μ ⊤ ((ball c r).indicator 1)
  have := isFiniteMeasure_variationMeasure_ball (μ := μ) (c := c) (r := r)
  have hpol : ∀ᵐ y ∂V,
      polarDensity μ ⊤ ((ball c r).indicator 1) y = -(r⁻¹ • ((y : E) - c)) := by
    filter_upwards [ae_outerNormal_eq, ae_outerNormal_ball_eq hr] with y h1 h2
    rw [← h2, h1, neg_neg]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨ε * r / 2, by positivity, fun ρ hρ hρd => ?_⟩
  have hρ : 0 < ρ := hρ
  rw [dist_zero_right, Real.norm_of_nonneg hρ.le] at hρd
  have hSm : MeasurableSet (((↑) : (⊤ : Opens E) → E) ⁻¹' closedBall x ρ) :=
    continuous_subtypeVal.measurable measurableSet_closedBall
  have hmem := Convex.set_average_mem (convex_closedBall (-(r⁻¹ • (x - c))) (ε / 2))
    isClosed_closedBall (variationMeasure_closedBall_ne_zero hr hx hρ) (measure_ne_top V _)
    ((ae_restrict_iff' hSm).2 (hpol.mono fun y hy hyS => ?_))
    (Measure.integrableOn_of_bounded (M := 1) (measure_ne_top V _)
      measurable_polarDensity.aestronglyMeasurable
      (ae_restrict_of_ae ((ae_norm_polarDensity_eq_one locallyIntegrableOn_indicator_ball
        forall_exists_totalVariationOn_indicator_ball_ne_top).mono fun y hy => hy.le)))
  · exact (mem_closedBall.1 hmem).trans_lt (half_lt_self hε)
  · rw [hy, mem_closedBall, dist_eq_norm, neg_sub_neg, ← smul_sub, sub_sub_sub_cancel_right,
      norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le), ← dist_eq_norm, dist_comm]
    calc r⁻¹ * dist (y : E) x ≤ r⁻¹ * ρ := by gcongr; exact hyS
      _ ≤ r⁻¹ * (ε * r / 2) := by gcongr
      _ = ε / 2 := by field_simp

/-- Every point of the sphere is in the reduced boundary of the ball. -/
theorem mem_reducedBoundary_ball (hr : 0 < r) (hx : x ∈ sphere c r) :
    x ∈ reducedBoundary μ ⊤ (ball c r) :=
  mem_reducedBoundary.2 ⟨by simp, _, by rw [norm_neg, norm_inv_smul_sub_eq_one hr hx],
    tendsto_setAverage_polarDensity_ball hr hx⟩

/-- **The reduced boundary of a ball** of radius `r > 0` is its sphere. -/
theorem reducedBoundary_ball (hr : 0 < r) : reducedBoundary μ ⊤ (ball c r) = sphere c r :=
  Subset.antisymm (fun _ hx => frontier_ball c hr.ne' ▸ reducedBoundary_subset_frontier hx)
    fun _ hx => mem_reducedBoundary_ball hr hx

/-- **The outer normal of a ball** of radius `r > 0` at a point `x` of its sphere is
`(x - c) / r`. -/
theorem outerNormal_ball (hr : 0 < r) (hx : x ∈ sphere c r) :
    outerNormal μ ⊤ (ball c r) x = r⁻¹ • (x - c) := by
  rw [outerNormal_eq_of_tendsto (tendsto_setAverage_polarDensity_ball hr hx), neg_neg]

/-- The exterior of a closed ball agrees with the complement of the open ball up to the sphere,
a null set. -/
private theorem compl_closedBall_ae_eq (hr : 0 < r) :
    (closedBall c r)ᶜ =ᵐ[μ.restrict (⊤ : Opens E)] (ball c r)ᶜ :=
  ae_restrict_of_ae (μ.addHaar_closedBall_ae_eq_ball_of_ne_zero c r hr.ne').compl

/-- **The reduced boundary of the exterior of a ball**: the complement of the closed ball of
radius `r > 0`, a set of infinite volume, has the same reduced boundary, the sphere. -/
theorem reducedBoundary_compl_closedBall (hr : 0 < r) :
    reducedBoundary μ ⊤ (closedBall c r)ᶜ = sphere c r := by
  rw [reducedBoundary_congr_ae (compl_closedBall_ae_eq hr), reducedBoundary_compl,
    reducedBoundary_ball hr]

/-- **The outer normal of the exterior of a ball** at a point `x` of the sphere is
`-(x - c) / r`, opposite to that of the ball. -/
theorem outerNormal_compl_closedBall (hr : 0 < r) (hx : x ∈ sphere c r) :
    outerNormal μ ⊤ (closedBall c r)ᶜ x = -(r⁻¹ • (x - c)) := by
  rw [outerNormal_congr_ae (compl_closedBall_ae_eq hr),
    outerNormal_compl (mem_reducedBoundary_ball hr hx), outerNormal_ball hr hx]

end TauCeti

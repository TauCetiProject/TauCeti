/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.FiniteDimensional
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Total
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.VolumeDensity

/-!
# The relative volume density of two Riemannian metrics

Let `g` and `g'` be two Riemannian metrics on the same manifold `M`. At a point `x`, the
*relative volume density* of `g'` with respect to `g` is

`J(x) = √(det G'(x) / det G(x))`,

where `G(x)` and `G'(x)` are the Gram matrices of `g_x` and `g'_x` in a basis of `T_x M`. The
ratio does not depend on the basis, since a change of basis multiplies both determinants by the
square of the same nonzero determinant; in a `g`-orthonormal basis, `J(x)` is the square root of
the Gram determinant of `g'_x`. The density is positive, and it is `C^n` for `C^n` metrics.

The Riemannian volume measures of the two metrics, which live on the copies `TauCeti.WithMetric g`
and `TauCeti.WithMetric g'` of `M`, satisfy

`dV_{g'} = J dV_g`,

so that `∫ φ dV_{g'} = ∫ J φ dV_g` for every function `φ` on `M`. In every chart, the chart
volume density of `g'` is `J` times that of `g`. No orientation is used. For a conformal metric
`g' = f g` in real dimension `N`, `J = f ^ (N / 2)`, recovering
`TauCeti.WithMetric.riemannianVolume_rescale`.

The density definition, basis formulas, positivity, and bundle regularity results live in
`TauCeti.Geometry.Manifold.VectorBundle.Riemannian.VolumeDensity`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.relativeVolumeDensity_pullback`: invariance under
  pullback with bijective differential.
* `integrable_riemannianVolume_iff_integrable_relativeVolumeDensity_smul`:
  integrability under a change of metric.
* `Bundle.ContMDiffRiemannianMetric.chartVolumeDensity_toWithMetric_eq_mul`:
  compatibility with chart volume densities.
* `Bundle.ContMDiffRiemannianMetric.riemannianVolume_eq_map_withDensity_relativeVolumeDensity`
  and its integral counterpart: `dV_{g'} = J dV_g`.
* `Bundle.ContMDiffRiemannianMetric.riemannianTotalVolume_eq_integral_relativeVolumeDensity`:
  on a compact manifold,
  `Vol(g') = ∫ J dV_g`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Proposition 2.44 and the discussion of Riemannian densities following it.
-/

public section

open Bundle MeasureTheory Set Riemannian.Tensor TauCeti Bundle.RiemannianMetric
open scoped ENNReal Manifold ContDiff Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {n n' : ℕ∞ω}

variable {g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
  {g' : ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x)}

section Transport

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]

/-- Pulling back both metrics preserves their relative volume density wherever the differential
is surjective as well as injective. -/
theorem relativeVolumeDensity_pullback
    (g : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y))
    (g' : ContMDiffRiemannianMetric J n' F (fun y : N ↦ TangentSpace J y))
    (f : M → N) (hf : ContMDiff I J (n + 1) f) (hf' : ContMDiff I J (n' + 1) f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (x : M) (hsurj : Function.Surjective (mfderiv I J f x)) :
    relativeVolumeDensity (g.pullback f hf hinj).toRiemannianMetric
      (g'.pullback f hf' hinj).toRiemannianMetric x =
      relativeVolumeDensity g.toRiemannianMetric g'.toRiemannianMetric (f x) := by
  have hbij : Function.Bijective (mfderiv I J f x).toLinearMap := ⟨hinj x, hsurj⟩
  let e := LinearEquiv.ofBijective (mfderiv I J f x).toLinearMap hbij
  exact relativeVolumeDensity_eq_of_linearEquiv _ _ g.toRiemannianMetric g'.toRiemannianMetric e
    (fun v w ↦ by simp [e, pullback_inner])
    (fun v w ↦ by simp [e, pullback_inner])

/-- In equal dimensions, pulling back both metrics along an immersion preserves their relative
volume density. -/
theorem relativeVolumeDensity_pullback_of_finrank_eq
    (g : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y))
    (g' : ContMDiffRiemannianMetric J n' F (fun y : N ↦ TangentSpace J y))
    (f : M → N) (hf : ContMDiff I J (n + 1) f) (hf' : ContMDiff I J (n' + 1) f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (x : M) :
    relativeVolumeDensity (g.pullback f hf hinj).toRiemannianMetric
      (g'.pullback f hf' hinj).toRiemannianMetric x =
      relativeVolumeDensity g.toRiemannianMetric g'.toRiemannianMetric (f x) := by
  have hdim' : Module.finrank ℝ (TangentSpace I x) =
      Module.finrank ℝ (TangentSpace J (f x)) := by
    rw [VectorBundle.finrank_eq ℝ E (TangentSpace I),
      VectorBundle.finrank_eq ℝ F (TangentSpace J), hdim]
  have hsurj : Function.Surjective (mfderiv I J f x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (mfderiv I J f x).toLinearMap) hdim').1 (hinj x)
  exact relativeVolumeDensity_pullback g g' f hf hf' hinj x hsurj

end Transport

variable (g g') in
/-- On the chart source at `α`, the relative volume density is the square root of the ratio
of the Gram determinants of `g'` and `g`, in that order, in the chart frame. -/
theorem relativeVolumeDensity_eq_sqrt_div_chartGramMatrix {α x : M}
    (hx : x ∈ (chartAt H α).source) :
    relativeVolumeDensity g.toRiemannianMetric g'.toRiemannianMetric x =
      √((chartGramMatrix (I := I) (WithMetric.toWithMetric g' α)
          (WithMetric.toWithMetric g' x)).det /
        (chartGramMatrix (I := I) (WithMetric.toWithMetric g α)
          (WithMetric.toWithMetric g x)).det) := by
  have hx' : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  rw [Module.Basis.relativeVolumeDensity_eq_sqrt_div
    ((trivializationAt E (TangentSpace I) α).basisAt (Module.finBasis ℝ E) hx'),
    ContMDiffRiemannianMetric.chartGramMatrix_toWithMetric,
    ContMDiffRiemannianMetric.chartGramMatrix_toWithMetric]
  simp only [chartLocalFrame_apply_of_mem_chart_source α hx, toRiemannianMetric_inner]

variable (g g') in
/-- **Compatibility with chart volume densities.** The chart volume density of `g'` is the
relative volume density times the chart volume density of `g`, including outside the chart
source. -/
theorem chartVolumeDensity_toWithMetric_eq_mul (α x : M) :
    chartVolumeDensity (I := I) (WithMetric.toWithMetric g' α) (WithMetric.toWithMetric g' x) =
      relativeVolumeDensity g.toRiemannianMetric g'.toRiemannianMetric x *
        chartVolumeDensity (I := I) (WithMetric.toWithMetric g α)
          (WithMetric.toWithMetric g x) := by
  by_cases hx : x ∈ (chartAt H α).source
  · have hpos : 0 < (chartGramMatrix (I := I) (WithMetric.toWithMetric g α)
        (WithMetric.toWithMetric g x)).det :=
      chartGramMatrix_det_pos _ (by
        rw [TangentBundle.trivializationAt_baseSet]
        exact (WithMetric.mem_chartAt_source_iff _ _).2 hx)
    rw [relativeVolumeDensity_eq_sqrt_div_chartGramMatrix g g' hx, chartVolumeDensity_def,
      chartVolumeDensity_def, ← Real.sqrt_mul (div_nonneg (chartGramMatrix_det_nonneg _ _)
        hpos.le), div_mul_cancel₀ _ hpos.ne']
  by_cases hdim : Module.finrank ℝ E = 0
  · have : Subsingleton (TangentSpace I x) := Module.finrank_zero_iff.mp (by
      rw [VectorBundle.finrank_eq ℝ E (TangentSpace I)]
      exact hdim)
    have hinner : g'.toRiemannianMetric.inner x = g.toRiemannianMetric.inner x := by
      ext v w
      have hv : v = 0 := Subsingleton.elim _ _
      simp [hv]
    have : IsEmpty (Fin (Module.finrank ℝ E)) := Fin.isEmpty_iff.mpr hdim
    rw [relativeVolumeDensity_congr _ _ rfl hinner, relativeVolumeDensity_self]
    simp [chartVolumeDensity_def]
  · have : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hdim)
    have hframe : ∀ i, chartLocalFrame (I := I) α i x = 0 := by
      intro i
      rw [chartLocalFrame_def, Trivialization.localFrame_apply_of_notMem]
      simpa only [TangentBundle.trivializationAt_baseSet] using hx
    have hzero (m : ℕ∞ω)
        (h : ContMDiffRiemannianMetric I m E (fun x : M ↦ TangentSpace I x)) :
        chartVolumeDensity (I := I) (WithMetric.toWithMetric h α)
          (WithMetric.toWithMetric h x) = 0 := by
      have hz : chartGramMatrix (I := I) (WithMetric.toWithMetric h α)
          (WithMetric.toWithMetric h x) = 0 := by
        rw [chartGramMatrix_toWithMetric]
        ext i j
        simp [hframe]
      rw [chartVolumeDensity_def, hz, Matrix.det_zero, Real.sqrt_zero]
    rw [hzero _ g, hzero _ g', mul_zero]

variable (g g') in
/-- On the chart source at `α`, the relative volume density is the ratio of the chart volume
densities of the two metrics. -/
theorem relativeVolumeDensity_eq_div_chartVolumeDensity {α x : M}
    (hx : x ∈ (chartAt H α).source) :
    relativeVolumeDensity g.toRiemannianMetric g'.toRiemannianMetric x =
      chartVolumeDensity (I := I) (WithMetric.toWithMetric g' α) (WithMetric.toWithMetric g' x) /
        chartVolumeDensity (I := I) (WithMetric.toWithMetric g α)
          (WithMetric.toWithMetric g x) := by
  have hpos : 0 < chartVolumeDensity (I := I) (WithMetric.toWithMetric g α)
      (WithMetric.toWithMetric g x) :=
    chartVolumeDensity_pos _ (by
      rw [TangentBundle.trivializationAt_baseSet]
      exact (WithMetric.mem_chartAt_source_iff _ _).2 hx)
  rw [chartVolumeDensity_toWithMetric_eq_mul g g' α x, mul_div_cancel_right₀ _ hpos.ne']


section Measure

variable [LindelofSpace M]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

omit [LindelofSpace M] in
/-- The relative volume density, as a density on the copy of `M` carrying `g`, is measurable. -/
private theorem measurable_ofReal_relativeVolumeDensity :
    Measurable fun x : WithMetric g ↦
      ENNReal.ofReal (relativeVolumeDensity g.toRiemannianMetric g'.toRiemannianMetric
        x.ofWithMetric) :=
  (((ContinuousRiemannianMetric.continuous_relativeVolumeDensity
    g.toContinuousRiemannianMetric g'.toContinuousRiemannianMetric
    ).comp WithMetric.continuous_ofWithMetric).measurable).ennreal_ofReal

variable (g g') in
/-- **Volume under a change of metric.** The Riemannian volume of `g'` is the image, under the
identity map between the copies of `M`, of the Riemannian volume of `g` weighted by the relative
volume density: `dV_{g'} = J dV_g`. -/
theorem riemannianVolume_eq_map_withDensity_relativeVolumeDensity :
    riemannianVolume I (WithMetric g') =
      ((riemannianVolume I (WithMetric g)).withDensity fun x ↦
          ENNReal.ofReal (relativeVolumeDensity g.toRiemannianMetric g'.toRiemannianMetric
            x.ofWithMetric)).map
        fun x ↦ WithMetric.toWithMetric g' x.ofWithMetric := by
  set ι : WithMetric g → WithMetric g' := fun x ↦ WithMetric.toWithMetric g' x.ofWithMetric
  have hι : Measurable ι :=
    (WithMetric.measurableEmbedding_toWithMetric_ofWithMetric g g').measurable
  symm
  refine eq_riemannianVolume_iff.2 fun β ↦ ?_
  obtain ⟨β⟩ := β
  ext s hs
  have hS : MeasurableSet (s ∩ (chartAt H (WithMetric.toWithMetric g' β)).source) :=
    hs.inter (chartAt H _).open_source.measurableSet
  have hsub : ι ⁻¹' (s ∩ (chartAt H (WithMetric.toWithMetric g' β)).source) ⊆
      (chartAt H (WithMetric.toWithMetric g β)).source := fun x hx ↦
    (WithMetric.mem_chartAt_source_iff _ x).2 ((WithMetric.mem_chartAt_source_iff _ (ι x)).1 hx.2)
  rw [Measure.restrict_apply hs, Measure.map_apply hι hS, withDensity_apply _ (hι hS),
    setLIntegral_riemannianVolume_of_subset hsub (hι hS), chartRiemannianVolume_apply _ hs]
  have himage : extChartAt I (WithMetric.toWithMetric g β) ''
      (ι ⁻¹' (s ∩ (chartAt H (WithMetric.toWithMetric g' β)).source)) =
      extChartAt I (WithMetric.toWithMetric g' β) ''
        (s ∩ (extChartAt I (WithMetric.toWithMetric g' β)).source) := by
    rw [extChartAt_source]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ι x, hx, by rw [WithMetric.extChartAt_apply, WithMetric.extChartAt_apply]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨WithMetric.toWithMetric g x.ofWithMetric, hx,
        by rw [WithMetric.extChartAt_apply, WithMetric.extChartAt_apply]⟩
  rw [himage]
  refine setLIntegral_congr_fun
    ((hs.inter (isOpen_extChartAt_source _).measurableSet).image_extChartAt _ inter_subset_right)
    fun y hy ↦ ?_
  obtain ⟨x, ⟨-, hx⟩, rfl⟩ := hy
  have hx' : x.ofWithMetric ∈ (chartAt H β).source :=
    (WithMetric.mem_chartAt_source_iff _ x).1 (by rwa [extChartAt_source] at hx)
  have hsymm : (extChartAt I β).symm (extChartAt I β x.ofWithMetric) = x.ofWithMetric :=
    (extChartAt I β).left_inv (by rwa [extChartAt_source])
  simp only [WithMetric.extChartAt_symm_apply, WithMetric.extChartAt_apply,
    WithMetric.ofWithMetric_toWithMetric, hsymm]
  rw [chartVolumeDensity_toWithMetric_eq_mul g g' β x.ofWithMetric,
    ENNReal.ofReal_mul
      (relativeVolumeDensity_nonneg g.toRiemannianMetric g'.toRiemannianMetric _), mul_comm]

variable (g g') in
/-- Integration of a nonnegative function against the volume of `g'`:
`∫ φ dV_{g'} = ∫ J φ dV_g`. -/
theorem lintegral_riemannianVolume_eq_lintegral_relativeVolumeDensity_mul (φ : M → ℝ≥0∞) :
    ∫⁻ x, φ x.ofWithMetric ∂riemannianVolume I (WithMetric g') =
      ∫⁻ x, ENNReal.ofReal (relativeVolumeDensity g.toRiemannianMetric g'.toRiemannianMetric
          x.ofWithMetric) * φ x.ofWithMetric ∂riemannianVolume I (WithMetric g) := by
  rw [riemannianVolume_eq_map_withDensity_relativeVolumeDensity g g',
    (WithMetric.measurableEmbedding_toWithMetric_ofWithMetric g g').lintegral_map,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      measurable_ofReal_relativeVolumeDensity (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [Pi.mul_apply]

variable (g g') in
/-- Integration against the volume of `g'`: `∫ φ dV_{g'} = ∫ J φ dV_g`. -/
theorem integral_riemannianVolume_eq_integral_relativeVolumeDensity_smul {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : M → F) :
    ∫ x, φ x.ofWithMetric ∂riemannianVolume I (WithMetric g') =
      ∫ x, relativeVolumeDensity g.toRiemannianMetric g'.toRiemannianMetric x.ofWithMetric •
        φ x.ofWithMetric ∂riemannianVolume I (WithMetric g) := by
  rw [riemannianVolume_eq_map_withDensity_relativeVolumeDensity g g',
    (WithMetric.measurableEmbedding_toWithMetric_ofWithMetric g g').integral_map,
    integral_withDensity_eq_integral_toReal_smul measurable_ofReal_relativeVolumeDensity
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal
    (relativeVolumeDensity_nonneg g.toRiemannianMetric g'.toRiemannianMetric _)]

variable (g g') in
/-- Integrability under a change of metric is integrability after multiplying by its density. -/
theorem integrable_riemannianVolume_iff_integrable_relativeVolumeDensity_smul {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : M → F) :
    Integrable (fun x : WithMetric g' ↦ φ x.ofWithMetric)
        (riemannianVolume I (WithMetric g')) ↔
      Integrable (fun x : WithMetric g ↦
        relativeVolumeDensity g.toRiemannianMetric g'.toRiemannianMetric x.ofWithMetric •
          φ x.ofWithMetric) (riemannianVolume I (WithMetric g)) := by
  rw [riemannianVolume_eq_map_withDensity_relativeVolumeDensity g g',
    (WithMetric.measurableEmbedding_toWithMetric_ofWithMetric g g').integrable_map_iff,
    integrable_withDensity_iff_integrable_smul' measurable_ofReal_relativeVolumeDensity
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [Function.comp_apply, ENNReal.toReal_ofReal
    (relativeVolumeDensity_nonneg g.toRiemannianMetric g'.toRiemannianMetric _)]

end Measure

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

variable (g g') in
/-- **Total volume under a change of metric.** On a compact manifold, the total volume of `g'` is
`∫ J dV_g`. -/
theorem riemannianTotalVolume_eq_integral_relativeVolumeDensity [CompactSpace M] :
    riemannianTotalVolume I (WithMetric g') =
      ∫ x, relativeVolumeDensity g.toRiemannianMetric g'.toRiemannianMetric x.ofWithMetric
        ∂riemannianVolume I (WithMetric g) := by
  simpa only [integral_const, smul_eq_mul, mul_one, ← riemannianTotalVolume_def] using
    integral_riemannianVolume_eq_integral_relativeVolumeDensity_smul g g'
      fun _ ↦ (1 : ℝ)

end Bundle.ContMDiffRiemannianMetric

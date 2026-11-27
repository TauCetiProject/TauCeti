/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import TauCeti.Geometry.Manifold.Measure.PositiveDensity
import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.MeasureTheory.Integral.CompactlySupported
import TauCeti.Analysis.Calculus.FDeriv.Equiv

/-!
# Measures with a smooth positive density on a manifold

A measure `μ` on a manifold `M` modelled on a real normed space `E` has a **smooth positive
density** when in every chart `e` of the maximal smooth atlas it is `ρ(y) dy` for a function `ρ`
smooth and positive on the chart target (`TauCeti.HasSmoothPositiveDensity`): the integral against
`μ` of a continuous complex-valued function `f` with compact support in the chart source is
`∫_{e.target} ρ(y) f(e⁻¹ y) dy`. Here `dy` is the measure `volume` of the `MeasureSpace E`
instance on the model space, which is Lebesgue measure for `CoordinateSpace n`. These are the
measures for which formal adjoints and transposes of differential and pseudodifferential operators
on `M` are taken; the Riemannian volume of a smooth metric is one, although that is not shown here.

The measure `volume` on `E` itself is one when it is an additive Haar measure, such as Lebesgue
measure (`TauCeti.hasSmoothPositiveDensity_volume`): in a chart `e` of the maximal atlas of `E`,
its density is the absolute Jacobian determinant `|det D(e⁻¹)(y)|`, by the change of variables
formula.

Conversely, a measure that has a smooth positive density and is finite on compact sets reads in
every chart of the maximal atlas as the measure `ρ(y) dy` on the chart target:
`(μ|_{e.source}).map e = ρ(y) dy|_{e.target}`
(`TauCeti.HasSmoothPositiveDensity.exists_map_restrict_source_eq_withDensity`). The defining
identity only tests continuous compactly supported functions, and these determine a measure that
is finite on compact sets, by the uniqueness part of the Riesz–Markov–Kakutani theorem on the
chart target (`MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported_of_isOpen`). So such
a measure is a positive continuous density measure
(`TauCeti.HasSmoothPositiveDensity.isPositiveDensityMeasure`), and in particular positive on
nonempty open sets.

## Main definitions

* `TauCeti.HasSmoothPositiveDensity E μ`: the measure `μ` on a manifold modelled on `E` is given in
  every chart of the maximal atlas by a smooth positive density with respect to the measure
  `volume` of the `MeasureSpace E` instance (Lebesgue measure for `CoordinateSpace n`).

## Main results

* `TauCeti.hasSmoothPositiveDensity_iff`: unfolding the definition.
* `TauCeti.HasSmoothPositiveDensity.exists_integral_real_eq`: the same chart formula for
  real-valued functions.
* `TauCeti.hasSmoothPositiveDensity_volume`: the measure `volume` on a finite-dimensional real
  normed space, when it is an additive Haar measure, has a smooth positive density for the maximal
  atlas.
* `TauCeti.map_restrict_source_eq_withDensity_of_forall_integral_eq`: a measure finite on compact
  sets whose integrals of continuous functions with compact support in a chart source are
  `∫_{e.target} ρ(y) f(e⁻¹ y) dy` reads in the chart as `ρ(y) dy`.
* `TauCeti.HasSmoothPositiveDensity.exists_map_restrict_source_eq_withDensity`: hence a measure
  with a smooth positive density that is finite on compact sets reads in every chart of the
  maximal atlas as a measure with a smooth positive density on the chart target.
* `TauCeti.HasSmoothPositiveDensity.exists_measure_le_smul`: on a compact subset of a chart
  target, such a measure read in the chart and Lebesgue measure bound each other up to constants.
* `TauCeti.HasSmoothPositiveDensity.isPositiveDensityMeasure`: such a measure is a positive
  continuous density measure.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 16,
  the section on densities.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped ContDiff Manifold ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MeasurableSpace M]

variable (E) in
/-- A measure `μ` on a manifold `M` modelled on a real normed space `E` **has a smooth positive
density** when in every chart `e` of the maximal smooth atlas it is `ρ(y) dy` for a function `ρ`
smooth and positive on the chart target: the integral against `μ` of every continuous
complex-valued function `f` with compact support in the chart source is
`∫_{e.target} ρ(y) f(e⁻¹ y) dy`, where `dy` is the measure `volume` of the `MeasureSpace E` instance
(Lebesgue measure for `CoordinateSpace n`). -/
def HasSmoothPositiveDensity (μ : Measure M) : Prop :=
  ∀ e : OpenPartialHomeomorph M E, e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M →
    ∃ ρ : E → ℝ, ContDiffOn ℝ ∞ ρ e.target ∧ (∀ y ∈ e.target, 0 < ρ y) ∧
      ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
        ∫ x, f x ∂μ = ∫ y in e.target, (ρ y : ℂ) * f (e.symm y)

/-- Unfolding `TauCeti.HasSmoothPositiveDensity`: in every chart of the maximal atlas, integration
against `μ` is integration in coordinates against a smooth positive density. -/
theorem hasSmoothPositiveDensity_iff {μ : Measure M} :
    HasSmoothPositiveDensity E μ ↔
      ∀ e : OpenPartialHomeomorph M E, e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M →
        ∃ ρ : E → ℝ, ContDiffOn ℝ ∞ ρ e.target ∧ (∀ y ∈ e.target, 0 < ρ y) ∧
          ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
            ∫ x, f x ∂μ = ∫ y in e.target, (ρ y : ℂ) * f (e.symm y) :=
  Iff.rfl

/-- The chart formula of `TauCeti.HasSmoothPositiveDensity` for real-valued functions: in every
chart `e` of the maximal atlas there is a smooth positive density `ρ` with
`∫ f dμ = ∫_{e.target} ρ(y) f(e⁻¹ y) dy` for every continuous real function `f` with compact
support in the chart source. -/
theorem HasSmoothPositiveDensity.exists_integral_real_eq {μ : Measure M}
    (hμ : HasSmoothPositiveDensity E μ) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    ∃ ρ : E → ℝ, ContDiffOn ℝ ∞ ρ e.target ∧ (∀ y ∈ e.target, 0 < ρ y) ∧
      ∀ f : M → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
        ∫ x, f x ∂μ = ∫ y in e.target, ρ y * f (e.symm y) := by
  obtain ⟨ρ, hρ, hρpos, hint⟩ := hasSmoothPositiveDensity_iff.1 hμ e he
  refine ⟨ρ, hρ, hρpos, fun f hf hfc hfs ↦ ?_⟩
  have h := hint (fun x ↦ (f x : ℂ)) (by fun_prop) (hfc.comp_left Complex.ofReal_zero)
    ((tsupport_comp_subset Complex.ofReal_zero f).trans hfs)
  exact_mod_cast h

/-- **Lebesgue measure has a smooth positive density.** In a chart `e` of the maximal atlas of a
finite-dimensional real normed space `E`, the density of `volume` (assumed to be an additive Haar
measure) is the absolute Jacobian determinant `|det D(e⁻¹)(y)|`, by the change of variables
formula. -/
theorem hasSmoothPositiveDensity_volume [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] :
    HasSmoothPositiveDensity E (volume : Measure E) := by
  refine hasSmoothPositiveDensity_iff.2 fun e he ↦ ?_
  have hs : ContDiffOn ℝ ∞ e e.source :=
    contMDiffOn_iff_contDiffOn.1 (contMDiffOn_of_mem_maximalAtlas he)
  have hs' : ContDiffOn ℝ ∞ e.symm e.target :=
    contMDiffOn_iff_contDiffOn.1 (contMDiffOn_symm_of_mem_maximalAtlas he)
  refine ⟨fun y ↦ |(fderiv ℝ e.symm y).det|,
    e.symm.contDiffOn_abs_det_fderiv_of_contDiffOn (by simp) hs' hs,
    fun y hy ↦ abs_pos.2 (e.symm.det_fderiv_ne_zero_of_contDiffOn hs' hs (by simp) hy),
    fun f _ _ hfs ↦ ?_⟩
  have hd : ∀ y ∈ e.symm.source, HasFDerivAt e.symm (fderiv ℝ e.symm y) y :=
    fun y hy ↦ ((hs'.differentiableOn (by simp)).differentiableAt
      (e.open_target.mem_nhds hy)).hasFDerivAt
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := e.source)
      fun x hx ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hx (hfs h),
    ← e.symm_target, integral_target_eq_integral_abs_det_fderiv_smul volume hd]
  simp [Complex.real_smul]

/-! ### Densities read in a chart -/

section Chart

variable [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [OpensMeasurableSpace M]
  {μ : Measure M} [IsFiniteMeasureOnCompacts μ]

omit [ChartedSpace E M] in
/-- **A density determines the measure in a chart.** Let `μ` be finite on compact sets, and let
integration against `μ` of every continuous complex-valued function `f` with compact support in the
source of the chart `e` be `∫_{e.target} ρ(y) f(e⁻¹ y) dy`, for a function `ρ` continuous and
nonnegative on the chart target. Then `μ` reads in the chart as the measure `ρ(y) dy` on the chart
target: `(μ|_{e.source}).map e = ρ(y) dy|_{e.target}`. -/
theorem map_restrict_source_eq_withDensity_of_forall_integral_eq
    [IsFiniteMeasureOnCompacts (volume : Measure E)] {e : OpenPartialHomeomorph M E} {ρ : E → ℝ}
    (hρ : ContinuousOn ρ e.target) (hρ0 : ∀ y ∈ e.target, 0 ≤ ρ y)
    (hint : ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
      ∫ x, f x ∂μ = ∫ y in e.target, (ρ y : ℂ) * f (e.symm y)) :
    (μ.restrict e.source).map e =
      (volume.restrict e.target).withDensity fun y ↦ ENNReal.ofReal (ρ y) := by
  have hs : MeasurableSet e.target := e.open_target.measurableSet
  have hsrc : MeasurableSet e.source := e.open_source.measurableSet
  have he : AEMeasurable e (μ.restrict e.source) := e.continuousOn.aemeasurable hsrc
  -- Both measures vanish off the chart target and are finite on its compact subsets.
  refine Measure.ext_of_integral_eq_on_compactlySupported_of_isOpen e.open_target ?_ ?_
    (fun K hK hKs ↦ ?_) (fun K hK hKs ↦ ?_) fun g hg ↦ ?_
  · rw [Measure.map_apply_of_aemeasurable he hs.compl, Measure.restrict_apply' hsrc]
    exact measure_mono_null (fun x hx ↦ hx.1 (e.map_source hx.2)) measure_empty
  · rw [withDensity_apply _ hs.compl, Measure.restrict_restrict hs.compl, compl_inter_self,
      Measure.restrict_empty, lintegral_zero_measure]
  · rw [Measure.map_apply_of_aemeasurable he hK.isClosed.measurableSet,
      Measure.restrict_apply' hsrc]
    refine (measure_mono fun x (hx : x ∈ e ⁻¹' K ∩ e.source) ↦
      (⟨e x, hx.1, e.left_inv hx.2⟩ : x ∈ e.symm '' K)).trans_lt
      (hK.image_of_continuousOn (e.continuousOn_symm.mono hKs)).measure_lt_top
  · rw [withDensity_apply _ hK.isClosed.measurableSet,
      Measure.restrict_restrict hK.isClosed.measurableSet, inter_eq_left.2 hKs]
    exact ((hρ.mono hKs).integrableOn_compact hK).lintegral_lt_top
  -- Test against `g`: read `g` on `M` through the chart, as the function `F` extended by zero.
  set F : M → ℂ := e.source.indicator fun x ↦ (g (e x) : ℂ)
  have hKsrc : e.symm '' tsupport g ⊆ e.source :=
    (image_mono hg).trans e.symm_image_target_eq_source.le
  have hFK : tsupport F ⊆ e.symm '' tsupport g := by
    refine closure_minimal (fun x hx ↦ ?_)
      (g.hasCompactSupport.isCompact.image_of_continuousOn (e.continuousOn_symm.mono hg)).isClosed
    have hxs : x ∈ e.source := by
      by_contra h
      simp [F, h] at hx
    exact ⟨e x, subset_tsupport _ (by simpa [F, hxs] using hx), e.left_inv hxs⟩
  have hF : Continuous F :=
    ((continuousOn_congr fun x hx ↦ by simp [F, hx]).2 (Complex.continuous_ofReal.comp_continuousOn
      (g.continuous.comp_continuousOn e.continuousOn))).continuous_of_tsupport_subset
      e.open_source (hFK.trans hKsrc)
  have key := hint F hF ((g.hasCompactSupport.isCompact.image_of_continuousOn
    (e.continuousOn_symm.mono hg)).of_isClosed_subset (isClosed_tsupport F) hFK) (hFK.trans hKsrc)
  -- Both sides of `key` are the integrals of `g` against the two measures.
  have hL : ∫ x, F x ∂μ = ((∫ y, g y ∂(μ.restrict e.source).map e : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, integral_map (f := fun y ↦ (g y : ℂ)) he
      (Complex.continuous_ofReal.comp g.continuous).aestronglyMeasurable,
      integral_indicator hsrc]
  have hR : ∫ y in e.target, (ρ y : ℂ) * F (e.symm y) = ((∫ y, g y ∂(volume.restrict
      e.target).withDensity fun y ↦ ENNReal.ofReal (ρ y) : ℝ) : ℂ) := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ (hρ.aemeasurable hs).ennreal_ofReal
        (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top),
      ← integral_complex_ofReal]
    refine setIntegral_congr_fun hs fun y hy ↦ ?_
    simp [F, e.map_target hy, e.right_inv hy, ENNReal.toReal_ofReal (hρ0 y hy)]
  exact_mod_cast hL.symm.trans (key.trans hR)

/-- **A smooth positive density in every chart.** A measure with a smooth positive density
(`TauCeti.HasSmoothPositiveDensity`) that is finite on compact sets reads in every chart `e` of the
maximal atlas as `ρ(y) dy` on the chart target, for a function `ρ` smooth and positive there. -/
theorem HasSmoothPositiveDensity.exists_map_restrict_source_eq_withDensity
    [IsFiniteMeasureOnCompacts (volume : Measure E)]
    (hμ : HasSmoothPositiveDensity E μ) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    ∃ ρ : E → ℝ, ContDiffOn ℝ ∞ ρ e.target ∧ (∀ y ∈ e.target, 0 < ρ y) ∧
      (μ.restrict e.source).map e =
        (volume.restrict e.target).withDensity fun y ↦ ENNReal.ofReal (ρ y) := by
  obtain ⟨ρ, hρ, hρ0, hint⟩ := hμ e he
  exact ⟨ρ, hρ, hρ0, map_restrict_source_eq_withDensity_of_forall_integral_eq hρ.continuousOn
    (fun y hy ↦ (hρ0 y hy).le) hint⟩

/-- **Lebesgue measure and a smooth positive density bound each other on compacts.** Let `μ` have a
smooth positive density and be finite on compact sets. On a compact subset `K` of the target of a
chart `e` of the maximal atlas, the measure `volume` and the reading `ρ(y) dy` of `μ` in the chart
dominate each other up to finite constants, because the density `ρ` is continuous and positive on
`K`. -/
theorem HasSmoothPositiveDensity.exists_measure_le_smul
    [IsFiniteMeasureOnCompacts (volume : Measure E)]
    (hμ : HasSmoothPositiveDensity E μ) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ e.target) :
    ∃ c D : ℝ≥0∞, c ≠ ⊤ ∧ D ≠ ⊤ ∧
      volume.restrict K ≤ c • (μ.restrict e.source).map e ∧
      ((μ.restrict e.source).map e).restrict K ≤ D • volume := by
  obtain ⟨ρ, hρ, hρ0, hmap⟩ := hμ.exists_map_restrict_source_eq_withDensity he
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hρK : ContinuousOn ρ K := hρ.continuousOn.mono hKt
  -- `ρ` lies between two positive constants on the compact set `K`.
  obtain ⟨c, hc0, hc⟩ : ∃ c > 0, ∀ y ∈ K, c ≤ ρ y := by
    rcases K.eq_empty_or_nonempty with hK' | hK'
    · exact ⟨1, one_pos, by simp [hK']⟩
    obtain ⟨y₀, hy₀, hmin⟩ := hK.exists_isMinOn hK' hρK
    exact ⟨ρ y₀, hρ0 y₀ (hKt hy₀), fun y hy ↦ hmin hy⟩
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hρK
  have hres : ((volume.restrict e.target).withDensity fun y ↦ ENNReal.ofReal (ρ y)).restrict K =
      (volume.restrict K).withDensity fun y ↦ ENNReal.ofReal (ρ y) := by
    rw [restrict_withDensity hKm, Measure.restrict_restrict hKm, inter_eq_left.2 hKt]
  refine ⟨(ENNReal.ofReal c)⁻¹, ENNReal.ofReal D, by simpa using hc0, ENNReal.ofReal_ne_top,
    ?_, ?_⟩ <;> rw [hmap]
  · have hc' : ENNReal.ofReal c ≠ 0 := by simpa using hc0
    calc volume.restrict K
        = (ENNReal.ofReal c)⁻¹ • (ENNReal.ofReal c • volume.restrict K) := by
          rw [smul_smul, ENNReal.inv_mul_cancel hc' ENNReal.ofReal_ne_top, one_smul]
      _ ≤ (ENNReal.ofReal c)⁻¹ •
            ((volume.restrict K).withDensity fun y ↦ ENNReal.ofReal (ρ y)) := by
          gcongr
          rw [← withDensity_const]
          exact withDensity_mono (ae_restrict_of_forall_mem hKm fun y hy ↦
            ENNReal.ofReal_le_ofReal (hc y hy))
      _ ≤ _ := by
          rw [← hres]
          gcongr
          exact Measure.restrict_le_self
  · rw [hres]
    calc (volume.restrict K).withDensity (fun y ↦ ENNReal.ofReal (ρ y))
        ≤ (volume.restrict K).withDensity fun _ ↦ ENNReal.ofReal D :=
          withDensity_mono (ae_restrict_of_forall_mem hKm fun y hy ↦
            ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hD y hy)))
      _ = ENNReal.ofReal D • volume.restrict K := withDensity_const _
      _ ≤ ENNReal.ofReal D • volume := by
          gcongr
          exact Measure.restrict_le_self

/-- A measure with a smooth positive density (`TauCeti.HasSmoothPositiveDensity`) that is finite on
compact sets is a positive continuous density measure (`TauCeti.IsPositiveDensityMeasure`); in
particular it is positive on nonempty open sets
(`TauCeti.IsPositiveDensityMeasure.isOpenPosMeasure`). -/
theorem HasSmoothPositiveDensity.isPositiveDensityMeasure
    [IsManifold 𝓘(ℝ, E) ∞ M] [(volume : Measure E).IsAddHaarMeasure]
    (hμ : HasSmoothPositiveDensity E μ) : IsPositiveDensityMeasure 𝓘(ℝ, E) μ := by
  refine (isPositiveDensityMeasure_iff_of_isAddHaarMeasure volume).2 fun x ↦ ?_
  obtain ⟨ρ, hρ, hρ0, h⟩ :=
    hμ.exists_map_restrict_source_eq_withDensity (IsManifold.chart_mem_maximalAtlas x)
  exact ⟨ρ, by simpa using hρ.continuousOn, by simpa using hρ0, by simpa using h⟩

end Chart

end TauCeti

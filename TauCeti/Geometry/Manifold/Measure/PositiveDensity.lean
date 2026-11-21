/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Measure.AE
public import TauCeti.Geometry.Manifold.Measure.Chart
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Positive continuous density measures on a manifold

A measure `μ` on a manifold `M` is a *positive continuous density measure* when, read in every
preferred chart, it is Haar measure on the model weighted by a strictly positive continuous
function: the pushforward of `μ` restricted to the source of `extChartAt I x` is
`w_x(y) dν(y)` on the chart target, with `w_x` continuous and positive there. Riemannian volume
measures of continuous metrics are examples (`TauCeti.isPositiveDensityMeasure_riemannianVolume`),
and so is any such measure reweighted by a strictly positive continuous function on `M`. No metric
and no orientation enters the definition.

These measures are the integration measures of first-order analysis on manifolds without a
preferred metric. They are interchangeable for every local question: they are locally finite and
positive on nonempty open sets. On a Lindelöf manifold their null sets are exactly the chartwise
null sets `TauCeti.IsNullSet`, so their almost-everywhere filters all agree with
`TauCeti.Manifold.ae I M`. On a second countable manifold any two of them differ by a strictly
positive continuous weight.

The general facts about chart pushforwards used here are in
`TauCeti.Geometry.Manifold.Measure.Chart`.

Like `TauCeti.IsNullSet`, the definition asks for a density with respect to every additive Haar
measure on the model. One Haar measure suffices
(`TauCeti.isPositiveDensityMeasure_iff_of_isAddHaarMeasure`), since two of them differ by a
positive constant factor.

## Main definitions

* `TauCeti.IsPositiveDensityMeasure I μ`: in every preferred chart, `μ` has a strictly positive
  continuous density with respect to every additive Haar measure on the model.

## Main results

* `TauCeti.isPositiveDensityMeasure_iff_of_isAddHaarMeasure`: one additive Haar measure on the
  model suffices to test the definition.
* `TauCeti.IsPositiveDensityMeasure.measure_eq_zero_iff_image_of_subset`: a subset of a chart
  source is `μ`-null exactly when its image in the chart is Haar-null.
* `TauCeti.IsPositiveDensityMeasure.isNullSet_iff_measure_eq_zero`,
  `TauCeti.IsPositiveDensityMeasure.ae_eq`: on a Lindelöf manifold, the `μ`-null sets are the
  chartwise null sets, so `ae μ = TauCeti.Manifold.ae I M`.
* `TauCeti.IsPositiveDensityMeasure.isLocallyFiniteMeasure`,
  `TauCeti.IsPositiveDensityMeasure.isOpenPosMeasure`: such a measure is locally finite and
  positive on nonempty open sets.
* `TauCeti.IsPositiveDensityMeasure.withDensity`: reweighting by a strictly positive continuous
  function on `M` gives another positive continuous density measure.
* `TauCeti.IsPositiveDensityMeasure.exists_eq_withDensity`: conversely, on a second countable
  manifold any two positive continuous density measures differ by a strictly positive continuous
  weight, `μ' = ρ μ`.

## References

* A. Convent, J. Van Schaftingen, *Intrinsic colocal weak derivatives and Sobolev spaces between
  manifolds*, Ann. Sc. Norm. Super. Pisa Cl. Sci. (5) 16 (2016), §1.1 (positive absolutely
  continuous Radon measures on a manifold, whose null sets are the chartwise null sets).
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [MeasurableSpace M] {μ : Measure M}

variable (I) in
/-- A measure on a manifold is a *positive continuous density measure* when in every preferred
chart it reads as every additive Haar measure `ν` on the model weighted by a strictly positive
continuous function: the pushforward by `extChartAt I x` of `μ` restricted to the chart source is
`ν` restricted to the chart target, with a density `y ↦ w y` that is continuous and positive on
the target. -/
def IsPositiveDensityMeasure (μ : Measure M) : Prop :=
  ∀ x : M, ∀ (ν : Measure E) [ν.IsAddHaarMeasure], ∃ w : E → ℝ,
    ContinuousOn w (extChartAt I x).target ∧ (∀ y ∈ (extChartAt I x).target, 0 < w y) ∧
    (μ.restrict (extChartAt I x).source).map (extChartAt I x) =
      (ν.restrict (extChartAt I x).target).withDensity fun y ↦ ENNReal.ofReal (w y)

/-- **Haar independence.** A measure on a manifold with a finite-dimensional model is a positive
continuous density measure as soon as it has strictly positive continuous chart densities with
respect to one additive Haar measure on the model. -/
theorem isPositiveDensityMeasure_iff_of_isAddHaarMeasure [BorelSpace E] [FiniteDimensional ℝ E]
    (ν : Measure E) [ν.IsAddHaarMeasure] :
    IsPositiveDensityMeasure I μ ↔ ∀ x : M, ∃ w : E → ℝ,
      ContinuousOn w (extChartAt I x).target ∧ (∀ y ∈ (extChartAt I x).target, 0 < w y) ∧
      (μ.restrict (extChartAt I x).source).map (extChartAt I x) =
        (ν.restrict (extChartAt I x).target).withDensity fun y ↦ ENNReal.ofReal (w y) := by
  refine ⟨fun hμ x ↦ hμ x ν, fun h x ν' _ ↦ ?_⟩
  obtain ⟨w, hwc, hwpos, hw⟩ := h x
  -- `ν = c • ν'` for a positive constant `c`, which is absorbed into the density.
  set c : ℝ≥0 := Measure.addHaarScalarFactor ν ν'
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν ν'
  refine ⟨fun y ↦ c * w y, continuousOn_const.mul hwc,
    fun y hy ↦ mul_pos (NNReal.coe_pos.2 hc) (hwpos y hy), ?_⟩
  rw [hw, Measure.isAddLeftInvariant_eq_smul ν ν', Measure.restrict_smul,
    ENNReal.smul_def, withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.coe_ne_top]
  congr 1
  ext y
  simp [c, ENNReal.ofReal_mul (NNReal.coe_nonneg c)]

variable [BorelSpace M] [BorelSpace E]

/-! ### Charts and null sets -/

/-- A subset of the source of a preferred chart is null for a positive continuous density measure
exactly when its image in the chart is null for an additive Haar measure. The set need not be
measurable. -/
theorem IsPositiveDensityMeasure.measure_eq_zero_iff_image_of_subset
    (hμ : IsPositiveDensityMeasure I μ) {x : M} {s : Set M} (hsub : s ⊆ (extChartAt I x).source)
    (ν : Measure E) [ν.IsAddHaarMeasure] : μ s = 0 ↔ ν ((extChartAt I x) '' s) = 0 := by
  let e := extChartAt I x
  have hsrc : MeasurableSet e.source := (isOpen_extChartAt_source x).measurableSet
  obtain ⟨w, hwc, hwpos, hw⟩ := hμ x ν
  have htgt : MeasurableSet e.target := measurableSet_extChartAt_target x
  -- The density is positive on the target, so the chart measure has the null sets of `ν` there.
  have hzero : ∀ A ⊆ e.target, (μ.restrict e.source).map e A = 0 ↔ ν A = 0 := fun A hA ↦ by
    rw [hw, withDensity_apply_eq_zero' (f := fun y ↦ ENNReal.ofReal (w y))
      ((ENNReal.continuous_ofReal.comp_continuousOn hwc).aemeasurable htgt),
      Measure.restrict_apply' htgt]
    congr! 2
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h ↦ h.1.2, fun hy ↦ ⟨⟨(ENNReal.ofReal_pos.2 (hwpos y (hA hy))).ne', hy⟩, hA hy⟩⟩
  have himage : e '' s ⊆ e.target := e.image_source_eq_target ▸ image_mono hsub
  rw [← hzero _ himage]
  constructor
  · intro hs
    -- Enlarge `s` to a measurable null subset of the chart source.
    let t := toMeasurable μ s ∩ e.source
    have ht : MeasurableSet t := (measurableSet_toMeasurable μ s).inter hsrc
    have hst : s ⊆ t := fun y hy ↦ ⟨subset_toMeasurable μ s hy, hsub hy⟩
    refine measure_mono_null (image_mono hst) ?_
    rw [map_restrict_extChartAt_source_apply_image ht inter_subset_right]
    exact measure_mono_null inter_subset_left (by rwa [measure_toMeasurable])
  · intro hs
    have hle := Measure.le_map_apply ((continuousOn_extChartAt x).aemeasurable hsrc (μ := μ))
      (e '' s)
    rw [hs, nonpos_iff_eq_zero, Measure.restrict_apply' hsrc] at hle
    have hs' : s ⊆ e ⁻¹' (e '' s) ∩ e.source := fun y hy ↦ ⟨mem_image_of_mem e hy, hsub hy⟩
    exact measure_mono_null hs' hle

/-- Every point has measure zero for a positive continuous density measure on a manifold of
positive dimension. -/
theorem IsPositiveDensityMeasure.nullSingletonClass [FiniteDimensional ℝ E]
    [Nontrivial E] (hμ : IsPositiveDensityMeasure I μ) : NullSingletonClass μ := by
  refine ⟨fun x ↦ ?_⟩
  rw [hμ.measure_eq_zero_iff_image_of_subset (singleton_subset_iff.2 (mem_extChartAt_source x))
    (Measure.addHaar : Measure E), image_singleton]
  exact measure_singleton _

/-- On a Lindelöf manifold, the null sets of a positive continuous density measure are the
chartwise null sets. -/
theorem IsPositiveDensityMeasure.isNullSet_iff_measure_eq_zero [FiniteDimensional ℝ E]
    [LindelofSpace M]
    (hμ : IsPositiveDensityMeasure I μ) {s : Set M} : IsNullSet I s ↔ μ s = 0 := by
  constructor
  · intro hs
    obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover
      (fun x : M ↦ (extChartAt I x).source) fun x ↦ extChartAt_source_mem_nhds x
    have hsub : s ⊆ ⋃ x ∈ t, s ∩ (extChartAt I x).source := fun y hy ↦ by
      obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hcover ▸ mem_univ y)
      exact mem_iUnion₂.mpr ⟨x, hx, hy, hyx⟩
    refine measure_mono_null hsub ((measure_biUnion_null_iff ht).mpr fun x _ ↦ ?_)
    exact (hμ.measure_eq_zero_iff_image_of_subset inter_subset_right Measure.addHaar).mpr
      (hs.chartwise x _)
  · intro hs
    rw [isNullSet_iff]
    intro x ν _
    exact (hμ.measure_eq_zero_iff_image_of_subset inter_subset_right ν).mp
      (measure_mono_null inter_subset_left hs)

/-- **Almost everywhere does not depend on the density.** On a Lindelöf manifold, the
almost-everywhere filter of a positive continuous density measure is the filter of complements of
chartwise null sets. -/
theorem IsPositiveDensityMeasure.ae_eq [FiniteDimensional ℝ E] [LindelofSpace M]
    (hμ : IsPositiveDensityMeasure I μ) :
    ae μ = Manifold.ae I M :=
  Manifold.ae_eq_iff_forall_measure_eq_zero_iff.2 fun _ ↦ hμ.isNullSet_iff_measure_eq_zero.symm

/-! ### Local finiteness and full support -/

/-- A positive continuous density measure is positive on nonempty open sets. -/
theorem IsPositiveDensityMeasure.isOpenPosMeasure [FiniteDimensional ℝ E]
    (hμ : IsPositiveDensityMeasure I μ) : μ.IsOpenPosMeasure where
  open_pos U hU hne := by
    obtain ⟨x, hx⟩ := hne
    refine (measure_mono_null (inter_subset_left : U ∩ (extChartAt I x).source ⊆ U)).mt ?_
    rw [hμ.measure_eq_zero_iff_image_of_subset inter_subset_right Measure.addHaar]
    exact (measure_image_extChartAt_inter_source_pos hU hx _).ne'

/-- A positive continuous density measure is locally finite: near a point, its chart density is
bounded, so a small neighbourhood has finite measure. -/
theorem IsPositiveDensityMeasure.isLocallyFiniteMeasure [FiniteDimensional ℝ E]
    (hμ : IsPositiveDensityMeasure I μ) : IsLocallyFiniteMeasure μ := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨w, hwc, -, hw⟩ := hμ x Measure.addHaar
  obtain ⟨U, hUo, hxU, hUsub, hU⟩ :=
    exists_isOpen_setLIntegral_image_extChartAt_lt_top hwc (Measure.addHaar : Measure E)
  have hUm : MeasurableSet (extChartAt I x '' U) := hUo.measurableSet.image_extChartAt x hUsub
  refine ⟨U, hUo.mem_nhds hxU, ?_⟩
  rwa [← map_restrict_extChartAt_source_apply_image hUo.measurableSet hUsub, hw,
    withDensity_apply _ hUm, Measure.restrict_restrict hUm,
    inter_eq_left.2 ((image_mono hUsub).trans (extChartAt I x).image_source_eq_target.subset)]

/-! ### Comparison of density measures -/

/-- **Reweighting.** A positive continuous density measure multiplied by a strictly positive
continuous function on the manifold is again a positive continuous density measure: in a chart,
its density is the old density times the function read in the chart. -/
theorem IsPositiveDensityMeasure.withDensity (hμ : IsPositiveDensityMeasure I μ) {ρ : M → ℝ}
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    IsPositiveDensityMeasure I (μ.withDensity fun x ↦ ENNReal.ofReal (ρ x)) := by
  intro x ν _
  let e := extChartAt I x
  have hsrc : MeasurableSet e.source := (isOpen_extChartAt_source x).measurableSet
  obtain ⟨w, hwc, hwpos, hw⟩ := hμ x ν
  have hρc : ContinuousOn (fun y ↦ ρ (e.symm y)) e.target :=
    hρ.comp_continuousOn (continuousOn_extChartAt_symm x)
  refine ⟨fun y ↦ ρ (e.symm y) * w y, hρc.mul hwc, fun y hy ↦ mul_pos (hρpos _) (hwpos y hy), ?_⟩
  have hcomp : (fun z ↦ ENNReal.ofReal (ρ z)) =ᵐ[μ.restrict e.source]
      fun z ↦ ENNReal.ofReal (ρ (e.symm (e z))) := by
    filter_upwards [ae_restrict_mem hsrc] with z hz
    rw [e.left_inv hz]
  rw [restrict_withDensity hsrc, withDensity_congr_ae hcomp]
  exact map_withDensity_restrict_extChartAt_source hwc hρc (fun y _ ↦ (hρpos _).le) hw

/-- In each chart source, a positive continuous density measure has a strictly positive continuous
density with respect to any other. -/
private theorem IsPositiveDensityMeasure.exists_restrict_extChartAt_source_eq_withDensity
    [FiniteDimensional ℝ E] {μ' : Measure M} (hμ : IsPositiveDensityMeasure I μ)
    (hμ' : IsPositiveDensityMeasure I μ') (x : M) :
    ∃ r : M → ℝ, ContinuousOn r (extChartAt I x).source ∧
      (∀ z ∈ (extChartAt I x).source, 0 < r z) ∧
      μ'.restrict (extChartAt I x).source =
        (μ.restrict (extChartAt I x).source).withDensity fun z ↦ ENNReal.ofReal (r z) := by
  let e := extChartAt I x
  obtain ⟨w, hwc, hwpos, hw⟩ := hμ x Measure.addHaar
  obtain ⟨w', hwc', hwpos', hw'⟩ := hμ' x Measure.addHaar
  have hq : ContinuousOn (fun y ↦ w' y / w y) e.target :=
    hwc'.div hwc fun y hy ↦ (hwpos y hy).ne'
  have hsrc : MeasurableSet e.source := (isOpen_extChartAt_source x).measurableSet
  refine ⟨fun z ↦ w' (e z) / w (e z), hq.comp (continuousOn_extChartAt x) fun z hz ↦
    e.map_source hz, fun z hz ↦ div_pos (hwpos' _ (e.map_source hz)) (hwpos _ (e.map_source hz)),
    ?_⟩
  rw [← restrict_withDensity hsrc]
  refine restrict_extChartAt_source_eq_of_map_eq ?_
  rw [restrict_withDensity hsrc, hw', map_withDensity_restrict_extChartAt_source hwc hq
    (fun y hy ↦ (div_pos (hwpos' y hy) (hwpos y hy)).le) hw]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_extChartAt_target x)] with y hy
  rw [div_mul_cancel₀ _ (hwpos y hy).ne']

/-- **Comparison of density measures.** On a second countable manifold, any two positive
continuous density measures differ by a strictly positive continuous weight: `μ' = ρ μ`. -/
theorem IsPositiveDensityMeasure.exists_eq_withDensity [FiniteDimensional ℝ E]
    [SecondCountableTopology M] {μ' : Measure M} (hμ : IsPositiveDensityMeasure I μ)
    (hμ' : IsPositiveDensityMeasure I μ') :
    ∃ ρ : M → ℝ, Continuous ρ ∧ (∀ x, 0 < ρ x) ∧
      μ' = μ.withDensity fun x ↦ ENNReal.ofReal (ρ x) := by
  have := hμ.isLocallyFiniteMeasure
  have := hμ.isOpenPosMeasure
  choose r hrc hrpos hr using hμ.exists_restrict_extChartAt_source_eq_withDensity hμ'
  -- On the overlap of two chart sources the two local densities agree, being continuous densities
  -- of `μ'` with respect to `μ` there.
  have hagree : ∀ x z, EqOn (r x) (r z) ((extChartAt I x).source ∩ (extChartAt I z).source) := by
    intro x z
    let O := (extChartAt I x).source ∩ (extChartAt I z).source
    have hO : IsOpen O := (isOpen_extChartAt_source x).inter (isOpen_extChartAt_source z)
    have hc : ∀ y, O ⊆ (extChartAt I y).source →
        ContinuousOn (fun t ↦ ENNReal.ofReal (r y t)) O := fun y hy ↦
      (ENNReal.continuous_ofReal.comp_continuousOn (hrc y)).mono hy
    have hO' : ∀ y, O ⊆ (extChartAt I y).source →
        μ'.restrict O = (μ.restrict O).withDensity fun t ↦ ENNReal.ofReal (r y t) := by
      intro y hy
      rw [← Measure.restrict_restrict_of_subset hy, hr y, restrict_withDensity hO.measurableSet,
        Measure.restrict_restrict_of_subset hy]
    have hae := (withDensity_eq_iff_of_sigmaFinite
      ((hc x inter_subset_left).aemeasurable hO.measurableSet)
      ((hc z inter_subset_right).aemeasurable hO.measurableSet)).1
      ((hO' x inter_subset_left).symm.trans (hO' z inter_subset_right))
    intro t ht
    exact (ENNReal.ofReal_eq_ofReal_iff (hrpos x t ht.1).le (hrpos z t ht.2).le).1
      (Measure.eqOn_open_of_ae_eq hae hO (hc x inter_subset_left) (hc z inter_subset_right) ht)
  have hρ : ∀ x, EqOn (fun t ↦ r t t) (r x) (extChartAt I x).source := fun x t ht ↦
    hagree t x ⟨mem_extChartAt_source t, ht⟩
  refine ⟨fun t ↦ r t t, continuous_iff_continuousAt.2 fun x ↦
    ((hrc x).congr (hρ x)).continuousAt (extChartAt_source_mem_nhds x),
    fun x ↦ hrpos x x (mem_extChartAt_source x), ?_⟩
  -- Compare the two measures on a countable cover by chart sources.
  obtain ⟨t, htc, hcover⟩ := TopologicalSpace.countable_cover_nhds fun x : M ↦
    extChartAt_source_mem_nhds (I := I) x
  have := htc.to_subtype
  refine Measure.ext_of_iUnion_eq_univ (s := fun x : t ↦ (extChartAt I (x : M)).source)
    (by rwa [biUnion_eq_iUnion] at hcover) fun x ↦ ?_
  have hsrc : MeasurableSet (extChartAt I (x : M)).source :=
    (isOpen_extChartAt_source (x : M)).measurableSet
  rw [hr, restrict_withDensity hsrc]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem hsrc] with z hz
  rw [← hρ x hz]

end TauCeti

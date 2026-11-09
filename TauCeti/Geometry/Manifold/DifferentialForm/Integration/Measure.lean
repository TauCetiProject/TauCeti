/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables
public import TauCeti.MeasureTheory.Measure.Glue
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The measure of a top form

A top-degree form `φ` on a `k`-dimensional manifold `M` determines a measure `|φ|` on `M`
(`TauCeti.RoughForm.measure`): on the source of each preferred chart it is coordinate Lebesgue
measure weighted by the absolute value of the coefficient `φ(∂₁, …, ∂ₖ)` of `φ` in that chart.
The coordinate measure is the Haar measure of the model space normalized by the same basis, which
gives the cube spanned by `∂₁, …, ∂ₖ` measure `1`, and `|φ|` of a subset of the chart source is the
integral of `|φ(∂₁, …, ∂ₖ)|` over its coordinate image. This is the manifold version of
Mathlib's `AlternatingMap.measure`, and it follows the same convention: the dimension is supplied
by a `Fact (finrank ℝ E = k)` instance, and the basis is `Module.finBasisOfFinrankEq`.

Under a change of chart the coefficient is multiplied by the Jacobian determinant of the
transition map, so its absolute value transforms exactly as Lebesgue measure does. Hence the local
measures agree on chart overlaps and, on a Lindelöf manifold, glue to a unique measure on the
Borel `σ`-algebra. No orientation is used, the form may vanish, and manifolds with boundary or
corners are allowed. The same computation shows that a differentiable homeomorphism `Φ : M → N`
carries `|Φ^* ψ|` to `|ψ|` (`Homeomorph.measurePreserving_measure_mpullback`); in particular a
diffeomorphism preserving `ψ` preserves `|ψ|`.

For a continuous form the measure is locally finite, and if moreover the form vanishes nowhere,
every nonempty open set has positive measure. Applied to the symplectic volume form `ωⁿ / n!`,
this construction gives the Liouville measure of a symplectic manifold.

## Main definitions

* `TauCeti.RoughForm.measure φ`: the measure `|φ|` of a top form.

## Main results

* `TauCeti.RoughForm.measure_apply_of_subset`: the measure of a subset of a chart source, in
  coordinates.
* `TauCeti.RoughForm.eq_measure_iff`: these values characterize `|φ|`.
* `TauCeti.RoughForm.measure_smul`, `TauCeti.RoughForm.measure_neg`,
  `TauCeti.RoughForm.measure_zero`: `|c • φ| = |c| • |φ|`.
* `TauCeti.RoughForm.isLocallyFiniteMeasure_measure`: the measure of a continuous form is locally
  finite.
* `TauCeti.RoughForm.isOpenPosMeasure_measure`: the measure of a continuous nowhere-vanishing form
  is positive on nonempty open sets.
* `Homeomorph.measurePreserving_measure_mpullback`: a differentiable homeomorphism `Φ` carries
  `|Φ^* ψ|` to `|ψ|`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 16
  (densities and their integrals).
-/

public section

noncomputable section

open Module MeasureTheory Set
open scoped ENNReal Manifold Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M] {k : ℕ} [hk : Fact (finrank ℝ E = k)]

attribute [local instance] TauCeti.extChartAtMeasurableSpaceE TauCeti.extChartAtBorelSpaceE

omit [FiniteDimensional ℝ E] in
/-- Transporting a basis along the identity equivalence does not change it. -/
private theorem map_basis_refl {ι : Type*} (b : Module.Basis ι ℝ E) :
    b.map (ContinuousLinearEquiv.refl ℝ E).toLinearEquiv = b :=
  Module.Basis.eq_of_apply_eq fun _ ↦ rfl

omit [FiniteDimensional ℝ E] in
/-- The image of a measure under the identity equivalence is the measure itself. -/
private theorem map_measure_refl [MeasurableSpace E] (μ : Measure E) :
    μ.map (ContinuousLinearEquiv.refl ℝ E) = μ := by
  rw [ContinuousLinearEquiv.coe_refl', Measure.map_id]

namespace TauCeti

namespace RoughForm

/-! ### The measure in one chart -/

/-- The measure supplied by the preferred chart at `α`: coordinate Lebesgue measure weighted by
the absolute coefficient of `φ`, carried to the chart source. -/
private def chartMeasure (φ : RoughForm I M ℝ k) (α : M) : Measure M :=
  (((finBasisOfFinrankEq ℝ E hk.out).addHaar.withDensity fun y ↦
      ENNReal.ofReal |φ.inChartAt α y (finBasisOfFinrankEq ℝ E hk.out)|).comap
    ((extChartAt I α).source.domRestrict (extChartAt I α))).map Subtype.val

omit [IsManifold I 1 M] in
private theorem chartMeasure_apply (φ : RoughForm I M ℝ k) (α : M) {s : Set M}
    (hs : MeasurableSet s) :
    chartMeasure φ α s =
      ∫⁻ y in (extChartAt I α) '' (s ∩ (extChartAt I α).source),
        ENNReal.ofReal |φ.inChartAt α y (finBasisOfFinrankEq ℝ E hk.out)|
          ∂(finBasisOfFinrankEq ℝ E hk.out).addHaar := by
  rw [chartMeasure, Measure.map_apply measurable_subtype_coe hs,
    (measurableEmbedding_extChartAt_restrict α).comap_apply, image_domRestrict,
    withDensity_apply _ ((hs.inter (isOpen_extChartAt_source α).measurableSet).image_extChartAt α
      inter_subset_right)]

omit [IsManifold I 1 M] in
private theorem chartMeasure_restrict_source (φ : RoughForm I M ℝ k) (α : M) :
    (chartMeasure φ α).restrict (extChartAt I α).source = chartMeasure φ α := by
  ext s hs
  rw [Measure.restrict_apply hs,
    chartMeasure_apply φ α (hs.inter (isOpen_extChartAt_source α).measurableSet),
    chartMeasure_apply φ α hs, inter_assoc, inter_self]

/-- The chart measures agree on chart overlaps: this is the change of variables along the chart
transition, applied to the identity map. -/
private theorem chartMeasure_restrict_overlap (φ : RoughForm I M ℝ k) (α β : M) :
    (chartMeasure φ α).restrict ((extChartAt I α).source ∩ (extChartAt I β).source) =
      (chartMeasure φ β).restrict ((extChartAt I α).source ∩ (extChartAt I β).source) := by
  set U := (extChartAt I α).source ∩ (extChartAt I β).source
  have hU : MeasurableSet U :=
    (isOpen_extChartAt_source α).measurableSet.inter (isOpen_extChartAt_source β).measurableSet
  ext s hs
  have hcov := φ.setLIntegral_ofReal_abs_inChartAt_mpullback (finBasisOfFinrankEq ℝ E hk.out)
    (ContinuousLinearEquiv.refl ℝ E) (injOn_id _) (fun x _ ↦ mdifferentiableAt_id)
    (hs.inter hU).isChartMeasurable (inter_subset_right : s ∩ U ⊆ U)
    (finBasisOfFinrankEq ℝ E hk.out).addHaar
  rw [mpullback_id, image_id, map_basis_refl, map_measure_refl] at hcov
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs, chartMeasure_apply φ α (hs.inter hU),
    chartMeasure_apply φ β (hs.inter hU),
    inter_eq_left.2 (inter_subset_right.trans inter_subset_left),
    inter_eq_left.2 (inter_subset_right.trans inter_subset_right), hcov]

variable [LindelofSpace M]

/-- The chart measures glue to a unique measure on the manifold. -/
private theorem existsUnique_restrict_eq_chartMeasure (φ : RoughForm I M ℝ k) :
    ∃! ν : Measure M, ∀ α : M, ν.restrict (extChartAt I α).source = chartMeasure φ α := by
  obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover
    (fun x : M ↦ (extChartAt I x).source) fun x ↦ extChartAt_source_mem_nhds x
  simpa only [chartMeasure_restrict_source] using
    existsUnique_restrict_eq (μ := chartMeasure φ)
      (fun α : M ↦ (isOpen_extChartAt_source α).measurableSet) ht hcover
      fun α _ β ↦ chartMeasure_restrict_overlap φ α β

/-! ### The measure of a top form -/

/-- The **measure `|φ|` of a top form** `φ` on a manifold modelled on a space of dimension `k`:
the unique measure which, on the source of each preferred chart, is coordinate Lebesgue measure
weighted by the absolute value of the coefficient `φ(∂₁, …, ∂ₖ)`. Here `∂₁, …, ∂ₖ` is the basis
`Module.finBasisOfFinrankEq` of the model space, and Lebesgue measure is normalized by it. The
measure does not depend on an orientation. It is characterized by
`TauCeti.RoughForm.eq_measure_iff`. -/
def measure (φ : RoughForm I M ℝ k) : Measure M :=
  (existsUnique_restrict_eq_chartMeasure φ).exists.choose

private theorem measure_restrict_source (φ : RoughForm I M ℝ k) (α : M) :
    φ.measure.restrict (extChartAt I α).source = chartMeasure φ α :=
  (existsUnique_restrict_eq_chartMeasure φ).exists.choose_spec α

/-- **The measure of a top form in coordinates.** The measure `|φ|` of a measurable subset `s` of
a chart source is the integral, over the coordinate image of `s`, of the absolute value of the
coefficient of `φ` in that chart. -/
theorem measure_apply_of_subset (φ : RoughForm I M ℝ k) {α : M} {s : Set M}
    (hs : MeasurableSet s) (hsub : s ⊆ (extChartAt I α).source) :
    φ.measure s =
      ∫⁻ y in (extChartAt I α) '' s,
        ENNReal.ofReal |φ.inChartAt α y (finBasisOfFinrankEq ℝ E hk.out)|
          ∂(finBasisOfFinrankEq ℝ E hk.out).addHaar := by
  rw [← Measure.restrict_eq_self φ.measure hsub, measure_restrict_source,
    chartMeasure_apply φ α hs, inter_eq_left.2 hsub]

/-- The measure `|φ|` is the only measure given in every chart by the coordinate formula of
`TauCeti.RoughForm.measure_apply_of_subset`. -/
theorem eq_measure_iff {φ : RoughForm I M ℝ k} {ν : Measure M} :
    ν = φ.measure ↔ ∀ (α : M) (s : Set M), MeasurableSet s → s ⊆ (extChartAt I α).source →
      ν s = ∫⁻ y in (extChartAt I α) '' s,
        ENNReal.ofReal |φ.inChartAt α y (finBasisOfFinrankEq ℝ E hk.out)|
          ∂(finBasisOfFinrankEq ℝ E hk.out).addHaar := by
  refine ⟨fun h α s hs hsub ↦ h ▸ φ.measure_apply_of_subset hs hsub, fun h ↦ ?_⟩
  refine (existsUnique_restrict_eq_chartMeasure φ).unique (fun α ↦ ?_) (measure_restrict_source φ)
  ext s hs
  rw [Measure.restrict_apply hs, chartMeasure_apply φ α hs,
    h α _ (hs.inter (isOpen_extChartAt_source α).measurableSet) inter_subset_right]

/-- Scaling a top form by `c` scales its measure by `|c|`. -/
@[simp]
theorem measure_smul (c : ℝ) (φ : RoughForm I M ℝ k) :
    (c • φ).measure = ENNReal.ofReal |c| • φ.measure := by
  refine (eq_measure_iff.2 fun α s hs hsub ↦ ?_).symm
  rw [smul_apply, φ.measure_apply_of_subset hs hsub, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun (hs.image_extChartAt α hsub) fun y _ ↦ ?_
  rw [← ENNReal.ofReal_mul (abs_nonneg c), ← abs_mul, inChartAt_apply, inChartAt_apply,
    Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]

/-- A top form and its negative have the same measure. -/
@[simp]
theorem measure_neg (φ : RoughForm I M ℝ k) : (-φ).measure = φ.measure := by
  rw [← neg_one_smul ℝ φ, measure_smul, abs_neg, abs_one, ENNReal.ofReal_one, one_smul]

/-- The zero form has zero measure. -/
@[simp]
theorem measure_zero : (0 : RoughForm I M ℝ k).measure = 0 := by
  rw [← zero_smul ℝ (0 : RoughForm I M ℝ k), measure_smul, abs_zero, ENNReal.ofReal_zero,
    zero_smul]

/-! ### Local finiteness and positivity -/

/-- **The measure of a continuous top form is locally finite.** Near each point the coordinate
coefficient is bounded, so a small neighbourhood has finite measure. In particular the measure of
a continuous top form on a compact manifold is finite. -/
theorem isLocallyFiniteMeasure_measure {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I 0 φ) :
    IsLocallyFiniteMeasure φ.measure := by
  refine ⟨fun x ↦ ?_⟩
  set b := finBasisOfFinrankEq ℝ E hk.out
  set e := extChartAt I x
  set g : E → ℝ := fun y ↦ |φ.inChartAt x y b|
  have hg : ContinuousOn g e.target :=
    continuous_abs.comp_continuousOn
      ((continuous_eval_const (b : Fin k → E)).comp_continuousOn
        (hφ.continuousOn_inChartAt x))
  have hxe : x ∈ e.source := mem_extChartAt_source x
  -- Near `e x` in the model, the coordinate density stays below `g (e x) + 1`.
  have hbound : {y | g y < g (e x) + 1} ∈ 𝓝[range I] (e x) := by
    rw [← nhdsWithin_extChartAt_target_eq' hxe]
    exact (hg (e x) (e.map_source hxe)).eventually_lt_const (lt_add_one _)
  set t := {y | g y < g (e x) + 1} ∩ Metric.ball (e x) 1
  have ht : t ∈ 𝓝[range I] (e x) :=
    Filter.inter_mem hbound (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ one_pos))
  have hs : e.source ∩ e ⁻¹' t ∈ 𝓝 x :=
    Filter.inter_mem (extChartAt_source_mem_nhds' hxe)
      (extChartAt_preimage_mem_nhds_of_mem_nhdsWithin hxe ht)
  refine ⟨interior (e.source ∩ e ⁻¹' t), interior_mem_nhds.2 hs, ?_⟩
  rw [φ.measure_apply_of_subset isOpen_interior.measurableSet
    (interior_subset.trans inter_subset_left)]
  have himage : e '' interior (e.source ∩ e ⁻¹' t) ⊆ t := by
    rintro _ ⟨z, hz, rfl⟩
    exact (interior_subset hz).2
  refine setLIntegral_lt_top_of_le_nnreal ?_ ⟨(g (e x) + 1).toNNReal, fun y hy ↦ ?_⟩
  · exact ((measure_mono (himage.trans inter_subset_right)).trans_lt measure_ball_lt_top).ne
  · exact ENNReal.ofReal_le_ofReal (himage hy).1.le

/-- **The measure of a continuous nowhere-vanishing top form is positive on nonempty open sets.**
In a chart the coefficient of such a form vanishes nowhere, and a nonempty open subset of a chart
source has a coordinate image of positive Lebesgue measure, even at boundary or corner points. -/
theorem isOpenPosMeasure_measure {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I 0 φ)
    (h0 : ∀ x, φ x ≠ 0) : φ.measure.IsOpenPosMeasure := by
  refine ⟨fun U hU hne ↦ ?_⟩
  obtain ⟨x, hx⟩ := hne
  set b := finBasisOfFinrankEq ℝ E hk.out
  set e := extChartAt I x
  set V := U ∩ e.source
  have hV : IsOpen V := hU.inter (isOpen_extChartAt_source x)
  have hVsub : V ⊆ e.source := inter_subset_right
  have hA : MeasurableSet (e '' V) := hV.measurableSet.image_extChartAt x hVsub
  refine ((?_ : 0 < φ.measure V).trans_le (measure_mono inter_subset_left)).ne'
  rw [φ.measure_apply_of_subset hV.measurableSet hVsub]
  -- The coordinate image of `V` has positive Lebesgue measure.
  have hApos : 0 < b.addHaar (e '' V) := by
    rw [e.image_eq_target_inter_inv_preimage hVsub]
    apply Measure.measure_pos_of_nonempty_interior
    refine Set.Nonempty.of_closure ⟨e x, ?_⟩
    simpa only [inter_comm] using
      (extChartAt_mem_closure_interior (I := I) (x₀ := x)
        (subset_closure (mem_interior_iff_mem_nhds.mpr (hV.mem_nhds ⟨hx, mem_extChartAt_source x⟩)))
        (mem_extChartAt_source x))
  -- The coordinate density is measurable and vanishes nowhere on that image.
  have hd : AEMeasurable (fun y ↦ ENNReal.ofReal |φ.inChartAt x y b|)
      (b.addHaar.restrict (e '' V)) :=
    (ENNReal.continuous_ofReal.comp_continuousOn (continuous_abs.comp_continuousOn
      ((continuous_eval_const (b : Fin k → E)).comp_continuousOn
        ((hφ.continuousOn_inChartAt x).mono
          (e.image_source_eq_target ▸ image_mono hVsub))))).aemeasurable hA
  have hpos : ∀ y ∈ e '' V, ENNReal.ofReal |φ.inChartAt x y b| ≠ 0 := by
    rintro _ ⟨z, hz, rfl⟩
    have hz0 : φ.inChartAt x (e z) ≠ 0 := by
      have h0' : (0 : RoughForm I M ℝ k).inChartAt x (e z) = 0 := by
        ext v
        simp only [inChartAt_apply, Pi.zero_apply, ContinuousAlternatingMap.coe_zero]
      rw [← h0', Ne, inChartAt_chart_eq_iff (hVsub hz)]
      exact h0 z
    rw [Ne, ENNReal.ofReal_eq_zero, not_le, abs_pos]
    exact ((φ.inChartAt x (e z)).map_basis_ne_zero_iff b).2 hz0
  rw [pos_iff_ne_zero, Ne, lintegral_eq_zero_iff' hd]
  intro h
  have hnull : ∀ᵐ y ∂b.addHaar, y ∉ e '' V :=
    ((ae_restrict_iff' hA).1 h).mono fun y hy hyA ↦ hpos y hyA (hy hyA)
  exact hApos.ne' (measure_eq_zero_iff_ae_notMem.2 hnull)

end RoughForm

end TauCeti

/-! ### Invariance under differentiable homeomorphisms -/

namespace Homeomorph

open TauCeti

variable {H' N : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'} [TopologicalSpace N]
  [ChartedSpace H' N] [IsManifold J 1 N] [MeasurableSpace N] [BorelSpace N]
  [LindelofSpace M] [LindelofSpace N]

/-- **Change of variables for the measure of a top form.** A differentiable homeomorphism
`Φ : M → N` between manifolds modelled on the same space carries the measure of the pulled-back
form `Φ^* ψ` to the measure of `ψ`. In particular a diffeomorphism preserving a top form preserves
its measure. No orientation is involved. -/
theorem measurePreserving_measure_mpullback (Φ : M ≃ₜ N) (hΦ : MDifferentiable I J Φ)
    (ψ : RoughForm J N ℝ k) :
    MeasurePreserving Φ (mpullback I J Φ ψ).measure ψ.measure := by
  refine ⟨Φ.measurable, ?_⟩
  -- Near each point `y`, the two measures agree on subsets of a chart source at `y` whose
  -- preimages lie in a chart source at `Φ.symm y`; a countable family of these sets covers `N`.
  set U : N → Set N := fun y ↦
    (extChartAt J y).source ∩ Φ.symm ⁻¹' (extChartAt I (Φ.symm y)).source
  have hU (y : N) : IsOpen (U y) :=
    (isOpen_extChartAt_source y).inter ((isOpen_extChartAt_source _).preimage Φ.symm.continuous)
  obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover U fun y ↦
    (hU y).mem_nhds ⟨mem_extChartAt_source y, mem_extChartAt_source (Φ.symm y)⟩
  refine Measure.ext_of_biUnion_eq_univ ht hcover fun y _ ↦ ?_
  ext s hs
  have hsU : MeasurableSet (s ∩ U y) := hs.inter (hU y).measurableSet
  have hpre : MeasurableSet (Φ ⁻¹' (s ∩ U y)) := hsU.preimage Φ.measurable
  have hsub : Φ ⁻¹' (s ∩ U y) ⊆
      (extChartAt I (Φ.symm y)).source ∩ Φ ⁻¹' (extChartAt J y).source := by
    intro x hx
    refine ⟨?_, hx.2.1⟩
    simpa only [mem_preimage, Homeomorph.symm_apply_apply] using hx.2.2
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs, Measure.map_apply Φ.measurable hsU,
    RoughForm.measure_apply_of_subset _ hpre (hsub.trans inter_subset_left),
    ψ.setLIntegral_ofReal_abs_inChartAt_mpullback _ (ContinuousLinearEquiv.refl ℝ E)
      Φ.injective.injOn (fun x _ ↦ hΦ x) hpre.isChartMeasurable hsub,
    map_basis_refl, map_measure_refl,
    image_preimage_eq _ Φ.surjective,
    ψ.measure_apply_of_subset hsU (inter_subset_right.trans inter_subset_left)]

end Homeomorph

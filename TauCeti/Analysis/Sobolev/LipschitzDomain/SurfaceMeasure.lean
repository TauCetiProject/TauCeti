/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import TauCeti.MeasureTheory.Function.AreaFormula.Graph
public import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz

/-!
# Surface measure in a Lipschitz boundary chart

A Lipschitz boundary chart parametrizes the part of the frontier inside its cylinder by

`y ↦ e.symm (normalGraphEmbedding φ y)`.

This file identifies the image of that parametrization and compares tangential Lebesgue measure
with normalized Euclidean Hausdorff measure on the frontier. It also gives the weighted area
formula in chart coordinates. These results are the measure-theoretic bridge from local Sobolev
traces in graph coordinates to traces on the boundary itself. Since tangential Lebesgue measure
charges nonempty open sets, so does surface measure on the frontier, which turns
almost-everywhere boundary statements about continuous functions into pointwise ones.

## Main declarations

* `Set.IsLipschitzChartWith.image_boundaryParametrization`: the chart parametrization covers
  exactly the frontier inside the chart cylinder.
* `Set.IsLipschitzChartWith.volume_le_euclideanHausdorffMeasure_frontier_inter`: surface measure
  dominates tangential volume in a chart.
* `Set.IsLipschitzChartWith.euclideanHausdorffMeasure_frontier_inter_le`: the converse estimate,
  with explicit dependence on the Lipschitz constant.
* `Set.IsLipschitzChartWith.lintegral_frontier_inter_eq`: the weighted area formula in chart
  coordinates.
* `Set.IsLipschitzChartWith.map_snd_euclideanHausdorffMeasure_frontier_inter_le`: the tangential
  coordinate pushes surface measure on a frontier patch forward to a bounded multiple of
  tangential volume.
* `Set.IsLipschitzChartWith.ae_restrict_frontier_inter_iff`: a property of the tangential
  coordinate holds almost everywhere on a frontier patch exactly when it holds for almost every
  tangential parameter in the chart.
* `Set.IsLipschitzChartWith.euclideanHausdorffMeasure_frontier_inter_ne_zero` and
  `Set.IsLipschitzDomainAtWith.euclideanHausdorffMeasure_frontier_inter_ne_zero`: surface measure
  charges every relatively open piece of the frontier around a point with a boundary chart, since
  its tangential parameters form a nonempty open set.
* `Set.IsLipschitzDomainWith.eqOn_frontier_of_ae_eq`: on a Lipschitz domain, functions continuous
  on the frontier that agree almost everywhere for surface measure agree at every frontier point.

## References

* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised ed.,
  §3.3 (the area formula and Lipschitz graphs).
* W. McLean, *Strongly Elliptic Systems and Boundary Integral Equations*, §3.1.
-/

public section

noncomputable section

open MeasureTheory Module Set
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The part of the frontier of a set lying in the preimage of a chart cylinder is measurable. -/
theorem measurableSet_frontier_inter_preimage_normalCylinder (Omega : Set F)
    (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (a b : ℝ) :
    MeasurableSet (frontier Omega ∩ e ⁻¹' normalCylinder a b) :=
  isClosed_frontier.measurableSet.inter
    ((isOpen_normalCylinder a b).preimage e.continuous).measurableSet

/-- The tangential coordinate `x ↦ (e x).snd` read through a chart map is measurable. -/
theorem _root_.AffineIsometryEquiv.measurable_snd_apply (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) :
    Measurable fun x ↦ (e x).snd :=
  ((WithLp.continuous_snd _ _ _).comp e.continuous).measurable

end TauCeti

namespace Set.IsLipschitzChartWith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section NormedTarget

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {Omega : Set F} {L : ℝ≥0} {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {phi : E → ℝ} {a b : ℝ}

omit [FiniteDimensional ℝ E] [MeasurableSpace F] [BorelSpace F] in
/-- The tangential parameters whose graph points lie in the cylinder of a boundary chart form
an open, hence measurable, set. -/
theorem measurableSet_normalGraphEmbedding_preimage_normalCylinder
    (h : Omega.IsLipschitzChartWith L e phi a b) :
    MeasurableSet (TauCeti.normalGraphEmbedding phi ⁻¹' TauCeti.normalCylinder a b) :=
  ((TauCeti.isOpen_normalCylinder a b).preimage
    h.lipschitzWith.normalGraphEmbedding.continuous).measurableSet

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] in
/-- The graph parametrization of a Lipschitz boundary chart is Lipschitz, with the same bound
as the normal graph parametrization. -/
theorem lipschitzWith_boundaryParametrization (h : Omega.IsLipschitzChartWith L e phi a b) :
    LipschitzWith (L + 1) (fun y ↦ e.symm (TauCeti.normalGraphEmbedding phi y)) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [e.symm.isometry.dist_eq]
  exact h.lipschitzWith.normalGraphEmbedding.dist_le_mul x y

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] in
/-- A Lipschitz chart parametrizes exactly the part of the frontier lying inside its cylinder. -/
theorem image_boundaryParametrization (h : Omega.IsLipschitzChartWith L e phi a b) :
    (fun y ↦ e.symm (TauCeti.normalGraphEmbedding phi y)) ''
        (TauCeti.normalGraphEmbedding phi ⁻¹' TauCeti.normalCylinder a b) =
      frontier Omega ∩ e ⁻¹' TauCeti.normalCylinder a b := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hz : TauCeti.normalGraphEmbedding phi y ∈
        e '' frontier Omega ∩ TauCeti.normalCylinder a b := by
      rw [h.toIsLipschitzChart.image_frontier_inter_normalCylinder]
      exact ⟨by simp, hy⟩
    obtain ⟨z, hzF, hze⟩ := hz.1
    have hzx : z = e.symm (TauCeti.normalGraphEmbedding phi y) := by
      rw [← hze, e.symm_apply_apply]
    have hxF : e.symm (TauCeti.normalGraphEmbedding phi y) ∈ frontier Omega := by
      rw [← hzx]
      exact hzF
    exact ⟨hxF, by simpa using hz.2⟩
  · rintro ⟨hx, hxC⟩
    have hz : e x ∈ {z | z.fst = phi z.snd} ∩ TauCeti.normalCylinder a b := by
      rw [← h.toIsLipschitzChart.image_frontier_inter_normalCylinder]
      exact ⟨⟨x, hx, rfl⟩, hxC⟩
    have hgraph : TauCeti.normalGraphEmbedding phi (e x).snd = e x :=
      (WithLp.ext_iff 2).2 <| Prod.ext (by simpa using hz.1.symm) (by simp)
    refine ⟨(e x).snd, ?_, ?_⟩
    · simpa [hgraph] using hz.2
    · apply e.injective
      rw [e.apply_symm_apply, hgraph]

/-- In a Lipschitz boundary chart, normalized surface measure dominates tangential Lebesgue
measure. -/
theorem volume_le_euclideanHausdorffMeasure_frontier_inter
    (h : Omega.IsLipschitzChartWith L e phi a b) :
    volume (TauCeti.normalGraphEmbedding phi ⁻¹' TauCeti.normalCylinder a b) ≤
      μHE[finrank ℝ E] (frontier Omega ∩ e ⁻¹' TauCeti.normalCylinder a b) := by
  rw [← h.image_boundaryParametrization]
  rw [← image_image]
  rw [e.symm.isometry.euclideanHausdorffMeasure_image]
  exact TauCeti.volume_le_euclideanHausdorffMeasure_normalGraphEmbedding_image phi _

/-- In a Lipschitz boundary chart, normalized surface measure is at most
`(L + 1) ^ dim E` times tangential Lebesgue measure. -/
theorem euclideanHausdorffMeasure_frontier_inter_le
    (h : Omega.IsLipschitzChartWith L e phi a b) :
    μHE[finrank ℝ E] (frontier Omega ∩ e ⁻¹' TauCeti.normalCylinder a b) ≤
      ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ finrank ℝ E *
        volume (TauCeti.normalGraphEmbedding phi ⁻¹' TauCeti.normalCylinder a b) := by
  rw [← h.image_boundaryParametrization]
  rw [← image_image]
  rw [e.symm.isometry.euclideanHausdorffMeasure_image]
  exact h.lipschitzWith.euclideanHausdorffMeasure_normalGraphEmbedding_image_le _

/-- Reading off the tangential coordinate pushes normalized surface measure on the frontier patch
of a Lipschitz chart forward to at most `(L + 1) ^ dim E` times tangential Lebesgue measure. -/
theorem map_snd_euclideanHausdorffMeasure_frontier_inter_le
    (h : Omega.IsLipschitzChartWith L e phi a b) :
    ((μHE[finrank ℝ E] : Measure F).restrict
        (frontier Omega ∩ e ⁻¹' TauCeti.normalCylinder a b)).map (fun x ↦ (e x).snd) ≤
      ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ finrank ℝ E • volume := by
  refine Measure.le_iff.2 fun S hS ↦ ?_
  have hm := e.measurable_snd_apply
  rw [Measure.map_apply hm hS, Measure.restrict_apply (hm hS), _root_.smul_apply, smul_eq_mul]
  calc
    _ ≤ μHE[finrank ℝ E] ((fun y ↦ e.symm (TauCeti.normalGraphEmbedding phi y)) '' S) := by
      refine measure_mono ?_
      rintro x ⟨hxS, hx⟩
      rw [← h.image_boundaryParametrization] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact ⟨y, by simpa using hxS, rfl⟩
    _ ≤ _ := by
      rw [← image_image, e.symm.isometry.euclideanHausdorffMeasure_image]
      exact h.lipschitzWith.euclideanHausdorffMeasure_normalGraphEmbedding_image_le S

/-- A set of tangential parameters is Lebesgue-null exactly when the corresponding part of the
boundary chart is null for normalized surface measure. -/
theorem euclideanHausdorffMeasure_image_boundaryParametrization_eq_zero_iff
    (h : Omega.IsLipschitzChartWith L e phi a b) (s : Set E) :
    μHE[finrank ℝ E]
        ((fun y ↦ e.symm (TauCeti.normalGraphEmbedding phi y)) '' s) = 0 ↔
      volume s = 0 := by
  rw [← image_image]
  rw [e.symm.isometry.euclideanHausdorffMeasure_image]
  exact h.lipschitzWith.euclideanHausdorffMeasure_normalGraphEmbedding_image_eq_zero_iff s

/-- The frontier patch in a Lipschitz boundary chart has zero normalized surface measure exactly
when its set of tangential parameters has zero Lebesgue measure. -/
theorem euclideanHausdorffMeasure_frontier_inter_eq_zero_iff
    (h : Omega.IsLipschitzChartWith L e phi a b) :
    μHE[finrank ℝ E] (frontier Omega ∩ e ⁻¹' TauCeti.normalCylinder a b) = 0 ↔
      volume (TauCeti.normalGraphEmbedding phi ⁻¹' TauCeti.normalCylinder a b) = 0 := by
  rw [← h.image_boundaryParametrization]
  exact h.euclideanHausdorffMeasure_image_boundaryParametrization_eq_zero_iff _

/-- **Surface measure charges the open pieces of a frontier patch.** If an open set `U` meets the
part of the frontier inside the cylinder of a Lipschitz boundary chart, then `frontier Omega ∩ U`
has positive normalized surface measure. -/
theorem euclideanHausdorffMeasure_frontier_inter_ne_zero
    (h : Omega.IsLipschitzChartWith L e phi a b) {U : Set F} (hU : IsOpen U)
    (hne : (frontier Omega ∩ e ⁻¹' TauCeti.normalCylinder a b ∩ U).Nonempty) :
    μHE[finrank ℝ E] (frontier Omega ∩ U) ≠ 0 := by
  -- The tangential parameters of the frontier points of the patch lying in `U` form a nonempty
  -- open set, and the chart parametrization carries it into `frontier Omega ∩ U`.
  set s := TauCeti.normalGraphEmbedding phi ⁻¹' TauCeti.normalCylinder a b ∩
    (fun y ↦ e.symm (TauCeti.normalGraphEmbedding phi y)) ⁻¹' U
  have hs : IsOpen s := ((TauCeti.isOpen_normalCylinder a b).preimage
    h.lipschitzWith.normalGraphEmbedding.continuous).inter
      (hU.preimage h.lipschitzWith_boundaryParametrization.continuous)
  obtain ⟨x, hx, hxU⟩ := hne
  rw [← h.image_boundaryParametrization] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have himage : (fun y ↦ e.symm (TauCeti.normalGraphEmbedding phi y)) '' s ⊆
      frontier Omega ∩ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨(h.image_boundaryParametrization ▸ mem_image_of_mem _ hz.1 :
      e.symm (TauCeti.normalGraphEmbedding phi z) ∈ frontier Omega ∩ _).1, hz.2⟩
  exact fun h0 ↦ hs.measure_ne_zero volume ⟨y, hy, hxU⟩
    ((h.euclideanHausdorffMeasure_image_boundaryParametrization_eq_zero_iff s).1
      (measure_mono_null himage h0))

/-- **Surface measure charges every neighbourhood of a regular boundary point.** If `Omega` has a
Lipschitz boundary chart centred at `x`, then for every neighbourhood `U` of `x` the part of the
frontier inside `U` has positive normalized surface measure. -/
theorem _root_.Set.IsLipschitzDomainAtWith.euclideanHausdorffMeasure_frontier_inter_ne_zero
    {x : F} (hx : Omega.IsLipschitzDomainAtWith (E := E) L x) {U : Set F} (hU : U ∈ 𝓝 x) :
    μHE[finrank ℝ E] (frontier Omega ∩ U) ≠ 0 := by
  obtain ⟨e, phi, a, b, hex, hc⟩ := (Omega.isLipschitzDomainAtWith_iff L x).1 hx
  obtain ⟨ha, hb, hphi, -, -⟩ := (Omega.isLipschitzChartWith_iff L e phi a b).1 hc
  -- The centre `x` is the boundary point over the tangential parameter `0`.
  have hg0 : TauCeti.normalGraphEmbedding phi 0 = 0 := by
    rw [TauCeti.normalGraphEmbedding_apply, hphi, ← Prod.zero_eq_mk, WithLp.toLp_zero]
  have hxF : x ∈ frontier Omega ∩ e ⁻¹' TauCeti.normalCylinder a b := by
    rw [← hc.image_boundaryParametrization]
    refine ⟨0, ?_, ?_⟩
    · rw [mem_preimage, hg0]
      exact TauCeti.zero_mem_normalCylinder ha hb
    · simp only [hg0]
      exact e.symm_apply_eq.2 hex.symm
  exact fun h0 ↦ hc.euclideanHausdorffMeasure_frontier_inter_ne_zero isOpen_interior
    ⟨x, hxF, mem_interior_iff_mem_nhds.2 hU⟩
    (measure_mono_null (inter_subset_inter_right _ interior_subset) h0)

/-- **Surface-almost-everywhere equality of continuous functions is equality on the frontier.**
On a Lipschitz domain, two functions continuous on the frontier that agree almost everywhere for
normalized surface measure on the frontier agree at every frontier point. -/
theorem _root_.Set.IsLipschitzDomainWith.eqOn_frontier_of_ae_eq
    {Omega : Set (WithLp 2 (ℝ × E))} (hΩ : Omega.IsLipschitzDomainWith L) {Y : Type*}
    [TopologicalSpace Y] [T2Space Y] {f g : WithLp 2 (ℝ × E) → Y}
    (hf : ContinuousOn f (frontier Omega)) (hg : ContinuousOn g (frontier Omega))
    (hfg : f =ᵐ[(μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict (frontier Omega)] g) :
    EqOn f g (frontier Omega) := by
  intro x hx
  by_contra hne
  -- The two functions differ on the part of the frontier inside some open `U ∋ x`, a set of
  -- positive surface measure.
  obtain ⟨U, hU, hxU, hUs⟩ := mem_nhdsWithin.1
    (((hf x hx).prodMk (hg x hx)).eventually_mem (isClosed_diagonal.isOpen_compl.mem_nhds hne))
  have hx' := ((isLipschitzDomainWith_iff Omega L).1 hΩ).2 x hx
  refine hx'.euclideanHausdorffMeasure_frontier_inter_ne_zero (hU.mem_nhds hxU)
    (measure_mono_null ?_ (ae_iff.1 ((ae_restrict_iff' isClosed_frontier.measurableSet).1 hfg)))
  rintro y ⟨hyF, hyU⟩ hy
  exact hUs ⟨hyU, hyF⟩ (hy hyF)

/-- A property of the tangential coordinate holds almost everywhere on the frontier patch of a
Lipschitz boundary chart, for normalized surface measure, exactly when it holds for almost every
tangential parameter whose graph point lies in the chart cylinder. -/
theorem ae_restrict_frontier_inter_iff (h : Omega.IsLipschitzChartWith L e phi a b)
    {P : E → Prop} :
    (∀ᵐ x ∂(μHE[finrank ℝ E] : Measure F).restrict
        (frontier Omega ∩ e ⁻¹' TauCeti.normalCylinder a b), P (e x).snd) ↔
      ∀ᵐ y ∂volume.restrict (TauCeti.normalGraphEmbedding phi ⁻¹' TauCeti.normalCylinder a b),
        P y := by
  rw [ae_restrict_iff' (TauCeti.measurableSet_frontier_inter_preimage_normalCylinder Omega e a b),
    ae_restrict_iff' h.measurableSet_normalGraphEmbedding_preimage_normalCylinder, ae_iff, ae_iff,
    ← h.euclideanHausdorffMeasure_image_boundaryParametrization_eq_zero_iff,
    ← h.image_boundaryParametrization]
  -- The chart parametrization carries the bad parameters onto the bad boundary points.
  congr! 3
  ext x
  simp only [not_imp, mem_image]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hP⟩
    exact ⟨y, ⟨hy, by simpa using hP⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hP⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, by simpa using hP⟩

end NormedTarget

section EuclideanTarget

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  {Omega : Set F} {L : ℝ≥0} {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {phi : E → ℝ} {a b : ℝ}

/-- **Weighted area formula in a Lipschitz boundary chart.** Surface integration over the part
of the frontier inside the chart cylinder is integration over its tangential parameters, weighted
by the geometric Jacobian of the boundary parametrization. The weight need not be measurable. -/
theorem lintegral_frontier_inter_eq (h : Omega.IsLipschitzChartWith L e phi a b)
    (g : F → ℝ≥0∞) :
    ∫⁻ x in frontier Omega ∩ e ⁻¹' TauCeti.normalCylinder a b, g x ∂μHE[finrank ℝ E] =
      ∫⁻ y in TauCeti.normalGraphEmbedding phi ⁻¹' TauCeti.normalCylinder a b,
        ENNReal.ofReal
            (fderiv ℝ (fun z ↦ e.symm (TauCeti.normalGraphEmbedding phi z)) y).normDet *
          g (e.symm (TauCeti.normalGraphEmbedding phi y)) := by
  rw [← h.image_boundaryParametrization]
  exact (h.lipschitzWith_boundaryParametrization.lintegral_image_eq_lintegral_normDet_fderiv_mul
    h.measurableSet_normalGraphEmbedding_preimage_normalCylinder
      (e.symm.injective.comp (TauCeti.injective_normalGraphEmbedding phi)).injOn g)

end EuclideanTarget

end Set.IsLipschitzChartWith

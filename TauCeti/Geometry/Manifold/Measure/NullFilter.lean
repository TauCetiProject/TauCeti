/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Measure
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Null
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Geometry.Manifold.Measure.Differentiable

/-!
# Atlas invariance of null sets and the almost-everywhere filter on a manifold

Chartwise nullity `TauCeti.IsNullSet` on a finite-dimensional real `C¹` manifold (possibly with
boundary or corners) does not depend on the preferred atlas or the choice of additive Haar measure
on the model space: a set is null exactly when its image in every chart of the `C¹` maximal atlas
is null for a single additive Haar measure, and it suffices to check this on any atlas covering the
manifold, or to check nullity of intersections with any open cover. No countability assumption on
the cover and no Lindelöf assumption on the manifold are needed, because each chart source is
homeomorphic to a subset of the finite-dimensional (hence hereditarily Lindelöf) model space.

The sets with null complement form a filter `TauCeti.Manifold.ae I M` closed under countable
intersections and nontrivial on every nonempty finite-dimensional manifold. On a normed space
modelled on itself it coincides with `MeasureTheory.ae μ` for every additive Haar measure `μ`, and
on a Lindelöf `C¹` manifold equipped with any continuous Riemannian metric it coincides with
`MeasureTheory.ae (TauCeti.riemannianVolume I M)`.

## Main definitions

* `TauCeti.Manifold.ae`: the filter of subsets of a manifold whose complements are chartwise null.

## Main results

* `TauCeti.isNullSet_iff_forall_extChartAt`: nullity can be tested against a single additive Haar
  measure.
* `TauCeti.isNullSet_iff_forall_inter_isOpen`: nullity is local for arbitrary open covers.
* `TauCeti.IsNullSet.image_extend_eq_zero`, `TauCeti.isNullSet_iff_forall_mem_maximalAtlas`:
  nullity is preserved in every chart of the `C¹` maximal atlas.
* `TauCeti.isNullSet_iff_forall_atlas`: nullity can be tested on any covering `C¹` atlas.
* `TauCeti.Manifold.ae_modelWithCornersSelf_eq`: on a finite-dimensional real normed space, the
  manifold almost-everywhere filter is the Haar almost-everywhere filter.
* `TauCeti.Manifold.ae_eq_ae_riemannianVolume`,
  `TauCeti.Manifold.eventually_ae_iff_ae_riemannianVolume`: on a Lindelöf `C¹` manifold, the
  almost-everywhere filter coincides with that of any continuous Riemannian volume measure.
-/

public section

open Bundle Filter MeasureTheory Set
open scoped Manifold Topology

namespace TauCeti

section NullSet

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The empty set is chartwise null. -/
@[simp]
theorem isNullSet_empty : IsNullSet I (∅ : Set M) := by
  rw [isNullSet_iff]
  intro x μ _
  simp

omit [MeasurableSpace E] [BorelSpace E] [ChartedSpace H M] in
/-- A finite-dimensional chart source is Lindelöf, because it embeds homeomorphically into the
second-countable model space. -/
private theorem isLindelof_source (I : ModelWithCorners ℝ E H) [FiniteDimensional ℝ E]
    (e : OpenPartialHomeomorph M H) : IsLindelof e.source := by
  have hL : IsLindelof (e.extend I).target := HereditarilyLindelofSpace.isLindelof _
  have him : (e.extend I).symm '' (e.extend I).target = e.source := by
    rw [PartialEquiv.symm_image_target_eq_source, e.extend_source]
  exact him ▸ hL.image_of_continuousOn e.continuousOn_extend_symm

/-- On a manifold modelled on a finite-dimensional space, nullity can be tested with a single
additive Haar measure, since any two additive Haar measures are mutually absolutely continuous. -/
theorem isNullSet_iff_forall_extChartAt [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set M} :
    IsNullSet I s ↔ ∀ x : M, μ (extChartAt I x '' (s ∩ (extChartAt I x).source)) = 0 := by
  refine ⟨fun hs x ↦ hs.chartwise x μ, fun hs ↦ (isNullSet_iff I s).2 fun x ν _ ↦ ?_⟩
  exact Measure.absolutelyContinuous_isAddHaarMeasure ν μ (hs x)

/-- **Locality of null sets.** On a manifold with a finite-dimensional model, a set is null iff its
intersection with every set of an open cover is null. Neither the cover nor the manifold need be
countable or Lindelöf. -/
theorem isNullSet_iff_forall_inter_isOpen [FiniteDimensional ℝ E] {ι : Type*} {U : ι → Set M}
    (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ) {s : Set M} :
    IsNullSet I s ↔ ∀ i, IsNullSet I (s ∩ U i) := by
  refine ⟨fun hs i ↦ hs.mono inter_subset_left, fun h ↦ (isNullSet_iff I s).2 fun x μ _ ↦ ?_⟩
  obtain ⟨t, ht, hsub⟩ := (isLindelof_source I (chartAt H x)).elim_countable_subcover U hU
    (hcover ▸ subset_univ _)
  have heq : s ∩ (extChartAt I x).source =
      ⋃ i ∈ t, (s ∩ U i) ∩ (extChartAt I x).source := by
    ext y
    simp only [mem_inter_iff, mem_iUnion, exists_prop]
    refine ⟨fun ⟨hys, hyx⟩ ↦ ?_, fun ⟨_, _, ⟨hys, _⟩, hyx⟩ ↦ ⟨hys, hyx⟩⟩
    obtain ⟨i, hit, hyi⟩ := mem_iUnion₂.1 (hsub (by simpa only [extChartAt_source] using hyx))
    exact ⟨i, hit, ⟨hys, hyi⟩, hyx⟩
  rw [heq, image_iUnion₂]
  exact (measure_biUnion_null_iff ht).2 fun i _ ↦ (h i).chartwise x μ

/-- Transferring nullity across a `C¹` coordinate change between two charts of the maximal atlas. -/
private theorem image_extend_inter_eq_zero_of_image_extend_eq_zero [FiniteDimensional ℝ E]
    {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set M}
    (hs : μ (e.extend I '' (s ∩ e.source)) = 0) :
    μ (e'.extend I '' (s ∩ e'.source ∩ e.source)) = 0 := by
  set Φ := I.extendCoordChange e e'
  set A := e.extend I '' (s ∩ e'.source ∩ e.source)
  have hA_sub : A ⊆ Φ.source := by
    dsimp only [A, Φ]
    rw [← OpenPartialHomeomorph.extend_image_source_inter (f := e) (f' := e')]
    exact image_mono fun _ hx ↦ ⟨hx.2, hx.1.2⟩
  have hA_null : μ A = 0 :=
    measure_mono_null (image_mono (t := s ∩ e.source) fun _ hx ↦ ⟨hx.1.1, hx.2⟩) hs
  have hdiff : DifferentiableOn ℝ Φ A :=
    ((I.contDiffOn_extendCoordChange he he').differentiableOn one_ne_zero).mono hA_sub
  have him : Φ '' A = e'.extend I '' (s ∩ e'.source ∩ e.source) := by
    simp only [A, image_image]
    refine image_congr fun y hy ↦ ?_
    have hye : y ∈ (e.extend I).source := by simpa only [e.extend_source] using hy.2
    simp only [Φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
      (e.extend I).left_inv hye]
  rw [← him]
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ hdiff hA_null

/-- **Maximal-atlas invariance of null sets.** On a finite-dimensional real `C¹` manifold, a null
set has Haar-null image in every chart of the `C¹` maximal atlas. -/
theorem IsNullSet.image_extend_eq_zero [FiniteDimensional ℝ E] [IsManifold I 1 M] {s : Set M}
    (hs : IsNullSet I s) {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 1 M)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    μ (e.extend I '' (s ∩ e.source)) = 0 := by
  obtain ⟨t, ht, -, hcover⟩ := (isLindelof_source I e).elim_nhds_subcover
    (fun x : M ↦ (chartAt H x).source) fun x _ ↦ chart_source_mem_nhds H x
  have heq : s ∩ e.source = ⋃ x ∈ t, s ∩ e.source ∩ (chartAt H x).source := by
    ext y
    simp only [mem_inter_iff, mem_iUnion, exists_prop]
    refine ⟨fun ⟨hys, hye⟩ ↦ ?_, fun ⟨_, _, ⟨hys, hye⟩, _⟩ ↦ ⟨hys, hye⟩⟩
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (hcover hye)
    exact ⟨x, hxt, ⟨hys, hye⟩, hyx⟩
  rw [heq, image_iUnion₂]
  refine (measure_biUnion_null_iff ht).2 fun x _ ↦ ?_
  refine image_extend_inter_eq_zero_of_image_extend_eq_zero (IsManifold.chart_mem_maximalAtlas x)
    he μ ?_
  simpa only [extChartAt, OpenPartialHomeomorph.extend_source] using hs.chartwise x μ

/-- A subset of a finite-dimensional `C¹` manifold is null iff its image in every chart of the `C¹`
maximal atlas is null for a fixed additive Haar measure. -/
theorem isNullSet_iff_forall_mem_maximalAtlas [FiniteDimensional ℝ E] [IsManifold I 1 M]
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set M} :
    IsNullSet I s ↔
      ∀ e ∈ IsManifold.maximalAtlas I 1 M, μ (e.extend I '' (s ∩ e.source)) = 0 :=
  ⟨fun hs _ he ↦ hs.image_extend_eq_zero he μ,
    fun h ↦ (isNullSet_iff_forall_extChartAt μ).2 fun x ↦ by
      simpa only [extChartAt, OpenPartialHomeomorph.extend_source] using
        h (chartAt H x) (IsManifold.chart_mem_maximalAtlas x)⟩

/-- **Atlas characterization of null sets.** On a finite-dimensional real `C¹` manifold, a set is
null iff its image in each chart of any covering `C¹` atlas is null for a fixed additive Haar
measure. Neither the atlas nor the manifold need be countable or Lindelöf. -/
theorem isNullSet_iff_forall_atlas [FiniteDimensional ℝ E] [IsManifold I 1 M]
    (μ : Measure E) [μ.IsAddHaarMeasure] {ι : Type*} {φ : ι → OpenPartialHomeomorph M H}
    (hφ : ∀ i, φ i ∈ IsManifold.maximalAtlas I 1 M) (hcover : ⋃ i, (φ i).source = univ)
    {s : Set M} :
    IsNullSet I s ↔ ∀ i, μ ((φ i).extend I '' (s ∩ (φ i).source)) = 0 := by
  refine ⟨fun hs i ↦ hs.image_extend_eq_zero (hφ i) μ,
    fun h ↦ (isNullSet_iff_forall_extChartAt μ).2 fun x ↦ ?_⟩
  obtain ⟨t, ht, hsub⟩ := (isLindelof_source I (chartAt H x)).elim_countable_subcover
    (fun i ↦ (φ i).source) (fun i ↦ (φ i).open_source) (hcover ▸ subset_univ _)
  have heq : s ∩ (extChartAt I x).source =
      ⋃ i ∈ t, s ∩ (chartAt H x).source ∩ (φ i).source := by
    ext y
    simp only [mem_inter_iff, mem_iUnion, exists_prop, extChartAt_source]
    refine ⟨fun ⟨hys, hyx⟩ ↦ ?_, fun ⟨_, _, ⟨hys, hyx⟩, _⟩ ↦ ⟨hys, hyx⟩⟩
    obtain ⟨i, hit, hyi⟩ := mem_iUnion₂.1 (hsub hyx)
    exact ⟨i, hit, ⟨hys, hyx⟩, hyi⟩
  rw [heq, image_iUnion₂]
  exact (measure_biUnion_null_iff ht).2 fun i _ ↦
    image_extend_inter_eq_zero_of_image_extend_eq_zero (hφ i)
      (IsManifold.chart_mem_maximalAtlas x) μ (h i)

end NullSet

namespace Manifold

section Filter

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- The **metric-free almost-everywhere filter** on a charted manifold: the filter of sets whose
complements are chartwise null (`TauCeti.IsNullSet`). This depends on neither a Riemannian metric
nor an orientation, and needs no measurable structure on the manifold itself. -/
def ae : Filter M where
  sets := {s | IsNullSet I sᶜ}
  univ_sets := by simp
  sets_of_superset hs hst := hs.mono (compl_subset_compl.2 hst)
  inter_sets hs ht := by
    simpa only [mem_ofPred_eq, compl_inter] using hs.union ht

variable {I M}

/-- A set belongs to the manifold almost-everywhere filter iff its complement is chartwise null. -/
@[simp]
theorem mem_ae_iff {s : Set M} : s ∈ ae I M ↔ IsNullSet I sᶜ := Iff.rfl

/-- A predicate holds eventually in `Manifold.ae I M` iff the set where it fails is null. -/
theorem eventually_ae_iff {p : M → Prop} :
    (∀ᶠ x in ae I M, p x) ↔ IsNullSet I {x | ¬ p x} := Iff.rfl

/-- The complement of a null set lies in the manifold almost-everywhere filter. -/
theorem _root_.TauCeti.IsNullSet.compl_mem_ae {s : Set M} (hs : IsNullSet I s) :
    sᶜ ∈ ae I M := by
  simpa only [mem_ae_iff, compl_compl] using hs

/-- Points almost everywhere on a manifold avoid any given null set. -/
theorem _root_.TauCeti.IsNullSet.eventually_notMem {s : Set M} (hs : IsNullSet I s) :
    ∀ᶠ x in ae I M, x ∉ s :=
  hs.compl_mem_ae

instance instCountableInterFilter_ae : CountableInterFilter (ae I M) where
  countable_sInter_mem S hSc hS := by
    rw [mem_ae_iff, compl_sInter, sUnion_image]
    exact IsNullSet.biUnion hSc fun s hs ↦ hS s hs

instance instNeBot_ae [FiniteDimensional ℝ E] [Nonempty M] : (ae I M).NeBot := by
  rw [neBot_iff]
  intro hbot
  have huniv : IsNullSet I (univ : Set M) := by
    simpa only [← compl_empty, ← mem_ae_iff, hbot] using mem_bot
  have hemp : (univ : Set M) = ∅ := by
    simpa only [interior_univ] using huniv.interior_eq_empty
  exact univ_nonempty.ne_empty hemp

/-- On a finite-dimensional real normed space modelled on itself, the manifold almost-everywhere
filter coincides with the almost-everywhere filter of any additive Haar measure. -/
theorem ae_modelWithCornersSelf_eq [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ae 𝓘(ℝ, E) E = MeasureTheory.ae μ := by
  ext s
  rw [mem_ae_iff, MeasureTheory.mem_ae_iff, isNullSet_modelWithCornersSelf_iff μ]

end Filter

section Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- On a Lindelöf `C¹` manifold with any continuous Riemannian metric, the metric-free
almost-everywhere filter coincides with the almost-everywhere filter of the Riemannian volume. -/
theorem ae_eq_ae_riemannianVolume :
    ae I M = MeasureTheory.ae (riemannianVolume I M) := by
  ext s
  rw [mem_ae_iff, MeasureTheory.mem_ae_iff, isNullSet_iff_riemannianVolume_eq_zero]

/-- A property holds almost everywhere for the Riemannian volume of any continuous Riemannian
metric iff it holds in the metric-free filter `TauCeti.Manifold.ae I M`. -/
theorem eventually_ae_iff_ae_riemannianVolume {p : M → Prop} :
    (∀ᶠ x in ae I M, p x) ↔ ∀ᵐ x ∂riemannianVolume I M, p x := by
  rw [ae_eq_ae_riemannianVolume]

end Riemannian

end Manifold

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Measure.AE
public import TauCeti.Geometry.Manifold.Measure.PositiveDensity.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.PartitionOfUnity
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.ExtChartAt.Measure

/-!
# Existence and basic properties of positive continuous density measures

Every Hausdorff paracompact finite-dimensional real `C¹` manifold `M` (possibly with boundary or
corners) admits a positive continuous density measure
(`TauCeti.exists_isPositiveContinuousDensity`), built by summing chart-localized additive Haar
measures weighted by a continuous partition of unity subordinate to the preferred charts. In
particular, every Hausdorff Lindelöf `C¹` manifold admits one
(`TauCeti.exists_isPositiveContinuousDensity_of_lindelof`).

Every positive continuous density measure is locally finite
(`TauCeti.IsPositiveContinuousDensity.isLocallyFiniteMeasure`) and positive on nonempty open sets
(`TauCeti.IsPositiveContinuousDensity.isOpenPosMeasure`). On every chart source, a subset (not
necessarily measurable) has measure zero iff its coordinate image has Haar measure zero
(`TauCeti.IsPositiveContinuousDensity.measure_eq_zero_iff_image_of_subset`); consequently, every
measure-zero set is chartwise null, and on a Lindelöf manifold the null sets coincide with
`TauCeti.IsNullSet I` and the almost-everywhere filter equals `TauCeti.Manifold.ae I M`.

## Main results

* `TauCeti.exists_isPositiveContinuousDensity`: existence of a positive continuous density measure
  on every Hausdorff paracompact `C¹` manifold via a partition of unity.
* `TauCeti.exists_isPositiveContinuousDensity_of_lindelof`: existence on every Hausdorff Lindelöf
  `C¹` manifold.
* `TauCeti.IsPositiveContinuousDensity.isLocallyFiniteMeasure`: local finiteness.
* `TauCeti.IsPositiveContinuousDensity.isOpenPosMeasure`: positivity on nonempty open sets.
* `TauCeti.IsPositiveContinuousDensity.measure_eq_zero_iff_image_of_subset`: chartwise null-set
  characterization for arbitrary subsets of chart sources.
* `TauCeti.IsPositiveContinuousDensity.isNullSet_of_measure_eq_zero`,
  `TauCeti.IsPositiveContinuousDensity.isNullSet_iff_measure_eq_zero`,
  `TauCeti.IsPositiveContinuousDensity.ae_eq_manifoldAE`,
  `TauCeti.IsPositiveContinuousDensity.eventually_ae_iff_manifoldAE`: agreement with chartwise null
  sets and the metric-free filter `TauCeti.Manifold.ae I M`.
-/

public section

open Filter Function MeasureTheory Set
open scoped ENNReal Manifold Topology

noncomputable section

namespace TauCeti

/-! ### Existence via partition of unity -/

section Existence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M]

/-- Local measure attached to a continuous nonnegative function `f` supported inside the chart
source at `i`. -/
private def localChartMeasure (ν : Measure E) (i : M) (f : M → ℝ) : Measure M :=
  (((ν.restrict (extChartAt I i).target).withDensity
      fun y ↦ ENNReal.ofReal (f ((extChartAt I i).symm y))).comap
    ((chartAt H i).source.domRestrict (extChartAt I i))).map Subtype.val

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
/-- Evaluating `localChartMeasure` on a measurable set pulls the integral back to chart `i`. -/
private theorem localChartMeasure_apply (ν : Measure E) (i : M) (f : M → ℝ)
    {s : Set M} (hs : MeasurableSet s) :
    localChartMeasure (I := I) ν i f s =
      ∫⁻ z in extChartAt I i '' (s ∩ (chartAt H i).source),
        ENNReal.ofReal (f ((extChartAt I i).symm z)) ∂ν := by
  set ei := chartAt H i
  have hRi : MeasurableEmbedding (ei.source.domRestrict (extChartAt I i)) :=
    ei.measurableEmbedding_extend_restrict I
  have hval : MeasurableEmbedding (Subtype.val : ei.source → M) :=
    .subtypeVal ei.open_source.measurableSet
  have him : ei.source.domRestrict (extChartAt I i) '' (Subtype.val ⁻¹' s) =
      extChartAt I i '' (s ∩ ei.source) := image_domRestrict _ _ _
  have hB : MeasurableSet (extChartAt I i '' (s ∩ ei.source)) :=
    ei.measurableSet_image_extend I (hs.inter ei.open_source.measurableSet) inter_subset_right
  have hBT : extChartAt I i '' (s ∩ ei.source) ⊆ (extChartAt I i).target :=
    (image_mono (by simpa only [extChartAt_source] using inter_subset_right)).trans
      (extChartAt I i).image_source_eq_target.subset
  rw [localChartMeasure, hval.map_apply, hRi.comap_apply, him, withDensity_apply _ hB,
    Measure.restrict_restrict hB, inter_eq_left.2 hBT]

open Classical in
/-- Pushing a `localChartMeasure` forward into another chart `x₀` yields a weighted Haar integral
with density `|det DΦ| * f ∘ (extChartAt I x₀).symm` supported on the overlap. -/
private theorem map_localChartMeasure_apply (ν : Measure E) [ν.IsAddHaarMeasure]
    {i x₀ : M} {f : M → ℝ} {A : Set E} (hA : MeasurableSet A) :
    (((localChartMeasure (I := I) ν i f).restrict (chartAt H x₀).source).map (extChartAt I x₀)) A =
      ∫⁻ y in A ∩ (extChartAt I x₀).target,
        ENNReal.ofReal
          (if y ∈ (I.extendCoordChange (chartAt H x₀) (chartAt H i)).source then
            |(fderivWithin ℝ (I.extendCoordChange (chartAt H x₀) (chartAt H i)) (range I) y).det| *
              f ((extChartAt I x₀).symm y)
          else 0) ∂ν := by
  set e₀ := chartAt H x₀
  set Φ := I.extendCoordChange e₀ (chartAt H i)
  have hΦ_meas := e₀.measurableSet_extendCoordChange_source (chartAt H i) I
  have hT₀ : MeasurableSet (extChartAt I x₀).target := e₀.measurableSet_extend_target I
  have hs_meas : MeasurableSet (extChartAt I x₀ ⁻¹' A ∩ e₀.source) :=
    e₀.measurableSet_preimage_extend_inter I hA
  conv_lhs => rw [extChartAt]
  rw [e₀.map_restrict_extend_apply I _ hA, ← extChartAt,
    localChartMeasure_apply (I := I) ν i f hs_meas]
  conv_lhs =>
    dsimp only [extChartAt]
    rw [e₀.image_extend_preimage_inter (chartAt H i) I A]
  rw [ν.setLIntegral_extendCoordChange (I := I)
      (IsManifold.chart_mem_maximalAtlas x₀) (IsManifold.chart_mem_maximalAtlas i)
      (hA.inter hΦ_meas) inter_subset_right,
    ← lintegral_indicator (hA.inter hΦ_meas), ← lintegral_indicator (hA.inter hT₀)]
  refine lintegral_congr fun y ↦ ?_
  by_cases hy : y ∈ A ∩ Φ.source
  · have hyT : y ∈ A ∩ (extChartAt I x₀).target := ⟨hy.1, hy.2.1⟩
    rw [indicator_of_mem hy, indicator_of_mem hyT, ite_eq_left hy.2,
      ENNReal.ofReal_mul (abs_nonneg _)]
    have hxi : (extChartAt I x₀).symm y ∈ (extChartAt I i).source := hy.2.2
    simp only [Φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply]
    congr 3
    exact (extChartAt I i).left_inv hxi
  · rw [indicator_of_notMem hy]
    by_cases hy' : y ∈ A ∩ (extChartAt I x₀).target
    · rw [indicator_of_mem hy', ite_eq_right fun h ↦ hy ⟨hy'.1, h⟩, ENNReal.ofReal_zero]
    · rw [indicator_of_notMem hy']

open Classical in
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] in
/-- Continuity of one partition-of-unity coordinate summand on `(extChartAt I x₀).target`. -/
private theorem continuousOn_summand (x₀ i : M) {f : M → ℝ} (hf : Continuous f)
    (hsupp : tsupport f ⊆ (chartAt H i).source) :
    ContinuousOn
      (fun y ↦
        if y ∈ (I.extendCoordChange (chartAt H x₀) (chartAt H i)).source then
          |(fderivWithin ℝ (I.extendCoordChange (chartAt H x₀) (chartAt H i)) (range I) y).det| *
            f ((extChartAt I x₀).symm y)
        else 0)
      (extChartAt I x₀).target := by
  set e₀ := chartAt H x₀
  set ei := chartAt H i
  set Φ := I.extendCoordChange e₀ ei
  intro y hy
  by_cases hyΦ : y ∈ Φ.source
  · have hmem : Φ.source ∈ 𝓝[(extChartAt I x₀).target] y :=
      nhdsWithin_mono y e₀.extend_target_subset_range
        (I.extendCoordChange_source_mem_nhdsWithin hyΦ)
    have hcont : ContinuousOn
        (fun z ↦ |(fderivWithin ℝ Φ (range I) z).det| * f ((extChartAt I x₀).symm z)) Φ.source :=
      (continuousOn_abs_det_fderivWithin_extendCoordChange (I := I)
        (IsManifold.chart_mem_maximalAtlas x₀) (IsManifold.chart_mem_maximalAtlas i)).mul
        (hf.comp_continuousOn ((continuousOn_extChartAt_symm x₀).mono fun _ hz ↦ hz.1))
    refine ((hcont y hyΦ).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem hmem fun z hz ↦ by simp only [hz, ↓reduceIte])
      (by simp only [hyΦ, ↓reduceIte])
  · have hnotSupp : (extChartAt I x₀).symm y ∉ tsupport f := fun hmem ↦ by
      have hxe : (extChartAt I x₀).symm y ∈ e₀.source :=
        e₀.extend_source (I := I) ▸ (extChartAt I x₀).map_target hy
      apply hyΦ
      rw [← OpenPartialHomeomorph.extend_image_source_inter (f := e₀) (f' := ei)]
      exact ⟨(extChartAt I x₀).symm y, ⟨hxe, hsupp hmem⟩, (extChartAt I x₀).right_inv hy⟩
    have hmem : (extChartAt I x₀).symm ⁻¹' (tsupport f)ᶜ ∈ 𝓝[(extChartAt I x₀).target] y :=
      (continuousOn_extChartAt_symm x₀ y hy).preimage_mem_nhdsWithin
        ((isClosed_tsupport f).isOpen_compl.mem_nhds hnotSupp)
    refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem hmem fun z hz ↦ ?_) (by simp only [hyΦ, ↓reduceIte])
    have hf0 : f ((extChartAt I x₀).symm z) = 0 :=
      (notMem_tsupport_iff_eventuallyEq.1 hz).self_of_nhds
    split_ifs
    · rw [hf0, mul_zero]
    · rfl

open Classical in
/-- Coordinate summand attached to a partition of unity `ρ` and chart `x₀`. -/
private def partitionSummand (ρ : PartitionOfUnity M M univ) (x₀ i : M) (y : E) : ℝ :=
  if y ∈ (I.extendCoordChange (chartAt H x₀) (chartAt H i)).source then
    |(fderivWithin ℝ (I.extendCoordChange (chartAt H x₀) (chartAt H i)) (range I) y).det| *
      ρ i ((extChartAt I x₀).symm y)
  else 0

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] in
private theorem partitionSummand_nonneg (ρ : PartitionOfUnity M M univ) (x₀ i : M) (y : E) :
    0 ≤ partitionSummand (I := I) ρ x₀ i y := by
  dsimp only [partitionSummand]
  split_ifs
  · exact mul_nonneg (abs_nonneg _) (ρ.nonneg i _)
  · exact le_rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] in
private theorem partitionSummand_locallyFinite (ρ : PartitionOfUnity M M univ) (x₀ : M)
    {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    ∃ N ∈ 𝓝[(extChartAt I x₀).target] y,
      {i : M | (N ∩ Function.support (partitionSummand (I := I) ρ x₀ i)).Nonempty}.Finite := by
  obtain ⟨W, hW, hWfin⟩ := ρ.locallyFinite ((extChartAt I x₀).symm y)
  refine ⟨(extChartAt I x₀).symm ⁻¹' W,
    (continuousOn_extChartAt_symm x₀ y hy).preimage_mem_nhdsWithin hW, hWfin.subset ?_⟩
  rintro i ⟨z, hzW, hzh⟩
  refine ⟨(extChartAt I x₀).symm z, fun hzero ↦ hzh ?_, hzW⟩
  dsimp only [partitionSummand]
  split_ifs
  · rw [hzero, mul_zero]
  · rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] in
private theorem continuousOn_finsum_partitionSummand (ρ : PartitionOfUnity M M univ)
    (hρ : ρ.IsSubordinate fun x : M ↦ (chartAt H x).source) (x₀ : M) :
    ContinuousOn (fun y ↦ ∑ᶠ i : M, partitionSummand (I := I) ρ x₀ i y)
      (extChartAt I x₀).target := by
  refine continuousOn_iff_continuous_domRestrict.2 <|
    continuous_finsum (f := fun i (y : (extChartAt I x₀).target) ↦
        partitionSummand (I := I) ρ x₀ i y.val)
      (fun i ↦ continuousOn_iff_continuous_domRestrict.1
        (continuousOn_summand (I := I) x₀ i (ρ i).continuous (hρ i))) fun y ↦ ?_
  obtain ⟨N, hN, hNfin⟩ := partitionSummand_locallyFinite (I := I) ρ x₀ y.property
  refine ⟨Subtype.val ⁻¹' N, ?_, hNfin.subset fun i ⟨z, hzh, hzN⟩ ↦ ⟨z.val, hzN, hzh⟩⟩
  rw [nhds_subtype_eq_comap_nhdsWithin]
  exact Filter.preimage_mem_comap hN

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] in
private theorem finsum_partitionSummand_pos (ρ : PartitionOfUnity M M univ)
    (hρ : ρ.IsSubordinate fun x : M ↦ (chartAt H x).source) (x₀ : M)
    {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    0 < ∑ᶠ i : M, partitionSummand (I := I) ρ x₀ i y := by
  obtain ⟨N, hN, hNfin⟩ := partitionSummand_locallyFinite (I := I) ρ x₀ hy
  have hfin : (Function.support fun i ↦ partitionSummand (I := I) ρ x₀ i y).Finite :=
    hNfin.subset fun i hi ↦ ⟨y, mem_of_mem_nhdsWithin hy hN, hi⟩
  have hsum1 : ∑ᶠ i, ρ i ((extChartAt I x₀).symm y) = 1 := ρ.sum_eq_one (mem_univ _)
  obtain ⟨i, hi_ne⟩ : ∃ i, ρ i ((extChartAt I x₀).symm y) ≠ 0 := by
    by_contra hall
    have h0 : ∀ i, ρ i ((extChartAt I x₀).symm y) = 0 := fun i ↦ not_not.1 fun h ↦ hall ⟨i, h⟩
    have : (fun i ↦ ρ i ((extChartAt I x₀).symm y)) = fun _ ↦ 0 := funext h0
    rw [this, finsum_zero] at hsum1
    exact zero_ne_one hsum1
  have hi_pos : 0 < ρ i ((extChartAt I x₀).symm y) := lt_of_le_of_ne (ρ.nonneg i _) hi_ne.symm
  have hxe : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    simpa only [← extChartAt_source (I := I)] using (extChartAt I x₀).map_target hy
  have hyΦ : y ∈ (I.extendCoordChange (chartAt H x₀) (chartAt H i)).source := by
    rw [← OpenPartialHomeomorph.extend_image_source_inter (f := chartAt H x₀) (f' := chartAt H i)]
    exact ⟨(extChartAt I x₀).symm y, ⟨hxe, hρ i (subset_tsupport _ hi_ne)⟩,
      (extChartAt I x₀).right_inv hy⟩
  have hhi_pos : 0 < partitionSummand (I := I) ρ x₀ i y := by
    simp only [partitionSummand, hyΦ, ↓reduceIte]
    exact mul_pos (abs_det_fderivWithin_extendCoordChange_pos (I := I)
      (IsManifold.chart_mem_maximalAtlas x₀) (IsManifold.chart_mem_maximalAtlas i) hyΦ) hi_pos
  calc (0 : ℝ) < partitionSummand (I := I) ρ x₀ i y := hhi_pos
    _ ≤ ∑ j ∈ hfin.toFinset, partitionSummand (I := I) ρ x₀ j y :=
      Finset.single_le_sum (fun j _ ↦ partitionSummand_nonneg (I := I) ρ x₀ j y)
        (hfin.mem_toFinset.2 hhi_pos.ne')
    _ = ∑ᶠ j : M, partitionSummand (I := I) ρ x₀ j y :=
      (finsum_eq_sum_of_support_subset _ fun j hj ↦ hfin.mem_toFinset.2 hj).symm

omit [MeasurableSpace E] [BorelSpace E] [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M] in
private theorem countable_support_partitionSummand (ρ : PartitionOfUnity M M univ) (x₀ : M) :
    {i : M | ((extChartAt I x₀).target ∩
      Function.support (partitionSummand (I := I) ρ x₀ i)).Nonempty}.Countable := by
  have hnhds : ∀ y ∈ (extChartAt I x₀).target, ∃ O, IsOpen O ∧ y ∈ O ∧
      {i : M | ((O ∩ (extChartAt I x₀).target) ∩
        Function.support (partitionSummand (I := I) ρ x₀ i)).Nonempty}.Finite := fun y hy ↦ by
    obtain ⟨N, hN, hNfin⟩ := partitionSummand_locallyFinite (I := I) ρ x₀ hy
    obtain ⟨O, hO, hyO, hON⟩ := mem_nhdsWithin.1 hN
    exact ⟨O, hO, hyO, hNfin.subset fun i ⟨z, hz, hzh⟩ ↦ ⟨z, hON hz, hzh⟩⟩
  choose O hO hyO hOfin using hnhds
  obtain ⟨t, ht, hsub⟩ :=
    (HereditarilyLindelofSpace.isLindelof (extChartAt I x₀).target).elim_countable_subcover
      (fun y : (extChartAt I x₀).target ↦ O y.val y.property) (fun y ↦ hO y.val y.property)
      fun y hy ↦ mem_iUnion.2 ⟨⟨y, hy⟩, hyO y hy⟩
  refine (ht.biUnion fun y _ ↦ (hOfin y.val y.property).countable).mono ?_
  rintro i ⟨z, hzT, hzh⟩
  obtain ⟨y, hyt, hzy⟩ := mem_iUnion₂.1 (hsub hzT)
  exact mem_iUnion₂.2 ⟨y, hyt, ⟨z, ⟨hzy, hzT⟩, hzh⟩⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] in
private theorem tsum_ofReal_partitionSummand (ρ : PartitionOfUnity M M univ) (x₀ : M)
    {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    ∑' i : {i : M | ((extChartAt I x₀).target ∩
        Function.support (partitionSummand (I := I) ρ x₀ i)).Nonempty},
        ENNReal.ofReal (partitionSummand (I := I) ρ x₀ i.val y) =
      ENNReal.ofReal (∑ᶠ i : M, partitionSummand (I := I) ρ x₀ i y) := by
  classical
  set S := {i : M | ((extChartAt I x₀).target ∩
    Function.support (partitionSummand (I := I) ρ x₀ i)).Nonempty}
  obtain ⟨N, hN, hNfin⟩ := partitionSummand_locallyFinite (I := I) ρ x₀ hy
  have hfin : (Function.support fun i : M ↦ partitionSummand (I := I) ρ x₀ i y).Finite :=
    hNfin.subset fun i hi ↦ ⟨y, mem_of_mem_nhdsWithin hy hN, hi⟩
  have hfinS : (Function.support fun i : S ↦
      ENNReal.ofReal (partitionSummand (I := I) ρ x₀ i.val y)).Finite :=
    (hfin.preimage Subtype.val_injective.injOn).subset fun i hi h0 ↦ hi (by simp [h0])
  rw [tsum_eq_sum (s := hfinS.toFinset) fun i hi ↦
      notMem_support.1 fun h' ↦ hi (hfinS.mem_toFinset.2 h'),
    ← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ partitionSummand_nonneg (I := I) ρ x₀ i.val y,
    finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) fun i hi ↦ hfin.mem_toFinset.2 hi]
  congr 1
  refine Finset.sum_bij (fun i _ ↦ i.val) (fun i hi ↦ ?_) (fun _ _ _ _ h ↦ Subtype.ext h)
    (fun i hi ↦ ?_) (fun _ _ ↦ rfl)
  · have hne := hfinS.mem_toFinset.1 hi
    exact hfin.mem_toFinset.2 fun h0 ↦ hne (by simp [h0])
  · have hiS : i ∈ S := ⟨y, hy, hfin.mem_toFinset.1 hi⟩
    refine ⟨⟨i, hiS⟩, ?_, rfl⟩
    simp only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact lt_of_le_of_ne (partitionSummand_nonneg (I := I) ρ x₀ i y)
      (Ne.symm (hfin.mem_toFinset.1 hi))

/-- Pushing the partition-of-unity sum of local chart measures forward into chart `x₀` yields
the finsum density `∑ᶠ i, partitionSummand ρ x₀ i`. -/
private theorem map_restrict_sum_localChartMeasure (ν : Measure E) [ν.IsAddHaarMeasure]
    (ρ : PartitionOfUnity M M univ) (hρ : ρ.IsSubordinate fun x : M ↦ (chartAt H x).source)
    (x₀ : M) :
    (((Measure.sum fun i : M ↦ localChartMeasure (I := I) ν i (ρ i)).restrict
        (chartAt H x₀).source).map (extChartAt I x₀)) =
      (ν.restrict (extChartAt I x₀).target).withDensity
        fun y ↦ ENNReal.ofReal (∑ᶠ i : M, partitionSummand (I := I) ρ x₀ i y) := by
  classical
  set S := {i : M | ((extChartAt I x₀).target ∩
    Function.support (partitionSummand (I := I) ρ x₀ i)).Nonempty}
  have : Countable S := (countable_support_partitionSummand (I := I) ρ x₀).to_subtype
  have hT₀ : MeasurableSet (extChartAt I x₀).target := (chartAt H x₀).measurableSet_extend_target I
  ext A hA
  have hpre := (chartAt H x₀).measurableSet_preimage_extend_inter I hA
  conv_lhs => rw [extChartAt]
  rw [(chartAt H x₀).map_restrict_extend_apply I _ hA, Measure.sum_apply _ hpre,
    withDensity_apply _ hA, Measure.restrict_restrict hA]
  have hterm (i : M) : localChartMeasure (I := I) ν i (ρ i)
      ((chartAt H x₀).extend I ⁻¹' A ∩ (chartAt H x₀).source) =
      ∫⁻ y in A ∩ (extChartAt I x₀).target,
        ENNReal.ofReal (partitionSummand (I := I) ρ x₀ i y) ∂ν := by
    rw [← (chartAt H x₀).map_restrict_extend_apply I _ hA, ← extChartAt]
    exact map_localChartMeasure_apply (I := I) ν hA
  have haem (i : S) : AEMeasurable
      (fun y ↦ ENNReal.ofReal (partitionSummand (I := I) ρ x₀ i.val y))
      (ν.restrict (A ∩ (extChartAt I x₀).target)) :=
    ((ENNReal.continuous_ofReal.comp_continuousOn
      (continuousOn_summand (I := I) x₀ i.val (ρ i.val).continuous (hρ i.val))).aemeasurable
      hT₀).mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
  simp_rw [hterm]
  rw [← tsum_subtype_eq_of_support_subset (s := S) fun i hi ↦ by
      by_contra hiS; apply hi; dsimp only
      rw [setLIntegral_congr_fun (g := fun _ ↦ 0) (hA.inter hT₀) fun y hy ↦ by
        have h0 : partitionSummand (I := I) ρ x₀ i y = 0 := by
          by_contra hne; exact hiS ⟨y, hy.2, hne⟩
        simp [h0], lintegral_zero],
    ← lintegral_tsum haem]
  exact setLIntegral_congr_fun (hA.inter hT₀) fun y hy ↦
    tsum_ofReal_partitionSummand (I := I) ρ x₀ hy.2

/-- **Existence of a positive continuous density measure.** Every Hausdorff paracompact
finite-dimensional `C¹` manifold (possibly with boundary or corners) admits a positive continuous
density measure, built from a continuous partition of unity subordinate to the preferred charts. -/
theorem exists_isPositiveContinuousDensity [T2Space M] [ParacompactSpace M] :
    ∃ μ : Measure M, IsPositiveContinuousDensity I μ := by
  have : NormalSpace M := NormalSpace.of_paracompactSpace_r1Space
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate (X := M) isClosed_univ
    (fun x : M ↦ (chartAt H x).source) (fun x ↦ (chartAt H x).open_source)
    fun x _ ↦ mem_iUnion.2 ⟨x, mem_chart_source H x⟩
  let ν : Measure E := (Module.finBasis ℝ E).addHaar
  refine ⟨Measure.sum fun i : M ↦ localChartMeasure (I := I) ν i (ρ i),
    (isPositiveContinuousDensity_iff_forall_chartAt (I := I) ν).2 fun x₀ ↦
      ⟨fun y ↦ ∑ᶠ i : M, partitionSummand (I := I) ρ x₀ i y,
        continuousOn_finsum_partitionSummand (I := I) ρ hρ x₀,
        fun _ hy ↦ finsum_partitionSummand_pos (I := I) ρ hρ x₀ hy,
        map_restrict_sum_localChartMeasure (I := I) ν ρ hρ x₀⟩⟩

/-- Every Hausdorff Lindelöf finite-dimensional `C¹` manifold admits a positive continuous density
measure. -/
theorem exists_isPositiveContinuousDensity_of_lindelof [T2Space M] [LindelofSpace M] :
    ∃ μ : Measure M, IsPositiveContinuousDensity I μ := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : SecondCountableTopology H := I.secondCountableTopology
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_lindelof H M
  have : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : ParacompactSpace M := paracompact_of_locallyCompact_sigmaCompact
  exact exists_isPositiveContinuousDensity (I := I)

end Existence

/-! ### Local finiteness, full support, and null sets -/

section MeasureProperties

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M]

/-- Every positive continuous density measure is locally finite. -/
theorem IsPositiveContinuousDensity.isLocallyFiniteMeasure {μ : Measure M}
    (hμ : IsPositiveContinuousDensity I μ) : IsLocallyFiniteMeasure μ := by
  refine ⟨fun x ↦ ?_⟩
  let ν : Measure E := (Module.finBasis ℝ E).addHaar
  set e := chartAt H x
  have he := IsManifold.chart_mem_maximalAtlas (I := I) (n := 1) x
  set w := hμ.chartWeight he ν
  have hx : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  have hbound : {y | w y < w (extChartAt I x x) + 1} ∈ 𝓝[range I] (extChartAt I x x) := by
    rw [← nhdsWithin_extChartAt_target_eq' hx]
    exact (hμ.continuousOn_chartWeight he ν _ ((extChartAt I x).map_source hx)).eventually_lt_const
      (lt_add_one _)
  set t := {y | w y < w (extChartAt I x x) + 1} ∩ Metric.ball (extChartAt I x x) 1
  have ht : t ∈ 𝓝[range I] (extChartAt I x x) :=
    Filter.inter_mem hbound (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ one_pos))
  have hs : e.source ∩ extChartAt I x ⁻¹' t ∈ 𝓝 x :=
    Filter.inter_mem (chart_source_mem_nhds H x)
      (extChartAt_preimage_mem_nhds_of_mem_nhdsWithin hx ht)
  refine ⟨interior (e.source ∩ extChartAt I x ⁻¹' t), interior_mem_nhds.2 hs, ?_⟩
  rw [hμ.measure_apply_of_subset he ν isOpen_interior.measurableSet
    (interior_subset.trans inter_subset_left)]
  have him : e.extend I '' interior (e.source ∩ extChartAt I x ⁻¹' t) ⊆ t := by
    rintro _ ⟨z, hz, rfl⟩
    exact (interior_subset hz).2
  refine setLIntegral_lt_top_of_le_nnreal ?_
    ⟨(w (extChartAt I x x) + 1).toNNReal, fun y hy ↦ ENNReal.ofReal_le_ofReal (him hy).1.le⟩
  exact ((measure_mono (him.trans inter_subset_right)).trans_lt measure_ball_lt_top).ne

/-- Every positive continuous density measure gives positive mass to every nonempty open set. -/
theorem IsPositiveContinuousDensity.isOpenPosMeasure {μ : Measure M}
    (hμ : IsPositiveContinuousDensity I μ) : Measure.IsOpenPosMeasure μ := by
  refine ⟨fun U hU ⟨x, hxU⟩ ↦ ?_⟩
  let ν : Measure E := (Module.finBasis ℝ E).addHaar
  set e := chartAt H x
  have he := IsManifold.chart_mem_maximalAtlas (I := I) (n := 1) x
  set s := U ∩ e.source
  have hs_open : IsOpen s := hU.inter e.open_source
  have hxs : x ∈ s := ⟨hxU, mem_chart_source H x⟩
  have hxs' : s ⊆ (extChartAt I x).source := by
    simpa only [extChartAt_source] using inter_subset_right
  have hpos_nu : 0 < ν (extChartAt I x '' s) := by
    rw [(extChartAt I x).image_eq_target_inter_inv_preimage hxs']
    refine Measure.measure_pos_of_nonempty_interior _ (Nonempty.of_closure ⟨extChartAt I x x, ?_⟩)
    simpa only [inter_comm] using extChartAt_mem_closure_interior (I := I) (x₀ := x)
      (subset_closure (mem_interior_iff_mem_nhds.2 (hs_open.mem_nhds hxs))) (hxs' hxs)
  have hmeas := e.measurableSet_image_extend I hs_open.measurableSet inter_subset_right
  have hsubT : extChartAt I x '' s ⊆ (extChartAt I x).target :=
    (image_mono hxs').trans (extChartAt I x).image_source_eq_target.subset
  intro hU0
  have hs0 : μ s = 0 := measure_mono_null inter_subset_left hU0
  rw [hμ.measure_apply_of_subset he ν hs_open.measurableSet inter_subset_right] at hs0
  have hae := (lintegral_eq_zero_iff' ((ENNReal.continuous_ofReal.comp_continuousOn
    ((hμ.continuousOn_chartWeight he ν).mono hsubT)).aemeasurable hmeas)).1 hs0
  have hfalse : ∀ᵐ _ ∂ν.restrict (extChartAt I x '' s), False := by
    filter_upwards [ae_restrict_mem hmeas, hae] with y hy hy0
    exact (ENNReal.ofReal_pos.2 (hμ.chartWeight_pos he ν (hsubT hy))).ne' hy0
  exact hpos_nu.ne' (by
    simpa only [not_false_eq_true, ofPred_true, Measure.restrict_apply_univ] using ae_iff.1 hfalse)

omit [FiniteDimensional ℝ E] in
/-- On a chart source, a measurable subset has `μ`-measure zero iff its coordinate image has
Haar measure zero. -/
private theorem measure_eq_zero_iff_image_of_measurableSet {μ : Measure M}
    (hμ : IsPositiveContinuousDensity I μ) (x : M) (ν : Measure E) [ν.IsAddHaarMeasure]
    {s : Set M} (hs : MeasurableSet s) (hsub : s ⊆ (chartAt H x).source) :
    μ s = 0 ↔ ν (extChartAt I x '' s) = 0 := by
  have he := IsManifold.chart_mem_maximalAtlas (I := I) (n := 1) x
  have hmeas := (chartAt H x).measurableSet_image_extend I hs hsub
  have hsubT : extChartAt I x '' s ⊆ (extChartAt I x).target :=
    (image_mono (by simpa only [extChartAt_source] using hsub)).trans
      (extChartAt I x).image_source_eq_target.subset
  rw [hμ.measure_apply_of_subset he ν hs hsub]
  constructor
  · intro hz
    have hae := (lintegral_eq_zero_iff' ((ENNReal.continuous_ofReal.comp_continuousOn
      ((hμ.continuousOn_chartWeight he ν).mono hsubT)).aemeasurable hmeas)).1 hz
    have hfalse : ∀ᵐ _ ∂ν.restrict (extChartAt I x '' s), False := by
      filter_upwards [ae_restrict_mem hmeas, hae] with y hy hy0
      exact (ENNReal.ofReal_pos.2 (hμ.chartWeight_pos he ν (hsubT hy))).ne' hy0
    simpa only [not_false_eq_true, ofPred_true, Measure.restrict_apply_univ] using ae_iff.1 hfalse
  · intro hz
    rw [← extChartAt, Measure.restrict_zero_set hz, lintegral_zero_measure]

omit [FiniteDimensional ℝ E] in
/-- On a chart source, an arbitrary (not necessarily measurable) subset has `μ`-measure zero iff
its coordinate image has Haar measure zero. -/
theorem IsPositiveContinuousDensity.measure_eq_zero_iff_image_of_subset
    {μ : Measure M} (hμ : IsPositiveContinuousDensity I μ) (x : M)
    (ν : Measure E) [ν.IsAddHaarMeasure] {s : Set M} (hsub : s ⊆ (chartAt H x).source) :
    μ s = 0 ↔ ν (extChartAt I x '' s) = 0 := by
  constructor
  · intro hz
    set t := toMeasurable μ s ∩ (chartAt H x).source
    have hst : s ⊆ t := fun y hy ↦ ⟨subset_toMeasurable μ s hy, hsub hy⟩
    have htm : MeasurableSet t :=
      (measurableSet_toMeasurable μ s).inter (chartAt H x).open_source.measurableSet
    have ht0 : μ t = 0 := measure_mono_null inter_subset_left (by rwa [measure_toMeasurable])
    exact measure_mono_null (image_mono hst)
      ((measure_eq_zero_iff_image_of_measurableSet hμ x ν htm inter_subset_right).1 ht0)
  · intro hz
    set A := toMeasurable ν (extChartAt I x '' s)
    set t : Set M := extChartAt I x ⁻¹' A ∩ (chartAt H x).source
    have htm : MeasurableSet t :=
      (chartAt H x).measurableSet_preimage_extend_inter I (measurableSet_toMeasurable _ _)
    have hst : s ⊆ t := fun y hy ↦
      ⟨subset_toMeasurable ν _ (mem_image_of_mem _ hy), hsub hy⟩
    have hAt : extChartAt I x '' t ⊆ A := by
      rintro _ ⟨z, ⟨hzA, _⟩, rfl⟩
      exact hzA
    refine measure_mono_null hst
      ((measure_eq_zero_iff_image_of_measurableSet hμ x ν htm inter_subset_right).2 ?_)
    exact measure_mono_null hAt (by rwa [measure_toMeasurable])

omit [FiniteDimensional ℝ E] in
/-- Every `μ`-null set of a positive continuous density measure is chartwise null. No Lindelöf
assumption on `M` is needed for this direction. -/
theorem IsPositiveContinuousDensity.isNullSet_of_measure_eq_zero
    {μ : Measure M} (hμ : IsPositiveContinuousDensity I μ) {s : Set M} (hs : μ s = 0) :
    IsNullSet I s := by
  rw [isNullSet_iff]
  intro x ν _
  rw [extChartAt_source]
  exact (hμ.measure_eq_zero_iff_image_of_subset x ν inter_subset_right).1
    (measure_mono_null inter_subset_left hs)

/-- On a Lindelöf manifold, a subset is chartwise null iff it has measure zero for a positive
continuous density measure. -/
theorem IsPositiveContinuousDensity.isNullSet_iff_measure_eq_zero [LindelofSpace M]
    {μ : Measure M} (hμ : IsPositiveContinuousDensity I μ) {s : Set M} :
    IsNullSet I s ↔ μ s = 0 := by
  refine ⟨fun hs ↦ ?_, hμ.isNullSet_of_measure_eq_zero⟩
  obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover (fun x : M ↦ (chartAt H x).source)
    fun x ↦ chart_source_mem_nhds H x
  have hsub : s ⊆ ⋃ x ∈ t, s ∩ (chartAt H x).source := fun y hy ↦ by
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (hcover ▸ mem_univ y)
    exact mem_iUnion₂.2 ⟨x, hxt, hy, hyx⟩
  let ν : Measure E := (Module.finBasis ℝ E).addHaar
  refine measure_mono_null hsub ((measure_biUnion_null_iff ht).2 fun x _ ↦ ?_)
  exact (hμ.measure_eq_zero_iff_image_of_subset x ν inter_subset_right).2
    (by simpa only [extChartAt_source] using hs.chartwise x ν)

/-- On a Lindelöf manifold, the almost-everywhere filter of any positive continuous density
measure coincides with the metric-free filter `TauCeti.Manifold.ae I M`. -/
theorem IsPositiveContinuousDensity.ae_eq_manifoldAE [LindelofSpace M]
    {μ : Measure M} (hμ : IsPositiveContinuousDensity I μ) :
    MeasureTheory.ae μ = Manifold.ae I M := by
  ext s
  rw [MeasureTheory.mem_ae_iff, Manifold.mem_ae_iff, hμ.isNullSet_iff_measure_eq_zero]

/-- A property holds almost everywhere for a positive continuous density measure on a Lindelöf
manifold iff it holds in the metric-free filter `TauCeti.Manifold.ae I M`. -/
theorem IsPositiveContinuousDensity.eventually_ae_iff_manifoldAE [LindelofSpace M]
    {μ : Measure M} (hμ : IsPositiveContinuousDensity I μ) {p : M → Prop} :
    (∀ᵐ x ∂μ, p x) ↔ ∀ᶠ x in Manifold.ae I M, p x := by
  rw [hμ.ae_eq_manifoldAE]

end MeasureProperties

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Measure.PositiveDensity.Basic
public import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.PartitionOfUnity
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.ExtChartAt.Basic
import TauCeti.Geometry.Manifold.ExtChartAt.Measurable
import TauCeti.Geometry.Manifold.ExtChartAt.Measure
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# Existence of positive continuous density measures on manifolds

Every Hausdorff paracompact finite-dimensional real `C¹` manifold `M` (possibly with boundary or
corners) admits a positive continuous density measure
(`TauCeti.exists_isPositiveContinuousDensity`), built by summing chart-localized additive Haar
measures (`OpenPartialHomeomorph.localChartMeasure`) weighted by a continuous partition of unity
subordinate to the preferred charts. In particular, every Hausdorff Lindelöf `C¹` manifold admits
one (`TauCeti.exists_isPositiveContinuousDensity_of_lindelof`).

## Main results

* `TauCeti.exists_isPositiveContinuousDensity`: existence of a positive continuous density measure
  on every Hausdorff paracompact `C¹` manifold via a partition of unity.
* `TauCeti.exists_isPositiveContinuousDensity_of_lindelof`: existence on every Hausdorff Lindelöf
  `C¹` manifold.
-/

public section

open Filter Function MeasureTheory Set
open scoped ENNReal Manifold Topology

noncomputable section

namespace TauCeti

section Existence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M]

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
        ((chartAt H x₀).continuousOn_ite_abs_det_fderivWithin_extendCoordChange_mul (chartAt H i)
          I (IsManifold.chart_mem_maximalAtlas x₀) (IsManifold.chart_mem_maximalAtlas i)
          (ρ i).continuous (hρ i))) fun y ↦ ?_
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
    (((Measure.sum fun i : M ↦ (chartAt H i).localChartMeasure I ν (ρ i)).restrict
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
  have hterm (i : M) : (chartAt H i).localChartMeasure I ν (ρ i)
      ((chartAt H x₀).extend I ⁻¹' A ∩ (chartAt H x₀).source) =
      ∫⁻ y in A ∩ (extChartAt I x₀).target,
        ENNReal.ofReal (partitionSummand (I := I) ρ x₀ i y) ∂ν := by
    rw [← (chartAt H x₀).map_restrict_extend_apply I _ hA, ← extChartAt]
    exact (chartAt H x₀).map_restrict_localChartMeasure_apply (chartAt H i) I
      (IsManifold.chart_mem_maximalAtlas x₀) (IsManifold.chart_mem_maximalAtlas i) ν (ρ i) hA
  have haem (i : S) : AEMeasurable
      (fun y ↦ ENNReal.ofReal (partitionSummand (I := I) ρ x₀ i.val y))
      (ν.restrict (A ∩ (extChartAt I x₀).target)) :=
    ((ENNReal.continuous_ofReal.comp_continuousOn
      ((chartAt H x₀).continuousOn_ite_abs_det_fderivWithin_extendCoordChange_mul (chartAt H i.val)
        I (IsManifold.chart_mem_maximalAtlas x₀) (IsManifold.chart_mem_maximalAtlas i.val)
        (ρ i.val).continuous (hρ i.val))).aemeasurable hT₀).mono_measure
      (Measure.restrict_mono inter_subset_right le_rfl)
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
  refine ⟨Measure.sum fun i : M ↦ (chartAt H i).localChartMeasure I ν (ρ i),
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

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Paracompact
public import TauCeti.Geometry.Manifold.Measure.PositiveDensity.Basic
import Mathlib.Topology.PartitionOfUnity
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.ExtChartAt.Measurable
import TauCeti.Geometry.Manifold.ExtChartAt.Measure
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Det

/-!
# Existence of positive continuous density measures on manifolds

Every Hausdorff paracompact finite-dimensional real `C¹` manifold `M` (possibly with boundary or
corners) admits a positive continuous density measure (`TauCeti.exists_isPositiveDensityMeasure`),
built by summing chart-localized additive Haar measures (`OpenPartialHomeomorph.localChartMeasure`)
weighted by a continuous partition of unity subordinate to the preferred charts. In particular,
every Hausdorff Lindelöf `C¹` manifold admits one
(`TauCeti.exists_isPositiveDensityMeasure_of_lindelof`).

## Main results

* `TauCeti.exists_isPositiveDensityMeasure`: existence of a positive continuous density measure on
  every Hausdorff paracompact `C¹` manifold via a partition of unity.
* `TauCeti.exists_isPositiveDensityMeasure_of_lindelof`: existence on every Hausdorff Lindelöf `C¹`
  manifold.
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
private def partitionSummand (ρ : PartitionOfUnity M M univ) (x₀ i : M) : E → ℝ :=
  (I.extendCoordChange (chartAt H x₀) (chartAt H i)).source.indicator fun y ↦
    |(fderivWithin ℝ (I.extendCoordChange (chartAt H x₀) (chartAt H i)) (range I) y).det| *
      ρ i ((extChartAt I x₀).symm y)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] in
private theorem partitionSummand_nonneg (ρ : PartitionOfUnity M M univ) (x₀ i : M) (y : E) :
    0 ≤ partitionSummand (I := I) ρ x₀ i y :=
  indicator_nonneg (fun _ _ ↦ mul_nonneg (abs_nonneg _) (ρ.nonneg i _)) y

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] in
private theorem locallyFinite_partitionSummand (ρ : PartitionOfUnity M M univ) (x₀ : M) :
    LocallyFinite fun i : M ↦
      {y : (extChartAt I x₀).target | partitionSummand (I := I) ρ x₀ i y.val ≠ 0} := by
  refine (ρ.locallyFinite.preimage_continuous
    (continuousOn_iff_continuous_domRestrict.1 (continuousOn_extChartAt_symm x₀))).subset ?_
  intro i y hy
  exact fun hzero ↦ hy (indicator_apply_eq_zero.2 fun _ ↦ by
    rw [domRestrict_apply] at hzero; rw [hzero, mul_zero])

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
        ((chartAt H x₀).continuousOn_abs_det_fderivWithin_extendCoordChange_mul (chartAt H i)
          I (IsManifold.chart_mem_maximalAtlas x₀) (IsManifold.chart_mem_maximalAtlas i)
          (ρ i).continuous (hρ i))) ?_
  exact locallyFinite_partitionSummand (I := I) ρ x₀

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] in
private theorem finsum_partitionSummand_pos (ρ : PartitionOfUnity M M univ)
    (hρ : ρ.IsSubordinate fun x : M ↦ (chartAt H x).source) (x₀ : M)
    {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    0 < ∑ᶠ i : M, partitionSummand (I := I) ρ x₀ i y := by
  have hfin : (Function.support fun i ↦ partitionSummand (I := I) ρ x₀ i y).Finite :=
    (locallyFinite_partitionSummand (I := I) ρ x₀).point_finite ⟨y, hy⟩
  obtain ⟨i, hi_pos⟩ := ρ.exists_pos (mem_univ ((extChartAt I x₀).symm y))
  have hyΦ : y ∈ (I.extendCoordChange (chartAt H x₀) (chartAt H i)).source :=
    I.mem_extendCoordChange_source (extChartAt_eq_extend (I := I) x₀ ▸ hy)
      (extChartAt_eq_extend (I := I) x₀ ▸ hρ i (subset_tsupport _ hi_pos.ne'))
  have hhi_pos : 0 < partitionSummand (I := I) ρ x₀ i y := by
    rw [partitionSummand, indicator_of_mem hyΦ]
    exact mul_pos (I.abs_det_fderivWithin_extendCoordChange_pos
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
  have := ProperSpace.of_locallyCompactSpace ℝ (E := E)
  have : SigmaCompactSpace (extChartAt I x₀).target :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  set S := {i : M | ((extChartAt I x₀).target ∩
    Function.support (partitionSummand (I := I) ρ x₀ i)).Nonempty}
  have hlf : LocallyFinite fun i : S ↦
      {y : (extChartAt I x₀).target | partitionSummand (I := I) ρ x₀ i.val y.val ≠ 0} :=
    (locallyFinite_partitionSummand (I := I) ρ x₀).comp_injective Subtype.val_injective
  have hne : ∀ i : S,
      {y : (extChartAt I x₀).target | partitionSummand (I := I) ρ x₀ i.val y.val ≠ 0}.Nonempty :=
    fun ⟨_, y, hyT, hy⟩ ↦ ⟨⟨y, hyT⟩, hy⟩
  exact Set.countable_coe_iff.1 (countable_univ_iff.1 (hlf.countable_univ hne))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] in
private theorem tsum_ofReal_partitionSummand (ρ : PartitionOfUnity M M univ) (x₀ : M)
    {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    ∑' i : {i : M | ((extChartAt I x₀).target ∩
        Function.support (partitionSummand (I := I) ρ x₀ i)).Nonempty},
        ENNReal.ofReal (partitionSummand (I := I) ρ x₀ i.val y) =
      ENNReal.ofReal (∑ᶠ i : M, partitionSummand (I := I) ρ x₀ i y) := by
  have hfin : (Function.support fun i : M ↦ partitionSummand (I := I) ρ x₀ i y).Finite :=
    (locallyFinite_partitionSummand (I := I) ρ x₀).point_finite ⟨y, hy⟩
  rw [tsum_subtype_eq_of_support_subset
      (s := {i : M | ((extChartAt I x₀).target ∩
        Function.support (partitionSummand (I := I) ρ x₀ i)).Nonempty})
      (f := fun i ↦ ENNReal.ofReal (partitionSummand (I := I) ρ x₀ i y))
      (fun i hi ↦ ⟨y, hy, fun h0 ↦ hi (by simp [h0])⟩),
    ← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ partitionSummand_nonneg (I := I) ρ x₀ i y)
      (summable_of_hasFiniteSupport hfin),
    tsum_eq_finsum hfin]

/-- Pushing the partition-of-unity sum of local chart measures forward into chart `x₀` yields
the finsum density `∑ᶠ i, partitionSummand ρ x₀ i`. -/
private theorem map_restrict_sum_localChartMeasure (ν : Measure E) [ν.IsAddHaarMeasure]
    (ρ : PartitionOfUnity M M univ) (hρ : ρ.IsSubordinate fun x : M ↦ (chartAt H x).source)
    (x₀ : M) :
    (((Measure.sum fun i : M ↦ (chartAt H i).localChartMeasure I ν (ρ i)).restrict
        (extChartAt I x₀).source).map (extChartAt I x₀)) =
      (ν.restrict (extChartAt I x₀).target).withDensity
        fun y ↦ ENNReal.ofReal (∑ᶠ i : M, partitionSummand (I := I) ρ x₀ i y) := by
  classical
  set S := {i : M | ((extChartAt I x₀).target ∩
    Function.support (partitionSummand (I := I) ρ x₀ i)).Nonempty}
  have : Countable S := (countable_support_partitionSummand (I := I) ρ x₀).to_subtype
  have hT₀ : MeasurableSet (extChartAt I x₀).target := (chartAt H x₀).measurableSet_extend_target I
  ext A hA
  have hpre := (chartAt H x₀).measurableSet_preimage_extend_inter I hA
  rw [extChartAt_source]
  conv_lhs => rw [extChartAt_eq_extend]
  rw [(chartAt H x₀).map_restrict_extend_apply I _ hA, Measure.sum_apply _ hpre,
    withDensity_apply _ hA, Measure.restrict_restrict hA]
  have hterm (i : M) : (chartAt H i).localChartMeasure I ν (ρ i)
      ((chartAt H x₀).extend I ⁻¹' A ∩ (chartAt H x₀).source) =
      ∫⁻ y in A ∩ (extChartAt I x₀).target,
        ENNReal.ofReal (partitionSummand (I := I) ρ x₀ i y) ∂ν := by
    rw [← (chartAt H x₀).map_restrict_extend_apply I _ hA, ← extChartAt_eq_extend]
    exact (chartAt H x₀).map_restrict_localChartMeasure_apply (chartAt H i) I
      (IsManifold.chart_mem_maximalAtlas x₀) (IsManifold.chart_mem_maximalAtlas i) ν (ρ i) hA
  have haem (i : S) : AEMeasurable
      (fun y ↦ ENNReal.ofReal (partitionSummand (I := I) ρ x₀ i.val y))
      (ν.restrict (A ∩ (extChartAt I x₀).target)) :=
    ((ENNReal.continuous_ofReal.comp_continuousOn
      ((chartAt H x₀).continuousOn_abs_det_fderivWithin_extendCoordChange_mul (chartAt H i.val)
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
theorem exists_isPositiveDensityMeasure [T2Space M] [ParacompactSpace M] :
    ∃ μ : Measure M, IsPositiveDensityMeasure I μ := by
  have : NormalSpace M := NormalSpace.of_paracompactSpace_r1Space
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate (X := M) isClosed_univ
    (fun x : M ↦ (chartAt H x).source) (fun x ↦ (chartAt H x).open_source)
    fun x _ ↦ mem_iUnion.2 ⟨x, mem_chart_source H x⟩
  let ν : Measure E := (Module.finBasis ℝ E).addHaar
  refine ⟨Measure.sum fun i : M ↦ (chartAt H i).localChartMeasure I ν (ρ i),
    (isPositiveDensityMeasure_iff_of_isAddHaarMeasure ν).2 fun x₀ ↦
      ⟨fun y ↦ ∑ᶠ i : M, partitionSummand (I := I) ρ x₀ i y,
        continuousOn_finsum_partitionSummand (I := I) ρ hρ x₀,
        fun _ hy ↦ finsum_partitionSummand_pos (I := I) ρ hρ x₀ hy,
        map_restrict_sum_localChartMeasure (I := I) ν ρ hρ x₀⟩⟩

/-- Every Hausdorff Lindelöf finite-dimensional `C¹` manifold admits a positive continuous density
measure. -/
theorem exists_isPositiveDensityMeasure_of_lindelof [T2Space M] [LindelofSpace M] :
    ∃ μ : Measure M, IsPositiveDensityMeasure I μ := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : SecondCountableTopology H := I.secondCountableTopology
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_lindelof H M
  have : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : ParacompactSpace M := paracompact_of_locallyCompact_sigmaCompact
  exact exists_isPositiveDensityMeasure (I := I)

end Existence

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover
public import TauCeti.Geometry.Manifold.VectorBundle.Section.TestFunction
public import TauCeti.Geometry.Manifold.PartitionOfUnity.ChartCutoffs
import TauCeti.Analysis.Distribution.TestFunction.WeakWhitney
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Chart localization of smooth bundle sections

A smooth section of a vector bundle can be multiplied by a smooth cutoff supported in a coordinate
chart and read in a bundle frame as a native test function on the chart target. This file defines
the chart localization map and proves continuity of the unweighted chart-coefficient map, chart
localizations, and fixed-support chart-coefficient readbacks for the compact derivative frame
topology.

Let `c` be a chart with `C^n` inverse, `t` a bundle trivialization over its source, and `ψ` a
`C^n` scalar function whose closed support is mapped by `c` into a compact subset `L` of the chart
target. The *chart localization* `Bundle.Trivialization.chartLocalization` reads `ψ • s` through
the unweighted chart-coefficient map `Bundle.Trivialization.chartCoeffLinearMap` as a native test
function supported in `L`. Continuity of `Bundle.Trivialization.chartCoeffLinearMap` on the
submodule `ContMDiffSection.zeroOffInChart` (`Bundle.Trivialization.continuous_chartCoeffLinearMap`)
immediately yields continuity of both `Bundle.Trivialization.chartLocalization` and the
fixed-support coefficient map `Bundle.Trivialization.chartTestCoeff`
(`Bundle.Trivialization.continuous_chartLocalization`,
`Bundle.Trivialization.continuous_chartTestCoeff`). Extending the localization back through the
chart recovers `ψ • s` when `tsupport ψ ⊆ c.source`
(`Bundle.Trivialization.chartTestSection_chartLocalization`).

For chart cutoffs (`TauCeti.ChartCutoffs`) every section supported in a compact set `K` is the sum
of these pieces over the cutoffs meeting `K`
(`TauCeti.ChartCutoffs.sum_chartTestSection_chartLocalization`).

## Main declarations

* `Bundle.Trivialization.chartLocalization`: the chart localization of sections, a linear map into
  the test functions supported in a fixed compact set.
* `Bundle.Trivialization.continuous_chartCoeffLinearMap`: continuity of the unweighted chart
  coefficient map on `ContMDiffSection.zeroOffInChart` for the subspace frame topology.
* `Bundle.Trivialization.continuous_chartLocalization` and
  `Bundle.Trivialization.continuous_chartTestCoeff`: continuity of chart localizations and
  fixed-support chart coefficients for the frame topology.
* `Bundle.Trivialization.chartTestSection_chartLocalization`: extending the localization through
  the chart recovers `ψ • s`.
* `TauCeti.ChartCutoffs.sum_chartTestSection_chartLocalization`: a section supported in a compact
  set is the sum of the chart extensions of its localizations along chart cutoffs.
* `TauCeti.baseSetChart`: the chart at a point restricted to the base set of the trivialization
  there and read in the model space, with `TauCeti.coe_baseSetChart` and
  `TauCeti.eqOn_baseSetChart_extChartAt`.
* `TauCeti.exists_chart_source_subset_baseSet`: on a boundaryless manifold, every point lies in a
  smooth chart into the model space with smooth inverse, inside the base set of the trivialization
  at that point.
* `TauCeti.ChartCutoffs.exists_source_subset_baseSet`: on a boundaryless Hausdorff `σ`-compact
  manifold, chart cutoffs whose charts lie inside the base sets of the trivializations.
* `ContMDiffSection.ChartTestData`: a trivialization together with a chart smooth on its source
  inside the base set, indexing the chart extensions `ChartTestData.chartTestSection`.

The fixed-support part rests on
`ContDiffMapSupportedIn.continuous_iff_continuous_toContMDiffMap`: on a fixed compact support, the
topology of test functions is the weak Whitney topology.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, 2nd ed., §6.3, for test
  functions and distributions on manifolds through partitions of unity subordinate to charts.
-/

public noncomputable section

open Bundle Set TopologicalSpace Topology
open scoped ContDiff Manifold Distributions TauCeti.ManifoldWeakWhitney

namespace Bundle.Trivialization

open ContMDiffSection

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞} [ContMDiffVectorBundle n F V I]
  (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
  (c : OpenPartialHomeomorph M E)
  (hc : ContMDiffOn 𝓘(ℝ, E) I n c.symm c.target) (hct : c.source ⊆ t.baseSet)

/-- The chart source, as an open subset of `M` contained in the base set of `t`. -/
private abbrev chartSource : Opens M := ⟨c.source, c.open_source⟩

section Localization

variable (ψ : C^n⟮I, M; ℝ⟯) (L : Compacts E) (hL : (L : Set E) ⊆ c.target)
  (hψ : MapsTo c (tsupport ψ) L)

include hψ in
omit [ContMDiffVectorBundle n F V I] in
private theorem smul_apply_symm_eq_zero (s : Cₛ^n⟮I; F, V⟯) {y : E} (hyc : y ∈ c.target)
    (hyL : y ∉ L) : (ψ • s) (c.symm y) = 0 := by
  rw [ContMDiffSection.smul_apply, image_eq_zero_of_notMem_tsupport
    (fun h ↦ hyL (c.right_inv hyc ▸ hψ h)), zero_smul]

/-- The **chart localization** of sections: a section `s` goes to the native test function
`y ↦ ψ (c⁻¹ y) • (t (s (c⁻¹ y))).2` on the chart target, extended by zero, which is supported in
the compact set `L`. -/
def chartLocalization : Cₛ^n⟮I; F, V⟯ →ₗ[ℝ] 𝓓^{n}_{L}(E, F) :=
  (t.chartCoeffLinearMap c hc hct hL Subset.rfl).comp
    ((smulLinearMap (I := I) (F := F) (V := V) (n := n) ψ).codRestrict
      (zeroOffInChart I F n V c L)
      fun s ↦ mem_zeroOffInChart.2 fun _ hyc hyL ↦ smul_apply_symm_eq_zero c ψ L hψ s hyc hyL)

private theorem chartLocalization_apply (s : Cₛ^n⟮I; F, V⟯) :
    t.chartLocalization c hc hct ψ L hL hψ s =
      t.chartCoeff c hc hct hL Subset.rfl (ψ • s)
        (fun _ hyc hyL ↦ smul_apply_symm_eq_zero c ψ L hψ s hyc hyL) := by
  dsimp only [chartLocalization, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.codRestrict_apply]
  exact t.chartCoeffLinearMap_apply c hc hct hL Subset.rfl _

/-- On the chart target the chart localization is `ψ` times the frame coefficients. -/
theorem chartLocalization_apply_of_mem (s : Cₛ^n⟮I; F, V⟯) {y : E} (hy : y ∈ c.target) :
    t.chartLocalization c hc hct ψ L hL hψ s y = ψ (c.symm y) • (t ⟨c.symm y, s (c.symm y)⟩).2 := by
  rw [chartLocalization_apply, chartCoeff_apply_of_mem t c hc hct hL Subset.rfl (ψ • s) _ hy,
    ContMDiffSection.smul_apply, map_smul,
    t.continuousLinearMapAt_apply_of_mem (R := ℝ) (hct (c.map_target hy))]

/-- The chart localization vanishes outside the chart target. -/
@[simp]
theorem chartLocalization_apply_of_notMem (s : Cₛ^n⟮I; F, V⟯) {y : E} (hy : y ∉ c.target) :
    t.chartLocalization c hc hct ψ L hL hψ s y = 0 := by
  rw [chartLocalization_apply, chartCoeff_apply_of_notMem t c hc hct hL Subset.rfl (ψ • s) _ hy]

/-- Extending the chart localization back through the chart and frame recovers `ψ • s`, as soon as
the closed support of `ψ` lies in the chart source. -/
theorem chartTestSection_chartLocalization [T2Space M]
    (hc' : ContMDiffOn I 𝓘(ℝ, E) n c c.source) (hψc : tsupport ψ ⊆ c.source)
    (s : Cₛ^n⟮I; F, V⟯) :
    (t.chartTestSection c hc' hct
      (TestFunction.ofSupportedIn hL (t.chartLocalization c hc hct ψ L hL hψ s))).val = ψ • s := by
  rw [chartLocalization_apply]
  exact t.chartTestSection_ofSupportedIn_chartCoeff c hc hct hc' hL Subset.rfl hL (ψ • s)
    (fun _ hyc hyL ↦ smul_apply_symm_eq_zero c ψ L hψ s hyc hyL)
    fun _ hx ↦ by
      rw [ContMDiffSection.smul_apply,
        image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hψc h)), zero_smul]

end Localization

section Continuity

variable [IsManifold I n M] [LocallyCompactSpace E] {ι : Type*}
  (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- **Unweighted chart coefficients are continuous** on the submodule of sections vanishing
outside `L₀` on the chart target, equipped with the subspace topology of the compact derivative
frame topology. -/
theorem continuous_chartCoeffLinearMap (hcover : ∀ x : M, ∃ i, x ∈ U i)
    {L₀ L : Compacts E} (hL₀ : (L₀ : Set E) ⊆ c.target) (hL₀L : (L₀ : Set E) ⊆ L) :
    letI := frameTopology (I := I) (n := n) e U hU
    Continuous (t.chartCoeffLinearMap c hc hct hL₀ hL₀L) := by
  let := frameTopology (I := I) (n := n) e U hU
  have hind : Topology.IsInducing (ContDiffMapSupportedIn.toContMDiffMap :
      𝓓^{n}_{L}(E, F) → C^n⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) := by
    rw [ContMDiffMap.manifoldWeakWhitneyTopology_self]
    exact ContDiffMapSupportedIn.isInducing_toContMDiffMap
  refine hind.continuous_iff.2 ?_
  have hL₀c : IsOpen ((L₀ : Set E)ᶜ) := L₀.isCompact.isClosed.isOpen_compl
  -- Cover `E` by the chart target, where the coefficients are frame coordinates pulled back by
  -- `c.symm`, and by the complement of `L₀`, where they vanish.
  let W : Bool → Opens E := fun b ↦
    bif b then ⟨c.target, c.open_target⟩ else ⟨(L₀ : Set E)ᶜ, hL₀c⟩
  have hW : ∀ y : E, ∃ b, y ∈ W b := fun y ↦ by
    by_cases hy : y ∈ c.target
    · exact ⟨true, hy⟩
    · exact ⟨false, fun h ↦ hy (hL₀ h)⟩
  refine ContMDiffMap.continuous_of_forall_continuous_restrict W hW fun b ↦ ?_
  cases b with
  | false =>
    convert continuous_const (y := (0 : C^n⟮𝓘(ℝ, E), W false; 𝓘(ℝ, F), F⟯)) using 1
    funext s
    ext y
    simp only [Function.comp_apply, ContMDiffMap.restrict_apply,
      ContDiffMapSupportedIn.coe_toContMDiffMap, chartCoeffLinearMap_apply,
      ContMDiffMap.coe_zero, Pi.zero_apply]
    exact t.chartCoeff_eq_zero c hc hct hL₀ hL₀L s.val (mem_zeroOffInChart.1 s.property) y.property
  | true =>
    have hsymm : ContMDiff 𝓘(ℝ, E) I n (fun y : W true ↦ c.symm y) :=
      hc.comp_contMDiff (contMDiff_subtypeVal (U := W true)) fun y ↦ y.property
    let j : C^n⟮𝓘(ℝ, E), W true; I, chartSource c⟯ :=
      ⟨fun y ↦ ⟨c.symm y, c.map_target y.property⟩,
        (TauCeti.ContMDiff.subtypeVal_comp_iff (chartSource c) _).mp hsymm⟩
    have hcoord : Continuous fun s : zeroOffInChart I F n V c L₀ ↦
        t.frameCoordinates (U := chartSource c) hct s.val :=
      (continuous_frameCoordinates_of_cover e U hU hcover t (chartSource c) hct).comp
        continuous_subtypeVal
    have hcomp : Continuous fun s : zeroOffInChart I F n V c L₀ ↦
        (t.frameCoordinates (U := chartSource c) hct s.val).comp j :=
      ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp (hcoord.prodMk continuous_const)
    convert hcomp using 1
    funext s
    ext y
    simp only [Function.comp_apply, ContMDiffMap.restrict_apply,
      ContDiffMapSupportedIn.coe_toContMDiffMap, chartCoeffLinearMap_apply,
      chartCoeff_apply_of_mem t c hc hct hL₀ hL₀L s.val (mem_zeroOffInChart.1 s.property)
        y.property,
      ContMDiffMap.comp_apply, frameCoordinates_apply,
      t.continuousLinearMapAt_apply_of_mem (R := ℝ) (hct (c.map_target y.property))]
    -- Both sides equal `(t ⟨c.symm y, s.val (c.symm y)⟩).2` after unfolding `j`.
    rfl

/-- **Chart localizations are continuous** from the compact derivative topology of a covering
frame system to the topology of test functions supported in `L`. -/
theorem continuous_chartLocalization
    (ψ : C^n⟮I, M; ℝ⟯) (L : Compacts E) (hL : (L : Set E) ⊆ c.target)
    (hψ : MapsTo c (tsupport ψ) L)
    {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    (hcover : ∀ x : M, ∃ i, x ∈ U i) :
    letI := frameTopology (I := I) (n := n) e U hU
    Continuous (t.chartLocalization c hc hct ψ L hL hψ) := by
  let := frameTopology (I := I) (n := n) e U hU
  exact (continuous_chartCoeffLinearMap t c hc hct e U hU hcover hL Subset.rfl).comp
    ((continuous_smul_function_frameTopology e U hU ψ).subtype_mk _)

end Continuity

/-- **Chart localization of supported sections is continuous.** On a fixed compact subset of a
chart source, reading sections in the chart and frame depends continuously on the section from the
compact derivative frame topology to `𝓓^{n}_{L}(E, F)`. -/
theorem continuous_chartTestCoeff [IsManifold I n M] [LocallyCompactSpace E]
    {K : Compacts M} (hK : (K : Set M) ⊆ c.source)
    {L : Compacts E} (hKL : c '' (K : Set M) ⊆ L)
    {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    (hcover : ∀ x : M, ∃ i, x ∈ U i) :
    letI := frameTopology (I := I) (n := n) e U hU
    Continuous (t.chartTestCoeff c hc hct hK hKL) := by
  let := frameTopology (I := I) (n := n) e U hU
  rw [chartTestCoeff_eq_comp]
  exact (continuous_chartCoeffLinearMap t c hc hct e U hU hcover (c.imageCompact_subset_target hK)
    (c.coe_imageCompact hK ▸ hKL)).comp (continuous_subtypeVal.subtype_mk _)

end Bundle.Trivialization

namespace TauCeti.ChartCutoffs

open ContMDiffSection

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞} [ContMDiffVectorBundle n F V I] {ι : Type*}

/-- **Decomposition along chart cutoffs.** A section `s` supported in a compact set `K` is the
sum, over the cutoffs `ρᵢ` meeting `K`, of the chart extensions of its chart localizations along
`ρᵢ`, read in trivializations `tᵢ` of the atlas over the chart sources. -/
theorem sum_chartTestSection_chartLocalization (A : ChartCutoffs I M n ι)
    (t : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (t i)]
    (ht : ∀ i, (A.chart i).source ⊆ (t i).baseSet) {K : Set M} (hK : IsCompact K)
    (s : Cₛ^n⟮I; F, V⟯) (hs : s.tsupport ⊆ K) :
    ∑ i ∈ A.meeting K hK, ((t i).chartTestSection (A.chart i) (A.contMDiffOn_chart i) (ht i)
      (TestFunction.ofSupportedIn (A.chartSupport_subset_target i)
        ((t i).chartLocalization (A.chart i) (A.contMDiffOn_chart_symm i) (ht i) (A.cutoff i)
          (A.chartSupport i) (A.chartSupport_subset_target i) (A.mapsTo_chartSupport i)
            s))).val = s := by
  simp only [Bundle.Trivialization.chartTestSection_chartLocalization _ _ _ _ _ _ _ _
    (A.contMDiffOn_chart _) (A.tsupport_subset _), ← Finset.sum_smul]
  ext y
  rw [ContMDiffSection.smul_apply]
  by_cases hy : y ∈ K
  · rw [ContMDiffMap.coe_sum]
    simp [A.sum_meeting_eq_one hK hy]
  · rw [s.eq_zero_of_notMem_tsupport fun h ↦ hy (hs h), smul_zero]

end TauCeti.ChartCutoffs

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace F]
  (V : M → Type*) [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V]

section BaseSetChart

variable [I.Boundaryless]

variable (I F) in
/-- The chart at `x`, restricted to the base set of the trivialization at `x` and read in the model
space: an open partial homeomorphism onto an open subset of `E` since the model is boundaryless. -/
def baseSetChart (x : M) : OpenPartialHomeomorph M E :=
  ((chartAt H x).restr (trivializationAt F V x).baseSet).extendTrans I (Homeomorph.refl E)

/-- The source of `baseSetChart F I V x` is the part of the chart source over the base set. -/
theorem baseSetChart_source (x : M) :
    (baseSetChart F I V x).source = (chartAt H x).source ∩ (trivializationAt F V x).baseSet := by
  rw [baseSetChart, OpenPartialHomeomorph.extendTrans_source,
    OpenPartialHomeomorph.restr_source' _ _ (trivializationAt F V x).open_baseSet]

/-- As a function, `baseSetChart F I V x` is the extended chart at `x`. -/
theorem coe_baseSetChart (x : M) : ⇑(baseSetChart F I V x) = extChartAt I x := by
  rw [baseSetChart, OpenPartialHomeomorph.coe_extendTrans_refl, OpenPartialHomeomorph.extend_coe,
    extChartAt_coe, OpenPartialHomeomorph.restr_apply]

/-- `baseSetChart F I V x` agrees with the extended chart at `x` on its source, the form in which
restrictions of the extended chart at `x` are taken as hypotheses. -/
theorem eqOn_baseSetChart_extChartAt (x : M) :
    EqOn (baseSetChart F I V x) (extChartAt I x) (baseSetChart F I V x).source :=
  fun y _ ↦ congrFun (coe_baseSetChart V x) y

/-- The extended chart at `x` inverts `baseSetChart F I V x` on its target. -/
theorem extChartAt_baseSetChart_symm (x : M) {z : E} (hz : z ∈ (baseSetChart F I V x).target) :
    extChartAt I x ((baseSetChart F I V x).symm z) = z := by
  rw [← coe_baseSetChart (F := F) V x, (baseSetChart F I V x).right_inv hz]

/-- The point `x` lies in the source of `baseSetChart F I V x`. -/
theorem mem_baseSetChart_source (x : M) : x ∈ (baseSetChart F I V x).source := by
  rw [baseSetChart_source]
  exact ⟨mem_chart_source H x, FiberBundle.mem_baseSet_trivializationAt' x⟩

/-- The source of `baseSetChart F I V x` lies in the base set of the trivialization at `x`. -/
theorem baseSetChart_source_subset (x : M) :
    (baseSetChart F I V x).source ⊆ (trivializationAt F V x).baseSet := by
  rw [baseSetChart_source]
  exact inter_subset_right

omit [I.Boundaryless] in
private theorem restr_chartAt_mem_maximalAtlas {n : ℕ∞ω} [IsManifold I n M] (x : M) :
    (chartAt H x).restr (trivializationAt F V x).baseSet ∈ IsManifold.maximalAtlas I n M :=
  restr_mem_maximalAtlas _ (IsManifold.chart_mem_maximalAtlas x)
    (trivializationAt F V x).open_baseSet

/-- `baseSetChart F I V x` is smooth on its source. -/
theorem contMDiffOn_baseSetChart {n : ℕ∞ω} [IsManifold I n M] (x : M) :
    ContMDiffOn I 𝓘(ℝ, E) n (baseSetChart F I V x) (baseSetChart F I V x).source :=
  OpenPartialHomeomorph.contMDiffOn_extendTrans _ (restr_chartAt_mem_maximalAtlas V x) contDiff_id

/-- The inverse of `baseSetChart F I V x` is smooth on its target. -/
theorem contMDiffOn_baseSetChart_symm {n : ℕ∞ω} [IsManifold I n M] (x : M) :
    ContMDiffOn 𝓘(ℝ, E) I n (baseSetChart F I V x).symm (baseSetChart F I V x).target :=
  OpenPartialHomeomorph.contMDiffOn_extendTrans_symm _ (restr_chartAt_mem_maximalAtlas V x)
    contDiff_id

variable (I F) in
/-- On a boundaryless Hausdorff `σ`-compact manifold with finite-dimensional model, there are chart
cutoffs whose chart at each point `x` has its source in the base set of the trivialization at
`x`. -/
theorem ChartCutoffs.exists_source_subset_baseSet {n : ℕ∞} [FiniteDimensional ℝ E]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] :
    ∃ A : ChartCutoffs I M n M,
      ∀ x, (A.chart x).source ⊆ (trivializationAt F V x).baseSet :=
  ChartCutoffs.exists_source_subset (fun x ↦ (trivializationAt F V x).open_baseSet)
    (FiberBundle.mem_baseSet_trivializationAt' ·)

end BaseSetChart

variable (I F) in
/-- On a boundaryless manifold, every point `x` lies in the source of a smooth chart into the
model space with smooth inverse, whose source lies in the base set of the trivialization at `x`. -/
theorem exists_chart_source_subset_baseSet {n : ℕ∞ω} [IsManifold I n M]
    [BoundarylessManifold I M] (x : M) :
    ∃ c : OpenPartialHomeomorph M E, ContMDiffOn I 𝓘(ℝ, E) n c c.source ∧
      ContMDiffOn 𝓘(ℝ, E) I n c.symm c.target ∧ c.source ⊆ (trivializationAt F V x).baseSet ∧
      x ∈ c.source :=
  exists_chart_source_subset (trivializationAt F V x).open_baseSet
    (mem_baseSet_trivializationAt F V x)

end TauCeti

namespace ContMDiffSection

open Bundle.Trivialization

section ChartTestData

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] (n : ℕ∞)

/-- The data of a chart extension of native test functions: a trivialization of the atlas
together with a chart that is `C^n` on its source and whose source lies in the base set. -/
structure ChartTestData where
  /-- The trivialization giving the bundle frame. -/
  trivialization : Trivialization F (π F V)
  /-- The trivialization belongs to the atlas of the fiber bundle. -/
  [memTrivializationAtlas : MemTrivializationAtlas trivialization]
  /-- The coordinate chart. -/
  chart : OpenPartialHomeomorph M E
  /-- The chart is `C^n` on its source. -/
  contMDiffOn_chart : ContMDiffOn I 𝓘(ℝ, E) n chart chart.source
  /-- The chart source lies in the base set of the trivialization. -/
  source_subset : chart.source ⊆ trivialization.baseSet

variable {I F V n} [T2Space M] [ContMDiffVectorBundle n F V I]

/-- The chart extension of native test functions given by chart data. -/
def ChartTestData.chartTestSection (p : ChartTestData I F V n) :
    𝓓^{n}(⟨p.chart.target, p.chart.open_target⟩, F) →ₗ[ℝ] compactlySupported I F n V :=
  letI := p.memTrivializationAtlas
  p.trivialization.chartTestSection p.chart p.contMDiffOn_chart p.source_subset

/-- The chart extension indexed by chart data is the chart extension of its trivialization and
chart. -/
@[simp]
theorem ChartTestData.chartTestSection_def (p : ChartTestData I F V n) :
    letI := p.memTrivializationAtlas
    p.chartTestSection =
      p.trivialization.chartTestSection p.chart p.contMDiffOn_chart p.source_subset :=
  (rfl)

end ChartTestData

end ContMDiffSection

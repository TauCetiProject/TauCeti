/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.CompactSupport.Topology
public import TauCeti.Geometry.Manifold.PartitionOfUnity.ChartCutoffs
public import TauCeti.Geometry.Manifold.VectorBundle.Trivialization
import TauCeti.Analysis.Distribution.TestFunction.WeakWhitney
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact

/-!
# Chart localization of bundle tests

A compactly supported smooth section of a vector bundle can be cut into pieces supported in
coordinate charts, and each piece read in a bundle frame is a native test function on the chart
target. This module establishes frame-topology continuity of chart reading and cutoff localization
(`Bundle.Trivialization.continuous_chartReadSupportedIn`,
`Bundle.Trivialization.continuous_chartReadTestFunction`,
`Bundle.Trivialization.continuous_chartCutoffTestFunction`), the continuous linear equivalence
`Bundle.Trivialization.chartTestSectionEquiv` when a chart covers `M`, as well as the finite cutoff
decomposition of sections supported in a compact set under any two-sided `C^n` chart/frame cover
(`ContMDiffSection.exists_ofSupportedIn_eq_sum_chartCutoffTestFunction`), without depending on the
compact-support inductive topology.

In particular, every compactly supported `C^n` section is a finite sum of chart extensions of
native test functions for any covering family of two-sided `C^n` charts subordinate to atlas
trivializations (`ContMDiffSection.span_iUnion_range_chartTestSection_eq_top_of_chart_cover`), and
on a boundaryless Hausdorff manifold for all `ChartTestData`
(`ContMDiffSection.span_iUnion_range_chartTestSection_eq_top`), using the subordinate smooth chart
at each point (`TauCeti.bundleChartAt`).

For chart cutoffs (`TauCeti.ChartCutoffs`) every section supported in a compact set `K` is the sum
of the pieces `Bundle.Trivialization.chartLocalization` over the cutoffs meeting `K`
(`TauCeti.ChartCutoffs.sum_chartTestSection_chartLocalization`). On a boundaryless, Hausdorff,
`σ`-compact manifold with finite-dimensional model, chart cutoffs exist for charts inside the base
sets of trivializations (`TauCeti.ChartCutoffs.exists_source_subset_baseSet`), yielding
`ContMDiffSection.compactlySupportedTopology_eq_finalLocallyConvexTopology_chartTestSection` and
`ContMDiffSection.continuous_compactlySupportedTopology_iff_chartTestSection` (which are also
obtained without `σ`-compactness or `C^∞` regularity in
`TauCeti.Geometry.Manifold.VectorBundle.Section.CompactSupport.FinalTopology`).

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

section ChartReadContinuity

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞} [ContMDiffVectorBundle n F V I] [IsManifold I n M] [LocallyCompactSpace E]
  (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
  (c : OpenPartialHomeomorph M E)
  (hc_symm : ContMDiffOn 𝓘(ℝ, E) I n c.symm c.target) (hct : c.source ⊆ t.baseSet)
  {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- Reading sections supported in a compact subset `K ⊆ c.source` in a chart `c` with `C^n`
inverse subordinate to `t` is continuous from any smooth frame topology whose domains cover `K`
into `𝓓^{n}_{c '' K}(E, F)`. -/
theorem continuous_chartReadSupportedIn {K : Compacts M} (hKc : (K : Set M) ⊆ c.source)
    (hcover : ∀ x ∈ (K : Set M), ∃ i, x ∈ U i) :
    letI := frameTopology (I := I) (n := n) e U hU
    Continuous (t.chartReadSupportedIn c hc_symm hct hKc) := by
  let := frameTopology (I := I) (n := n) e U hU
  let K' : Compacts E := ⟨c '' (K : Set M), K.isCompact.image_of_continuousOn
    (c.continuousOn.mono hKc)⟩
  refine ContDiffMapSupportedIn.continuous_iff_continuous_toContMDiffMap.2 ?_
  suffices h : Continuous (fun s : supportedIn I F n V K ↦
      ContDiffMapSupportedIn.toContMDiffMap (t.chartReadSupportedIn c hc_symm hct hKc s)) by
    rwa [ContMDiffMap.manifoldWeakWhitneyTopology_self] at h
  have hVopen : IsOpen (⋃ i, (U i : Set M)) := isOpen_iUnion fun i ↦ (U i).isOpen
  have hWtrue : IsOpen (c.target ∩ c.symm ⁻¹' (⋃ i, (U i : Set M))) :=
    c.continuousOn_symm.isOpen_inter_preimage c.open_target hVopen
  let W : Bool → Opens E := fun b ↦
    bif b then ⟨c.target ∩ c.symm ⁻¹' (⋃ i, (U i : Set M)), hWtrue⟩
    else ⟨(K' : Set E)ᶜ, K'.isCompact.isClosed.isOpen_compl⟩
  have hW : ∀ y : E, ∃ b, y ∈ W b := fun y ↦ by
    by_cases hy : y ∈ (K' : Set E)
    · obtain ⟨x, hxK, rfl⟩ := hy
      exact ⟨true, c.map_source (hKc hxK), by simpa [c.left_inv (hKc hxK)] using hcover x hxK⟩
    · exact ⟨false, hy⟩
  refine ContMDiffMap.continuous_of_forall_continuous_restrict W hW fun b ↦ ?_
  cases b with
  | false =>
    convert continuous_const (y := (0 : C^n⟮𝓘(ℝ, E), W false; 𝓘(ℝ, F), F⟯)) using 1
    funext s
    ext y
    rw [ContMDiffMap.restrict_apply, ContDiffMapSupportedIn.coe_toContMDiffMap,
      (t.chartReadSupportedIn c hc_symm hct hKc s).zero_on_compl y.property]
    simp
  | true =>
    let Uc : Opens M := ⟨c.source ∩ ⋃ i, (U i : Set M), c.open_source.inter hVopen⟩
    have hUct : (Uc : Set M) ⊆ t.baseSet := inter_subset_left.trans hct
    let j : C^n⟮𝓘(ℝ, E), W true; I, Uc⟯ :=
      ⟨fun y ↦ ⟨c.symm y, c.map_target y.property.1, y.property.2⟩,
        (TauCeti.ContMDiff.subtypeVal_comp_iff Uc _).mp
          (hc_symm.comp_contMDiff contMDiff_subtypeVal fun y ↦ y.property.1)⟩
    have hcoord : Continuous (fun s : supportedIn I F n V K ↦
        t.frameCoordinates (I := I) (n := n) (U := Uc) hUct s.val) :=
      (continuous_frameCoordinates_of_subset_iUnion e U hU t Uc hUct
        inter_subset_right).comp continuous_subtypeVal
    refine (ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp
      (hcoord.prodMk (continuous_const (y := j)))).congr fun s ↦ ?_
    ext y
    rw [Function.comp_apply, ContMDiffMap.comp_apply]
    simp [j, t.chartReadSupportedIn_apply_of_mem c hc_symm hct hKc s y.property.1,
      hUct ⟨c.map_target y.property.1, y.property.2⟩]

/-- Reading sections supported in `K ⊆ c.source` as native test functions on `c.target` is
continuous from any smooth frame topology whose domains cover `K`. -/
theorem continuous_chartReadTestFunction {K : Compacts M} (hKc : (K : Set M) ⊆ c.source)
    (hcover : ∀ x ∈ (K : Set M), ∃ i, x ∈ U i) :
    letI := frameTopology (I := I) (n := n) e U hU
    Continuous (t.chartReadTestFunction c hc_symm hct hKc) := by
  let := frameTopology (I := I) (n := n) e U hU
  let K' : Compacts E :=
    ⟨c '' (K : Set M), K.isCompact.image_of_continuousOn (c.continuousOn.mono hKc)⟩
  have hK't : (K' : Set E) ⊆ (⟨c.target, c.open_target⟩ : Opens E) :=
    image_subset_iff.2 fun _ hx ↦ c.map_source (hKc hx)
  refine ((TestFunction.ofSupportedInCLM ℝ hK't).continuous.comp
    (t.continuous_chartReadSupportedIn c hc_symm hct e U hU hKc hcover)).congr fun s ↦ ?_
  ext y
  simp [TestFunction.coe_ofSupportedInCLM, t.chartReadSupportedIn_apply,
    t.chartReadTestFunction_apply]

/-- Localizing sections by a compactly supported `C^n` cutoff `ρ` with `tsupport ρ ⊆ c.source`
and reading the result in `t` and `c` is continuous from any smooth frame topology whose domains
cover `tsupport ρ` into `𝓓^{n}(⟨c.target, c.open_target⟩, F)`. -/
theorem continuous_chartCutoffTestFunction
    (ρ : C^n⟮I, M; ℝ⟯) (hρc : HasCompactSupport ρ) (hρs : _root_.tsupport ρ ⊆ c.source)
    (hcover : ∀ x ∈ _root_.tsupport ρ, ∃ i, x ∈ U i) :
    letI := frameTopology (I := I) (n := n) e U hU
    Continuous (t.chartCutoffTestFunction c hc_symm hct ρ hρc hρs) := by
  let := frameTopology (I := I) (n := n) e U hU
  let Kρ : Compacts M := ⟨_root_.tsupport ρ, hρc⟩
  refine ((t.continuous_chartReadTestFunction c hc_symm hct e U hU (K := Kρ) hρs hcover).comp
    ((continuous_smul_function_frameTopology e U hU ρ).subtype_mk fun s ↦
      mem_supportedIn.2 ((tsupport_smul_function_subset ρ s).trans inter_subset_left))).congr
    fun s ↦ ?_
  ext y
  simp [t.chartCutoffTestFunction_apply, t.chartReadTestFunction_apply]

end ChartReadContinuity

section ChartTestSectionEquiv

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
  (hc_symm : ContMDiffOn 𝓘(ℝ, E) I n c.symm c.target)
  (hct : c.source ⊆ t.baseSet)

private def chartTestSectionInv (hc_univ : c.source = univ) :
    compactlySupported I F n V →ₗ[ℝ] 𝓓^{n}(⟨c.target, c.open_target⟩, F) where
  toFun s :=
    t.chartReadTestFunction c hc_symm hct
      (K := ⟨s.val.tsupport, mem_compactlySupported.1 s.property⟩)
      ((subset_univ _).trans hc_univ.symm.subset) ⟨s.val, mem_supportedIn.2 Subset.rfl⟩
  map_add' s₁ s₂ := by
    ext y
    by_cases hy : y ∈ c.target <;> simp [t.chartReadTestFunction_apply, hy]
  map_smul' a s := by
    ext y
    by_cases hy : y ∈ c.target <;> simp [t.chartReadTestFunction_apply, hy]

private theorem chartTestSectionInv_apply (hc_univ : c.source = univ)
    (s : compactlySupported I F n V) :
    t.chartTestSectionInv c hc_symm hct hc_univ s =
      t.chartReadTestFunction c hc_symm hct
        (K := ⟨s.val.tsupport, mem_compactlySupported.1 s.property⟩)
        ((subset_univ _).trans hc_univ.symm.subset) ⟨s.val, mem_supportedIn.2 Subset.rfl⟩ :=
  rfl

variable [LocallyCompactSpace E] [IsManifold I n M]
  {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  (hcover : ∀ x : M, ∃ i, x ∈ U i)

include hcover in
private theorem continuous_chartTestSectionInv (hc_univ : c.source = univ) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    Continuous (t.chartTestSectionInv c hc_symm hct hc_univ) := by
  let := frameTopology (I := I) (n := n) e U hU
  let := compactlySupportedTopology (I := I) (n := n) e U hU
  refine (continuous_compactlySupportedTopology_iff e U hU
    (t.chartTestSectionInv c hc_symm hct hc_univ)).2 fun K ↦ ?_
  refine (t.continuous_chartReadTestFunction c hc_symm hct e U hU
    ((subset_univ _).trans hc_univ.symm.subset) fun x _ ↦ hcover x).congr fun s ↦ ?_
  ext y
  simp only [Function.comp_apply, chartTestSectionInv_apply, t.chartReadTestFunction_apply,
    ofSupportedIn_apply]

/-- When a two-sided `C^n` chart `c` subordinate to a smooth bundle trivialization `t` has
`c.source = univ`, extending native test functions by `t.chartTestSection` is a continuous linear
equivalence onto `compactlySupported I F n V` with its fixed-compact inductive topology. -/
def chartTestSectionEquiv [T2Space M] (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source)
    (hc_univ : c.source = univ) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    𝓓^{n}(⟨c.target, c.open_target⟩, F) ≃L[ℝ] compactlySupported I F n V :=
  letI := compactlySupportedTopology (I := I) (n := n) e U hU
  have hright : Function.RightInverse (t.chartTestSectionInv c hc_symm hct hc_univ)
      (t.chartTestSection c hc hct) := fun s ↦ by
    rw [t.chartTestSectionInv_apply, t.chartTestSection_chartReadTestFunction c hc_symm hct hc]
    exact Subtype.ext (ofSupportedIn_apply _ _)
  { toLinearEquiv :=
      { toLinearMap := t.chartTestSection c hc hct
        invFun := t.chartTestSectionInv c hc_symm hct hc_univ
        left_inv φ := t.chartTestSection_injective c hc hct (hright (t.chartTestSection c hc hct φ))
        right_inv := hright }
    continuous_toFun := t.continuous_chartTestSection c hc hct e U hU
    continuous_invFun := t.continuous_chartTestSectionInv c hc_symm hct e U hU hcover hc_univ }

@[simp]
theorem chartTestSectionEquiv_apply [T2Space M] (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source)
    (hc_univ : c.source = univ) (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F)) :
    t.chartTestSectionEquiv c hc_symm hct e U hU hcover hc hc_univ φ =
      t.chartTestSection c hc hct φ :=
  (rfl)

private theorem chartTestSectionEquiv_symm_apply [T2Space M]
    (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source) (hc_univ : c.source = univ)
    (s : compactlySupported I F n V) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    (t.chartTestSectionEquiv c hc_symm hct e U hU hcover hc hc_univ).symm s =
      t.chartTestSectionInv c hc_symm hct hc_univ s :=
  rfl

/-- On the chart target, the inverse of `chartTestSectionEquiv` reads the section in `t` along
`c.symm`. -/
theorem chartTestSectionEquiv_symm_apply_of_mem [T2Space M]
    (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source) (hc_univ : c.source = univ)
    (s : compactlySupported I F n V) {y : E} (hy : y ∈ c.target) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    (t.chartTestSectionEquiv c hc_symm hct e U hU hcover hc hc_univ).symm s y =
      t.continuousLinearMapAt ℝ (c.symm y) (s.val (c.symm y)) := by
  let := compactlySupportedTopology (I := I) (n := n) e U hU
  rw [t.chartTestSectionEquiv_symm_apply c hc_symm hct e U hU hcover hc hc_univ s,
    t.chartTestSectionInv_apply]
  exact t.chartReadTestFunction_apply_of_mem c hc_symm hct _ _ hy

/-- Outside the chart target, the inverse of `chartTestSectionEquiv` vanishes. -/
@[simp]
theorem chartTestSectionEquiv_symm_apply_of_notMem [T2Space M]
    (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source) (hc_univ : c.source = univ)
    (s : compactlySupported I F n V) {y : E} (hy : y ∉ c.target) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    (t.chartTestSectionEquiv c hc_symm hct e U hU hcover hc hc_univ).symm s y = 0 := by
  let := compactlySupportedTopology (I := I) (n := n) e U hU
  rw [t.chartTestSectionEquiv_symm_apply c hc_symm hct e U hU hcover hc hc_univ s,
    t.chartTestSectionInv_apply]
  exact t.chartReadTestFunction_apply_of_notMem c hc_symm hct _ _ hy

end ChartTestSectionEquiv

section ChartLocalization

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
  (ψ : C^n⟮I, M; ℝ⟯) (L : Compacts E) (hL : (L : Set E) ⊆ c.target)
  (hψ : MapsTo c (tsupport ψ) L)

/-- The chart source, as an open subset of `M` contained in the base set of `t`. -/
private abbrev chartSource : Opens M := ⟨c.source, c.open_source⟩

/-- The values of the chart localization: on the chart target, the frame coefficients of `s` at
`c⁻¹ y`, multiplied by `ψ (c⁻¹ y)`; zero elsewhere. -/
private def localizationFun (s : Cₛ^n⟮I; F, V⟯) (y : E) : F :=
  open scoped Classical in
  if hy : y ∈ c.target then
    ψ (c.symm y) • t.frameCoordinates (U := chartSource c) hct s ⟨c.symm y, c.map_target hy⟩
  else 0

private theorem localizationFun_of_mem (s : Cₛ^n⟮I; F, V⟯) {y : E} (hy : y ∈ c.target) :
    localizationFun t c hct ψ s y = ψ (c.symm y) • (t ⟨c.symm y, s (c.symm y)⟩).2 := by
  simp [localizationFun, hy]

private theorem localizationFun_of_notMem (s : Cₛ^n⟮I; F, V⟯) {y : E} (hy : y ∉ c.target) :
    localizationFun t c hct ψ s y = 0 := by
  simp [localizationFun, hy]

include hψ in
private theorem localizationFun_eq_zero (s : Cₛ^n⟮I; F, V⟯) {y : E} (hy : y ∉ L) :
    localizationFun t c hct ψ s y = 0 := by
  by_cases hyc : y ∈ c.target
  · rw [localizationFun_of_mem t c hct ψ s hyc, image_eq_zero_of_notMem_tsupport
      (fun h ↦ hy (c.right_inv hyc ▸ hψ h)), zero_smul]
  · exact localizationFun_of_notMem t c hct ψ s hyc

private theorem localizationFun_add (s s' : Cₛ^n⟮I; F, V⟯) :
    localizationFun t c hct ψ (s + s') =
      localizationFun t c hct ψ s + localizationFun t c hct ψ s' := by
  ext y
  by_cases hy : y ∈ c.target <;> simp [localizationFun, hy]

private theorem localizationFun_smul (a : ℝ) (s : Cₛ^n⟮I; F, V⟯) :
    localizationFun t c hct ψ (a • s) = a • localizationFun t c hct ψ s := by
  ext y
  by_cases hy : y ∈ c.target <;> simp [localizationFun, hy, smul_comm a]

include hc hL hψ in
private theorem contDiff_localizationFun (s : Cₛ^n⟮I; F, V⟯) :
    ContDiff ℝ n (localizationFun t c hct ψ s) := by
  refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
  by_cases hy : y ∈ c.target
  · -- On the chart target the localization is a product of smooth coordinate expressions.
    have hsy : ContMDiffAt I 𝓘(ℝ, F) n (fun x ↦ (t ⟨x, s x⟩).2) (c.symm y) :=
      (t.contMDiffAt_section_iff (hct (c.map_target hy))).1 (s.contMDiff _)
    have hcy : ContMDiffAt 𝓘(ℝ, E) I n c.symm y := hc.contMDiffAt (c.open_target.mem_nhds hy)
    have h : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) n
        (fun y ↦ ψ (c.symm y) • (t ⟨c.symm y, s (c.symm y)⟩).2) y :=
      ((ψ.contMDiff.contMDiffAt).comp y hcy).smul (hsy.comp y hcy)
    refine (contMDiffAt_iff_contDiffAt.1 h).congr_of_eventuallyEq ?_
    filter_upwards [c.open_target.mem_nhds hy] with z hz
    exact localizationFun_of_mem t c hct ψ s hz
  · -- Off the chart target the point lies outside the compact set `L`, where all values vanish.
    have hyL : y ∉ L := fun h ↦ hy (hL h)
    refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [L.isCompact.isClosed.isOpen_compl.mem_nhds hyL] with z hz
    exact localizationFun_eq_zero t c hct ψ L hψ s hz

/-- The **chart localization** of sections: a section `s` goes to the native test function
`y ↦ ψ (c⁻¹ y) • (t (s (c⁻¹ y))).2` on the chart target, extended by zero, which is supported in
the compact set `L`. -/
def chartLocalization : Cₛ^n⟮I; F, V⟯ →ₗ[ℝ] 𝓓^{n}_{L}(E, F) where
  toFun s := ContDiffMapSupportedIn.of_support_subset
    (contDiff_localizationFun t c hc hct ψ L hL hψ s) fun y hy ↦ by
      by_contra hyL
      exact hy (localizationFun_eq_zero t c hct ψ L hψ s hyL)
  map_add' s s' := ContDiffMapSupportedIn.ext fun y ↦
    congrFun (localizationFun_add t c hct ψ s s') y
  map_smul' a s := ContDiffMapSupportedIn.ext fun y ↦
    congrFun (localizationFun_smul t c hct ψ a s) y

/-- On the chart target the chart localization is `ψ` times the frame coefficients. -/
theorem chartLocalization_apply_of_mem (s : Cₛ^n⟮I; F, V⟯) {y : E} (hy : y ∈ c.target) :
    t.chartLocalization c hc hct ψ L hL hψ s y = ψ (c.symm y) • (t ⟨c.symm y, s (c.symm y)⟩).2 :=
  localizationFun_of_mem t c hct ψ s hy

/-- The chart localization vanishes outside the chart target. -/
@[simp]
theorem chartLocalization_apply_of_notMem (s : Cₛ^n⟮I; F, V⟯) {y : E} (hy : y ∉ c.target) :
    t.chartLocalization c hc hct ψ L hL hψ s y = 0 :=
  localizationFun_of_notMem t c hct ψ s hy

section Continuity

variable [IsManifold I n M] [LocallyCompactSpace E] {ι : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- **Chart localizations are continuous** from the compact derivative topology of a covering
frame system to the topology of test functions supported in `L`. -/
theorem continuous_chartLocalization (hcover : ∀ x : M, ∃ i, x ∈ U i) :
    letI := frameTopology (I := I) (n := n) e U hU
    Continuous (t.chartLocalization c hc hct ψ L hL hψ) := by
  let := frameTopology (I := I) (n := n) e U hU
  rw [ContDiffMapSupportedIn.continuous_iff_continuous_toContMDiffMap]
  suffices h : Continuous fun s ↦ (t.chartLocalization c hc hct ψ L hL hψ s).toContMDiffMap by
    rwa [ContMDiffMap.manifoldWeakWhitneyTopology_self] at h
  have hLc : IsOpen ((L : Set E)ᶜ) := L.isCompact.isClosed.isOpen_compl
  -- Cover `E` by the chart target, where the localization is a coordinate expression, and by the
  -- complement of `L`, where it vanishes.
  let W : Bool → Opens E := fun b ↦ bif b then ⟨c.target, c.open_target⟩ else ⟨(L : Set E)ᶜ, hLc⟩
  have hW : ∀ y : E, ∃ b, y ∈ W b := by
    intro y
    by_cases hy : y ∈ c.target
    · exact ⟨true, hy⟩
    · exact ⟨false, fun h ↦ hy (hL h)⟩
  refine ContMDiffMap.continuous_of_forall_continuous_restrict W hW fun b ↦ ?_
  cases b with
  | false =>
    convert continuous_const (y := (0 : C^n⟮𝓘(ℝ, E), W false; 𝓘(ℝ, F), F⟯)) using 1
    funext s
    ext y
    simp only [ContMDiffMap.restrict_apply, ContDiffMapSupportedIn.coe_toContMDiffMap]
    exact localizationFun_eq_zero t c hct ψ L hψ s y.property
  | true =>
    -- On the chart target, compose the frame coefficients with the inverse chart and multiply by
    -- `ψ ∘ c⁻¹`.
    have hsymm : ContMDiff 𝓘(ℝ, E) I n (fun y : W true ↦ c.symm y) :=
      hc.comp_contMDiff (contMDiff_subtypeVal (U := W true)) fun y ↦ y.property
    let j : C^n⟮𝓘(ℝ, E), W true; I, chartSource c⟯ :=
      ⟨fun y ↦ ⟨c.symm y, c.map_target y.property⟩,
        (TauCeti.ContMDiff.subtypeVal_comp_iff (chartSource c) _).mp hsymm⟩
    let A : C^n⟮𝓘(ℝ, E), W true; 𝓘(ℝ, F →L[ℝ] F), F →L[ℝ] F⟯ :=
      ⟨fun y ↦ ψ (c.symm y) • ContinuousLinearMap.id ℝ F,
        (ψ.contMDiff.comp hsymm).smul contMDiff_const⟩
    have hcomp : Continuous fun s : Cₛ^n⟮I; F, V⟯ ↦
        (t.frameCoordinates (U := chartSource c) hct s).comp j :=
      ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp
        ((continuous_frameCoordinates_of_subset_iUnion e U hU t (chartSource c) hct
          fun x _ ↦ mem_iUnion.2 (hcover x)).prodMk continuous_const)
    convert (ContMDiffMap.continuous_clmApplyLinearMap A).comp hcomp using 1
    funext s
    ext y
    simp only [Function.comp_apply, ContMDiffMap.restrict_apply,
      ContMDiffMap.clmApplyLinearMap_apply, ContMDiffMap.comp_apply,
      ContDiffMapSupportedIn.coe_toContMDiffMap, frameCoordinates_apply]
    exact localizationFun_of_mem t c hct ψ s y.property

end Continuity

variable [T2Space M]

/-- Extending the chart localization back through the chart and frame recovers `ψ • s`, as soon as
the closed support of `ψ` lies in the chart source. -/
theorem chartTestSection_chartLocalization (hc' : ContMDiffOn I 𝓘(ℝ, E) n c c.source)
    (hψc : tsupport ψ ⊆ c.source) (s : Cₛ^n⟮I; F, V⟯) :
    (t.chartTestSection c hc' hct
      (TestFunction.ofSupportedIn hL (t.chartLocalization c hc hct ψ L hL hψ s))).val = ψ • s := by
  ext x
  by_cases hx : x ∈ c.source
  · rw [chartTestSection_apply_of_mem t c hc' hct _ hx, TestFunction.coe_ofSupportedIn,
      chartLocalization_apply_of_mem t c hc hct ψ L hL hψ s (c.map_source hx), c.left_inv hx,
      map_smul]
    simp [t.symmL_apply (hct hx), t.symm_apply_apply_mk (hct hx)]
  · rw [chartTestSection_apply_of_notMem t c hc' hct _ hx, ContMDiffSection.smul_apply,
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hψc h)), zero_smul]

end ChartLocalization

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
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace F]
  (V : M → Type*) [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V]

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

end TauCeti

namespace ContMDiffSection

open Bundle.Trivialization

universe u

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] {n : ℕ∞} [IsManifold I n M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle n F V I]

/-- **Finite chart-cutoff decomposition on a compact support.** On a Hausdorff `C^n` manifold
modelled on a finite-dimensional real space, given a family of two-sided `C^n` charts `c`
subordinate to atlas trivializations `t` whose sources cover a compact set `K`, there exist a
finite cutoff family `(r, χ)` with `tsupport (χ a) ⊆ (c (r a)).source` decomposing every section
supported in `K` as a finite sum of `chartCutoffTestFunction` chart extensions. -/
theorem exists_ofSupportedIn_eq_sum_chartCutoffTestFunction
    {κ : Type*} (t : κ → Trivialization F (π F V)) [∀ j, MemTrivializationAtlas (t j)]
    (c : κ → OpenPartialHomeomorph M E)
    (hc : ∀ j, ContMDiffOn I 𝓘(ℝ, E) n (c j) (c j).source)
    (hc_symm : ∀ j, ContMDiffOn 𝓘(ℝ, E) I n (c j).symm (c j).target)
    (hct : ∀ j, (c j).source ⊆ (t j).baseSet)
    (K : Compacts M) (hKcover : ∀ x ∈ (K : Set M), ∃ j, x ∈ (c j).source) :
    ∃ (α : Type u) (_ : Fintype α) (r : α → κ) (χ : α → C^n⟮I, M; ℝ⟯)
      (hχc : ∀ a, HasCompactSupport (χ a))
      (hχs : ∀ a, _root_.tsupport (χ a) ⊆ (c (r a)).source),
      ∀ s : supportedIn I F n V K,
        ofSupportedIn K s = ∑ a : α, (t (r a)).chartTestSection (c (r a)) (hc (r a)) (hct (r a))
          ((t (r a)).chartCutoffTestFunction (c (r a)) (hc_symm (r a)) (hct (r a))
            (χ a) (hχc a) (hχs a) s.val) := by
  obtain ⟨α, hfin, r, χ, hχc, hχs, -, -, hχsum⟩ :=
    K.isCompact.exists_contMDiffMap_partitionOfUnity I (n := n)
      (U := fun j ↦ (c j).source) fun x hx ↦
        let ⟨j, hj⟩ := hKcover x hx
        ⟨j, (c j).open_source.mem_nhds hj⟩
  refine ⟨α, hfin, r, χ, hχc, hχs, fun s ↦ ?_⟩
  apply Subtype.ext
  ext x
  have hcoe : ((∑ a : α, (t (r a)).chartTestSection (c (r a)) (hc (r a)) (hct (r a))
        ((t (r a)).chartCutoffTestFunction (c (r a)) (hc_symm (r a)) (hct (r a))
          (χ a) (hχc a) (hχs a) s.val) : compactlySupported I F n V) : Cₛ^n⟮I; F, V⟯) =
      ∑ a : α, χ a • s.val := by
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl fun a _ ↦ congrArg Subtype.val
      ((t (r a)).chartTestSection_chartCutoffTestFunction (c (r a)) (hc_symm (r a))
        (hct (r a)) (hc (r a)) (χ a) (hχc a) (hχs a) s.val)
  rw [ofSupportedIn_apply, hcoe, ContMDiffSection.coe_sum, Finset.sum_apply]
  simp only [ContMDiffSection.smul_apply, ← Finset.sum_smul]
  by_cases hx : x ∈ (K : Set M)
  · rw [hχsum x hx, one_smul]
  · rw [s.val.eq_zero_of_notMem_tsupport fun h ↦ hx (mem_supportedIn.1 s.property h), smul_zero]

/-- **Compactly supported sections are spanned by any two-sided `C^n` chart/frame cover.** On a
Hausdorff `C^n` manifold with finite-dimensional model, every compactly supported `C^n` section is a
finite sum of chart extensions of native test functions drawn from any supplied covering family of
two-sided `C^n` charts subordinate to atlas trivializations. -/
theorem span_iUnion_range_chartTestSection_eq_top_of_chart_cover
    {κ : Type*} (t : κ → Trivialization F (π F V)) [∀ j, MemTrivializationAtlas (t j)]
    (c : κ → OpenPartialHomeomorph M E)
    (hc : ∀ j, ContMDiffOn I 𝓘(ℝ, E) n (c j) (c j).source)
    (hc_symm : ∀ j, ContMDiffOn 𝓘(ℝ, E) I n (c j).symm (c j).target)
    (hct : ∀ j, (c j).source ⊆ (t j).baseSet)
    (hchart_cover : ∀ x : M, ∃ j, x ∈ (c j).source) :
    Submodule.span ℝ (⋃ j : κ, range ((t j).chartTestSection (c j) (hc j) (hct j))) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun s ↦ ?_
  let K : Compacts M := ⟨tsupport (s : Cₛ^n⟮I; F, V⟯), mem_compactlySupported.1 s.property⟩
  obtain ⟨α, _, r, χ, hχc, hχs, hdecomp⟩ :=
    exists_ofSupportedIn_eq_sum_chartCutoffTestFunction (I := I) (F := F) (V := V) (n := n)
      t c hc hc_symm hct K fun x _ ↦ hchart_cover x
  have hs_eq : s = _ :=
    (Subtype.ext (ofSupportedIn_apply K _)).symm.trans
      (hdecomp ⟨s.val, mem_supportedIn.2 Subset.rfl⟩)
  rw [hs_eq]
  exact Submodule.sum_mem _ fun a _ ↦
    Submodule.subset_span (mem_iUnion.2 ⟨r a, mem_range_self _⟩)

/-- **Compactly supported sections are spanned by chart extensions.** On a boundaryless Hausdorff
manifold with finite-dimensional model, every compactly supported `C^n` section is a finite sum
of chart extensions of native test functions. In particular a linear map on compactly supported
sections is determined by its composites with the chart extensions. -/
theorem span_iUnion_range_chartTestSection_eq_top [I.Boundaryless] :
    Submodule.span ℝ (⋃ p : ChartTestData I F V n, range p.chartTestSection) = ⊤ := by
  rw [eq_top_iff, ← span_iUnion_range_chartTestSection_eq_top_of_chart_cover
    (fun x ↦ trivializationAt F V x) (TauCeti.bundleChartAt I F V)
    (TauCeti.contMDiffOn_bundleChartAt (I := I) (F := F) (V := V) (n := n))
    (TauCeti.contMDiffOn_bundleChartAt_symm (I := I) (F := F) (V := V) (n := n))
    TauCeti.bundleChartAt_source_subset_baseSet
    (fun x ↦ ⟨x, TauCeti.mem_bundleChartAt_source x⟩)]
  refine Submodule.span_mono (iUnion_subset fun x ↦ ?_)
  refine subset_iUnion_of_subset ⟨trivializationAt F V x, TauCeti.bundleChartAt I F V x,
    TauCeti.contMDiffOn_bundleChartAt x, TauCeti.bundleChartAt_source_subset_baseSet x⟩ ?_
  simp only [ChartTestData.chartTestSection_def, Subset.rfl]

section SigmaCompact

variable [I.Boundaryless] [SigmaCompactSpace M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [SigmaCompactSpace M] [IsManifold I ∞ M]
  [IsManifold I n M] in
/-- Every section supported in the compact set `K` is a finite sum of chart extensions of its
chart localizations along chart cutoffs. -/
private theorem ofSupportedIn_eq_sum (A : TauCeti.ChartCutoffs I M n M)
    (hA : ∀ x, (A.chart x).source ⊆ (trivializationAt F V x).baseSet) (K : Compacts M)
    (σ : supportedIn I F n V K) :
    ofSupportedIn K σ = ∑ x ∈ A.meeting K K.isCompact,
      (trivializationAt F V x).chartTestSection (A.chart x) (A.contMDiffOn_chart x) (hA x)
        (TestFunction.ofSupportedIn (A.chartSupport_subset_target x)
          ((trivializationAt F V x).chartLocalization (A.chart x) (A.contMDiffOn_chart_symm x)
            (hA x) (A.cutoff x) (A.chartSupport x) (A.chartSupport_subset_target x)
            (A.mapsTo_chartSupport x) σ)) :=
  Subtype.ext <| by
    rw [ofSupportedIn_apply, Submodule.coe_sum]
    exact (A.sum_chartTestSection_chartLocalization _ hA K.isCompact _
      (mem_supportedIn.1 σ.property)).symm

variable {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- **The test topology is generated by chart extensions.** On a boundaryless Hausdorff `σ`-compact
manifold with finite-dimensional model, the fixed-compact topology on compactly supported sections
is the final locally convex topology of the chart extensions of native test functions, over all
charts that are smooth on their source and lie in the base set of a trivialization of the bundle
atlas. -/
theorem compactlySupportedTopology_eq_finalLocallyConvexTopology_chartTestSection
    (hcover : ∀ x : M, ∃ i, x ∈ U i) :
    compactlySupportedTopology (I := I) (n := n) e U hU =
      TauCeti.finalLocallyConvexTopology (ChartTestData.chartTestSection (I := I) (F := F)
        (V := V) (n := n)) := by
  let := frameTopology (I := I) (n := n) e U hU
  let := compactlySupportedTopology (I := I) (n := n) e U hU
  let := isTopologicalAddGroup_compactlySupportedTopology (I := I) (n := n) e U hU
  let := continuousSMul_compactlySupportedTopology (I := I) (n := n) e U hU
  let := locallyConvexSpace_compactlySupportedTopology (I := I) (n := n) e U hU
  refine le_antisymm ?_ ((TauCeti.FinalLocallyConvexTopology.le_iff _ _).2 fun p ↦ by
    let := p.memTrivializationAtlas
    rw [ChartTestData.chartTestSection_def]
    exact continuous_chartTestSection _ _ p.contMDiffOn_chart p.source_subset e U hU)
  -- Each fixed-compact stage is a finite sum of continuous factorizations through the chart
  -- extensions of test charts at points of `M`.
  obtain ⟨A, hA⟩ := TauCeti.ChartCutoffs.exists_source_subset_baseSet F I V (n := n)
  let p : M → ChartTestData I F V n := fun x ↦ ⟨trivializationAt F V x, A.chart x,
    A.contMDiffOn_chart x, hA x⟩
  let := TauCeti.finalLocallyConvexTopology
    (ChartTestData.chartTestSection (I := I) (F := F) (V := V) (n := n))
  rw [compactlySupportedTopology_def]
  refine (TauCeti.FinalLocallyConvexTopology.le_of_sum_factor _ (fun x ↦ (p x).chartTestSection)
    fun K ↦ ?_).trans ((TauCeti.FinalLocallyConvexTopology.le_iff _ _).2 fun x ↦
      TauCeti.FinalLocallyConvexTopology.continuous _ (p x))
  refine ⟨A.meeting K K.isCompact, fun x ↦
    (TestFunction.ofSupportedInCLM ℝ (A.chartSupport_subset_target x)).toLinearMap ∘ₗ
    (trivializationAt F V x).chartLocalization (A.chart x) (A.contMDiffOn_chart_symm x) (hA x)
      (A.cutoff x) (A.chartSupport x) (A.chartSupport_subset_target x)
      (A.mapsTo_chartSupport x) ∘ₗ
    (supportedIn I F n V K).subtype, fun x _ ↦ ?_, LinearMap.ext fun σ ↦ ?_⟩
  · exact (TestFunction.ofSupportedInCLM ℝ (A.chartSupport_subset_target x)).continuous.comp
      ((continuous_chartLocalization _ _ (A.contMDiffOn_chart_symm x) _ _ _
        (A.chartSupport_subset_target x) (A.mapsTo_chartSupport x) e U hU hcover).comp
          continuous_subtypeVal)
  · simp [p, ofSupportedIn_eq_sum A hA K σ]

variable {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G]

/-- **The universal property of bundle tests with respect to charts.** On a boundaryless Hausdorff
`σ`-compact manifold with finite-dimensional model, a linear map from compactly supported sections
into a locally convex space is continuous exactly when its composite with the chart extension of
native test functions is continuous for every chart smooth on its source and contained in the base
set of a trivialization of the bundle atlas. -/
theorem continuous_compactlySupportedTopology_iff_chartTestSection
    (hcover : ∀ x : M, ∃ i, x ∈ U i) (g : compactlySupported I F n V →ₗ[ℝ] G) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    Continuous g ↔ ∀ (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
      (c : OpenPartialHomeomorph M E) (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source)
      (hct : c.source ⊆ t.baseSet), Continuous (g ∘ t.chartTestSection c hc hct) := by
  rw [compactlySupportedTopology_eq_finalLocallyConvexTopology_chartTestSection e U hU hcover,
    TauCeti.FinalLocallyConvexTopology.continuous_iff_continuous_comp]
  refine ⟨fun h t _ c hc hct ↦ ?_, fun h p ↦ ?_⟩
  · simpa only [ChartTestData.chartTestSection_def] using h ⟨t, c, hc, hct⟩
  · let := p.memTrivializationAtlas
    rw [ChartTestData.chartTestSection_def]
    exact h _ _ p.contMDiffOn_chart p.source_subset

end SigmaCompact

end ContMDiffSection

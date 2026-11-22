/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover
public import TauCeti.Geometry.Manifold.VectorBundle.Section.TestFunction
import TauCeti.Analysis.Distribution.TestFunction.WeakWhitney
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact

/-!
# Chart localization of bundle tests

A compactly supported smooth section of a vector bundle can be cut into pieces supported in
coordinate charts, and each piece read in a bundle frame is a native test function on the chart
target. This module establishes frame-topology continuity of chart localization and chart reading
(`Bundle.Trivialization.continuous_chartLocalization`,
`Bundle.Trivialization.continuous_chartReadSupportedIn`,
`Bundle.Trivialization.continuous_chartReadTestFunction`,
`Bundle.Trivialization.continuous_chartCutoffTestFunction`) as well as the finite cutoff
decomposition of sections supported in a compact set under any two-sided `C^n` chart/frame cover
(`ContMDiffSection.exists_ofSupportedIn_eq_sum_chartCutoffTestFunction`), without depending on the
compact-support inductive topology.

In particular, every compactly supported `C^n` section is a finite sum of chart extensions of
native test functions for any covering family of two-sided `C^n` charts subordinate to atlas
trivializations (`ContMDiffSection.span_iUnion_range_chartTestSection_eq_top_of_chart_cover`), and
on a boundaryless Hausdorff manifold for all `ChartTestData`
(`ContMDiffSection.span_iUnion_range_chartTestSection_eq_top`).

The fixed-support continuity proofs rest on
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
  {n : ℕ∞} [ContMDiffVectorBundle n F V I] [IsManifold I n M] [LocallyCompactSpace E]
  (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
  (c : OpenPartialHomeomorph M E)
  (hc_symm : ContMDiffOn 𝓘(ℝ, E) I n c.symm c.target) (hct : c.source ⊆ t.baseSet)
  {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- **Chart localizations are continuous** from the compact derivative topology of any frame system
whose domains cover `c.symm '' L` to the topology of test functions supported in `L`. -/
theorem continuous_chartLocalization
    (ψ : C^n⟮I, M; ℝ⟯) (L : Compacts E) (hL : (L : Set E) ⊆ c.target)
    (hψ : MapsTo c (_root_.tsupport ψ) L)
    (hcover : ∀ x ∈ c.symm '' (L : Set E), ∃ i, x ∈ U i) :
    letI := frameTopology (I := I) (n := n) e U hU
    Continuous (t.chartLocalization c hc_symm hct ψ L hL hψ) := by
  let := frameTopology (I := I) (n := n) e U hU
  rw [ContDiffMapSupportedIn.continuous_iff_continuous_toContMDiffMap]
  suffices h : Continuous fun s ↦ (t.chartLocalization c hc_symm hct ψ L hL hψ s).toContMDiffMap by
    rwa [ContMDiffMap.manifoldWeakWhitneyTopology_self] at h
  have hLc : IsOpen ((L : Set E)ᶜ) := L.isCompact.isClosed.isOpen_compl
  have hVopen : IsOpen (⋃ i, (U i : Set M)) := isOpen_iUnion fun i ↦ (U i).isOpen
  have hWtrue : IsOpen (c.target ∩ c.symm ⁻¹' (⋃ i, (U i : Set M))) :=
    c.continuousOn_symm.isOpen_inter_preimage c.open_target hVopen
  -- Cover `E` by the chart image of the covered part of the source, where the localization is a
  -- coordinate expression, and by the complement of `L`, where it vanishes.
  let W : Bool → Opens E := fun b ↦
    bif b then ⟨c.target ∩ c.symm ⁻¹' (⋃ i, (U i : Set M)), hWtrue⟩
    else ⟨(L : Set E)ᶜ, hLc⟩
  have hW : ∀ y : E, ∃ b, y ∈ W b := by
    intro y
    by_cases hy : y ∈ L
    · exact ⟨true, hL hy, mem_iUnion.2 (hcover (c.symm y) ⟨y, hy, rfl⟩)⟩
    · exact ⟨false, hy⟩
  refine ContMDiffMap.continuous_of_forall_continuous_restrict W hW fun b ↦ ?_
  cases b with
  | false =>
    convert continuous_const (y := (0 : C^n⟮𝓘(ℝ, E), W false; 𝓘(ℝ, F), F⟯)) using 1
    funext s
    ext y
    rw [ContMDiffMap.restrict_apply, ContDiffMapSupportedIn.coe_toContMDiffMap,
      (t.chartLocalization c hc_symm hct ψ L hL hψ s).zero_on_compl y.property]
    simp
  | true =>
    -- On the covered part of the chart target, compose the frame coefficients with the inverse
    -- chart and multiply by `ψ ∘ c⁻¹`.
    let Uc : Opens M := ⟨c.source ∩ ⋃ i, (U i : Set M), c.open_source.inter hVopen⟩
    have hUct : (Uc : Set M) ⊆ t.baseSet := inter_subset_left.trans hct
    have hsymm : ContMDiff 𝓘(ℝ, E) I n (fun y : W true ↦ c.symm y) :=
      hc_symm.comp_contMDiff (contMDiff_subtypeVal (U := W true)) fun y ↦ y.property.1
    let j : C^n⟮𝓘(ℝ, E), W true; I, Uc⟯ :=
      ⟨fun y ↦ ⟨c.symm y, c.map_target y.property.1, y.property.2⟩,
        (TauCeti.ContMDiff.subtypeVal_comp_iff Uc _).mp hsymm⟩
    let A : C^n⟮𝓘(ℝ, E), W true; 𝓘(ℝ, F →L[ℝ] F), F →L[ℝ] F⟯ :=
      ⟨fun y ↦ ψ (c.symm y) • ContinuousLinearMap.id ℝ F,
        (ψ.contMDiff.comp hsymm).smul contMDiff_const⟩
    have hcomp : Continuous fun s : Cₛ^n⟮I; F, V⟯ ↦
        (t.frameCoordinates (U := Uc) hUct s).comp j :=
      ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp
        ((continuous_frameCoordinates_of_subset_iUnion e U hU t Uc hUct
          inter_subset_right).prodMk continuous_const)
    refine ((ContMDiffMap.continuous_clmApplyLinearMap A).comp hcomp).congr fun s ↦ ?_
    ext y
    simp only [Function.comp_apply, ContMDiffMap.restrict_apply,
      ContMDiffMap.clmApplyLinearMap_apply, ContMDiffMap.comp_apply,
      ContDiffMapSupportedIn.coe_toContMDiffMap, frameCoordinates_apply]
    simp [A, j, t.chartLocalization_apply_of_mem c hc_symm hct ψ L hL hψ s y.property.1,
      t.continuousLinearMapAt_apply_of_mem (R := ℝ) (hct (c.map_target y.property.1))]

/-- Reading sections supported in a compact subset `K ⊆ c.source` in a chart `c` with `C^n`
inverse subordinate to `t` is continuous from any smooth frame topology whose domains cover `K`
into `𝓓^{n}_{c '' K}(E, F)`.

The continuity argument adapts `Bundle.Trivialization.continuous_chartLocalization` to the
fixed-support reading map along `c⁻¹`. -/
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
  by_cases hy : y ∈ c.target
  · simp [TestFunction.coe_ofSupportedInCLM,
      t.chartReadSupportedIn_apply_of_mem c hc_symm hct hKc s hy,
      t.chartReadTestFunction_apply_of_mem c hc_symm hct hKc s hy]
  · simp [TestFunction.coe_ofSupportedInCLM,
      t.chartReadSupportedIn_apply_of_notMem c hc_symm hct hKc s hy, hy]

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
    ((continuous_smulLinearMap e U hU ρ).subtype_mk fun s ↦
      mem_supportedIn.2 ((tsupport_smul_function_subset ρ s).trans inter_subset_left))).congr
    fun s ↦ ?_
  ext y
  by_cases hy : y ∈ c.target
  · simp [t.chartReadTestFunction_apply_of_mem c hc_symm hct (K := Kρ) hρs _ hy,
      t.chartCutoffTestFunction_apply_of_mem c hc_symm hct ρ hρc hρs s hy]
  · simp [hy]

end Bundle.Trivialization

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
  have heval : (∑ a : α, χ a • s.val : Cₛ^n⟮I; F, V⟯) x = ∑ a : α, (χ a • s.val) x := by
    have h := congrFun (map_sum (coeAddHom I F n V) (fun a : α ↦ χ a • s.val) Finset.univ) x
    simp only [coeAddHom_apply, Finset.sum_apply] at h
    exact h
  rw [ofSupportedIn_apply, hcoe, heval]
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
  rw [ChartTestData.chartTestSection_def]

end ContMDiffSection

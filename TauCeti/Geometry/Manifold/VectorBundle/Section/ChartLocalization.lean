/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.CompactSupport.Topology
import TauCeti.Analysis.Distribution.TestFunction.WeakWhitney
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# Chart localization of bundle tests

A compactly supported smooth section of a vector bundle can be cut into pieces supported in
coordinate charts, and each piece read in a bundle frame is a native test function on the chart
target. This file shows that these localizations are continuous and invert chart extension.

Let `c` be a chart with smooth inverse, `t` a bundle trivialization over its source, and `ψ` a
smooth function whose closed support is mapped by `c` into a compact subset `L` of the chart target.
The *chart localization* `Bundle.Trivialization.chartLocalization` sends a section `s` to the
function `y ↦ ψ (c⁻¹ y) • (t (s (c⁻¹ y))).2` on the chart target, extended by zero, a native test
function supported in `L`. It is continuous from any compact derivative topology on sections whose
frame domains cover `c.symm '' L` to the topology of `𝓓^{n}_{L}(E, F)`
(`Bundle.Trivialization.continuous_chartLocalization`), and extending it back through the chart
gives `ψ • s` when `tsupport ψ` lies in the chart source
(`Bundle.Trivialization.chartTestSection_chartLocalization`).

## Main declarations

* `Bundle.Trivialization.chartLocalization`: the chart localization of sections, a linear map into
  the test functions supported in a fixed compact set.
* `Bundle.Trivialization.continuous_chartLocalization`: it is continuous.
* `Bundle.Trivialization.chartTestSection_chartLocalization`: extending the localization through
  the chart recovers `ψ • s`.
* `ContMDiffSection.span_iUnion_range_chartTestSection_eq_top`: compactly supported sections are
  finite sums of chart extensions of native test functions.

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

/-- **Chart localizations are continuous** from the compact derivative topology of any frame system
whose domains cover `c.symm '' L` to the topology of test functions supported in `L`. -/
theorem continuous_chartLocalization (hcover : ∀ x ∈ c.symm '' (L : Set E), ∃ i, x ∈ U i) :
    letI := frameTopology (I := I) (n := n) e U hU
    Continuous (t.chartLocalization c hc hct ψ L hL hψ) := by
  let := frameTopology (I := I) (n := n) e U hU
  rw [ContDiffMapSupportedIn.continuous_iff_continuous_toContMDiffMap]
  suffices h : Continuous fun s ↦ (t.chartLocalization c hc hct ψ L hL hψ s).toContMDiffMap by
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
    simp only [ContMDiffMap.restrict_apply, ContDiffMapSupportedIn.coe_toContMDiffMap]
    exact localizationFun_eq_zero t c hct ψ L hψ s y.property
  | true =>
    -- On the covered part of the chart target, compose the frame coefficients with the inverse
    -- chart and multiply by `ψ ∘ c⁻¹`.
    let Uc : Opens M := ⟨c.source ∩ ⋃ i, (U i : Set M), c.open_source.inter hVopen⟩
    have hUct : (Uc : Set M) ⊆ t.baseSet := inter_subset_left.trans hct
    have hsymm : ContMDiff 𝓘(ℝ, E) I n (fun y : W true ↦ c.symm y) :=
      hc.comp_contMDiff (contMDiff_subtypeVal (U := W true)) fun y ↦ y.property.1
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
    convert (ContMDiffMap.continuous_clmApplyLinearMap A).comp hcomp using 1
    funext s
    ext y
    simp only [Function.comp_apply, ContMDiffMap.restrict_apply,
      ContMDiffMap.clmApplyLinearMap_apply, ContMDiffMap.comp_apply,
      ContDiffMapSupportedIn.coe_toContMDiffMap, frameCoordinates_apply]
    exact localizationFun_of_mem t c hct ψ s y.property.1

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

end Bundle.Trivialization

namespace ContMDiffSection

open Bundle.Trivialization

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] {n : ℕ∞} [IsManifold I n M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle n F V I]

/-- **Compactly supported sections are spanned by chart extensions.** On a boundaryless Hausdorff
manifold with finite-dimensional model, every compactly supported `C^n` section is a finite sum
of chart extensions of native test functions. In particular a linear map on compactly supported
sections is determined by its composites with the chart extensions. -/
theorem span_iUnion_range_chartTestSection_eq_top :
    Submodule.span ℝ (⋃ p : ChartTestData I F V n, range p.chartTestSection) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun s ↦ ?_
  let K : Set M := tsupport (s : Cₛ^n⟮I; F, V⟯)
  have hK : IsCompact K := mem_compactlySupported.1 s.property
  obtain ⟨α, _, r, χ, hχc, hχs, -, -, hχsum⟩ :=
    hK.exists_contMDiffMap_partitionOfUnity I (n := n)
      (U := fun x : M ↦ (TauCeti.bundleChartAt I F V x).source) fun x _ ↦
        ⟨x, (TauCeti.bundleChartAt I F V x).open_source.mem_nhds
          (TauCeti.mem_bundleChartAt_source x)⟩
  have hs_eq : s = ∑ a : α, (trivializationAt F V (r a)).chartTestSection
      (TauCeti.bundleChartAt I F V (r a)) (TauCeti.contMDiffOn_bundleChartAt (r a))
      (TauCeti.bundleChartAt_source_subset_baseSet (r a))
      ((trivializationAt F V (r a)).chartCutoffTestFunction (TauCeti.bundleChartAt I F V (r a))
        (TauCeti.contMDiffOn_bundleChartAt_symm (r a))
        (TauCeti.bundleChartAt_source_subset_baseSet (r a)) (χ a) (hχc a) (hχs a) s.val) := by
    apply Subtype.ext
    ext x
    have hcoe : ((∑ a : α, (trivializationAt F V (r a)).chartTestSection
          (TauCeti.bundleChartAt I F V (r a)) (TauCeti.contMDiffOn_bundleChartAt (r a))
          (TauCeti.bundleChartAt_source_subset_baseSet (r a))
          ((trivializationAt F V (r a)).chartCutoffTestFunction
            (TauCeti.bundleChartAt I F V (r a)) (TauCeti.contMDiffOn_bundleChartAt_symm (r a))
            (TauCeti.bundleChartAt_source_subset_baseSet (r a)) (χ a) (hχc a) (hχs a) s.val) :
          compactlySupported I F n V) : Cₛ^n⟮I; F, V⟯) = ∑ a : α, χ a • s.val := by
      rw [Submodule.coe_sum]
      exact Finset.sum_congr rfl fun a _ ↦ congrArg Subtype.val
        ((trivializationAt F V (r a)).chartTestSection_chartCutoffTestFunction
          (TauCeti.bundleChartAt I F V (r a)) (TauCeti.contMDiffOn_bundleChartAt_symm (r a))
          (TauCeti.bundleChartAt_source_subset_baseSet (r a))
          (TauCeti.contMDiffOn_bundleChartAt (r a)) (χ a) (hχc a) (hχs a) s.val)
    have heval : (∑ a : α, χ a • s.val : Cₛ^n⟮I; F, V⟯) x = ∑ a : α, (χ a • s.val) x := by
      have h := congrFun (map_sum (coeAddHom I F n V) (fun a : α ↦ χ a • s.val) Finset.univ) x
      simp only [coeAddHom_apply, Finset.sum_apply] at h
      exact h
    rw [hcoe, heval]
    simp only [ContMDiffSection.smul_apply, ← Finset.sum_smul]
    by_cases hx : x ∈ K
    · rw [hχsum x hx, one_smul]
    · rw [s.val.eq_zero_of_notMem_tsupport hx, smul_zero]
  rw [hs_eq]
  refine Submodule.sum_mem _ fun a _ ↦ Submodule.subset_span (mem_iUnion.2
    ⟨⟨trivializationAt F V (r a), TauCeti.bundleChartAt I F V (r a),
      TauCeti.contMDiffOn_bundleChartAt (r a),
      TauCeti.bundleChartAt_source_subset_baseSet (r a)⟩, ?_⟩)
  rw [ChartTestData.chartTestSection_def]
  exact mem_range_self _

end ContMDiffSection

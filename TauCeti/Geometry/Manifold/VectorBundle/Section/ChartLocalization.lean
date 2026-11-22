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

/-!
# Chart localization of smooth bundle sections

A smooth section of a vector bundle can be multiplied by a smooth cutoff supported in a coordinate
chart and read in a bundle frame as a native test function on the chart target. This file defines
the chart localization map and proves continuity of both chart localizations and fixed-support
chart-coefficient readbacks for the compact derivative frame topology.

Let `c` be a chart with `C^n` inverse, `t` a bundle trivialization over its source, and `ψ` a
`C^n` scalar function whose closed support is mapped by `c` into a compact subset `L` of the chart
target. The *chart localization* `Bundle.Trivialization.chartLocalization` reads `ψ • s` through
the unweighted chart-coefficient map `Bundle.Trivialization.chartCoeffLinearMap` as a native test
function supported in `L`. Both `Bundle.Trivialization.chartLocalization` and the fixed-support
coefficient map `Bundle.Trivialization.chartTestCoeff` are continuous from the compact derivative
frame topology to `𝓓^{n}_{L}(E, F)` (`Bundle.Trivialization.continuous_chartLocalization`,
`Bundle.Trivialization.continuous_chartTestCoeff`), via a shared two-open-set continuity lemma.
Extending the localization back through the chart recovers `ψ • s` when `tsupport ψ ⊆ c.source`
(`Bundle.Trivialization.chartTestSection_chartLocalization`).

## Main declarations

* `Bundle.Trivialization.chartLocalization`: the chart localization of sections, a linear map into
  the test functions supported in a fixed compact set.
* `Bundle.Trivialization.continuous_chartLocalization` and
  `Bundle.Trivialization.continuous_chartTestCoeff`: continuity of chart localizations and
  fixed-support chart coefficients for the frame topology.
* `Bundle.Trivialization.chartTestSection_chartLocalization`: extending the localization through
  the chart recovers `ψ • s`.
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

private theorem continuous_chartCoeff (hcover : ∀ x : M, ∃ i, x ∈ U i)
    {P : Type*} [TopologicalSpace P] {L₀ L : Compacts E}
    (hL₀ : (L₀ : Set E) ⊆ c.target) (hL₀L : (L₀ : Set E) ⊆ L)
    (f : P → Cₛ^n⟮I; F, V⟯)
    (hf : letI := frameTopology (I := I) (n := n) e U hU; Continuous f)
    (hf_supp : ∀ p y, y ∈ c.target → y ∉ L₀ → (f p) (c.symm y) = 0) :
    Continuous fun p ↦ t.chartCoeff c hc hct hL₀ hL₀L (f p) (hf_supp p) := by
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
    funext p
    ext y
    simp only [Function.comp_apply, ContMDiffMap.restrict_apply,
      ContDiffMapSupportedIn.coe_toContMDiffMap, ContMDiffMap.coe_zero, Pi.zero_apply]
    exact t.chartCoeff_eq_zero c hc hct hL₀ hL₀L (f p) (hf_supp p) y.property
  | true =>
    have hsymm : ContMDiff 𝓘(ℝ, E) I n (fun y : W true ↦ c.symm y) :=
      hc.comp_contMDiff (contMDiff_subtypeVal (U := W true)) fun y ↦ y.property
    let j : C^n⟮𝓘(ℝ, E), W true; I, chartSource c⟯ :=
      ⟨fun y ↦ ⟨c.symm y, c.map_target y.property⟩,
        (TauCeti.ContMDiff.subtypeVal_comp_iff (chartSource c) _).mp hsymm⟩
    have hcoord : Continuous fun p ↦ t.frameCoordinates (U := chartSource c) hct (f p) :=
      (continuous_frameCoordinates_of_cover e U hU hcover t (chartSource c) hct).comp hf
    have hcomp : Continuous fun p ↦
        (t.frameCoordinates (U := chartSource c) hct (f p)).comp j :=
      ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp (hcoord.prodMk continuous_const)
    convert hcomp using 1
    funext p
    ext y
    simp only [Function.comp_apply, ContMDiffMap.restrict_apply,
      ContDiffMapSupportedIn.coe_toContMDiffMap,
      chartCoeff_apply_of_mem t c hc hct hL₀ hL₀L (f p) (hf_supp p) y.property,
      ContMDiffMap.comp_apply, frameCoordinates_apply,
      t.continuousLinearMapAt_apply_of_mem (R := ℝ) (hct (c.map_target y.property))]
    rfl

/-- **Chart localizations are continuous** from the compact derivative topology of a covering
frame system to the topology of test functions supported in `L`. -/
theorem continuous_chartLocalization
    (ψ : C^n⟮I, M; ℝ⟯) (L : Compacts E) (hL : (L : Set E) ⊆ c.target)
    (hψ : MapsTo c (tsupport ψ) L) (hcover : ∀ x : M, ∃ i, x ∈ U i) :
    letI := frameTopology (I := I) (n := n) e U hU
    Continuous (t.chartLocalization c hc hct ψ L hL hψ) := by
  let := frameTopology (I := I) (n := n) e U hU
  refine (continuous_chartCoeff t c hc hct e U hU hcover hL Subset.rfl (smulLinearMap ψ)
    (continuous_smulLinearMap_frameTopology e U hU ψ)
    fun _ _ hyc hyL ↦ smul_apply_symm_eq_zero c ψ L hψ _ hyc hyL).congr fun s ↦
    (chartLocalization_apply t c hc hct ψ L hL hψ s).symm

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
  refine (continuous_chartCoeff t c hc hct e U hU hcover (c.imageCompact_subset_target hK)
    (c.coe_imageCompact hK ▸ hKL) Subtype.val continuous_subtypeVal
    fun s _ hyc hyL₀ ↦ s.val.eq_zero_of_notMem_tsupport fun h ↦ by
      rw [← SetLike.mem_coe, c.coe_imageCompact hK] at hyL₀
      exact hyL₀ ⟨c.symm _, mem_supportedIn.1 s.property h, c.right_inv hyc⟩).congr fun s ↦ ?_
  ext y
  by_cases hy : y ∈ c.target
  · rw [chartCoeff_apply_of_mem _ _ _ _ _ _ _ _ hy, chartTestCoeff_apply_of_mem _ _ _ _ _ _ _ hy]
  · rw [chartCoeff_apply_of_notMem _ _ _ _ _ _ _ _ hy,
      chartTestCoeff_apply_of_notMem _ _ _ _ _ _ _ hy]

end Bundle.Trivialization

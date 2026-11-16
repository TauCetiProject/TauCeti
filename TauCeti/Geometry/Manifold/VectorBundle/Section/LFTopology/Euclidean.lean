/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.LFTopology.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Single-chart and Euclidean open-set LF equivalences for bundle test sections

On a single smooth chart `c : OpenPartialHomeomorph M E` subordinate to a smooth bundle frame `t`,
chart extension restricts on each fixed compact `K ⊆ c.target` to a continuous linear equivalence
`Bundle.Trivialization.chartTestSectionSupportedInCLE` between `𝓓^{n}_{K}(E, F)` and the
fixed-support stage `supportedIn I F n V (c.symm '' K)`.

When `c.source = univ`, reading compactly supported sections in the chart and frame yields a
continuous inverse `Bundle.Trivialization.chartTestCoords` to `chartTestSection`, establishing the
single-chart LF continuous linear equivalence `Bundle.Trivialization.chartTestSectionCLE` between
`𝓓^{n}(⟨c.target, c.open_target⟩, F)` and `ContMDiffSection.compactlySupported I F n V`. On any
open subset `Ω : Opens E` of a locally compact normed space, this specializes to
`Bundle.Trivialization.opensChartTestSectionCLE` for any globally trivialized smooth bundle and to
`Bundle.Trivial.opensTestSectionCLE` for the trivial bundle `Bundle.Trivial Ω F`.
-/

public noncomputable section

open Bundle Set TopologicalSpace Topology
open scoped ContDiff Manifold Distributions

namespace Bundle.Trivialization

open ContMDiffSection

section SingleChart

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞} [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
  (c : OpenPartialHomeomorph M E)
  (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source)
  (hc_symm : ContMDiffOn 𝓘(ℝ, E) I n c.symm c.target)
  (hct : c.source ⊆ t.baseSet)
  {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  (hcover : ∀ x : M, ∃ i, x ∈ U i)

include hcover in
/-- On any fixed compact subset `K` of a smooth chart target, chart extension is a continuous
linear equivalence between `𝓓^{n}_{K}(E, F)` and the fixed-support stage `c.symm '' K` in the
compact derivative section topology. -/
def chartTestSectionSupportedInCLE {K : Compacts E} (hK : (K : Set E) ⊆ c.target) :
    letI := frameTopology (I := I) (n := n) e U hU
    𝓓^{n}_{K}(E, F) ≃L[ℝ] supportedIn I F n V (c.symm '' K) :=
  letI := frameTopology (I := I) (n := n) e U hU
  let Ω : Opens E := ⟨c.target, c.open_target⟩
  have hKs : (K : Set E) ⊆ c.symm.source := c.symm_source.symm ▸ hK
  let K_M : Compacts M := c.symm.compactsImage K hKs
  have hK_eq : (K_M : Set M) = c.symm '' K := c.symm.coe_compactsImage K hKs
  have hKM : (K_M : Set M) ⊆ c.source := c.symm_target ▸ c.symm.compactsImage_subset_target K hKs
  have hK_le : c.compactsImage K_M hKM ≤ K := (c.compactsImage_compactsImage_symm K hKs hKM).le
  let toKM : supportedIn I F n V (c.symm '' K) → supportedIn I F n V K_M :=
    fun s ↦ ⟨s.1, hK_eq.symm ▸ s.2⟩
  let toFunLM : 𝓓^{n}_{K}(E, F) →ₗ[ℝ] supportedIn I F n V (c.symm '' K) :=
    ((compactlySupported I F n V).subtype ∘ₗ t.chartTestSection c hc hct ∘ₗ
        (TestFunction.ofSupportedInCLM ℝ (Ω := Ω) hK).toLinearMap).codRestrict
      (supportedIn I F n V (c.symm '' K)) fun φ ↦ by
        simpa only [LinearMap.comp_apply, Submodule.coe_subtype, ContinuousLinearMap.coe_coe,
          TestFunction.coe_ofSupportedInCLM] using
          t.chartTestSection_mem_supportedIn c hc hct _
            (by simpa only [TestFunction.coe_ofSupportedIn] using φ.tsupport_subset)
  { toLinearMap := toFunLM
    invFun s := ContDiffMapSupportedIn.monoCLM ℝ (t.chartTestSupportedIn c hc_symm hct hKM (toKM s))
    left_inv φ := by
      ext y
      simp only [LinearMap.toFun_eq_coe, toFunLM, toKM,
        ContDiffMapSupportedIn.monoCLM_apply, le_rfl, hK_le, and_self, ↓reduceIte,
        LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.coe_subtype,
        ContinuousLinearMap.coe_coe, TestFunction.coe_ofSupportedInCLM,
        chartTestSupportedIn_chartTestSection_apply, TestFunction.coe_ofSupportedIn]
    right_inv s := by
      apply Subtype.ext
      have hre :=
        t.chartTestSection_ofSupportedIn_chartTestSupportedIn c hc_symm hct hc hKM (toKM s)
      have hmono :
          TestFunction.ofSupportedIn (Ω := Ω) hK
            (ContDiffMapSupportedIn.monoCLM ℝ
              (t.chartTestSupportedIn c hc_symm hct hKM (toKM s))) =
            TestFunction.ofSupportedIn (Ω := Ω) (c.compactsImage_subset_target K_M hKM)
              (t.chartTestSupportedIn c hc_symm hct hKM (toKM s)) := by
        ext y
        simp [ContDiffMapSupportedIn.monoCLM_apply, hK_le]
      simpa only [LinearMap.toFun_eq_coe, toFunLM, LinearMap.codRestrict_apply,
        LinearMap.comp_apply, Submodule.coe_subtype, ContinuousLinearMap.coe_coe,
        TestFunction.coe_ofSupportedInCLM, hmono, ofSupportedIn_apply] using
        congrArg Subtype.val hre
    continuous_toFun := Continuous.subtype_mk
      ((continuous_frameTopology_iff_frameCoordinates e U hU).2 fun i ↦
        t.continuous_frameCoordinates_chartTestSection_ofSupportedIn c hc hct hK (e i) (hU i)) _
    continuous_invFun :=
      (ContDiffMapSupportedIn.monoCLM ℝ).continuous.comp
        ((t.continuous_chartTestSupportedIn c hc_symm hct hKM e U hU hcover).comp
          (Continuous.subtype_mk continuous_subtype_val _)) }

/-- The forward map of `chartTestSectionSupportedInCLE` agrees with `chartTestSection`. -/
@[simp]
theorem coe_chartTestSectionSupportedInCLE {K : Compacts E} (hK : (K : Set E) ⊆ c.target)
    (φ : 𝓓^{n}_{K}(E, F)) :
    letI := frameTopology (I := I) (n := n) e U hU
    ((t.chartTestSectionSupportedInCLE c hc hc_symm hct e U hU hcover hK φ).1 : Cₛ^n⟮I; F, V⟯) =
      (t.chartTestSection c hc hct
        (TestFunction.ofSupportedIn (Ω := ⟨c.target, c.open_target⟩) hK φ)).1 := by
  change (t.chartTestSection c hc hct
    (TestFunction.ofSupportedInCLM ℝ (Ω := ⟨c.target, c.open_target⟩) hK φ)).1 = _
  rw [TestFunction.coe_ofSupportedInCLM]

/-- On the chart target, the inverse of `chartTestSectionSupportedInCLE` reads the section value in
the defining frame. -/
@[simp]
theorem chartTestSectionSupportedInCLE_symm_apply_of_mem {K : Compacts E}
    (hK : (K : Set E) ⊆ c.target)
    (s : supportedIn I F n V (c.symm '' K)) {y : E} (hy : y ∈ c.target) :
    letI := frameTopology (I := I) (n := n) e U hU
    (t.chartTestSectionSupportedInCLE c hc hc_symm hct e U hU hcover hK).symm s y =
      t.continuousLinearMapAt ℝ (c.symm y) (s.1 (c.symm y)) := by
  have hKs : (K : Set E) ⊆ c.symm.source := c.symm_source.symm ▸ hK
  have hKM : (c.symm.compactsImage K hKs : Set M) ⊆ c.source :=
    c.symm_target ▸ c.symm.compactsImage_subset_target K hKs
  change ContDiffMapSupportedIn.monoCLM ℝ
    (t.chartTestSupportedIn c hc_symm hct hKM ⟨s.1, (c.symm.coe_compactsImage K hKs).symm ▸ s.2⟩)
    y = _
  simp [ContDiffMapSupportedIn.monoCLM_apply, hy]

/-- Outside the chart target, the inverse of `chartTestSectionSupportedInCLE` vanishes. -/
@[simp]
theorem chartTestSectionSupportedInCLE_symm_apply_of_notMem {K : Compacts E}
    (hK : (K : Set E) ⊆ c.target)
    (s : supportedIn I F n V (c.symm '' K)) {y : E} (hy : y ∉ c.target) :
    letI := frameTopology (I := I) (n := n) e U hU
    (t.chartTestSectionSupportedInCLE c hc hc_symm hct e U hU hcover hK).symm s y = 0 := by
  have hKs : (K : Set E) ⊆ c.symm.source := c.symm_source.symm ▸ hK
  have hKM : (c.symm.compactsImage K hKs : Set M) ⊆ c.source :=
    c.symm_target ▸ c.symm.compactsImage_subset_target K hKs
  change ContDiffMapSupportedIn.monoCLM ℝ
    (t.chartTestSupportedIn c hc_symm hct hKM ⟨s.1, (c.symm.coe_compactsImage K hKs).symm ▸ s.2⟩)
    y = 0
  simp [ContDiffMapSupportedIn.monoCLM_apply, hy]

/-- The inverse of `chartTestSectionSupportedInCLE` preserves closed support, transported by the
chart. -/
@[simp]
theorem tsupport_chartTestSectionSupportedInCLE_symm {K : Compacts E}
    (hK : (K : Set E) ⊆ c.target) (s : supportedIn I F n V (c.symm '' K)) :
    letI := frameTopology (I := I) (n := n) e U hU
    _root_.tsupport
        ((t.chartTestSectionSupportedInCLE c hc hc_symm hct e U hU hcover hK).symm s) =
      c '' s.1.tsupport := by
  let := frameTopology (I := I) (n := n) e U hU
  have hKs : (K : Set E) ⊆ c.symm.source := c.symm_source.symm ▸ hK
  have hKM : (c.symm.compactsImage K hKs : Set M) ⊆ c.source :=
    c.symm_target ▸ c.symm.compactsImage_subset_target K hKs
  let s' : supportedIn I F n V (c.symm.compactsImage K hKs) :=
    ⟨s.1, (c.symm.coe_compactsImage K hKs).symm ▸ s.2⟩
  have hcoe :
      ⇑((t.chartTestSectionSupportedInCLE c hc hc_symm hct e U hU hcover hK).symm s) =
        ⇑(t.chartTestSupportedIn c hc_symm hct hKM s') := by
    funext y
    change ContDiffMapSupportedIn.monoCLM ℝ (t.chartTestSupportedIn c hc_symm hct hKM s') y = _
    simp [ContDiffMapSupportedIn.monoCLM_apply]
  rw [hcoe, tsupport_chartTestSupportedIn]

section GlobalChart

variable (hsource : c.source = univ)

omit [T2Space M] in
include hcover in
/-- Reading a compactly supported section in a single global chart is continuous from
`compactlySupportedTopology` into the native LF space `𝓓^{n}(⟨c.target, c.open_target⟩, F)`. -/
theorem continuous_chartTestCoords :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    Continuous (t.chartTestCoords c hc_symm hct hsource) := by
  let := frameTopology (I := I) (n := n) e U hU
  let := compactlySupportedTopology (I := I) (n := n) e U hU
  refine (continuous_compactlySupportedTopology_iff e U hU
    (t.chartTestCoords c hc_symm hct hsource)).2 fun K ↦ ?_
  have hK : (K : Set M) ⊆ c.source := hsource.symm ▸ subset_univ _
  refine ((TestFunction.ofSupportedInCLM ℝ (Ω := ⟨c.target, c.open_target⟩)
      (c.compactsImage_subset_target K hK)).continuous.comp
    (t.continuous_chartTestSupportedIn c hc_symm hct hK e U hU hcover)).congr fun s ↦ by
      simpa only [Function.comp_apply, TestFunction.coe_ofSupportedInCLM] using
        (t.chartTestCoords_ofSupportedIn c hc_symm hct hsource s).symm

omit [T2Space M] in
include hcover in
/-- **Single-chart LF equivalence.** On a manifold covered by a single smooth chart subordinate to
a smooth bundle frame, chart extension is a continuous linear equivalence between the native
Euclidean LF test space `𝓓^{n}(⟨c.target, c.open_target⟩, F)` and compactly supported bundle
sections with `compactlySupportedTopology`. -/
def chartTestSectionCLE :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    𝓓^{n}(⟨c.target, c.open_target⟩, F) ≃L[ℝ] compactlySupported I F n V :=
  letI : T2Space M := T2Space.of_injective_continuous
    (Set.injOn_univ.1 (hsource ▸ c.injOn)) (continuousOn_univ.1 (hsource ▸ c.continuousOn))
  letI := compactlySupportedTopology (I := I) (n := n) e U hU
  { toLinearMap := t.chartTestSection c hc hct
    invFun := t.chartTestCoords c hc_symm hct hsource
    left_inv := t.chartTestCoords_chartTestSection c hc_symm hct hc hsource
    right_inv := t.chartTestSection_chartTestCoords c hc_symm hct hc hsource
    continuous_toFun := t.continuous_chartTestSection c hc hct e U hU
    continuous_invFun := t.continuous_chartTestCoords c hc_symm hct e U hU hcover hsource }

/-- The underlying linear map of `chartTestSectionCLE` is `chartTestSection`. -/
@[simp]
theorem toLinearMap_chartTestSectionCLE :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    (t.chartTestSectionCLE c hc hc_symm hct e U hU hcover hsource).toLinearMap =
      t.chartTestSection c hc hct := (rfl)

/-- Applying `chartTestSectionCLE` agrees with `chartTestSection`. -/
theorem chartTestSectionCLE_eq_chartTestSection (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F)) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    t.chartTestSectionCLE c hc hc_symm hct e U hU hcover hsource φ =
      t.chartTestSection c hc hct φ := (rfl)

omit [T2Space M] in
/-- The underlying linear map of the inverse of `chartTestSectionCLE` is `chartTestCoords`. -/
@[simp]
theorem toLinearMap_symm_chartTestSectionCLE :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    (t.chartTestSectionCLE c hc hc_symm hct e U hU hcover hsource).toLinearEquiv.symm.toLinearMap =
      t.chartTestCoords c hc_symm hct hsource := (rfl)

omit [T2Space M] in
/-- Applying the inverse of `chartTestSectionCLE` agrees with `chartTestCoords`. -/
theorem chartTestSectionCLE_symm_eq_chartTestCoords (s : compactlySupported I F n V) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    (t.chartTestSectionCLE c hc hc_symm hct e U hU hcover hsource).symm s =
      t.chartTestCoords c hc_symm hct hsource s := (rfl)

omit [T2Space M] in
/-- Evaluating `chartTestSectionCLE φ` at `x` applies the inverse frame to `φ (c x)`. -/
@[simp]
theorem chartTestSectionCLE_apply (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F)) (x : M) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    (t.chartTestSectionCLE c hc hc_symm hct e U hU hcover hsource φ).1 x =
      t.symmL ℝ x (φ (c x)) := by
  have : T2Space M := T2Space.of_injective_continuous
    (Set.injOn_univ.1 (hsource ▸ c.injOn)) (continuousOn_univ.1 (hsource ▸ c.continuousOn))
  exact t.chartTestSection_apply_of_mem c hc hct φ (hsource.symm ▸ mem_univ x)

omit [T2Space M] in
/-- On the chart target, the inverse of `chartTestSectionCLE` reads the section value in the
defining frame. -/
@[simp]
theorem chartTestSectionCLE_symm_apply_of_mem (s : compactlySupported I F n V) {y : E}
    (hy : y ∈ c.target) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    (t.chartTestSectionCLE c hc hc_symm hct e U hU hcover hsource).symm s y =
      t.continuousLinearMapAt ℝ (c.symm y) (s.1 (c.symm y)) :=
  t.chartTestCoords_apply_of_mem c hc_symm hct hsource s hy

omit [T2Space M] in
/-- Outside the chart target, the inverse of `chartTestSectionCLE` vanishes. -/
@[simp]
theorem chartTestSectionCLE_symm_apply_of_notMem (s : compactlySupported I F n V) {y : E}
    (hy : y ∉ c.target) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    (t.chartTestSectionCLE c hc hc_symm hct e U hU hcover hsource).symm s y = 0 :=
  t.chartTestCoords_apply_of_notMem c hc_symm hct hsource s hy

omit [T2Space M] in
/-- `chartTestSectionCLE` preserves closed support, transported by the inverse chart. -/
@[simp]
theorem tsupport_chartTestSectionCLE (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F)) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    (t.chartTestSectionCLE c hc hc_symm hct e U hU hcover hsource φ).1.tsupport =
      c.symm '' _root_.tsupport φ := by
  have : T2Space M := T2Space.of_injective_continuous
    (Set.injOn_univ.1 (hsource ▸ c.injOn)) (continuousOn_univ.1 (hsource ▸ c.continuousOn))
  exact t.tsupport_chartTestSection c hc hct φ

omit [T2Space M] in
/-- The inverse of `chartTestSectionCLE` preserves closed support, transported by the chart. -/
@[simp]
theorem tsupport_chartTestSectionCLE_symm (s : compactlySupported I F n V) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    _root_.tsupport ((t.chartTestSectionCLE c hc hc_symm hct e U hU hcover hsource).symm s) =
      c '' s.1.tsupport :=
  t.tsupport_chartTestCoords c hc_symm hct hsource s

end GlobalChart

end SingleChart

section OpensEuclidean

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E}
  {V : Ω → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞} [ContMDiffVectorBundle n F V 𝓘(ℝ, E)]

/-- On any open subset `Ω` of a locally compact normed space, a globally trivialized smooth vector
bundle has compactly supported sections continuously linearly equivalent to `𝓓^{n}(Ω, F)`. -/
def opensChartTestSectionCLE
    (t : Trivialization F (π F V)) [MemTrivializationAtlas t] (ht : t.baseSet = univ)
    {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens Ω) (hU : ∀ i, (U i : Set Ω) ⊆ (e i).baseSet)
    (hcover : ∀ x : Ω, ∃ i, x ∈ U i) :
    letI := compactlySupportedTopology (I := 𝓘(ℝ, E)) (n := n) e U hU
    𝓓^{n}(Ω, F) ≃L[ℝ] compactlySupported 𝓘(ℝ, E) F n V := by
  classical
  letI := compactlySupportedTopology (I := 𝓘(ℝ, E)) (n := n) e U hU
  by_cases hΩ : Nonempty Ω
  · let c := Ω.openPartialHomeomorphSubtypeCoe hΩ
    have hΩ_eq : Ω = ⟨c.target, c.open_target⟩ :=
      Opens.ext (Ω.openPartialHomeomorphSubtypeCoe_target hΩ).symm
    let eΩ : 𝓓^{n}(Ω, F) ≃L[ℝ] 𝓓^{n}(⟨c.target, c.open_target⟩, F) :=
      ContinuousLinearEquiv.equivOfInverse
        (TestFunction.monoCLM ℝ) (TestFunction.monoCLM ℝ)
        (fun φ ↦ by ext y; simp [TestFunction.monoCLM_apply, hΩ_eq])
        (fun φ ↦ by ext y; simp [TestFunction.monoCLM_apply, hΩ_eq])
    exact eΩ.trans <| t.chartTestSectionCLE c
      (Ω.contMDiff_openPartialHomeomorphSubtypeCoe hΩ).contMDiffOn
      (Ω.contMDiffOn_openPartialHomeomorphSubtypeCoe_symm hΩ)
      (ht.symm ▸ subset_univ _) e U hU hcover
      (Ω.openPartialHomeomorphSubtypeCoe_source hΩ)
  · -- When `Ω` is empty, both `𝓓^{n}(Ω, F)` and compactly supported sections are subsingletons.
    haveI : IsEmpty Ω := not_nonempty_iff.1 hΩ
    have hzero : ∀ φ : 𝓓^{n}(Ω, F), φ = 0 := fun φ ↦ by
      ext y
      exact φ.zero_on_compl fun hy ↦ hΩ ⟨⟨y, hy⟩⟩
    haveI : Subsingleton 𝓓^{n}(Ω, F) := ⟨fun φ ψ ↦ (hzero φ).trans (hzero ψ).symm⟩
    haveI : Subsingleton (compactlySupported 𝓘(ℝ, E) F n V) :=
      ⟨fun s₁ s₂ ↦ Subtype.ext <| ContMDiffSection.ext fun x ↦ IsEmpty.elim inferInstance x⟩
    exact
      { LinearEquiv.ofSubsingleton _ _ with
        continuous_toFun := continuous_const
        continuous_invFun := continuous_const }

/-- Evaluating `opensChartTestSectionCLE φ` at `x` applies the inverse frame to `φ x`. -/
@[simp]
theorem opensChartTestSectionCLE_apply
    (t : Trivialization F (π F V)) [MemTrivializationAtlas t] (ht : t.baseSet = univ)
    {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens Ω) (hU : ∀ i, (U i : Set Ω) ⊆ (e i).baseSet)
    (hcover : ∀ x : Ω, ∃ i, x ∈ U i)
    (φ : 𝓓^{n}(Ω, F)) (x : Ω) :
    letI := compactlySupportedTopology (I := 𝓘(ℝ, E)) (n := n) e U hU
    (t.opensChartTestSectionCLE ht e U hU hcover φ).1 x = t.symmL ℝ x (φ x) := by
  have hΩ : Nonempty Ω := ⟨x⟩
  have hΩ_eq : Ω = ⟨(Ω.openPartialHomeomorphSubtypeCoe hΩ).target,
      (Ω.openPartialHomeomorphSubtypeCoe hΩ).open_target⟩ :=
    Opens.ext (Ω.openPartialHomeomorphSubtypeCoe_target hΩ).symm
  simp only [opensChartTestSectionCLE, dite_eq_left hΩ, ContinuousLinearEquiv.trans_apply,
    chartTestSectionCLE_apply, ContinuousLinearEquiv.equivOfInverse_apply,
    Opens.openPartialHomeomorphSubtypeCoe_coe, TestFunction.monoCLM_apply, le_rfl, hΩ_eq.le,
    and_self, ↓reduceIte]

/-- On `Ω`, the inverse of `opensChartTestSectionCLE` reads the section value in the frame `t`. -/
@[simp]
theorem opensChartTestSectionCLE_symm_apply_of_mem
    (t : Trivialization F (π F V)) [MemTrivializationAtlas t] (ht : t.baseSet = univ)
    {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens Ω) (hU : ∀ i, (U i : Set Ω) ⊆ (e i).baseSet)
    (hcover : ∀ x : Ω, ∃ i, x ∈ U i)
    (s : compactlySupported 𝓘(ℝ, E) F n V) {y : E} (hy : y ∈ Ω) :
    letI := compactlySupportedTopology (I := 𝓘(ℝ, E)) (n := n) e U hU
    (t.opensChartTestSectionCLE ht e U hU hcover).symm s y =
      t.continuousLinearMapAt ℝ ⟨y, hy⟩ (s.1 ⟨y, hy⟩) := by
  have hΩ : Nonempty Ω := ⟨⟨y, hy⟩⟩
  have hΩ_eq : Ω = ⟨(Ω.openPartialHomeomorphSubtypeCoe hΩ).target,
      (Ω.openPartialHomeomorphSubtypeCoe hΩ).open_target⟩ :=
    Opens.ext (Ω.openPartialHomeomorphSubtypeCoe_target hΩ).symm
  have hyt : y ∈ (Ω.openPartialHomeomorphSubtypeCoe hΩ).target := by
    rwa [Ω.openPartialHomeomorphSubtypeCoe_target hΩ]
  have hsymm : (Ω.openPartialHomeomorphSubtypeCoe hΩ).symm y = ⟨y, hy⟩ := by
    apply Subtype.ext
    simpa only [Opens.openPartialHomeomorphSubtypeCoe_coe] using
      (Ω.openPartialHomeomorphSubtypeCoe hΩ).right_inv hyt
  simp only [opensChartTestSectionCLE, dite_eq_left hΩ, ContinuousLinearEquiv.symm_trans_apply,
    ContinuousLinearEquiv.symm_equivOfInverse, ContinuousLinearEquiv.equivOfInverse_apply,
    TestFunction.monoCLM_apply, le_rfl, hΩ_eq.ge, and_self, ↓reduceIte,
    chartTestSectionCLE_symm_apply_of_mem, hyt]
  rw [hsymm]

/-- Outside `Ω`, the inverse of `opensChartTestSectionCLE` vanishes. -/
@[simp]
theorem opensChartTestSectionCLE_symm_apply_of_notMem
    (t : Trivialization F (π F V)) [MemTrivializationAtlas t] (ht : t.baseSet = univ)
    {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens Ω) (hU : ∀ i, (U i : Set Ω) ⊆ (e i).baseSet)
    (hcover : ∀ x : Ω, ∃ i, x ∈ U i)
    (s : compactlySupported 𝓘(ℝ, E) F n V) {y : E} (hy : y ∉ Ω) :
    letI := compactlySupportedTopology (I := 𝓘(ℝ, E)) (n := n) e U hU
    (t.opensChartTestSectionCLE ht e U hU hcover).symm s y = 0 := by
  let := compactlySupportedTopology (I := 𝓘(ℝ, E)) (n := n) e U hU
  exact ((t.opensChartTestSectionCLE ht e U hU hcover).symm s).zero_on_compl hy

/-- `opensChartTestSectionCLE` preserves closed support, pulled back along the open-subtype
inclusion `Subtype.val : Ω → E`. -/
@[simp]
theorem tsupport_opensChartTestSectionCLE
    (t : Trivialization F (π F V)) [MemTrivializationAtlas t] (ht : t.baseSet = univ)
    {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens Ω) (hU : ∀ i, (U i : Set Ω) ⊆ (e i).baseSet)
    (hcover : ∀ x : Ω, ∃ i, x ∈ U i) (φ : 𝓓^{n}(Ω, F)) :
    letI := compactlySupportedTopology (I := 𝓘(ℝ, E)) (n := n) e U hU
    (t.opensChartTestSectionCLE ht e U hU hcover φ).1.tsupport =
      Subtype.val ⁻¹' _root_.tsupport φ := by
  by_cases hΩ : Nonempty Ω
  · have hmono_coe :
        ⇑(TestFunction.monoCLM ℝ (n₂ := n) (Ω₁ := Ω)
          (Ω₂ := ⟨(Ω.openPartialHomeomorphSubtypeCoe hΩ).target,
            (Ω.openPartialHomeomorphSubtypeCoe hΩ).open_target⟩) φ) = ⇑φ := by
      simp [TestFunction.monoCLM_apply]
    simp only [opensChartTestSectionCLE, dite_eq_left hΩ, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.equivOfInverse_apply, tsupport_chartTestSectionCLE, hmono_coe]
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyt : y ∈ (Ω.openPartialHomeomorphSubtypeCoe hΩ).target := by
        rw [Ω.openPartialHomeomorphSubtypeCoe_target hΩ]
        exact φ.tsupport_subset hy
      have hxy : (x : E) = y := by
        rw [← hyx, ← Ω.openPartialHomeomorphSubtypeCoe_coe hΩ,
          (Ω.openPartialHomeomorphSubtypeCoe hΩ).right_inv hyt]
      simpa only [mem_preimage, hxy] using hy
    · intro hx
      refine ⟨x, hx, ?_⟩
      simpa only [Opens.openPartialHomeomorphSubtypeCoe_coe] using
        (Ω.openPartialHomeomorphSubtypeCoe hΩ).left_inv
          (by rw [Ω.openPartialHomeomorphSubtypeCoe_source hΩ]; exact mem_univ x)
  · have : IsEmpty Ω := not_nonempty_iff.1 hΩ
    exact Subsingleton.elim _ _

/-- The inverse of `opensChartTestSectionCLE` preserves closed support, pushed forward along the
open-subtype inclusion `Subtype.val : Ω → E`. -/
@[simp]
theorem tsupport_opensChartTestSectionCLE_symm
    (t : Trivialization F (π F V)) [MemTrivializationAtlas t] (ht : t.baseSet = univ)
    {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens Ω) (hU : ∀ i, (U i : Set Ω) ⊆ (e i).baseSet)
    (hcover : ∀ x : Ω, ∃ i, x ∈ U i) (s : compactlySupported 𝓘(ℝ, E) F n V) :
    letI := compactlySupportedTopology (I := 𝓘(ℝ, E)) (n := n) e U hU
    _root_.tsupport ((t.opensChartTestSectionCLE ht e U hU hcover).symm s) =
      Subtype.val '' s.1.tsupport := by
  let := compactlySupportedTopology (I := 𝓘(ℝ, E)) (n := n) e U hU
  by_cases hΩ : Nonempty Ω
  · have hΩ_eq : Ω = ⟨(Ω.openPartialHomeomorphSubtypeCoe hΩ).target,
        (Ω.openPartialHomeomorphSubtypeCoe hΩ).open_target⟩ :=
      Opens.ext (Ω.openPartialHomeomorphSubtypeCoe_target hΩ).symm
    simp only [opensChartTestSectionCLE, dite_eq_left hΩ, ContinuousLinearEquiv.symm_trans_apply,
      ContinuousLinearEquiv.symm_equivOfInverse, ContinuousLinearEquiv.equivOfInverse_apply,
      TestFunction.monoCLM_apply, le_rfl, hΩ_eq.ge, and_self, ↓reduceIte,
      tsupport_chartTestSectionCLE_symm, Opens.openPartialHomeomorphSubtypeCoe_coe]
  · have : IsEmpty Ω := not_nonempty_iff.1 hΩ
    have h0 : ⇑((t.opensChartTestSectionCLE ht e U hU hcover).symm s) = 0 := by
      funext y
      exact opensChartTestSectionCLE_symm_apply_of_notMem t ht e U hU hcover s
        (fun hy ↦ hΩ ⟨⟨y, hy⟩⟩)
    rw [h0, _root_.tsupport_zero, eq_empty_of_isEmpty s.1.tsupport, image_empty]

end OpensEuclidean

end Bundle.Trivialization

namespace Bundle.Trivial

open ContMDiffSection

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞}

/-- **Euclidean trivial-bundle LF equivalence.** On an open subset `Ω` of a locally compact normed
space, compactly supported smooth sections of the trivial bundle `Bundle.Trivial Ω F` are
continuously linearly equivalent to the native LF test-function space `𝓓^{n}(Ω, F)`. -/
def opensTestSectionCLE (Ω : Opens E)
    {ι : Type*} (e : ι → Trivialization F (π F (Bundle.Trivial Ω F)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens Ω) (hU : ∀ i, (U i : Set Ω) ⊆ (e i).baseSet)
    (hcover : ∀ x : Ω, ∃ i, x ∈ U i) :
    letI := compactlySupportedTopology (I := 𝓘(ℝ, E)) (n := n) e U hU
    𝓓^{n}(Ω, F) ≃L[ℝ] compactlySupported 𝓘(ℝ, E) F n (Bundle.Trivial Ω F) :=
  haveI : MemTrivializationAtlas (Bundle.Trivial.trivialization Ω F) := ⟨mem_singleton _⟩
  (Bundle.Trivial.trivialization Ω F).opensChartTestSectionCLE
    (Bundle.Trivial.trivialization_baseSet Ω F) e U hU hcover

/-- Evaluating `opensTestSectionCLE Ω φ` at `x : Ω` recovers `φ x`. -/
@[simp]
theorem opensTestSectionCLE_apply (Ω : Opens E)
    {ι : Type*} (e : ι → Trivialization F (π F (Bundle.Trivial Ω F)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens Ω) (hU : ∀ i, (U i : Set Ω) ⊆ (e i).baseSet)
    (hcover : ∀ x : Ω, ∃ i, x ∈ U i)
    (φ : 𝓓^{n}(Ω, F)) (x : Ω) :
    letI := compactlySupportedTopology (I := 𝓘(ℝ, E)) (n := n) e U hU
    (opensTestSectionCLE (n := n) Ω e U hU hcover φ).1 x = φ x := by
  have : MemTrivializationAtlas (Bundle.Trivial.trivialization Ω F) := ⟨mem_singleton _⟩
  rw [opensTestSectionCLE, Trivialization.opensChartTestSectionCLE_apply,
    symmL_trivialization, ContinuousLinearMap.id_apply]

/-- On `Ω`, the inverse of `opensTestSectionCLE Ω` evaluates the trivial-bundle section at
`⟨y, hy⟩`. -/
@[simp]
theorem opensTestSectionCLE_symm_apply_of_mem (Ω : Opens E)
    {ι : Type*} (e : ι → Trivialization F (π F (Bundle.Trivial Ω F)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens Ω) (hU : ∀ i, (U i : Set Ω) ⊆ (e i).baseSet)
    (hcover : ∀ x : Ω, ∃ i, x ∈ U i)
    (s : compactlySupported 𝓘(ℝ, E) F n (Bundle.Trivial Ω F)) {y : E} (hy : y ∈ Ω) :
    letI := compactlySupportedTopology (I := 𝓘(ℝ, E)) (n := n) e U hU
    (opensTestSectionCLE (n := n) Ω e U hU hcover).symm s y = s.1 ⟨y, hy⟩ := by
  have : MemTrivializationAtlas (Bundle.Trivial.trivialization Ω F) := ⟨mem_singleton _⟩
  simp only [opensTestSectionCLE, Trivialization.opensChartTestSectionCLE_symm_apply_of_mem, hy,
    continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply]

/-- Outside `Ω`, the inverse of `opensTestSectionCLE Ω` vanishes. -/
@[simp]
theorem opensTestSectionCLE_symm_apply_of_notMem (Ω : Opens E)
    {ι : Type*} (e : ι → Trivialization F (π F (Bundle.Trivial Ω F)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens Ω) (hU : ∀ i, (U i : Set Ω) ⊆ (e i).baseSet)
    (hcover : ∀ x : Ω, ∃ i, x ∈ U i)
    (s : compactlySupported 𝓘(ℝ, E) F n (Bundle.Trivial Ω F)) {y : E} (hy : y ∉ Ω) :
    letI := compactlySupportedTopology (I := 𝓘(ℝ, E)) (n := n) e U hU
    (opensTestSectionCLE (n := n) Ω e U hU hcover).symm s y = 0 := by
  have : MemTrivializationAtlas (Bundle.Trivial.trivialization Ω F) := ⟨mem_singleton _⟩
  simp only [opensTestSectionCLE, Trivialization.opensChartTestSectionCLE_symm_apply_of_notMem, hy,
    not_false_eq_true]

/-- `opensTestSectionCLE Ω` preserves closed support, pulled back along the open-subtype inclusion
`Subtype.val : Ω → E`. -/
@[simp]
theorem tsupport_opensTestSectionCLE (Ω : Opens E)
    {ι : Type*} (e : ι → Trivialization F (π F (Bundle.Trivial Ω F)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens Ω) (hU : ∀ i, (U i : Set Ω) ⊆ (e i).baseSet)
    (hcover : ∀ x : Ω, ∃ i, x ∈ U i) (φ : 𝓓^{n}(Ω, F)) :
    letI := compactlySupportedTopology (I := 𝓘(ℝ, E)) (n := n) e U hU
    (opensTestSectionCLE (n := n) Ω e U hU hcover φ).1.tsupport =
      Subtype.val ⁻¹' _root_.tsupport φ := by
  have : MemTrivializationAtlas (Bundle.Trivial.trivialization Ω F) := ⟨mem_singleton _⟩
  rw [opensTestSectionCLE, Trivialization.tsupport_opensChartTestSectionCLE]

/-- The inverse of `opensTestSectionCLE Ω` preserves closed support, pushed forward along the
open-subtype inclusion `Subtype.val : Ω → E`. -/
@[simp]
theorem tsupport_opensTestSectionCLE_symm (Ω : Opens E)
    {ι : Type*} (e : ι → Trivialization F (π F (Bundle.Trivial Ω F)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens Ω) (hU : ∀ i, (U i : Set Ω) ⊆ (e i).baseSet)
    (hcover : ∀ x : Ω, ∃ i, x ∈ U i)
    (s : compactlySupported 𝓘(ℝ, E) F n (Bundle.Trivial Ω F)) :
    letI := compactlySupportedTopology (I := 𝓘(ℝ, E)) (n := n) e U hU
    _root_.tsupport ((opensTestSectionCLE (n := n) Ω e U hU hcover).symm s) =
      Subtype.val '' s.1.tsupport := by
  have : MemTrivializationAtlas (Bundle.Trivial.trivialization Ω F) := ⟨mem_singleton _⟩
  rw [opensTestSectionCLE, Trivialization.tsupport_opensChartTestSectionCLE_symm]

end Bundle.Trivial

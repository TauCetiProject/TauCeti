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

private def chartTestSupportedInToTarget {K : Compacts E} (hK : (K : Set E) ⊆ c.target) :
    supportedIn I F n V (c.symm '' K) →ₗ[ℝ] 𝓓^{n}_{K}(E, F) :=
  let K_M : Compacts M :=
    ⟨c.symm '' K, K.isCompact.image_of_continuousOn (c.continuousOn_symm.mono hK)⟩
  have hKM : (K_M : Set M) ⊆ c.source := image_subset_iff.2 fun _ hy ↦ c.map_target (hK hy)
  have hKe : c '' (K_M : Set M) = K := by
    ext y
    simp only [K_M, Compacts.coe_mk, mem_image]
    exact ⟨fun ⟨_, ⟨z, hz, rfl⟩, hzy⟩ ↦ hzy ▸ (c.right_inv (hK hz)).symm ▸ hz,
      fun hy ↦ ⟨c.symm y, ⟨y, hy, rfl⟩, c.right_inv (hK hy)⟩⟩
  { toFun s :=
      ⟨t.chartTestSupportedIn c hc_symm hct hKM s,
        (t.chartTestSupportedIn c hc_symm hct hKM s).contDiff,
        fun y hy ↦ (t.chartTestSupportedIn c hc_symm hct hKM s).zero_on_compl
          (by simpa only [Compacts.coe_mk, hKe] using hy)⟩
    map_add' s₁ s₂ := by
      ext y
      exact congrFun (congrArg DFunLike.coe
        ((t.chartTestSupportedIn c hc_symm hct hKM).map_add s₁ s₂)) y
    map_smul' a s := by
      ext y
      exact congrFun (congrArg DFunLike.coe
        ((t.chartTestSupportedIn c hc_symm hct hKM).map_smul a s)) y }

include hcover in
/-- On any fixed compact subset `K` of a smooth chart target, chart extension is a continuous
linear equivalence between `𝓓^{n}_{K}(E, F)` and the fixed-support stage `c.symm '' K` in the
compact derivative section topology. -/
def chartTestSectionSupportedInCLE {K : Compacts E} (hK : (K : Set E) ⊆ c.target) :
    letI := frameTopology (I := I) (n := n) e U hU
    𝓓^{n}_{K}(E, F) ≃L[ℝ] supportedIn I F n V (c.symm '' K) :=
  letI := frameTopology (I := I) (n := n) e U hU
  let Ω : Opens E := ⟨c.target, c.open_target⟩
  let K_M : Compacts M :=
    ⟨c.symm '' K, K.isCompact.image_of_continuousOn (c.continuousOn_symm.mono hK)⟩
  have hKM : (K_M : Set M) ⊆ c.source := image_subset_iff.2 fun _ hy ↦ c.map_target (hK hy)
  let toFunLM : 𝓓^{n}_{K}(E, F) →ₗ[ℝ] supportedIn I F n V (c.symm '' K) :=
    { toFun φ := ⟨(t.chartTestSection c hc hct (TestFunction.ofSupportedIn (Ω := Ω) hK φ)).1,
        t.chartTestSection_mem_supportedIn c hc hct _ (by
          rw [TestFunction.coe_ofSupportedIn]
          exact φ.tsupport_subset)⟩
      map_add' φ ψ := Subtype.ext <| by
        have hadd : TestFunction.ofSupportedIn (Ω := Ω) hK (φ + ψ) =
            TestFunction.ofSupportedIn (Ω := Ω) hK φ +
              TestFunction.ofSupportedIn (Ω := Ω) hK ψ := by
          ext y
          simp
        simp only [Submodule.coe_add, hadd]
        exact congrArg Subtype.val ((t.chartTestSection c hc hct).map_add _ _)
      map_smul' a φ := Subtype.ext <| by
        have hsmul : TestFunction.ofSupportedIn (Ω := Ω) hK (a • φ) =
            a • TestFunction.ofSupportedIn (Ω := Ω) hK φ := by
          ext y
          simp
        simp only [RingHom.id_apply, SetLike.val_smul, hsmul]
        exact congrArg Subtype.val ((t.chartTestSection c hc hct).map_smul a _) }
  { toLinearMap := toFunLM
    invFun := t.chartTestSupportedInToTarget c hc_symm hct hK
    left_inv φ := by
      ext y
      exact congrFun (t.chartTestSupportedIn_chartTestSection_ofSupportedIn c hc_symm hct hc hK φ) y
    right_inv s := by
      apply Subtype.ext
      have hre := t.chartTestSection_ofSupportedIn_chartTestSupportedIn c hc_symm hct hc hKM s
      have heq : TestFunction.ofSupportedIn (Ω := Ω) hK
          (t.chartTestSupportedInToTarget c hc_symm hct hK s) =
          TestFunction.ofSupportedIn (Ω := Ω) (K := ⟨c '' (K_M : Set M), _⟩)
            (image_subset_iff.2 fun _ hx ↦ c.map_source (hKM hx))
            (t.chartTestSupportedIn c hc_symm hct hKM s) := by
        ext y
        rfl
      rw [LinearMap.toFun_eq_coe]
      simpa only [toFunLM, LinearMap.coe_mk, AddHom.coe_mk, heq, ofSupportedIn_apply] using
        congrArg Subtype.val hre
    continuous_toFun := Continuous.subtype_mk
      ((continuous_frameTopology_iff_frameCoordinates e U hU).2 fun i ↦
        t.continuous_frameCoordinates_chartTestSection_ofSupportedIn c hc hct hK (e i) (hU i)) _
    continuous_invFun := by
      have hcont := t.continuous_chartTestSupportedIn c hc_symm hct hKM e U hU hcover
      refine (ContDiffMapSupportedIn.continuous_iff_comp_order_le _).2 fun m hm ↦ ?_
      refine ((ContDiffMapSupportedIn.continuous_iff_comp_order_le _).1 hcont m hm).congr fun s ↦ ?_
      ext y
      simp only [Function.comp_apply, ContDiffMapSupportedIn.structureMapCLM_apply, hm]
      rfl }

/-- The forward map of `chartTestSectionSupportedInCLE` agrees with `chartTestSection`. -/
@[simp]
theorem coe_chartTestSectionSupportedInCLE {K : Compacts E} (hK : (K : Set E) ⊆ c.target)
    (φ : 𝓓^{n}_{K}(E, F)) :
    letI := frameTopology (I := I) (n := n) e U hU
    ((t.chartTestSectionSupportedInCLE c hc hc_symm hct e U hU hcover hK φ).1 : Cₛ^n⟮I; F, V⟯) =
      (t.chartTestSection c hc hct
        (TestFunction.ofSupportedIn (Ω := ⟨c.target, c.open_target⟩) hK φ)).1 := (rfl)

/-- On the chart target, the inverse of `chartTestSectionSupportedInCLE` reads the section value in
the defining frame. -/
@[simp]
theorem chartTestSectionSupportedInCLE_symm_apply_of_mem {K : Compacts E}
    (hK : (K : Set E) ⊆ c.target)
    (s : supportedIn I F n V (c.symm '' K)) {y : E} (hy : y ∈ c.target) :
    letI := frameTopology (I := I) (n := n) e U hU
    (t.chartTestSectionSupportedInCLE c hc hc_symm hct e U hU hcover hK).symm s y =
      t.continuousLinearMapAt ℝ (c.symm y) (s.1 (c.symm y)) :=
  t.chartTestSupportedIn_apply_of_mem c hc_symm hct
    (K := ⟨c.symm '' K, K.isCompact.image_of_continuousOn (c.continuousOn_symm.mono hK)⟩)
    (image_subset_iff.2 fun _ hz ↦ c.map_target (hK hz)) s hy

/-- Outside the chart target, the inverse of `chartTestSectionSupportedInCLE` vanishes. -/
@[simp]
theorem chartTestSectionSupportedInCLE_symm_apply_of_notMem {K : Compacts E}
    (hK : (K : Set E) ⊆ c.target)
    (s : supportedIn I F n V (c.symm '' K)) {y : E} (hy : y ∉ c.target) :
    letI := frameTopology (I := I) (n := n) e U hU
    (t.chartTestSectionSupportedInCLE c hc hc_symm hct e U hU hcover hK).symm s y = 0 :=
  t.chartTestSupportedIn_apply_of_notMem c hc_symm hct
    (K := ⟨c.symm '' K, K.isCompact.image_of_continuousOn (c.continuousOn_symm.mono hK)⟩)
    (image_subset_iff.2 fun _ hz ↦ c.map_target (hK hz)) s hy

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
  let K' : Compacts E := ⟨c '' K, K.isCompact.image_of_continuousOn (c.continuousOn.mono hK)⟩
  have hK' : (K' : Set E) ⊆ c.target := image_subset_iff.2 fun _ hx ↦ c.map_source (hK hx)
  refine ((TestFunction.ofSupportedInCLM ℝ (Ω := ⟨c.target, c.open_target⟩) hK').continuous.comp
    (t.continuous_chartTestSupportedIn c hc_symm hct hK e U hU hcover)).congr fun s ↦ ?_
  ext y
  rw [Function.comp_apply, Function.comp_apply, TestFunction.coe_ofSupportedInCLM,
    TestFunction.coe_ofSupportedIn]
  by_cases hy : y ∈ c.target
  · rw [chartTestSupportedIn_apply_of_mem _ _ _ _ _ _ hy,
      chartTestCoords_apply_of_mem _ _ _ _ _ _ hy, ofSupportedIn_apply]
  · rw [chartTestSupportedIn_apply_of_notMem _ _ _ _ _ _ hy,
      chartTestCoords_apply_of_notMem _ _ _ _ _ _ hy]

include hcover in
/-- **Single-chart LF equivalence.** On a manifold covered by a single smooth chart subordinate to
a smooth bundle frame, chart extension is a continuous linear equivalence between the native
Euclidean LF test space `𝓓^{n}(⟨c.target, c.open_target⟩, F)` and compactly supported bundle
sections with `compactlySupportedTopology`. -/
def chartTestSectionCLE :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    𝓓^{n}(⟨c.target, c.open_target⟩, F) ≃L[ℝ] compactlySupported I F n V :=
  letI := compactlySupportedTopology (I := I) (n := n) e U hU
  { toLinearMap := t.chartTestSection c hc hct
    invFun := t.chartTestCoords c hc_symm hct hsource
    left_inv φ := by
      ext y
      rw [LinearMap.toFun_eq_coe]
      by_cases hy : y ∈ c.target
      · rw [chartTestCoords_apply_of_mem t c hc_symm hct hsource _ hy,
          t.continuousLinearMapAt_chartTestSection c hc hct φ (c.map_target hy), c.right_inv hy]
      · rw [chartTestCoords_apply_of_notMem t c hc_symm hct hsource _ hy]
        exact (φ.zero_on_compl hy).symm
    right_inv s := by
      apply Subtype.ext
      ext x
      rw [LinearMap.toFun_eq_coe]
      have hx : x ∈ c.source := hsource.symm ▸ mem_univ x
      rw [chartTestSection_apply_of_mem t c hc hct _ hx,
        chartTestCoords_apply_of_mem t c hc_symm hct hsource s (c.map_source hx),
        c.left_inv hx, t.symmL_continuousLinearMapAt (hct hx)]
    continuous_toFun := t.continuous_chartTestSection c hc hct e U hU
    continuous_invFun := t.continuous_chartTestCoords c hc_symm hct e U hU hcover hsource }

/-- The underlying linear map of `chartTestSectionCLE` is `chartTestSection`. -/
@[simp]
theorem toLinearMap_chartTestSectionCLE :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    (t.chartTestSectionCLE c hc hc_symm hct e U hU hcover hsource).toLinearMap =
      t.chartTestSection c hc hct := (rfl)

/-- Evaluating `chartTestSectionCLE φ` at `x` applies the inverse frame to `φ (c x)`. -/
@[simp]
theorem chartTestSectionCLE_apply (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F)) (x : M) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    (t.chartTestSectionCLE c hc hc_symm hct e U hU hcover hsource φ).1 x =
      t.symmL ℝ x (φ (c x)) :=
  t.chartTestSection_apply_of_mem c hc hct φ (hsource.symm ▸ mem_univ x)

/-- On the chart target, the inverse of `chartTestSectionCLE` reads the section value in the
defining frame. -/
@[simp]
theorem chartTestSectionCLE_symm_apply_of_mem (s : compactlySupported I F n V) {y : E}
    (hy : y ∈ c.target) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    (t.chartTestSectionCLE c hc hc_symm hct e U hU hcover hsource).symm s y =
      t.continuousLinearMapAt ℝ (c.symm y) (s.1 (c.symm y)) :=
  t.chartTestCoords_apply_of_mem c hc_symm hct hsource s hy

/-- Outside the chart target, the inverse of `chartTestSectionCLE` vanishes. -/
@[simp]
theorem chartTestSectionCLE_symm_apply_of_notMem (s : compactlySupported I F n V) {y : E}
    (hy : y ∉ c.target) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    (t.chartTestSectionCLE c hc hc_symm hct e U hU hcover hsource).symm s y = 0 :=
  t.chartTestCoords_apply_of_notMem c hc_symm hct hsource s hy

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

/-- `Opens.openPartialHomeomorphSubtypeCoe` with `target` definitionally equal to `(Ω : Set E)`. -/
private def opensSubtypeChart (hΩ : Nonempty Ω) : OpenPartialHomeomorph Ω E where
  toPartialEquiv := (Ω.openPartialHomeomorphSubtypeCoe hΩ).toPartialEquiv.copy Subtype.val
    (Ω.openPartialHomeomorphSubtypeCoe_coe hΩ)
    (Ω.openPartialHomeomorphSubtypeCoe hΩ).symm rfl univ
    (Ω.openPartialHomeomorphSubtypeCoe_source hΩ) Ω
    (Ω.openPartialHomeomorphSubtypeCoe_target hΩ)
  open_source := isOpen_univ
  open_target := Ω.isOpen
  continuousOn_toFun := continuous_subtype_val.continuousOn
  continuousOn_invFun := by
    have h : ContinuousOn (Ω.openPartialHomeomorphSubtypeCoe hΩ).symm (Ω : Set E) := by
      rw [← Ω.openPartialHomeomorphSubtypeCoe_target hΩ]
      exact (Ω.openPartialHomeomorphSubtypeCoe hΩ).continuousOn_symm
    exact h

omit [NormedSpace ℝ E] [LocallyCompactSpace E] in
private theorem opensSubtypeChart_source (hΩ : Nonempty Ω) :
    (opensSubtypeChart hΩ).source = univ := rfl

omit [LocallyCompactSpace E] in
private theorem contMDiffOn_opensSubtypeChart (hΩ : Nonempty Ω) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) n (opensSubtypeChart hΩ) (opensSubtypeChart hΩ).source :=
  contMDiff_subtype_val.contMDiffOn

omit [LocallyCompactSpace E] in
private theorem contMDiffOn_opensSubtypeChart_symm (hΩ : Nonempty Ω) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) n (opensSubtypeChart hΩ).symm (opensSubtypeChart hΩ).target := by
  intro y hy
  refine ((TauCeti.ContMDiffAt.subtypeVal_comp_iff Ω _ y).mp ?_).contMDiffWithinAt
  refine contMDiffAt_id.congr_of_eventuallyEq ?_
  filter_upwards [Ω.isOpen.mem_nhds hy] with z hz
  exact (opensSubtypeChart hΩ).right_inv hz

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
  · exact t.chartTestSectionCLE (opensSubtypeChart hΩ)
      (contMDiffOn_opensSubtypeChart hΩ) (contMDiffOn_opensSubtypeChart_symm hΩ)
      (ht.symm ▸ subset_univ _) e U hU hcover (opensSubtypeChart_source hΩ)
  · -- When `Ω` is empty, both `𝓓^{n}(Ω, F)` and compactly supported sections are subsingletons.
    haveI : IsEmpty Ω := not_nonempty_iff.1 hΩ
    have hzero : ∀ φ : 𝓓^{n}(Ω, F), φ = 0 := fun φ ↦ by
      ext y
      exact φ.zero_on_compl fun hy ↦ hΩ ⟨⟨y, hy⟩⟩
    haveI : Subsingleton 𝓓^{n}(Ω, F) := ⟨fun φ ψ ↦ (hzero φ).trans (hzero ψ).symm⟩
    haveI : Subsingleton (compactlySupported 𝓘(ℝ, E) F n V) :=
      ⟨fun s₁ s₂ ↦ Subtype.ext <| ContMDiffSection.ext fun x ↦ IsEmpty.elim inferInstance x⟩
    exact
      { toFun := 0
        invFun := 0
        map_add' _ _ := Subsingleton.elim _ _
        map_smul' _ _ := Subsingleton.elim _ _
        left_inv _ := Subsingleton.elim _ _
        right_inv _ := Subsingleton.elim _ _
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
  simp only [opensChartTestSectionCLE, hΩ, ↓reduceDIte]
  exact t.chartTestSectionCLE_apply (opensSubtypeChart hΩ)
    (contMDiffOn_opensSubtypeChart hΩ) (contMDiffOn_opensSubtypeChart_symm hΩ)
    (ht.symm ▸ subset_univ _) e U hU hcover (opensSubtypeChart_source hΩ) φ x

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
  simp only [opensChartTestSectionCLE, hΩ, ↓reduceDIte]
  have hyt : y ∈ (opensSubtypeChart hΩ).target := hy
  have hsymm : (opensSubtypeChart hΩ).symm y = ⟨y, hy⟩ :=
    Subtype.ext ((opensSubtypeChart hΩ).right_inv hyt)
  refine (t.chartTestSectionCLE_symm_apply_of_mem (opensSubtypeChart hΩ)
    (contMDiffOn_opensSubtypeChart hΩ) (contMDiffOn_opensSubtypeChart_symm hΩ)
    (ht.symm ▸ subset_univ _) e U hU hcover (opensSubtypeChart_source hΩ) s hyt).trans ?_
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
  by_cases hΩ : Nonempty Ω
  · simp only [opensChartTestSectionCLE, hΩ, ↓reduceDIte]
    exact t.chartTestSectionCLE_symm_apply_of_notMem (opensSubtypeChart hΩ)
      (contMDiffOn_opensSubtypeChart hΩ) (contMDiffOn_opensSubtypeChart_symm hΩ)
      (ht.symm ▸ subset_univ _) e U hU hcover (opensSubtypeChart_source hΩ) s hy
  · simp only [opensChartTestSectionCLE, hΩ, ↓reduceDIte]
    rfl

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
    Trivialization.symmL_apply _ (mem_univ x), trivialization_symm_apply]

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
  rw [opensTestSectionCLE,
    Trivialization.opensChartTestSectionCLE_symm_apply_of_mem _ _ _ _ _ _ s hy,
    Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ (mem_univ _)]
  rfl

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
  exact Trivialization.opensChartTestSectionCLE_symm_apply_of_notMem _ _ _ _ _ _ s hy

end Bundle.Trivial

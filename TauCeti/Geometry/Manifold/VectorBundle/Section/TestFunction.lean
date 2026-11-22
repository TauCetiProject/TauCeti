/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
public import Mathlib.Analysis.Distribution.TestFunction
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Native test functions in bundle charts

A smooth coordinate chart subordinate to a smooth bundle frame sends a native test function
on its target to a compactly supported smooth section. On the chart source the section is
obtained by applying the inverse frame to the test function's value in coordinates; elsewhere
it is zero. Its closed support is exactly the inverse chart image of the test function's closed
support. In particular this map is injective and sends support bounds `tsupport φ ⊆ K`
to support bounds in `c.symm '' K` (`ContMDiffSection.ChartTestData` packages these admissible
chart-trivialization pairs). When the vector bundle also carries a compatible structure over a
normed `ℝ`-algebra `𝕜'`, chart extension commutes with `𝕜'`-scalars
(`Bundle.Trivialization.chartTestSectionOfNormedAlgebra`).

In the reverse direction, a chart `c` with `C^n` inverse subordinate to a smooth bundle frame `t`
reads sections supported in a compact subset `K ⊆ c.source` back into `𝓓^{n}_{c '' K}(E, F)` and
`𝓓^{n}(⟨c.target, c.open_target⟩, F)` (`Bundle.Trivialization.chartReadSupportedIn`,
`Bundle.Trivialization.chartReadTestFunction`), and reads arbitrary sections localized by a
compactly supported `C^n` cutoff `ρ` with `tsupport ρ ⊆ c.source` into
`𝓓^{n}(⟨c.target, c.open_target⟩, F)` (`Bundle.Trivialization.chartCutoffTestFunction`).
On a Hausdorff base when `c` is also forward `C^n`, extending these readings by zero recovers the
original or localized section (`Bundle.Trivialization.chartTestSection_chartReadTestFunction`,
`Bundle.Trivialization.chartTestSection_chartCutoffTestFunction`). This chart-reading, cutoff, and
extension-back API is adapted from `Bundle.Trivialization.chartLocalization` and
`Bundle.Trivialization.chartTestSection_chartLocalization` in
`TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization`.

These are algebraic chart extension and chart-reading maps for constructing locally convex
test-section spaces. No topology on compactly supported sections is installed here. Extension only
needs forward `C^n` regularity of the chart, while reading only needs inverse `C^n` regularity;
neither requires finite-dimensional fibres or a countable atlas.

The exact nonzero-locus formula is adapted from Tau Ceti PR #22144
(commit `8cab1a135d7b2826fcb4508770e82aebf9713614`).
-/

public noncomputable section

open Bundle Set Filter TopologicalSpace
open scoped Manifold ContDiff Distributions Topology

namespace Bundle.Trivialization

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞} [ContMDiffVectorBundle n F V I]

section

variable (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
  (c : OpenPartialHomeomorph M E)
  (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source) (hce : c.source ⊆ e.baseSet)

private def testSection (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F)) (x : M) : V x := by
  classical
  exact if x ∈ c.source then e.symmL ℝ x (φ (c x)) else 0

omit [T2Space M] in
private theorem testSection_of_mem (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F))
    {x : M} (hx : x ∈ c.source) :
    testSection e c φ x = e.symmL ℝ x (φ (c x)) := by
  simp [testSection, hx]

omit [T2Space M] in
private theorem testSection_eq_zero (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F))
    {x : M} (hx : x ∉ c.symm '' tsupport φ) : testSection e c φ x = 0 := by
  by_cases hs : x ∈ c.source
  · have hφ : c x ∉ tsupport φ := fun h ↦ hx ⟨c x, h, c.left_inv hs⟩
    simp [testSection, hs, image_eq_zero_of_notMem_tsupport hφ]
  · simp [testSection, hs]

omit [T2Space M] in
private theorem isCompact_symm_image_tsupport (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F)) :
    IsCompact (c.symm '' tsupport φ) :=
  φ.hasCompactSupport.image_of_continuousOn (c.continuousOn_symm.mono φ.tsupport_subset)

include hc hce in
private theorem contMDiff_testSection (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F)) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) n (fun x ↦ TotalSpace.mk' F x (testSection e c φ x)) := by
  intro x
  by_cases hx : x ∈ c.source
  · apply (e.contMDiffAt_section_iff (hce hx)).2
    refine (φ.contDiff.contMDiff.contMDiffAt.comp x
      (hc.contMDiffAt (c.open_source.mem_nhds hx))).congr_of_eventuallyEq ?_
    filter_upwards [c.open_source.mem_nhds hx] with y hy
    rw [testSection_of_mem e c φ hy, ← e.continuousLinearMapAt_apply_of_mem (R := ℝ) (hce hy),
      e.continuousLinearMapAt_symmL (hce hy)]
    rfl
  · have hclosed := (isCompact_symm_image_tsupport c φ).isClosed
    have hx' : x ∉ c.symm '' tsupport φ := by
      rintro ⟨y, hy, rfl⟩
      exact hx (c.map_target (φ.tsupport_subset hy))
    refine (Bundle.contMDiff_zeroSection ℝ V x).congr_of_eventuallyEq ?_
    filter_upwards [hclosed.isOpen_compl.mem_nhds hx'] with y hy
    rw [testSection_eq_zero e c φ hy]
    simp [Bundle.zeroSection]

private theorem tsupport_testSection_subset (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F)) :
    (⟨testSection e c φ, contMDiff_testSection e c hc hce φ⟩ : Cₛ^n⟮I; F, V⟯).tsupport ⊆
      c.symm '' tsupport φ := by
  apply (ContMDiffSection.tsupport_subset_iff (isCompact_symm_image_tsupport c φ).isClosed).2
  exact fun x hx ↦ testSection_eq_zero e c φ hx

/-- Extend a native test function through a coordinate chart and a bundle frame, by zero
outside the chart source. The codomain is the existing compactly supported section submodule;
this map does not choose a topology on it. -/
def chartTestSection : 𝓓^{n}(⟨c.target, c.open_target⟩, F) →ₗ[ℝ]
    ContMDiffSection.compactlySupported I F n V where
  toFun φ := by
    let s : Cₛ^n⟮I; F, V⟯ := ⟨testSection e c φ, contMDiff_testSection e c hc hce φ⟩
    refine ⟨s, ContMDiffSection.mem_compactlySupported.2 ?_⟩
    exact (isCompact_symm_image_tsupport c φ).of_isClosed_subset s.isClosed_tsupport
      (tsupport_testSection_subset e c hc hce φ)
  map_add' φ ψ := by
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ c.source <;> simp [testSection, hx]
  map_smul' a φ := by
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ c.source <;> simp [testSection, hx]

/-- On the chart source, extension is the inverse frame applied to the coefficient value. -/
theorem chartTestSection_apply_of_mem (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F))
    {x : M} (hx : x ∈ c.source) :
    (e.chartTestSection c hc hce φ).val x = e.symmL ℝ x (φ (c x)) :=
  testSection_of_mem e c φ hx

/-- The section vanishes outside the chart source. -/
@[simp]
theorem chartTestSection_apply_of_notMem (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F))
    {x : M} (hx : x ∉ c.source) : (e.chartTestSection c hc hce φ).val x = 0 := by
  simp [chartTestSection, testSection, hx]

/-- Reading the extended section in its defining frame recovers the native test function. -/
@[simp]
theorem continuousLinearMapAt_chartTestSection (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F))
    {x : M} (hx : x ∈ c.source) :
    e.continuousLinearMapAt ℝ x ((e.chartTestSection c hc hce φ).val x) = φ (c x) := by
  rw [chartTestSection_apply_of_mem e c hc hce φ hx, e.continuousLinearMapAt_symmL (hce hx)]

/-- Native test functions are determined by their extended bundle sections. -/
theorem chartTestSection_injective : Function.Injective (e.chartTestSection c hc hce) := by
  intro φ ψ h
  ext y
  by_cases hy : y ∈ c.target
  · have hval := congrArg (fun s : ContMDiffSection.compactlySupported I F n V ↦
      e.continuousLinearMapAt ℝ (c.symm y) (s.val (c.symm y))) h
    simpa [continuousLinearMapAt_chartTestSection e c hc hce _ (c.map_target hy),
      c.right_inv hy] using hval
  · exact (φ.zero_on_compl hy).trans (ψ.zero_on_compl hy).symm

/-- Extension preserves the exact nonzero locus, transported by the inverse chart. -/
theorem support_chartTestSection (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F)) :
    {x | (e.chartTestSection c hc hce φ).val x ≠ 0} = c.symm '' Function.support φ := by
  ext x
  by_cases hx : x ∈ c.source
  · rw [mem_ofPred_eq, chartTestSection_apply_of_mem e c hc hce φ hx]
    constructor
    · intro h
      refine ⟨c x, ?_, c.left_inv hx⟩
      intro hz
      exact h (by simp [hz])
    · rintro ⟨y, hy, hxy⟩ hz
      have hyt := φ.tsupport_subset (subset_tsupport φ hy)
      have heq : c x = y := by rw [← hxy, c.right_inv hyt]
      have := congrArg (e.continuousLinearMapAt ℝ x) hz
      exact hy (by simpa [e.continuousLinearMapAt_symmL (hce hx), heq] using this)
  · simp only [chartTestSection_apply_of_notMem e c hc hce φ hx,
      ne_self_iff_false, mem_ofPred_eq, false_iff, mem_image, not_exists, not_and]
    intro y hy hxy
    exact hx (hxy ▸ c.map_target (φ.tsupport_subset (subset_tsupport φ hy)))

/-- Extension preserves the exact closed support, transported by the inverse chart. -/
@[simp]
theorem tsupport_chartTestSection (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F)) :
    (e.chartTestSection c hc hce φ).val.tsupport = c.symm '' tsupport φ := by
  apply le_antisymm
  · exact tsupport_testSection_subset e c hc hce φ
  · rw [ContMDiffSection.tsupport_def, support_chartTestSection]
    exact (c.continuousOn_symm.mono φ.tsupport_subset).image_closure

/-- The closed support of an extended test lies entirely in the chart source. -/
theorem tsupport_chartTestSection_subset_source (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F)) :
    (e.chartTestSection c hc hce φ).val.tsupport ⊆ c.source := by
  rw [tsupport_chartTestSection]
  exact image_subset_iff.2 fun _ hy ↦ c.map_target (φ.tsupport_subset hy)

/-- A support bound in an arbitrary set `K` becomes a support bound in `c.symm '' K`. -/
theorem chartTestSection_mem_supportedIn (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F))
    {K : Set E} (hφ : tsupport φ ⊆ K) :
    (e.chartTestSection c hc hce φ).val ∈ ContMDiffSection.supportedIn I F n V (c.symm '' K) := by
  rw [ContMDiffSection.mem_supportedIn, tsupport_chartTestSection]
  exact image_mono hφ

/-- In a second bundle frame, the extended section has the actual vector-bundle transition
applied to its defining coefficients. -/
theorem continuousLinearMapAt_chartTestSection_eq_coordChangeL
    (e' : Trivialization F (π F V)) [e'.IsLinear ℝ]
    (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F)) {x : M}
    (hx : x ∈ c.source) (hx' : x ∈ e'.baseSet) :
    e'.continuousLinearMapAt ℝ x ((e.chartTestSection c hc hce φ).val x) =
      e.coordChangeL ℝ e' x (φ (c x)) := by
  rw [chartTestSection_apply_of_mem e c hc hce φ hx,
    e.symmL_apply (hce hx), e'.continuousLinearMapAt_apply_of_mem (R := ℝ) hx',
    e.coordChangeL_apply e' ⟨hce hx, hx'⟩]

end

section ExtensionScalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra ℝ 𝕜']
  [NormedSpace 𝕜' F] [IsScalarTower ℝ 𝕜' F]
  [∀ x, Module 𝕜' (V x)] [VectorBundle 𝕜' F V]
  (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
  (c : OpenPartialHomeomorph M E)
  (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source) (hce : c.source ⊆ e.baseSet)

/-- Extending native test functions through an extension-linear bundle frame commutes with
extension scalars. -/
theorem chartTestSection_smul_ofNormedAlgebra (a : 𝕜')
    (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F)) :
    e.chartTestSection c hc hce (a • φ) = a • e.chartTestSection c hc hce φ := by
  apply Subtype.ext
  ext x
  by_cases hx : x ∈ c.source
  · simp [e.chartTestSection_apply_of_mem c hc hce _ hx,
      e.coe_symmL_eq_coe_symmL ℝ 𝕜' x]
  · simp [e.chartTestSection_apply_of_notMem c hc hce _ hx]

variable (𝕜') in
/-- Chart extension of native test functions regarded as a `𝕜'`-linear map into compactly
supported sections. -/
def chartTestSectionOfNormedAlgebra :
    𝓓^{n}(⟨c.target, c.open_target⟩, F) →ₗ[𝕜'] ContMDiffSection.compactlySupported I F n V where
  toFun := e.chartTestSection c hc hce
  map_add' := (e.chartTestSection c hc hce).map_add
  map_smul' := e.chartTestSection_smul_ofNormedAlgebra c hc hce

@[simp]
theorem coe_chartTestSectionOfNormedAlgebra :
    ⇑(e.chartTestSectionOfNormedAlgebra 𝕜' c hc hce) = e.chartTestSection c hc hce :=
  (rfl)

end ExtensionScalars

end Bundle.Trivialization

namespace ContMDiffSection

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

namespace Bundle.Trivialization

open ContMDiffSection

section ChartRead

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞}
  (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
  (c : OpenPartialHomeomorph M E)
  (hc_symm : ContMDiffOn 𝓘(ℝ, E) I n c.symm c.target)
  (hct : c.source ⊆ t.baseSet)

private def chartReadFun (s : Cₛ^n⟮I; F, V⟯) (y : E) : F := by
  classical
  exact if y ∈ c.target then t.continuousLinearMapAt ℝ (c.symm y) (s (c.symm y)) else 0

private theorem chartReadFun_of_mem (s : Cₛ^n⟮I; F, V⟯) {y : E} (hy : y ∈ c.target) :
    chartReadFun t c s y = t.continuousLinearMapAt ℝ (c.symm y) (s (c.symm y)) := by
  simp [chartReadFun, hy]

private theorem chartReadFun_of_notMem (s : Cₛ^n⟮I; F, V⟯) {y : E} (hy : y ∉ c.target) :
    chartReadFun t c s y = 0 := by
  simp [chartReadFun, hy]

private theorem chartReadFun_eq_zero_of_notMem_image {K : Set M} {s : Cₛ^n⟮I; F, V⟯}
    (hs : s.tsupport ⊆ K) {y : E} (hy : y ∉ c '' K) :
    chartReadFun t c s y = 0 := by
  by_cases hyt : y ∈ c.target
  · have hsymm : c.symm y ∉ s.tsupport := fun hmem ↦ hy ⟨c.symm y, hs hmem, c.right_inv hyt⟩
    rw [chartReadFun_of_mem t c s hyt, s.eq_zero_of_notMem_tsupport hsymm, map_zero]
  · exact chartReadFun_of_notMem t c s hyt

variable [ContMDiffVectorBundle n F V I]

include hc_symm hct in
private theorem contDiff_chartReadFun {K : Compacts M} (hKc : (K : Set M) ⊆ c.source)
    (s : supportedIn I F n V K) :
    ContDiff ℝ n (chartReadFun t c s.val) := by
  have hK' : IsCompact (c '' (K : Set M)) :=
    K.isCompact.image_of_continuousOn (c.continuousOn.mono hKc)
  refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
  by_cases hy : y ∈ c.target
  · have hsec : ContMDiffAt I 𝓘(ℝ, F) n (fun x ↦ (t ⟨x, s.val x⟩).2) (c.symm y) :=
      (t.contMDiffAt_section_iff (hct (c.map_target hy))).1 (s.val.contMDiff (c.symm y))
    have hcomp : ContDiffAt ℝ n (fun z ↦ (t ⟨c.symm z, s.val (c.symm z)⟩).2) y :=
      contMDiffAt_iff_contDiffAt.1
        (hsec.comp y (hc_symm.contMDiffAt (c.open_target.mem_nhds hy)))
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [c.open_target.mem_nhds hy] with z hz
    rw [chartReadFun_of_mem t c s.val hz,
      t.continuousLinearMapAt_apply_of_mem (R := ℝ) (hct (c.map_target hz))]
  · have hyK' : y ∉ c '' (K : Set M) := fun ⟨x, hxK, hxy⟩ ↦ hy (hxy ▸ c.map_source (hKc hxK))
    refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [hK'.isClosed.isOpen_compl.mem_nhds hyK'] with z hz
    exact chartReadFun_eq_zero_of_notMem_image t c (mem_supportedIn.1 s.property) hz

private def chartReadSupportedInFun {K : Compacts M} (hKc : (K : Set M) ⊆ c.source)
    (s : supportedIn I F n V K) :
    𝓓^{n}_{⟨c '' (K : Set M), K.isCompact.image_of_continuousOn (c.continuousOn.mono hKc)⟩}(E,
      F) :=
  ⟨chartReadFun t c s.val, contDiff_chartReadFun t c hc_symm hct hKc s,
    fun _ hy ↦ chartReadFun_eq_zero_of_notMem_image t c (mem_supportedIn.1 s.property) hy⟩

@[simp]
private theorem chartReadSupportedInFun_apply {K : Compacts M} (hKc : (K : Set M) ⊆ c.source)
    (s : supportedIn I F n V K) (y : E) :
    chartReadSupportedInFun t c hc_symm hct hKc s y = chartReadFun t c s.val y :=
  rfl

/-- Read a `C^n` bundle section supported in a compact subset `K ⊆ c.source` in the coordinate
chart `c` and bundle frame `t`, extending by zero outside `c '' K`. -/
def chartReadSupportedIn {K : Compacts M} (hKc : (K : Set M) ⊆ c.source) :
    supportedIn I F n V K →ₗ[ℝ]
      𝓓^{n}_{⟨c '' (K : Set M), K.isCompact.image_of_continuousOn (c.continuousOn.mono hKc)⟩}(E,
        F) where
  toFun := chartReadSupportedInFun t c hc_symm hct hKc
  map_add' s₁ s₂ := by
    ext y
    by_cases hy : y ∈ c.target <;> simp [chartReadFun, hy]
  map_smul' a s := by
    ext y
    by_cases hy : y ∈ c.target <;> simp [chartReadFun, hy]

/-- On the chart target, `chartReadSupportedIn` reads the section in `t` along `c.symm`. -/
theorem chartReadSupportedIn_apply_of_mem {K : Compacts M} (hKc : (K : Set M) ⊆ c.source)
    (s : supportedIn I F n V K) {y : E} (hy : y ∈ c.target) :
    t.chartReadSupportedIn c hc_symm hct hKc s y =
      t.continuousLinearMapAt ℝ (c.symm y) (s.val (c.symm y)) :=
  chartReadFun_of_mem t c s.val hy

/-- Outside the chart target, `chartReadSupportedIn` vanishes. -/
@[simp]
theorem chartReadSupportedIn_apply_of_notMem {K : Compacts M} (hKc : (K : Set M) ⊆ c.source)
    (s : supportedIn I F n V K) {y : E} (hy : y ∉ c.target) :
    t.chartReadSupportedIn c hc_symm hct hKc s y = 0 :=
  chartReadFun_of_notMem t c s.val hy

/-- Read a `C^n` bundle section supported in a compact subset `K ⊆ c.source` as a native test
function on the chart target `c.target`. -/
def chartReadTestFunction {K : Compacts M} (hKc : (K : Set M) ⊆ c.source) :
    supportedIn I F n V K →ₗ[ℝ] 𝓓^{n}(⟨c.target, c.open_target⟩, F) :=
  let K' : Compacts E :=
    ⟨c '' (K : Set M), K.isCompact.image_of_continuousOn (c.continuousOn.mono hKc)⟩
  have hK't : (K' : Set E) ⊆ (⟨c.target, c.open_target⟩ : Opens E) :=
    image_subset_iff.2 fun _ hx ↦ c.map_source (hKc hx)
  (TestFunction.ofSupportedInCLM ℝ hK't).toLinearMap.comp
    (t.chartReadSupportedIn c hc_symm hct hKc)

/-- On the chart target, `chartReadTestFunction` reads the section in `t` along `c.symm`. -/
theorem chartReadTestFunction_apply_of_mem {K : Compacts M} (hKc : (K : Set M) ⊆ c.source)
    (s : supportedIn I F n V K) {y : E} (hy : y ∈ c.target) :
    t.chartReadTestFunction c hc_symm hct hKc s y =
      t.continuousLinearMapAt ℝ (c.symm y) (s.val (c.symm y)) :=
  t.chartReadSupportedIn_apply_of_mem c hc_symm hct hKc s hy

/-- Outside the chart target, `chartReadTestFunction` vanishes. -/
@[simp]
theorem chartReadTestFunction_apply_of_notMem {K : Compacts M} (hKc : (K : Set M) ⊆ c.source)
    (s : supportedIn I F n V K) {y : E} (hy : y ∉ c.target) :
    t.chartReadTestFunction c hc_symm hct hKc s y = 0 :=
  t.chartReadSupportedIn_apply_of_notMem c hc_symm hct hKc s hy

/-- Extending `chartReadTestFunction` by zero recovers the original section supported in `K`. -/
@[simp]
theorem chartTestSection_chartReadTestFunction [T2Space M]
    (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source) {K : Compacts M} (hKc : (K : Set M) ⊆ c.source)
    (s : supportedIn I F n V K) :
    t.chartTestSection c hc hct (t.chartReadTestFunction c hc_symm hct hKc s) =
      ofSupportedIn K s := by
  apply Subtype.ext
  ext x
  by_cases hx : x ∈ c.source
  · rw [t.chartTestSection_apply_of_mem c hc hct _ hx,
      t.chartReadTestFunction_apply_of_mem c hc_symm hct hKc s (c.map_source hx),
      c.left_inv hx, t.symmL_continuousLinearMapAt (hct hx), ofSupportedIn_apply]
  · rw [t.chartTestSection_apply_of_notMem c hc hct _ hx, ofSupportedIn_apply]
    exact (s.val.eq_zero_of_notMem_tsupport fun h ↦ hx (hKc (mem_supportedIn.1 s.property h))).symm

/-- Multiply an arbitrary `C^n` section by a compactly supported `C^n` cutoff `ρ` with
`tsupport ρ ⊆ c.source` and read the localized section as a native test function on `c.target`. -/
def chartCutoffTestFunction (ρ : C^n⟮I, M; ℝ⟯) (hρc : HasCompactSupport ρ)
    (hρs : _root_.tsupport ρ ⊆ c.source) :
    Cₛ^n⟮I; F, V⟯ →ₗ[ℝ] 𝓓^{n}(⟨c.target, c.open_target⟩, F) :=
  let Kρ : Compacts M := ⟨_root_.tsupport ρ, hρc⟩
  (t.chartReadTestFunction c hc_symm hct (K := Kρ) hρs).comp
    ((smulLinearMap ρ).codRestrict (supportedIn I F n V Kρ) fun s ↦
      mem_supportedIn.2 ((tsupport_smul_function_subset ρ s).trans inter_subset_left))

/-- On the chart target, `chartCutoffTestFunction` evaluates to the cutoff-weighted frame
coordinates along `c.symm`. -/
theorem chartCutoffTestFunction_apply_of_mem (ρ : C^n⟮I, M; ℝ⟯) (hρc : HasCompactSupport ρ)
    (hρs : _root_.tsupport ρ ⊆ c.source) (s : Cₛ^n⟮I; F, V⟯) {y : E} (hy : y ∈ c.target) :
    t.chartCutoffTestFunction c hc_symm hct ρ hρc hρs s y =
      ρ (c.symm y) • t.continuousLinearMapAt ℝ (c.symm y) (s (c.symm y)) := by
  simp [chartCutoffTestFunction,
    t.chartReadTestFunction_apply_of_mem c hc_symm hct (K := ⟨_root_.tsupport ρ, hρc⟩) hρs _ hy]

/-- Outside the chart target, `chartCutoffTestFunction` vanishes. -/
@[simp]
theorem chartCutoffTestFunction_apply_of_notMem (ρ : C^n⟮I, M; ℝ⟯) (hρc : HasCompactSupport ρ)
    (hρs : _root_.tsupport ρ ⊆ c.source) (s : Cₛ^n⟮I; F, V⟯) {y : E} (hy : y ∉ c.target) :
    t.chartCutoffTestFunction c hc_symm hct ρ hρc hρs s y = 0 :=
  t.chartReadTestFunction_apply_of_notMem c hc_symm hct hρs _ hy

/-- Extending `chartCutoffTestFunction` by zero yields the localized section `ρ • s`. -/
@[simp]
theorem chartTestSection_chartCutoffTestFunction [T2Space M]
    (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source) (ρ : C^n⟮I, M; ℝ⟯) (hρc : HasCompactSupport ρ)
    (hρs : _root_.tsupport ρ ⊆ c.source) (s : Cₛ^n⟮I; F, V⟯) :
    t.chartTestSection c hc hct (t.chartCutoffTestFunction c hc_symm hct ρ hρc hρs s) =
      ⟨ρ • s, smul_function_mem_compactlySupported_of_hasCompactSupport ρ hρc s⟩ := by
  rw [chartCutoffTestFunction, LinearMap.comp_apply,
    t.chartTestSection_chartReadTestFunction c hc_symm hct hc hρs]
  apply Subtype.ext
  rw [ofSupportedIn_apply, LinearMap.codRestrict_apply, smulLinearMap_eq_smul]

end ChartRead

end Bundle.Trivialization

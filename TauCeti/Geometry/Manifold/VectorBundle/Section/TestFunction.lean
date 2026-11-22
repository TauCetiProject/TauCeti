/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Topology.OpenPartialHomeomorph.Basic

/-!
# Native test functions in bundle charts

A smooth coordinate chart subordinate to a smooth bundle frame sends a native test function
on its target to a compactly supported smooth section. On the chart source the section is
obtained by applying the inverse frame to the test function's value in coordinates; elsewhere
it is zero. Its closed support is exactly the inverse chart image of the test function's closed
support. In particular this map is injective and sends support bounds `tsupport φ ⊆ K`
to support bounds in `c.symm '' K`.

These are algebraic chart extension and coefficient maps for constructing locally convex
test-section spaces. No topology on compactly supported sections is installed here. Chart
extension only needs forward smoothness of the chart; reading sections back into test
functions (`Bundle.Trivialization.chartCoeff`, `Bundle.Trivialization.chartTestCoeff`) uses
`C^n` smoothness of the inverse chart, and requires neither finite-dimensional fibres nor a
countable atlas.

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
  (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
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

end Bundle.Trivialization

namespace Bundle.Trivialization

open ContMDiffSection

section ChartCoeff

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
  (hc_symm : ContMDiffOn 𝓘(ℝ, E) I n c.symm c.target) (hct : c.source ⊆ t.baseSet)

private def chartCoeffFun (s : Cₛ^n⟮I; F, V⟯) (y : E) : F := by
  classical
  exact if y ∈ c.target then t.continuousLinearMapAt ℝ (c.symm y) (s (c.symm y)) else 0

omit [ContMDiffVectorBundle n F V I] in
private theorem chartCoeffFun_of_mem (s : Cₛ^n⟮I; F, V⟯) {y : E} (hy : y ∈ c.target) :
    chartCoeffFun t c s y = t.continuousLinearMapAt ℝ (c.symm y) (s (c.symm y)) := by
  simp [chartCoeffFun, hy]

omit [ContMDiffVectorBundle n F V I] in
private theorem chartCoeffFun_of_notMem (s : Cₛ^n⟮I; F, V⟯) {y : E} (hy : y ∉ c.target) :
    chartCoeffFun t c s y = 0 := by
  simp [chartCoeffFun, hy]

omit [ContMDiffVectorBundle n F V I] in
private theorem chartCoeffFun_eq_zero {L₀ : Set E} (s : Cₛ^n⟮I; F, V⟯)
    (hs : ∀ y ∈ c.target, y ∉ L₀ → s (c.symm y) = 0) {y : E} (hy : y ∉ L₀) :
    chartCoeffFun t c s y = 0 := by
  by_cases hyt : y ∈ c.target
  · simp [chartCoeffFun, hyt, hs y hyt hy]
  · simp [chartCoeffFun, hyt]

include hc_symm hct in
private theorem contDiff_chartCoeffFun {L₀ : Compacts E} (hL₀ : (L₀ : Set E) ⊆ c.target)
    (s : Cₛ^n⟮I; F, V⟯) (hs : ∀ y ∈ c.target, y ∉ L₀ → s (c.symm y) = 0) :
    ContDiff ℝ n (chartCoeffFun t c s) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ c.target
  · have hsec : ContMDiffAt I 𝓘(ℝ, F) n (fun x ↦ (t ⟨x, s x⟩).2) (c.symm y) :=
      (t.contMDiffAt_section_iff (hct (c.map_target hy))).1 (s.contMDiff (c.symm y))
    have hcomp : ContDiffAt ℝ n (fun z ↦ (t ⟨c.symm z, s (c.symm z)⟩).2) y :=
      contMDiffAt_iff_contDiffAt.1 <|
        hsec.comp y (hc_symm.contMDiffAt (c.open_target.mem_nhds hy))
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [c.open_target.mem_nhds hy] with z hz
    simp only [chartCoeffFun, hz, ↓reduceIte,
      t.continuousLinearMapAt_apply_of_mem (R := ℝ) (hct (c.map_target hz))]
  · have hyL₀ : y ∉ (L₀ : Set E) := fun h ↦ hy (hL₀ h)
    refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [L₀.isCompact.isClosed.isOpen_compl.mem_nhds hyL₀] with z hz
    exact chartCoeffFun_eq_zero t c s hs hz

/-- Read a `C^n` section on a chart target in a bundle frame as a supported test function in `E`,
given a compact subset `L₀` of the chart target outside which the section vanishes on the chart
target. -/
def chartCoeff {L₀ L : Compacts E} (hL₀ : (L₀ : Set E) ⊆ c.target) (hL₀L : (L₀ : Set E) ⊆ L)
    (s : Cₛ^n⟮I; F, V⟯) (hs : ∀ y ∈ c.target, y ∉ L₀ → s (c.symm y) = 0) :
    𝓓^{n}_{L}(E, F) :=
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_chartCoeffFun t c hc_symm hct hL₀ s hs) fun _ hy ↦ by
      by_contra hyL
      exact hy (chartCoeffFun_eq_zero t c s hs fun h ↦ hyL (hL₀L h))

/-- On the chart target, `chartCoeff` evaluates the bundle frame on the section at the
inverse-chart point. -/
theorem chartCoeff_apply_of_mem {L₀ L : Compacts E} (hL₀ : (L₀ : Set E) ⊆ c.target)
    (hL₀L : (L₀ : Set E) ⊆ L) (s : Cₛ^n⟮I; F, V⟯)
    (hs : ∀ y ∈ c.target, y ∉ L₀ → s (c.symm y) = 0) {y : E} (hy : y ∈ c.target) :
    t.chartCoeff c hc_symm hct hL₀ hL₀L s hs y =
      t.continuousLinearMapAt ℝ (c.symm y) (s (c.symm y)) :=
  chartCoeffFun_of_mem t c s hy

/-- Outside the chart target, `chartCoeff` vanishes. -/
@[simp]
theorem chartCoeff_apply_of_notMem {L₀ L : Compacts E} (hL₀ : (L₀ : Set E) ⊆ c.target)
    (hL₀L : (L₀ : Set E) ⊆ L) (s : Cₛ^n⟮I; F, V⟯)
    (hs : ∀ y ∈ c.target, y ∉ L₀ → s (c.symm y) = 0) {y : E} (hy : y ∉ c.target) :
    t.chartCoeff c hc_symm hct hL₀ hL₀L s hs y = 0 :=
  chartCoeffFun_of_notMem t c s hy

/-- Outside `L₀`, `chartCoeff` vanishes. -/
theorem chartCoeff_eq_zero {L₀ L : Compacts E} (hL₀ : (L₀ : Set E) ⊆ c.target)
    (hL₀L : (L₀ : Set E) ⊆ L) (s : Cₛ^n⟮I; F, V⟯)
    (hs : ∀ y ∈ c.target, y ∉ L₀ → s (c.symm y) = 0) {y : E} (hy : y ∉ L₀) :
    t.chartCoeff c hc_symm hct hL₀ hL₀L s hs y = 0 :=
  chartCoeffFun_eq_zero t c s hs hy

/-- The unweighted chart coefficient map as an `ℝ`-linear map on sections vanishing outside `L₀`
on the chart target. -/
def chartCoeffLinearMap {L₀ L : Compacts E} (hL₀ : (L₀ : Set E) ⊆ c.target)
    (hL₀L : (L₀ : Set E) ⊆ L) :
    zeroOffInChart I F n V c L₀ →ₗ[ℝ] 𝓓^{n}_{L}(E, F) where
  toFun s := t.chartCoeff c hc_symm hct hL₀ hL₀L s.val (mem_zeroOffInChart.1 s.property)
  map_add' s₁ s₂ := by
    ext y
    by_cases hy : y ∈ c.target
    · simp only [FunLike.coe_add, Pi.add_apply]
      rw [chartCoeff_apply_of_mem t c hc_symm hct hL₀ hL₀L (s₁ + s₂).val _ hy,
        chartCoeff_apply_of_mem t c hc_symm hct hL₀ hL₀L s₁.val _ hy,
        chartCoeff_apply_of_mem t c hc_symm hct hL₀ hL₀L s₂.val _ hy]
      simp [map_add]
    · simp only [FunLike.coe_add, Pi.add_apply]
      rw [chartCoeff_apply_of_notMem t c hc_symm hct hL₀ hL₀L (s₁ + s₂).val _ hy,
        chartCoeff_apply_of_notMem t c hc_symm hct hL₀ hL₀L s₁.val _ hy,
        chartCoeff_apply_of_notMem t c hc_symm hct hL₀ hL₀L s₂.val _ hy,
        add_zero]
  map_smul' a s := by
    ext y
    by_cases hy : y ∈ c.target
    · simp only [FunLike.coe_smul, Pi.smul_apply, RingHom.id_apply]
      rw [chartCoeff_apply_of_mem t c hc_symm hct hL₀ hL₀L (a • s).val _ hy,
        chartCoeff_apply_of_mem t c hc_symm hct hL₀ hL₀L s.val _ hy]
      simp [map_smul]
    · simp only [FunLike.coe_smul, Pi.smul_apply, RingHom.id_apply]
      rw [chartCoeff_apply_of_notMem t c hc_symm hct hL₀ hL₀L (a • s).val _ hy,
        chartCoeff_apply_of_notMem t c hc_symm hct hL₀ hL₀L s.val _ hy,
        smul_zero]

/-- Evaluation of `chartCoeffLinearMap` agrees with `chartCoeff`. -/
@[simp]
theorem chartCoeffLinearMap_apply {L₀ L : Compacts E} (hL₀ : (L₀ : Set E) ⊆ c.target)
    (hL₀L : (L₀ : Set E) ⊆ L) (s : zeroOffInChart I F n V c L₀) :
    t.chartCoeffLinearMap c hc_symm hct hL₀ hL₀L s =
      t.chartCoeff c hc_symm hct hL₀ hL₀L s.val (mem_zeroOffInChart.1 s.property) :=
  (rfl)

/-- Extending the unweighted chart coefficients of a section that vanishes outside the chart source
recovers the original section. -/
theorem chartTestSection_ofSupportedIn_chartCoeff [T2Space M]
    (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source)
    {L₀ L : Compacts E} (hL₀ : (L₀ : Set E) ⊆ c.target) (hL₀L : (L₀ : Set E) ⊆ L)
    (hL : (L : Set E) ⊆ c.target) (s : Cₛ^n⟮I; F, V⟯)
    (hs : ∀ y ∈ c.target, y ∉ L₀ → s (c.symm y) = 0) (hs_compl : ∀ x ∉ c.source, s x = 0) :
    (t.chartTestSection c hc hct
      (TestFunction.ofSupportedIn hL (t.chartCoeff c hc_symm hct hL₀ hL₀L s hs))).val = s := by
  ext x
  by_cases hx : x ∈ c.source
  · rw [chartTestSection_apply_of_mem t c hc hct _ hx, TestFunction.coe_ofSupportedIn,
      chartCoeff_apply_of_mem t c hc_symm hct hL₀ hL₀L s hs (c.map_source hx), c.left_inv hx,
      t.symmL_continuousLinearMapAt (hct hx)]
  · rw [chartTestSection_apply_of_notMem t c hc hct _ hx]
    exact (hs_compl x hx).symm

omit [ContMDiffVectorBundle n F V I] in
private theorem chartTestCoeff_zero_of_notMem {K : Compacts M} (hK : (K : Set M) ⊆ c.source)
    (s : supportedIn I F n V K) {y : E} (hyc : y ∈ c.target)
    (hy : y ∉ (c.imageCompact hK : Set E)) :
    s.val (c.symm y) = 0 :=
  s.val.eq_zero_of_notMem_tsupport fun h ↦ by
    rw [c.coe_imageCompact hK] at hy
    exact hy ⟨c.symm y, mem_supportedIn.1 s.property h, c.right_inv hyc⟩

omit [ContMDiffVectorBundle n F V I] in
/-- A section supported in a compact subset `K` of a chart source vanishes outside `c '' K` on the
chart target. -/
theorem supportedIn_le_zeroOffInChart {K : Compacts M} (hK : (K : Set M) ⊆ c.source) :
    supportedIn I F n V K ≤ zeroOffInChart I F n V c (c.imageCompact hK) :=
  fun s hs ↦ mem_zeroOffInChart.2 fun _ hyc hy ↦ chartTestCoeff_zero_of_notMem c hK ⟨s, hs⟩ hyc hy

/-- Read a `C^n` section supported in a compact subset `K` of a chart source as a supported test
function in `E`, via the inverse chart and the bundle frame. -/
def chartTestCoeff {K : Compacts M} (hK : (K : Set M) ⊆ c.source)
    {L : Compacts E} (hKL : c '' (K : Set M) ⊆ L) :
    supportedIn I F n V K →ₗ[ℝ] 𝓓^{n}_{L}(E, F) :=
  (t.chartCoeffLinearMap c hc_symm hct (c.imageCompact_subset_target hK)
    (c.coe_imageCompact hK ▸ hKL)).comp
    (Submodule.inclusion (supportedIn_le_zeroOffInChart c hK))

/-- `chartTestCoeff` factors through `chartCoeffLinearMap` via the support inclusion into
`zeroOffInChart`. -/
theorem chartTestCoeff_eq_comp {K : Compacts M} (hK : (K : Set M) ⊆ c.source)
    {L : Compacts E} (hKL : c '' (K : Set M) ⊆ L) :
    t.chartTestCoeff c hc_symm hct hK hKL =
      (t.chartCoeffLinearMap c hc_symm hct (c.imageCompact_subset_target hK)
        (c.coe_imageCompact hK ▸ hKL)).comp
        (Submodule.inclusion (supportedIn_le_zeroOffInChart c hK)) :=
  (rfl)

/-- On the chart target, `chartTestCoeff` evaluates the bundle frame on the section at the
inverse-chart point. -/
theorem chartTestCoeff_apply_of_mem {K : Compacts M} (hK : (K : Set M) ⊆ c.source)
    {L : Compacts E} (hKL : c '' (K : Set M) ⊆ L)
    (s : supportedIn I F n V K) {y : E} (hy : y ∈ c.target) :
    t.chartTestCoeff c hc_symm hct hK hKL s y =
      t.continuousLinearMapAt ℝ (c.symm y) (s.val (c.symm y)) :=
  chartCoeff_apply_of_mem t c hc_symm hct (c.imageCompact_subset_target hK)
    (c.coe_imageCompact hK ▸ hKL) s.val
    (fun _ hyc hy' ↦ chartTestCoeff_zero_of_notMem c hK s hyc hy') hy

/-- Outside the chart target, `chartTestCoeff` vanishes. -/
@[simp]
theorem chartTestCoeff_apply_of_notMem {K : Compacts M} (hK : (K : Set M) ⊆ c.source)
    {L : Compacts E} (hKL : c '' (K : Set M) ⊆ L)
    (s : supportedIn I F n V K) {y : E} (hy : y ∉ c.target) :
    t.chartTestCoeff c hc_symm hct hK hKL s y = 0 :=
  chartCoeff_apply_of_notMem t c hc_symm hct (c.imageCompact_subset_target hK)
    (c.coe_imageCompact hK ▸ hKL) s.val
    (fun _ hyc hy' ↦ chartTestCoeff_zero_of_notMem c hK s hyc hy') hy

/-- Extending the chart coefficients of a section supported inside the chart source recovers the
original section. -/
theorem chartTestSection_ofSupportedIn_chartTestCoeff [T2Space M]
    (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source)
    {K : Compacts M} (hK : (K : Set M) ⊆ c.source)
    {L : Compacts E} (hKL : c '' (K : Set M) ⊆ L) (hL : (L : Set E) ⊆ c.target)
    (s : supportedIn I F n V K) :
    t.chartTestSection c hc hct
      (TestFunction.ofSupportedIn hL (t.chartTestCoeff c hc_symm hct hK hKL s)) =
      ofSupportedIn K s := by
  refine Subtype.ext ?_
  rw [ofSupportedIn_apply]
  exact t.chartTestSection_ofSupportedIn_chartCoeff c hc_symm hct hc
    (c.imageCompact_subset_target hK) (c.coe_imageCompact hK ▸ hKL) hL s.val
    (fun _ hyc hy ↦ chartTestCoeff_zero_of_notMem c hK s hyc hy)
    fun _ hx ↦ s.val.eq_zero_of_notMem_tsupport fun h ↦ hx (hK (mem_supportedIn.1 s.property h))

/-- Reading back an extended supported test function recovers it identically. -/
theorem chartTestCoeff_chartTestSection_ofSupportedIn [T2Space M]
    (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source)
    {L : Compacts E} (hL : (L : Set E) ⊆ c.target)
    {K : Compacts M} (hK : (K : Set M) ⊆ c.source) (hKL : c '' (K : Set M) ⊆ L)
    (hLK : c.symm '' (L : Set E) ⊆ K) (φ : 𝓓^{n}_{L}(E, F)) :
    t.chartTestCoeff c hc_symm hct hK hKL
      ⟨(t.chartTestSection c hc hct (TestFunction.ofSupportedIn hL φ)).val,
        mem_supportedIn.2 ((mem_supportedIn.1 (t.chartTestSection_mem_supportedIn c hc hct
          (TestFunction.ofSupportedIn hL φ) (K := (L : Set E)) (by
            rw [TestFunction.coe_ofSupportedIn]
            exact φ.tsupport_subset))).trans hLK)⟩ = φ := by
  ext y
  by_cases hy : y ∈ c.target
  · rw [chartTestCoeff_apply_of_mem t c hc_symm hct hK hKL _ hy,
      continuousLinearMapAt_chartTestSection t c hc hct _ (c.map_target hy),
      c.right_inv hy, TestFunction.coe_ofSupportedIn]
  · rw [chartTestCoeff_apply_of_notMem t c hc_symm hct hK hKL _ hy]
    exact (φ.zero_on_compl fun h ↦ hy (hL h)).symm

end ChartCoeff

end Bundle.Trivialization

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Native test functions in bundle charts

A smooth coordinate chart subordinate to a smooth bundle frame sends a native test function
on its target to a compactly supported smooth section. On the chart source the section is
obtained by applying the inverse frame to the test function's value in coordinates; elsewhere
it is zero. Its closed support is exactly the inverse chart image of the test function's closed
support. In particular this map is injective and sends support bounds `tsupport φ ⊆ K`
to support bounds in `c.symm '' K`.

These are algebraic chart extension maps for constructing locally convex test-section spaces.
No topology on compactly supported sections is installed here. The chart only needs to be
smooth in the forward direction; the support and smoothness arguments do not require
smoothness of its inverse, finite-dimensional fibres, or a countable atlas.

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
    (e.chartTestSection c hc hce φ).1 x = e.symmL ℝ x (φ (c x)) :=
  testSection_of_mem e c φ hx

/-- The section vanishes outside the chart source. -/
@[simp]
theorem chartTestSection_apply_of_notMem (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F))
    {x : M} (hx : x ∉ c.source) : (e.chartTestSection c hc hce φ).1 x = 0 := by
  simp [chartTestSection, testSection, hx]

/-- Reading the extended section in its defining frame recovers the native test function. -/
@[simp]
theorem continuousLinearMapAt_chartTestSection (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F))
    {x : M} (hx : x ∈ c.source) :
    e.continuousLinearMapAt ℝ x ((e.chartTestSection c hc hce φ).1 x) = φ (c x) := by
  rw [chartTestSection_apply_of_mem e c hc hce φ hx, e.continuousLinearMapAt_symmL (hce hx)]

/-- Native test functions are determined by their extended bundle sections. -/
theorem chartTestSection_injective : Function.Injective (e.chartTestSection c hc hce) := by
  intro φ ψ h
  ext y
  by_cases hy : y ∈ c.target
  · have hval := congrArg (fun s : ContMDiffSection.compactlySupported I F n V ↦
      e.continuousLinearMapAt ℝ (c.symm y) (s.1 (c.symm y))) h
    simpa [continuousLinearMapAt_chartTestSection e c hc hce _ (c.map_target hy),
      c.right_inv hy] using hval
  · exact (φ.zero_on_compl hy).trans (ψ.zero_on_compl hy).symm

/-- Extension preserves the exact nonzero locus, transported by the inverse chart. -/
theorem support_chartTestSection (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F)) :
    {x | (e.chartTestSection c hc hce φ).1 x ≠ 0} = c.symm '' Function.support φ := by
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
    (e.chartTestSection c hc hce φ).1.tsupport = c.symm '' tsupport φ := by
  apply le_antisymm
  · exact tsupport_testSection_subset e c hc hce φ
  · rw [ContMDiffSection.tsupport_def, support_chartTestSection]
    exact (c.continuousOn_symm.mono φ.tsupport_subset).image_closure

/-- The closed support of an extended test lies entirely in the chart source. -/
theorem tsupport_chartTestSection_subset_source (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F)) :
    (e.chartTestSection c hc hce φ).1.tsupport ⊆ c.source := by
  rw [tsupport_chartTestSection]
  exact image_subset_iff.2 fun _ hy ↦ c.map_target (φ.tsupport_subset hy)

/-- A support bound in an arbitrary set `K` becomes a support bound in `c.symm '' K`. -/
theorem chartTestSection_mem_supportedIn (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F))
    {K : Set E} (hφ : tsupport φ ⊆ K) :
    (e.chartTestSection c hc hce φ).1 ∈ ContMDiffSection.supportedIn I F n V (c.symm '' K) := by
  rw [ContMDiffSection.mem_supportedIn, tsupport_chartTestSection]
  exact image_mono hφ

/-- In a second bundle frame, the extended section has the actual vector-bundle transition
applied to its defining coefficients. -/
theorem continuousLinearMapAt_chartTestSection_eq_coordChangeL
    (e' : Trivialization F (π F V)) [e'.IsLinear ℝ]
    (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F)) {x : M}
    (hx : x ∈ c.source) (hx' : x ∈ e'.baseSet) :
    e'.continuousLinearMapAt ℝ x ((e.chartTestSection c hc hce φ).1 x) =
      e.coordChangeL ℝ e' x (φ (c x)) := by
  rw [chartTestSection_apply_of_mem e c hc hce φ hx,
    e.symmL_apply (hce hx), e'.continuousLinearMapAt_apply_of_mem (R := ℝ) hx',
    e.coordChangeL_apply e' ⟨hce hx, hx'⟩]

end Bundle.Trivialization

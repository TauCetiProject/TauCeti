/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Extending test functions to bundle sections

A vector-valued test function on the target of a smooth chart defines a global bundle
section when the chart source lies in a bundle trivialization. Use that frame on the
chart source and extend by zero elsewhere. Compact support inside the chart target
ensures smoothness across the edge of the chart.

`Bundle.Trivialization.testFunctionExtension` is the resulting linear map into native
`ContMDiffSection`. Its fibre-coordinate formula recovers the original test function;
its nonzero locus and its closed support are exactly the inverse-chart images of the
corresponding supports of the test function. These maps provide local test sections
without choosing a global frame or a fibre norm.

The regularity may be any `n : ℕ∞`; neither the base nor the model fibre needs to
be finite dimensional. The base is modelled on a real normed space without boundary.
-/

public section

open Bundle Set IsManifold
open scoped ContDiff Manifold Topology

namespace Bundle.Trivialization

variable {E M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞}
  (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
  (c : OpenPartialHomeomorph M E)

private noncomputable def testSection (f : TestFunction ⟨c.target, c.open_target⟩ F n)
    (x : M) : V x := by
  classical
  exact if x ∈ c.source then e.symmL ℝ x (f (c x)) else 0

private theorem testSection_apply (f : TestFunction ⟨c.target, c.open_target⟩ F n)
    {x : M} (hx : x ∈ c.source) :
    e.testSection c f x = e.symmL ℝ x (f (c x)) := by
  simp [testSection, hx]

private theorem testSection_eq_zero (f : TestFunction ⟨c.target, c.open_target⟩ F n)
    {x : M} (hx : x ∉ c.source) : e.testSection c f x = 0 := by
  simp [testSection, hx]

private theorem testSection_coordinate (hce : c.source ⊆ e.baseSet)
    (f : TestFunction ⟨c.target, c.open_target⟩ F n) {x : M} (hx : x ∈ c.source) :
    (e ⟨x, e.testSection c f x⟩).2 = f (c x) := by
  rw [testSection_apply e c f hx,
    ← continuousLinearMapAt_apply_of_mem ℝ e (hce hx),
    e.continuousLinearMapAt_symmL (hce hx)]

variable [T2Space M] [ChartedSpace E M]
  [ContMDiffVectorBundle (n : WithTop ℕ∞) F V 𝓘(ℝ, E)]

private theorem contMDiff_testSection
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) (n : WithTop ℕ∞) M)
    (hce : c.source ⊆ e.baseSet)
    (f : TestFunction ⟨c.target, c.open_target⟩ F n) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) n
      (fun x ↦ TotalSpace.mk' F x (e.testSection c f x)) := by
  let K := c.symm '' tsupport f
  have hK : IsCompact K := f.hasCompactSupport.image_of_continuousOn
    (c.continuousOn_symm.mono f.tsupport_subset)
  have hKs : K ⊆ c.source := image_subset_iff.mpr fun y hy ↦
    c.map_target (f.tsupport_subset hy)
  have hs : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) n
      (fun x ↦ TotalSpace.mk' F x (e.testSection c f x)) c.source := by
    rw [e.contMDiffOn_section_iff c.open_source hce]
    exact (f.contDiff.contMDiff.comp_contMDiffOn
      (contMDiffOn_of_mem_maximalAtlas hc)).congr
      (fun x hx ↦ testSection_coordinate e c hce f hx)
  have hz : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) n
      (fun x ↦ TotalSpace.mk' F x (e.testSection c f x)) Kᶜ := by
    apply (contMDiff_zeroSection ℝ V).contMDiffOn.congr
    intro x hx
    congr 1
    by_cases hxs : x ∈ c.source
    · rw [testSection_apply e c f hxs]
      have hfx : f (c x) = 0 := image_eq_zero_of_notMem_tsupport
        (fun hf ↦ hx ⟨c x, hf, c.left_inv hxs⟩)
      simp [hfx]
    · exact testSection_eq_zero e c f hxs
  exact contMDiff_of_contMDiffOn_union_of_isOpen hs hz
    (by grind)
    c.open_source hK.isClosed.isOpen_compl

/-- Extend a native vector-valued test function through a smooth chart and a bundle
frame, using zero outside the chart source. -/
noncomputable def testFunctionExtension
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) (n : WithTop ℕ∞) M)
    (hce : c.source ⊆ e.baseSet) :
    TestFunction ⟨c.target, c.open_target⟩ F n →ₗ[ℝ]
      ContMDiffSection 𝓘(ℝ, E) F n V where
  toFun f := ⟨e.testSection c f, contMDiff_testSection e c hc hce f⟩
  map_add' f g := by
    ext x
    by_cases hx : x ∈ c.source <;> simp [testSection, hx]
  map_smul' a f := by
    ext x
    by_cases hx : x ∈ c.source <;> simp [testSection, hx]

/-- Inside the chart, extension reads the test function in the chosen frame. -/
theorem testFunctionExtension_apply
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) (n : WithTop ℕ∞) M)
    (hce : c.source ⊆ e.baseSet)
    (f : TestFunction ⟨c.target, c.open_target⟩ F n) {x : M} (hx : x ∈ c.source) :
    e.testFunctionExtension c hc hce f x = e.symmL ℝ x (f (c x)) :=
  testSection_apply e c f hx

/-- Extension vanishes off the chart source. -/
@[simp] theorem testFunctionExtension_apply_of_notMem
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) (n : WithTop ℕ∞) M)
    (hce : c.source ⊆ e.baseSet)
    (f : TestFunction ⟨c.target, c.open_target⟩ F n) {x : M} (hx : x ∉ c.source) :
    e.testFunctionExtension c hc hce f x = 0 :=
  testSection_eq_zero e c f hx

/-- The original test function is recovered in fibre coordinates on the chart. -/
@[simp] theorem testFunctionExtension_coordinate
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) (n : WithTop ℕ∞) M)
    (hce : c.source ⊆ e.baseSet)
    (f : TestFunction ⟨c.target, c.open_target⟩ F n) {x : M} (hx : x ∈ c.source) :
    (e ⟨x, e.testFunctionExtension c hc hce f x⟩).2 = f (c x) :=
  testSection_coordinate e c hce f hx

/-- Extension preserves precisely the nonzero locus under the inverse chart. -/
theorem testFunctionExtension_support
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) (n : WithTop ℕ∞) M)
    (hce : c.source ⊆ e.baseSet)
    (f : TestFunction ⟨c.target, c.open_target⟩ F n) :
    {x | e.testFunctionExtension c hc hce f x ≠ 0} = c.symm '' Function.support f := by
  ext x
  by_cases hx : x ∈ c.source
  · rw [mem_ofPred_eq, testFunctionExtension_apply e c hc hce f hx]
    constructor
    · intro h
      refine ⟨c x, ?_, c.left_inv hx⟩
      intro hz
      exact h (by simp [hz])
    · rintro ⟨y, hy, hxy⟩ hz
      have hyt := f.tsupport_subset (subset_tsupport f hy)
      have heq : c x = y := by rw [← hxy, c.right_inv hyt]
      have := congrArg (e.continuousLinearMapAt ℝ x) hz
      exact hy (by simpa [e.continuousLinearMapAt_symmL (hce hx), heq] using this)
  · simp only [testFunctionExtension_apply_of_notMem e c hc hce f hx,
      ne_self_iff_false, mem_ofPred_eq, false_iff, mem_image, not_exists, not_and]
    intro y hy hxy
    exact hx (hxy ▸ c.map_target (f.tsupport_subset (subset_tsupport f hy)))

/-- The closed support of an extended test section is the inverse-chart image of the
test function's topological support. -/
theorem testFunctionExtension_closedSupport
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) (n : WithTop ℕ∞) M)
    (hce : c.source ⊆ e.baseSet)
    (f : TestFunction ⟨c.target, c.open_target⟩ F n) :
    closure {x | e.testFunctionExtension c hc hce f x ≠ 0} = c.symm '' tsupport f := by
  rw [testFunctionExtension_support]
  apply Subset.antisymm
  · exact closure_minimal (image_mono (subset_tsupport f))
      (f.hasCompactSupport.image_of_continuousOn
        (c.continuousOn_symm.mono f.tsupport_subset)).isClosed
  · exact (c.continuousOn_symm.mono f.tsupport_subset).image_closure

/-- Extended test sections have compact closed support. -/
theorem isCompact_closedSupport_testFunctionExtension
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) (n : WithTop ℕ∞) M)
    (hce : c.source ⊆ e.baseSet)
    (f : TestFunction ⟨c.target, c.open_target⟩ F n) :
    IsCompact (closure {x | e.testFunctionExtension c hc hce f x ≠ 0}) := by
  rw [testFunctionExtension_closedSupport]
  exact f.hasCompactSupport.image_of_continuousOn
    (c.continuousOn_symm.mono f.tsupport_subset)

/-- A test function is determined by its global extension in a chart and frame. -/
theorem testFunctionExtension_injective
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) (n : WithTop ℕ∞) M)
    (hce : c.source ⊆ e.baseSet) : Function.Injective (e.testFunctionExtension c hc hce) := by
  intro f g h
  ext y
  by_cases hy : y ∈ c.target
  · have heq := congrArg (fun s : ContMDiffSection 𝓘(ℝ, E) F n V ↦
      (e ⟨c.symm y, s (c.symm y)⟩).2) h
    simpa [testFunctionExtension_coordinate e c hc hce _ (c.map_target hy),
      c.right_inv hy] using heq
  · exact (f.zero_on_compl hy).trans (g.zero_on_compl hy).symm

end Bundle.Trivialization

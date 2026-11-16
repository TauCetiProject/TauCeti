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
Conversely, when `c.symm` is `C^n` on `c.target`, reading a section supported in a compact subset
`K ⊆ c.source` through `c` and `e` produces a native test function supported in `c '' K`
(`Bundle.Trivialization.chartTestSupportedIn`), inverting `chartTestSection` on compact subsets of
the chart domain; when `c.source = univ`, this gives the global extraction linear map
`Bundle.Trivialization.chartTestCoords`. No topology on compactly supported sections is installed
here. The forward chart extension only needs smoothness of `c`; neither direction requires
finite-dimensional fibres or a countable atlas.

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

namespace Bundle.Trivialization

open ContMDiffSection

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞} [ContMDiffVectorBundle n F V I]
  (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
  (c : OpenPartialHomeomorph M E)
  (hc_symm : ContMDiffOn 𝓘(ℝ, E) I n c.symm c.target) (hct : c.source ⊆ t.baseSet)

private def coordTestFun (s : Cₛ^n⟮I; F, V⟯) (y : E) : F := by
  classical
  exact if y ∈ c.target then t.continuousLinearMapAt ℝ (c.symm y) (s (c.symm y)) else 0

omit [T2Space M] [ContMDiffVectorBundle n F V I] in
private theorem coordTestFun_of_mem (s : Cₛ^n⟮I; F, V⟯) {y : E} (hy : y ∈ c.target) :
    coordTestFun t c s y = t.continuousLinearMapAt ℝ (c.symm y) (s (c.symm y)) := by
  simp [coordTestFun, hy]

omit [T2Space M] [ContMDiffVectorBundle n F V I] in
private theorem coordTestFun_of_notMem (s : Cₛ^n⟮I; F, V⟯) {y : E} (hy : y ∉ c.target) :
    coordTestFun t c s y = 0 := by
  simp [coordTestFun, hy]

omit [T2Space M] [ContMDiffVectorBundle n F V I] in
private theorem coordTestFun_eq_zero_of_notMem_image {s : Cₛ^n⟮I; F, V⟯} {K : Set M}
    (hs : s.tsupport ⊆ K) {y : E} (hy : y ∉ c '' K) :
    coordTestFun t c s y = 0 := by
  by_cases hyt : y ∈ c.target
  · rw [coordTestFun_of_mem t c s hyt]
    have hns : c.symm y ∉ s.tsupport := fun h ↦ hy ⟨c.symm y, hs h, c.right_inv hyt⟩
    rw [s.eq_zero_of_notMem_tsupport hns, map_zero]
  · exact coordTestFun_of_notMem t c s hyt

omit [T2Space M] in
include hc_symm hct in
private theorem contDiff_coordTestFun {s : Cₛ^n⟮I; F, V⟯} (hcomp : IsCompact s.tsupport)
    (hsub : s.tsupport ⊆ c.source) :
    ContDiff ℝ n (coordTestFun t c s) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ c.target
  · have hcoord :
        ContMDiffAt I 𝓘(ℝ, F) n (fun x ↦ t.continuousLinearMapAt ℝ x (s x)) (c.symm y) := by
      have hsec := (t.contMDiffAt_section_iff (hct (c.map_target hy))).1 (s.contMDiff (c.symm y))
      refine hsec.congr_of_eventuallyEq ?_
      filter_upwards [t.open_baseSet.mem_nhds (hct (c.map_target hy))] with x hx
      exact t.continuousLinearMapAt_apply_of_mem (R := ℝ) hx (s x)
    have hcomp_at : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) n
        (fun z ↦ t.continuousLinearMapAt ℝ (c.symm z) (s (c.symm z))) y :=
      hcoord.comp y (hc_symm.contMDiffAt (c.open_target.mem_nhds hy))
    exact (hcomp_at.congr_of_eventuallyEq <| by
      filter_upwards [c.open_target.mem_nhds hy] with z hz
      exact coordTestFun_of_mem t c s hz).contDiffAt
  · have hclosed : IsClosed (c '' s.tsupport) :=
      (hcomp.image_of_continuousOn (c.continuousOn.mono hsub)).isClosed
    have hy' : y ∉ c '' s.tsupport := by
      rintro ⟨x, hx, rfl⟩
      exact hy (c.map_source (hsub hx))
    refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [hclosed.isOpen_compl.mem_nhds hy'] with z hz
    exact coordTestFun_eq_zero_of_notMem_image t c Subset.rfl hz

omit [T2Space M] [ContMDiffVectorBundle n F V I] in
include hct in
private theorem support_coordTestFun {s : Cₛ^n⟮I; F, V⟯} (hsub : s.tsupport ⊆ c.source) :
    Function.support (coordTestFun t c s) = c '' {x | s x ≠ 0} := by
  ext y
  by_cases hy : y ∈ c.target
  · rw [Function.mem_support, coordTestFun_of_mem t c s hy]
    have hsrc : c.symm y ∈ c.source := c.map_target hy
    constructor
    · intro hne
      refine ⟨c.symm y, fun hz ↦ hne (by simp [hz]), c.right_inv hy⟩
    · rintro ⟨x, hx, rfl⟩ hzero
      have hxsrc : x ∈ c.source := hsub (ContMDiffSection.tsupport_def s ▸ subset_closure hx)
      have hsymm := congrArg (t.symmL ℝ (c.symm (c x))) hzero
      rw [t.symmL_continuousLinearMapAt (hct hsrc), map_zero, c.left_inv hxsrc] at hsymm
      exact hx hsymm
  · simp only [Function.mem_support, coordTestFun_of_notMem t c s hy, ne_eq, not_true_eq_false,
      false_iff, mem_image, not_exists, not_and]
    intro x hx hxy
    exact hy (hxy ▸ c.map_source (hsub (ContMDiffSection.tsupport_def s ▸ subset_closure hx)))

omit [T2Space M] [ContMDiffVectorBundle n F V I] in
include hct in
private theorem tsupport_coordTestFun {s : Cₛ^n⟮I; F, V⟯} (hcomp : IsCompact s.tsupport)
    (hsub : s.tsupport ⊆ c.source) :
    _root_.tsupport (coordTestFun t c s) = c '' s.tsupport := by
  have hclosed : IsClosed (c '' s.tsupport) :=
    (hcomp.image_of_continuousOn (c.continuousOn.mono hsub)).isClosed
  apply le_antisymm
  · exact closure_minimal (fun y hy ↦ by
      by_contra hny
      exact Function.mem_support.1 hy (coordTestFun_eq_zero_of_notMem_image t c Subset.rfl hny))
      hclosed
  · rw [_root_.tsupport, support_coordTestFun t c hct hsub, ContMDiffSection.tsupport_def]
    rw [ContMDiffSection.tsupport_def] at hsub
    exact (c.continuousOn.mono hsub).image_closure

omit [T2Space M] in
/-- Read a smooth bundle section supported in a compact subset `K ⊆ c.source` through the chart `c`
and bundle frame `t`, obtaining a native test function supported in `c '' K`. -/
def chartTestSupportedIn {K : Compacts M} (hK : (K : Set M) ⊆ c.source) :
    supportedIn I F n V K →ₗ[ℝ]
      𝓓^{n}_{⟨c '' K, K.isCompact.image_of_continuousOn (c.continuousOn.mono hK)⟩}(E, F) where
  toFun s :=
    ⟨coordTestFun t c s.1,
      contDiff_coordTestFun t c hc_symm hct
        (K.isCompact.of_isClosed_subset s.1.isClosed_tsupport (mem_supportedIn.1 s.2))
        ((mem_supportedIn.1 s.2).trans hK),
      fun _ hy ↦ coordTestFun_eq_zero_of_notMem_image t c (mem_supportedIn.1 s.2) hy⟩
  map_add' s₁ s₂ := by
    ext y
    rw [FunLike.coe_add, Pi.add_apply, ← ContDiffMapSupportedIn.toFun_eq_coe,
      ← ContDiffMapSupportedIn.toFun_eq_coe, ← ContDiffMapSupportedIn.toFun_eq_coe]
    by_cases hy : y ∈ c.target
    · simp [coordTestFun_of_mem t c _ hy]
    · simp [coordTestFun_of_notMem t c _ hy]
  map_smul' a s := by
    ext y
    rw [RingHom.id_apply, FunLike.coe_smul, Pi.smul_apply, ← ContDiffMapSupportedIn.toFun_eq_coe,
      ← ContDiffMapSupportedIn.toFun_eq_coe]
    by_cases hy : y ∈ c.target
    · simp [coordTestFun_of_mem t c _ hy]
    · simp [coordTestFun_of_notMem t c _ hy]

omit [T2Space M] in
/-- On the chart target, chart extraction reads the section value in the defining frame. -/
@[simp]
theorem chartTestSupportedIn_apply_of_mem {K : Compacts M} (hK : (K : Set M) ⊆ c.source)
    (s : supportedIn I F n V K) {y : E} (hy : y ∈ c.target) :
    t.chartTestSupportedIn c hc_symm hct hK s y =
      t.continuousLinearMapAt ℝ (c.symm y) (s.1 (c.symm y)) :=
  coordTestFun_of_mem t c s.1 hy

omit [T2Space M] in
/-- Outside the chart target, chart extraction vanishes. -/
@[simp]
theorem chartTestSupportedIn_apply_of_notMem {K : Compacts M} (hK : (K : Set M) ⊆ c.source)
    (s : supportedIn I F n V K) {y : E} (hy : y ∉ c.target) :
    t.chartTestSupportedIn c hc_symm hct hK s y = 0 :=
  coordTestFun_of_notMem t c s.1 hy

omit [T2Space M] in
/-- Evaluated at a chart coordinate `c x`, chart extraction recovers the frame coefficient at
`x`. -/
theorem chartTestSupportedIn_apply_chart {K : Compacts M} (hK : (K : Set M) ⊆ c.source)
    (s : supportedIn I F n V K) {x : M} (hx : x ∈ c.source) :
    t.chartTestSupportedIn c hc_symm hct hK s (c x) = t.continuousLinearMapAt ℝ x (s.1 x) := by
  rw [chartTestSupportedIn_apply_of_mem t c hc_symm hct hK s (c.map_source hx), c.left_inv hx]

omit [T2Space M] in
/-- Chart extraction preserves closed support, transported by the chart. -/
@[simp]
theorem tsupport_chartTestSupportedIn {K : Compacts M} (hK : (K : Set M) ⊆ c.source)
    (s : supportedIn I F n V K) :
    _root_.tsupport (t.chartTestSupportedIn c hc_symm hct hK s) = c '' s.1.tsupport :=
  tsupport_coordTestFun t c hct
    (K.isCompact.of_isClosed_subset s.1.isClosed_tsupport (mem_supportedIn.1 s.2))
    ((mem_supportedIn.1 s.2).trans hK)

/-- Re-extending a chart-extracted section recovers the original section. -/
theorem chartTestSection_ofSupportedIn_chartTestSupportedIn
    (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source) {K : Compacts M} (hK : (K : Set M) ⊆ c.source)
    (s : supportedIn I F n V K) :
    t.chartTestSection c hc hct
        (TestFunction.ofSupportedIn
          (Ω := ⟨c.target, c.open_target⟩)
          (K := ⟨c '' K, K.isCompact.image_of_continuousOn (c.continuousOn.mono hK)⟩)
          (image_subset_iff.2 fun _ hx ↦ c.map_source (hK hx))
          (t.chartTestSupportedIn c hc_symm hct hK s)) =
      ofSupportedIn K s := by
  apply Subtype.ext
  ext x
  by_cases hx : x ∈ c.source
  · rw [chartTestSection_apply_of_mem t c hc hct _ hx, TestFunction.coe_ofSupportedIn,
      chartTestSupportedIn_apply_chart t c hc_symm hct hK s hx,
      t.symmL_continuousLinearMapAt (hct hx), ofSupportedIn_apply]
  · rw [chartTestSection_apply_of_notMem t c hc hct _ hx, ofSupportedIn_apply]
    exact (s.1.eq_zero_of_notMem_tsupport fun h ↦ hx (hK (mem_supportedIn.1 s.2 h))).symm

/-- Extracting a chart-extended test function recovers the original test function. -/
theorem chartTestSupportedIn_chartTestSection_ofSupportedIn
    (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source) {K : Compacts E} (hK : (K : Set E) ⊆ c.target)
    (φ : 𝓓^{n}_{K}(E, F)) :
    let K_M : Compacts M := ⟨c.symm '' K, K.isCompact.image_of_continuousOn
      (c.continuousOn_symm.mono hK)⟩
    let hKM : (K_M : Set M) ⊆ c.source := image_subset_iff.2 fun _ hy ↦ c.map_target (hK hy)
    let s : supportedIn I F n V K_M :=
      ⟨(t.chartTestSection c hc hct (TestFunction.ofSupportedIn (Ω := ⟨c.target, c.open_target⟩)
          hK φ)).1,
        t.chartTestSection_mem_supportedIn c hc hct _ (by
          rw [TestFunction.coe_ofSupportedIn]
          exact φ.tsupport_subset)⟩
    ⇑(t.chartTestSupportedIn c hc_symm hct hKM s) = ⇑φ := by
  intro K_M hKM s
  funext y
  by_cases hy : y ∈ c.target
  · rw [chartTestSupportedIn_apply_of_mem t c hc_symm hct hKM s hy,
      t.continuousLinearMapAt_chartTestSection c hc hct _ (c.map_target hy),
      c.right_inv hy, TestFunction.coe_ofSupportedIn]
  · rw [chartTestSupportedIn_apply_of_notMem t c hc_symm hct hKM s hy]
    exact (φ.zero_on_compl fun h ↦ hy (hK h)).symm

omit [T2Space M] in
/-- In a single global chart, reading a compactly supported section in the defining frame and chart
gives a native test function on the chart target. -/
def chartTestCoords (hsource : c.source = univ) :
    compactlySupported I F n V →ₗ[ℝ] 𝓓^{n}(⟨c.target, c.open_target⟩, F) where
  toFun s :=
    let K : Compacts M := ⟨s.1.tsupport, mem_compactlySupported.1 s.2⟩
    have hK : (K : Set M) ⊆ c.source := hsource.symm ▸ subset_univ _
    TestFunction.ofSupportedIn (Ω := ⟨c.target, c.open_target⟩)
      (K := ⟨c '' K, K.isCompact.image_of_continuousOn (c.continuousOn.mono hK)⟩)
      (image_subset_iff.2 fun _ hx ↦ c.map_source (hK hx))
      (t.chartTestSupportedIn c hc_symm hct hK ⟨s.1, mem_supportedIn.2 Subset.rfl⟩)
  map_add' s₁ s₂ := by
    ext y
    rw [FunLike.coe_add, Pi.add_apply, TestFunction.coe_ofSupportedIn,
      TestFunction.coe_ofSupportedIn, TestFunction.coe_ofSupportedIn]
    by_cases hy : y ∈ c.target
    · rw [chartTestSupportedIn_apply_of_mem _ _ _ _ _ _ hy,
        chartTestSupportedIn_apply_of_mem _ _ _ _ _ _ hy,
        chartTestSupportedIn_apply_of_mem _ _ _ _ _ _ hy]
      simp [map_add]
    · rw [chartTestSupportedIn_apply_of_notMem _ _ _ _ _ _ hy,
        chartTestSupportedIn_apply_of_notMem _ _ _ _ _ _ hy,
        chartTestSupportedIn_apply_of_notMem _ _ _ _ _ _ hy, add_zero]
  map_smul' a s := by
    ext y
    rw [RingHom.id_apply, FunLike.coe_smul, Pi.smul_apply, TestFunction.coe_ofSupportedIn,
      TestFunction.coe_ofSupportedIn]
    by_cases hy : y ∈ c.target
    · rw [chartTestSupportedIn_apply_of_mem _ _ _ _ _ _ hy,
        chartTestSupportedIn_apply_of_mem _ _ _ _ _ _ hy]
      simp [map_smul]
    · rw [chartTestSupportedIn_apply_of_notMem _ _ _ _ _ _ hy,
        chartTestSupportedIn_apply_of_notMem _ _ _ _ _ _ hy, smul_zero]

omit [T2Space M] in
/-- On the chart target, `chartTestCoords` reads the section value in the defining frame. -/
@[simp]
theorem chartTestCoords_apply_of_mem (hsource : c.source = univ)
    (s : compactlySupported I F n V) {y : E} (hy : y ∈ c.target) :
    t.chartTestCoords c hc_symm hct hsource s y =
      t.continuousLinearMapAt ℝ (c.symm y) (s.1 (c.symm y)) := by
  rw [chartTestCoords, LinearMap.coe_mk, AddHom.coe_mk, TestFunction.coe_ofSupportedIn,
    chartTestSupportedIn_apply_of_mem _ _ _ _ _ _ hy]

omit [T2Space M] in
/-- Outside the chart target, `chartTestCoords` vanishes. -/
@[simp]
theorem chartTestCoords_apply_of_notMem (hsource : c.source = univ)
    (s : compactlySupported I F n V) {y : E} (hy : y ∉ c.target) :
    t.chartTestCoords c hc_symm hct hsource s y = 0 := by
  rw [chartTestCoords, LinearMap.coe_mk, AddHom.coe_mk, TestFunction.coe_ofSupportedIn,
    chartTestSupportedIn_apply_of_notMem _ _ _ _ _ _ hy]

omit [T2Space M] in
/-- Global chart extraction preserves closed support, transported by the chart. -/
@[simp]
theorem tsupport_chartTestCoords (hsource : c.source = univ) (s : compactlySupported I F n V) :
    _root_.tsupport (t.chartTestCoords c hc_symm hct hsource s) = c '' s.1.tsupport := by
  rw [chartTestCoords, LinearMap.coe_mk, AddHom.coe_mk, TestFunction.coe_ofSupportedIn,
    tsupport_chartTestSupportedIn]

end Bundle.Trivialization

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.CompactSupport.Topology
public import TauCeti.Geometry.Manifold.VectorBundle.Section.CompactSupport.Complexification.Basic
public import TauCeti.Analysis.Distribution.TestFunction.Postcomp
import TauCeti.Geometry.Manifold.VectorBundle.Section.Complexification

/-!
# Real and complex compactly supported bundle tests

The algebraic comparisons in `CompactSupport.Complexification.Basic` identify native sections
of a complexified real bundle with real pairs at all orders `n : ℕ∞ω`. This module adds
continuity at all orders `n : ℕ∞ω`, including every prescribed compact-support stage, for the
existing compactly-supported final locally convex topologies induced by any matched family of real
and complexified atlas frames (without needing a frame cover, boundarylessness, Hausdorffness, or
finite-dimensionality of the model space). The fibre model can be arbitrary normed,
infinite dimensional or incomplete. These results make no LF or strict inductive-limit assertion.

Restricting the frame-topology continuous linear maps from `Section.Complexification` to each
fixed-compact support stage and applying the universal property
`ContMDiffSection.continuous_compactlySupportedTopology_iff` proves continuity on compactly
supported tests. The compact stages retain their original frame subspace topologies. On a
Hausdorff base at orders `n : ℕ∞`, the real and imaginary projections and inclusions also commute
with chart extension and constant model postcomposition (`section Charts`). Original real tests
identify with the pullback of the existing native `TauCeti.realPoints` submodule, using the
original real scalar action explicitly.

## Main definitions

* `ContMDiffSection.CompactlySupported.complexificationCLEProd`: the real pair equivalence.
* `ContMDiffSection.SupportedIn.complexificationCLEProd`: the same comparison at each compact stage.
* `ContMDiffSection.CompactlySupported.realPointsConjCLE` and
  `ContMDiffSection.SupportedIn.realPointsConjCLE`: the native real fixed subspaces.
* `ContMDiffSection.CompactlySupported.smulICLE` and `ContMDiffSection.CompactlySupported.conjCLE`:
  the quarter-turn and conjugation, with actual original-fibre evaluation and exact support laws.

## References

* Trèves, *Topological Vector Spaces, Distributions and Kernels*, Chapter 13 (test-function spaces).
-/

public section

noncomputable section
open Bundle Set TopologicalSpace TauCeti ContMDiffSection
open scoped ContDiff Manifold TensorProduct Topology Distributions

namespace ContMDiffSection

section Charts

variable {n : ℕ∞}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] V x)] [∀ x, IsComplexificationTopology (V x)]
  [ContMDiffVectorBundle n F V I]

/-- Real projection commutes with native chart extension and model postcomposition. -/
theorem _root_.Bundle.Trivialization.realPart_chartTestSection_complexification
    (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
    (c : OpenPartialHomeomorph M E) (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source)
    (hct : c.source ⊆ t.baseSet)
    (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, Complexification F)) :
    CompactlySupported.realPart (n := n) (t.complexification.chartTestSection c hc (by simpa only
      [Trivialization.baseSet_complexification] using hct) φ) =
      t.chartTestSection c hc hct (TestFunction.postcompCLM (Complexification.reCLM F) φ) := by
  apply Subtype.ext
  apply ContMDiffSection.ext
  intro x
  by_cases hx : x ∈ c.source
  · simp only [CompactlySupported.coe_realPart, realPartLinearMap_apply,
      Trivialization.chartTestSection_apply_of_mem _ _ _ _ _ hx, TestFunction.postcompCLM_apply]
    rw [t.complexification.symmL_apply (R := ℝ) (by simpa using hct hx),
      t.complexification_symm_apply (hct hx), t.symmL_apply (hct hx)]
    simp
  · simp [hx]

/-- Imaginary projection commutes with native chart extension and model postcomposition. -/
theorem _root_.Bundle.Trivialization.imaginaryPart_chartTestSection_complexification
    (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
    (c : OpenPartialHomeomorph M E) (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source)
    (hct : c.source ⊆ t.baseSet)
    (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, Complexification F)) :
    CompactlySupported.imaginaryPart (n := n) (t.complexification.chartTestSection c hc (by simpa
      only [Trivialization.baseSet_complexification] using hct) φ) =
      t.chartTestSection c hc hct (TestFunction.postcompCLM (Complexification.imCLM F) φ) := by
  apply Subtype.ext
  apply ContMDiffSection.ext
  intro x
  by_cases hx : x ∈ c.source
  · simp only [CompactlySupported.coe_imaginaryPart, imaginaryPartLinearMap_apply,
      Trivialization.chartTestSection_apply_of_mem _ _ _ _ _ hx, TestFunction.postcompCLM_apply]
    rw [t.complexification.symmL_apply (R := ℝ) (by simpa using hct hx),
      t.complexification_symm_apply (hct hx), t.symmL_apply (hct hx)]
    simp
  · simp [hx]

/-- The real inclusion commutes with native chart extension and model postcomposition. -/
theorem _root_.Bundle.Trivialization.oneTmul_chartTestSection (t : Trivialization F (π F V))
    [MemTrivializationAtlas t]
    (c : OpenPartialHomeomorph M E) (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source)
    (hct : c.source ⊆ t.baseSet) (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F)) :
    CompactlySupported.oneTmul (n := n) (t.chartTestSection c hc hct φ) =
      t.complexification.chartTestSection c hc
        (by simpa only [Trivialization.baseSet_complexification] using hct)
        (TestFunction.postcompCLM (Complexification.ofRealLI F).toContinuousLinearMap φ) := by
  apply Subtype.ext
  apply ContMDiffSection.ext
  intro x
  by_cases hx : x ∈ c.source
  · simp only [CompactlySupported.coe_oneTmul, oneTmulLinearMap_apply,
      Trivialization.chartTestSection_apply_of_mem _ _ _ _ _ hx, TestFunction.postcompCLM_apply]
    rw [t.complexification.symmL_apply (R := ℝ) (by simpa using hct hx),
      t.complexification_symm_apply (hct hx), t.symmL_apply (hct hx)]
    have hz : t.symm x 0 = 0 := by
      rw [← t.symmL_apply (R := ℝ) (hct hx)]
      exact map_zero _
    simp [hz]
  · simp [hx]

/-- The imaginary inclusion commutes with native chart extension and model
postcomposition. -/
theorem _root_.Bundle.Trivialization.ITmul_chartTestSection (t : Trivialization F (π F V))
    [MemTrivializationAtlas t]
    (c : OpenPartialHomeomorph M E) (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source)
    (hct : c.source ⊆ t.baseSet) (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F)) :
    CompactlySupported.ITmul (n := n) (t.chartTestSection c hc hct φ) =
      t.complexification.chartTestSection c hc
        (by simpa only [Trivialization.baseSet_complexification] using hct)
        (TestFunction.postcompCLM (Complex.I • (Complexification.ofRealLI
          F).toContinuousLinearMap) φ) := by
  apply Subtype.ext
  apply ContMDiffSection.ext
  intro x
  by_cases hx : x ∈ c.source
  · simp only [CompactlySupported.coe_ITmul, ITmulLinearMap_apply,
      Trivialization.chartTestSection_apply_of_mem _ _ _ _ _ hx, TestFunction.postcompCLM_apply]
    rw [t.complexification.symmL_apply (R := ℝ) (by simpa using hct hx),
      t.complexification_symm_apply (hct hx), t.symmL_apply (hct hx)]
    have hz : t.symm x 0 = 0 := by
      rw [← t.symmL_apply (R := ℝ) (hct hx)]
      exact map_zero _
    simp [hz]
  · simp [hx]

end Charts


section Topology

variable {n : ℕ∞ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] V x)] [∀ x, IsComplexificationTopology (V x)]
  [ContMDiffVectorBundle n F V I]
  {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- The real projection is continuous for matched fixed-compact inductive topologies. -/
theorem CompactlySupported.continuous_realPart :
    let _ := compactlySupportedTopology (I := I) (n := n) e U hU
    let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    Continuous (CompactlySupported.realPart (n := n) (I := I) (F := F) (V := V)) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  let _ := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
    (by simpa only [Trivialization.baseSet_complexification] using hU)
  let _ := compactlySupportedTopology (I := I) (n := n) e U hU
  let _ := isTopologicalAddGroup_compactlySupportedTopology (I := I) (n := n) e U hU
  let _ := continuousSMul_compactlySupportedTopology (I := I) (n := n) e U hU
  let _ := locallyConvexSpace_compactlySupportedTopology (I := I) (n := n) e U hU
  refine (continuous_compactlySupportedTopology_iff (fun i ↦ (e i).complexification) U
    (by simpa only [Trivialization.baseSet_complexification] using hU)
    (CompactlySupported.realPart (n := n) (I := I) (F := F) (V := V))).2 fun K ↦ ?_
  have hstage : Continuous (fun s : supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K ↦
      (⟨ContMDiffSection.realPartCLM e U hU s.val, mem_supportedIn.2 (by
        rw [ContMDiffSection.realPartCLM_apply]
        exact (tsupport_realPartLinearMap_subset s.val).trans
          (mem_supportedIn.1 s.property))⟩ : supportedIn I F n V K)) :=
    ((ContMDiffSection.realPartCLM e U hU).continuous.comp continuous_subtypeVal).subtype_mk _
  exact ((continuous_ofSupportedIn e U hU K).comp hstage).congr fun s ↦
    Subtype.ext (by simp [ContMDiffSection.realPartCLM_apply])

/-- The imaginary projection is continuous for matched fixed-compact inductive topologies. -/
theorem CompactlySupported.continuous_imaginaryPart :
    let _ := compactlySupportedTopology (I := I) (n := n) e U hU
    let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    Continuous (CompactlySupported.imaginaryPart (n := n) (I := I) (F := F) (V := V)) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  let _ := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
    (by simpa only [Trivialization.baseSet_complexification] using hU)
  let _ := compactlySupportedTopology (I := I) (n := n) e U hU
  let _ := isTopologicalAddGroup_compactlySupportedTopology (I := I) (n := n) e U hU
  let _ := continuousSMul_compactlySupportedTopology (I := I) (n := n) e U hU
  let _ := locallyConvexSpace_compactlySupportedTopology (I := I) (n := n) e U hU
  refine (continuous_compactlySupportedTopology_iff (fun i ↦ (e i).complexification) U
    (by simpa only [Trivialization.baseSet_complexification] using hU)
    (CompactlySupported.imaginaryPart (n := n) (I := I) (F := F) (V := V))).2 fun K ↦ ?_
  have hstage : Continuous (fun s : supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K ↦
      (⟨ContMDiffSection.imaginaryPartCLM e U hU s.val, mem_supportedIn.2 (by
        rw [ContMDiffSection.imaginaryPartCLM_apply]
        exact (tsupport_imaginaryPartLinearMap_subset s.val).trans
          (mem_supportedIn.1 s.property))⟩ : supportedIn I F n V K)) :=
    ((ContMDiffSection.imaginaryPartCLM e U hU).continuous.comp continuous_subtypeVal).subtype_mk _
  exact ((continuous_ofSupportedIn e U hU K).comp hstage).congr fun s ↦
    Subtype.ext (by simp [ContMDiffSection.imaginaryPartCLM_apply])

/-- The real inclusion is continuous for matched fixed-compact inductive topologies. -/
theorem CompactlySupported.continuous_oneTmul :
    let _ := compactlySupportedTopology (I := I) (n := n) e U hU
    let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    Continuous (CompactlySupported.oneTmul (n := n) (I := I) (F := F) (V := V)) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  let _ := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
    (by simpa only [Trivialization.baseSet_complexification] using hU)
  let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
    (by simpa only [Trivialization.baseSet_complexification] using hU)
  let _ := isTopologicalAddGroup_compactlySupportedTopology (I := I) (n := n)
    (fun i ↦ (e i).complexification) U (by simpa only [Trivialization.baseSet_complexification]
      using hU)
  let _ := continuousSMul_compactlySupportedTopology (I := I) (n := n)
    (fun i ↦ (e i).complexification) U (by simpa only [Trivialization.baseSet_complexification]
      using hU)
  let _ := locallyConvexSpace_compactlySupportedTopology (I := I) (n := n)
    (fun i ↦ (e i).complexification) U (by simpa only [Trivialization.baseSet_complexification]
      using hU)
  refine (continuous_compactlySupportedTopology_iff e U hU
    (CompactlySupported.oneTmul (n := n) (I := I) (F := F) (V := V))).2 fun K ↦ ?_
  have hstage : Continuous (fun s : supportedIn I F n V K ↦
      (⟨ContMDiffSection.oneTmulCLM e U hU s.val, mem_supportedIn.2 (by
        rw [ContMDiffSection.oneTmulCLM_apply, tsupport_oneTmulLinearMap]
        exact mem_supportedIn.1 s.property)⟩ :
        supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K)) :=
    ((ContMDiffSection.oneTmulCLM e U hU).continuous.comp continuous_subtypeVal).subtype_mk _
  exact ((continuous_ofSupportedIn (fun i ↦ (e i).complexification) U
    (by simpa only [Trivialization.baseSet_complexification] using hU) K).comp hstage).congr
    fun s ↦ Subtype.ext (by simp [ContMDiffSection.oneTmulCLM_apply])

/-- The imaginary inclusion is continuous for matched fixed-compact inductive topologies. -/
theorem CompactlySupported.continuous_ITmul :
    let _ := compactlySupportedTopology (I := I) (n := n) e U hU
    let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    Continuous (CompactlySupported.ITmul (n := n) (I := I) (F := F) (V := V)) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  let _ := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
    (by simpa only [Trivialization.baseSet_complexification] using hU)
  let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
    (by simpa only [Trivialization.baseSet_complexification] using hU)
  let _ := isTopologicalAddGroup_compactlySupportedTopology (I := I) (n := n)
    (fun i ↦ (e i).complexification) U (by simpa only [Trivialization.baseSet_complexification]
      using hU)
  let _ := continuousSMul_compactlySupportedTopology (I := I) (n := n)
    (fun i ↦ (e i).complexification) U (by simpa only [Trivialization.baseSet_complexification]
      using hU)
  let _ := locallyConvexSpace_compactlySupportedTopology (I := I) (n := n)
    (fun i ↦ (e i).complexification) U (by simpa only [Trivialization.baseSet_complexification]
      using hU)
  refine (continuous_compactlySupportedTopology_iff e U hU
    (CompactlySupported.ITmul (n := n) (I := I) (F := F) (V := V))).2 fun K ↦ ?_
  have hstage : Continuous (fun s : supportedIn I F n V K ↦
      (⟨ContMDiffSection.ITmulCLM e U hU s.val, mem_supportedIn.2 (by
        rw [ContMDiffSection.ITmulCLM_apply, tsupport_ITmulLinearMap]
        exact mem_supportedIn.1 s.property)⟩ :
        supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K)) :=
    ((ContMDiffSection.ITmulCLM e U hU).continuous.comp continuous_subtypeVal).subtype_mk _
  exact ((continuous_ofSupportedIn (fun i ↦ (e i).complexification) U
    (by simpa only [Trivialization.baseSet_complexification] using hU) K).comp hstage).congr
    fun s ↦ Subtype.ext (by simp [ContMDiffSection.ITmulCLM_apply])

/-- The real pair equivalence for matched fixed-compact inductive locally convex topologies. -/
def CompactlySupported.complexificationCLEProd :
    let _ := compactlySupportedTopology (I := I) (n := n) e U hU
    let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) ≃L[ℝ]
      compactlySupported I F n V × compactlySupported I F n V := by
  let _ := compactlySupportedTopology (I := I) (n := n) e U hU
  let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
    (by simpa only [Trivialization.baseSet_complexification] using hU)
  let _ := isTopologicalAddGroup_compactlySupportedTopology (I := I) (n := n)
    (fun i ↦ (e i).complexification) U (by simpa only [Trivialization.baseSet_complexification]
      using hU)
  refine { CompactlySupported.complexificationEquivProd (n := n) (I := I) (F := F) (V := V) with
    continuous_toFun := ?_, continuous_invFun := ?_ }
  · rw [LinearEquiv.toFun_eq_coe]
    exact ((CompactlySupported.continuous_realPart (n := n) e U hU).prodMk
      (CompactlySupported.continuous_imaginaryPart (n := n) e U hU)).congr
      fun φ ↦ (CompactlySupported.complexificationEquivProd_apply φ).symm
  · rw [LinearEquiv.invFun_eq_symm]
    exact (((CompactlySupported.continuous_oneTmul (n := n) e U hU).comp continuous_fst).add
      ((CompactlySupported.continuous_ITmul (n := n) e U hU).comp continuous_snd)).congr
      fun p ↦ (CompactlySupported.complexificationEquivProd_symm_apply p).symm

/-- The bundled map evaluates by the stated original-fibre formula. -/
@[simp] theorem CompactlySupported.complexificationCLEProd_apply (φ : compactlySupported I
  (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    let _ := compactlySupportedTopology (I := I) (n := n) e U hU
    let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    CompactlySupported.complexificationCLEProd (n := n) e U hU φ =
      (CompactlySupported.realPart φ, CompactlySupported.imaginaryPart φ) := by
  simpa only [CompactlySupported.complexificationCLEProd, ContinuousLinearEquiv.coe_mk] using
    CompactlySupported.complexificationEquivProd_apply φ

/-- The bundled map evaluates by the stated original-fibre formula. -/
@[simp] theorem CompactlySupported.complexificationCLEProd_symm_apply (p : compactlySupported I F
  n V × compactlySupported I F n V) :
    let _ := compactlySupportedTopology (I := I) (n := n) e U hU
    let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    (CompactlySupported.complexificationCLEProd (n := n) e U hU).symm p =
      CompactlySupported.complexificationEquivProd.symm p := by rfl

/-- The pair equivalence on each compact stage with its original frame subspace topology. -/
def SupportedIn.complexificationCLEProd (K : Compacts M) :
    let _ := frameTopology (I := I) (n := n) e U hU
    let _ := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K ≃L[ℝ]
      supportedIn I F n V K × supportedIn I F n V K := by
  let _ := frameTopology (I := I) (n := n) e U hU
  let _ := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
    (by simpa only [Trivialization.baseSet_complexification] using hU)
  let _ := compactlySupportedTopology (I := I) (n := n) e U hU
  let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
    (by simpa only [Trivialization.baseSet_complexification] using hU)
  let L := CompactlySupported.complexificationCLEProd (n := n) (I := I) e U hU
  have hc := continuous_ofSupportedIn (I := I) (n := n) (fun i ↦ (e i).complexification) U
    (by simpa only [Trivialization.baseSet_complexification] using hU) K
  have hr := continuous_ofSupportedIn (I := I) (n := n) e U hU K
  have he := isEmbedding_ofSupportedIn (I := I) (n := n) e U hU K
  have hec := isEmbedding_ofSupportedIn (I := I) (n := n)
    (fun i ↦ (e i).complexification) U (by simpa only [Trivialization.baseSet_complexification]
      using hU) K
  refine { SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V) K with
    continuous_toFun := ?_, continuous_invFun := ?_ }
  · rw [LinearEquiv.toFun_eq_coe]
    apply (he.prodMap he).continuous_iff.2
    exact (L.continuous.comp hc).congr fun φ ↦
      (SupportedIn.complexificationEquivProd_ofSupportedIn (n := n) (I := I) K φ).symm
  · rw [LinearEquiv.invFun_eq_symm]
    apply hec.continuous_iff.2
    refine (L.symm.continuous.comp (hr.prodMap hr)).congr fun p ↦ ?_
    simpa only [Function.comp_apply, L, CompactlySupported.complexificationCLEProd_symm_apply,
      Prod.map] using
      (SupportedIn.complexificationEquivProd_symm_ofSupportedIn (n := n) (I := I) K p).symm

/-- The continuous stage comparison has the native algebraic comparison as its underlying map. -/
@[simp] theorem SupportedIn.complexificationCLEProd_apply (K : Compacts M)
    (φ : supportedIn I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) K) :
    let _ := frameTopology (I := I) (n := n) e U hU
    let _ := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    SupportedIn.complexificationCLEProd (n := n) (I := I) e U hU K φ =
      SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V) K φ := by rfl

/-- Continuous stage reconstruction has the same underlying native reconstruction. -/
@[simp] theorem SupportedIn.complexificationCLEProd_symm_apply (K : Compacts M)
    (p : supportedIn I F n V K × supportedIn I F n V K) :
    let _ := frameTopology (I := I) (n := n) e U hU
    let _ := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    (SupportedIn.complexificationCLEProd (n := n) (I := I) e U hU K).symm p =
      (SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V) K).symm p :=
  by rfl

/-- The original real compact stage identifies continuously with its native fixed subspace. -/
def SupportedIn.realPointsConjCLE (K : Compacts M) :
    let _ := frameTopology (I := I) (n := n) e U hU
    let _ := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    supportedIn I F n V K ≃L[ℝ] SupportedIn.realPointsConj (n := n) (I := I) (F := F) (V := V) K
      := by
  let _ := frameTopology (I := I) (n := n) e U hU
  let _ := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
    (by simpa only [Trivialization.baseSet_complexification] using hU)
  let L := SupportedIn.complexificationCLEProd (n := n) (I := I) e U hU K
  refine { SupportedIn.realPointsConjEquiv (n := n) (I := I) (F := F) (V := V) K with
    continuous_toFun := ?_, continuous_invFun := ?_ }
  · rw [LinearEquiv.toFun_eq_coe]
    apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
    refine (L.symm.continuous.comp (continuous_id.prodMk
      (continuous_const (y := (0 : supportedIn I F n V K))))).congr fun φ ↦ ?_
    simpa only [Function.comp_apply, id_eq, L, SupportedIn.complexificationCLEProd_symm_apply]
      using (SupportedIn.coe_realPointsConjEquiv_apply (n := n) (I := I)
        (F := F) (V := V) (K : Set M) φ).symm
  · rw [LinearEquiv.invFun_eq_symm]
    refine (continuous_fst.comp (L.continuous.comp continuous_subtypeVal)).congr fun φ ↦ ?_
    simpa only [Function.comp_apply, L, SupportedIn.complexificationCLEProd_apply] using
      (SupportedIn.realPointsConjEquiv_symm_apply (n := n) (I := I)
        (F := F) (V := V) (K : Set M) φ).symm

/-- The original real tests identify continuously with the native fixed subspace. -/
def CompactlySupported.realPointsConjCLE :
    let _ := compactlySupportedTopology (I := I) (n := n) e U hU
    let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    compactlySupported I F n V ≃L[ℝ] CompactlySupported.realPointsConj (n := n) (I := I) (F := F)
      (V := V) := by
  let _ := compactlySupportedTopology (I := I) (n := n) e U hU
  let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
    (by simpa only [Trivialization.baseSet_complexification] using hU)
  refine { CompactlySupported.realPointsConjEquiv (n := n) (I := I) (F := F) (V := V) with
    continuous_toFun := ?_, continuous_invFun := ?_ }
  · rw [LinearEquiv.toFun_eq_coe]
    apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
    exact (CompactlySupported.continuous_oneTmul (n := n) (I := I) e U hU).congr
      fun φ ↦ (CompactlySupported.coe_realPointsConjEquiv_apply φ).symm
  · rw [LinearEquiv.invFun_eq_symm]
    exact ((CompactlySupported.continuous_realPart (n := n) (I := I) e U hU).comp
      (continuous_subtypeVal : Continuous (Subtype.val :
        CompactlySupported.realPointsConj (n := n) (I := I) (F := F) (V := V) → _))).congr
      fun φ ↦ (CompactlySupported.realPointsConjEquiv_symm_apply φ).symm


/-- The bundled map evaluates by the stated original-fibre formula. -/
@[simp] theorem CompactlySupported.coe_realPointsConjCLE_apply (φ : compactlySupported I F n V) :
    let _ := compactlySupportedTopology (I := I) (n := n) e U hU
    let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    (CompactlySupported.realPointsConjCLE (n := n) (I := I) e U hU φ).val =
      CompactlySupported.oneTmul φ := by
  simpa only [CompactlySupported.realPointsConjCLE, ContinuousLinearEquiv.coe_mk] using
    CompactlySupported.coe_realPointsConjEquiv_apply φ

/-- The bundled map evaluates by the stated original-fibre formula. -/
@[simp] theorem SupportedIn.coe_realPointsConjCLE_apply (K : Compacts M)
    (φ : supportedIn I F n V K) :
    let _ := frameTopology (I := I) (n := n) e U hU
    let _ := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    (SupportedIn.realPointsConjCLE (n := n) (I := I) e U hU K φ).val =
      (SupportedIn.complexificationEquivProd (n := n) (I := I) (F := F) (V := V) K).symm (φ, 0) :=
        by
  simpa only [SupportedIn.realPointsConjCLE, ContinuousLinearEquiv.coe_mk] using
    SupportedIn.coe_realPointsConjEquiv_apply (n := n) (I := I)
      (F := F) (V := V) (K : Set M) φ

/-- Multiplication by i as a real continuous linear equivalence of native compact tests. -/
def CompactlySupported.smulICLE :
    let _ := compactlySupportedTopology (I := I) (n := n) e U hU
    let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) ≃L[ℝ]
      compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) := by
  let _ := compactlySupportedTopology (I := I) (n := n) e U hU
  let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
    (by simpa only [Trivialization.baseSet_complexification] using hU)
  let _ := isTopologicalAddGroup_compactlySupportedTopology (I := I) (n := n) e U hU
  let _ := isTopologicalAddGroup_compactlySupportedTopology (I := I) (n := n)
    (fun i ↦ (e i).complexification) U
    (by simpa only [Trivialization.baseSet_complexification] using hU)
  let L := CompactlySupported.complexificationCLEProd (n := n) (I := I) e U hU
  have hc : Continuous (CompactlySupported.smulIEquiv
      (n := n) (I := I) (F := F) (V := V)) := by
    refine (L.symm.continuous.comp ((continuous_snd.neg.prodMk continuous_fst).comp
      L.continuous)).congr ?_
    intro φ
    apply L.injective
    simp only [Function.comp_apply, Pi.neg_apply, L.apply_symm_apply]
    simpa only [L, CompactlySupported.complexificationCLEProd_apply,
      CompactlySupported.complexificationEquivProd_apply] using
      (CompactlySupported.complexificationEquivProd_smulIEquiv φ).symm
  refine { CompactlySupported.smulIEquiv (n := n) (I := I) (F := F) (V := V) with
    continuous_toFun := ?_, continuous_invFun := ?_ }
  · simpa only [LinearEquiv.toFun_eq_coe] using hc
  · rw [LinearEquiv.invFun_eq_symm]
    exact hc.neg.congr fun φ ↦
      (CompactlySupported.smulIEquiv_symm_apply φ).symm



/-- Fibrewise tensor conjugation as a real continuous linear equivalence of native compact tests. -/
def CompactlySupported.conjCLE :
    let _ := compactlySupportedTopology (I := I) (n := n) e U hU
    let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) ≃L[ℝ]
      compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x) := by
  let _ := compactlySupportedTopology (I := I) (n := n) e U hU
  let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
    (by simpa only [Trivialization.baseSet_complexification] using hU)
  let _ := isTopologicalAddGroup_compactlySupportedTopology (I := I) (n := n) e U hU
  let _ := isTopologicalAddGroup_compactlySupportedTopology (I := I) (n := n)
    (fun i ↦ (e i).complexification) U
    (by simpa only [Trivialization.baseSet_complexification] using hU)
  let L := CompactlySupported.complexificationCLEProd (n := n) (I := I) e U hU
  have hc : Continuous (CompactlySupported.conjEquiv
      (n := n) (I := I) (F := F) (V := V)) := by
    refine (L.symm.continuous.comp ((continuous_fst.prodMk continuous_snd.neg).comp
      L.continuous)).congr ?_
    intro φ
    apply L.injective
    simp only [Function.comp_apply, Pi.neg_apply, L.apply_symm_apply]
    simpa only [L, CompactlySupported.complexificationCLEProd_apply,
      CompactlySupported.complexificationEquivProd_apply] using
      (CompactlySupported.complexificationEquivProd_conjEquiv φ).symm
  refine { CompactlySupported.conjEquiv (n := n) (I := I) (F := F) (V := V) with
    continuous_toFun := ?_, continuous_invFun := ?_ }
  · simpa only [LinearEquiv.toFun_eq_coe] using hc
  · rw [LinearEquiv.invFun_eq_symm]
    exact hc.congr fun φ ↦
      (CompactlySupported.conjEquiv_symm_apply φ).symm


/-- In real-pair coordinates, multiplication by i sends (a,b) to (-b,a). -/
theorem CompactlySupported.complexificationCLEProd_smulICLE
    (φ : compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    let _ := compactlySupportedTopology (I := I) (n := n) e U hU
    let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    CompactlySupported.complexificationCLEProd (n := n) e U hU (CompactlySupported.smulICLE
      (n := n) (I := I) e U hU φ) = (-CompactlySupported.imaginaryPart φ,
      CompactlySupported.realPart φ) := by
  simpa only [CompactlySupported.smulICLE, ContinuousLinearEquiv.coe_mk,
    CompactlySupported.complexificationCLEProd_apply,
    CompactlySupported.complexificationEquivProd_apply] using
    CompactlySupported.complexificationEquivProd_smulIEquiv (n := n) (I := I) (F := F) (V := V) φ

/-- In real-pair coordinates, conjugation sends (a,b) to (a,-b). -/
theorem CompactlySupported.complexificationCLEProd_conjCLE
    (φ : compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    let _ := compactlySupportedTopology (I := I) (n := n) e U hU
    let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    CompactlySupported.complexificationCLEProd (n := n) e U hU (CompactlySupported.conjCLE
      (n := n) (I := I) e U hU φ) = (CompactlySupported.realPart φ,
      -CompactlySupported.imaginaryPart φ) := by
  simpa only [CompactlySupported.conjCLE, ContinuousLinearEquiv.coe_mk,
    CompactlySupported.complexificationCLEProd_apply,
    CompactlySupported.complexificationEquivProd_apply] using
    CompactlySupported.complexificationEquivProd_conjEquiv (n := n) (I := I) (F := F) (V := V) φ

/-- The real continuous conjugation acts by the native tensor conjugation in each fibre. -/
@[simp] theorem CompactlySupported.conjCLE_apply
    (φ : compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) (x : M) :
    let _ := compactlySupportedTopology (I := I) (n := n) e U hU
    let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    (CompactlySupported.conjCLE (n := n) (I := I) e U hU φ).val x = tmulConj (V x) (φ.val
      x) := by
  simpa only [CompactlySupported.conjCLE, ContinuousLinearEquiv.coe_mk] using
    CompactlySupported.conjEquiv_apply (n := n) (I := I) (F := F) (V := V) φ x

/-- The real continuous quarter-turn acts by the actual complex scalar in each original fibre. -/
@[simp] theorem CompactlySupported.smulICLE_apply
    (φ : compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) (x : M) :
    let _ := compactlySupportedTopology (I := I) (n := n) e U hU
    let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    (CompactlySupported.smulICLE (n := n) (I := I) e U hU φ).val x = Complex.I • φ.val x :=
      by
  simpa only [CompactlySupported.smulICLE, ContinuousLinearEquiv.coe_mk] using
    CompactlySupported.smulIEquiv_apply (n := n) (I := I) (F := F) (V := V) φ x

/-- Conjugation preserves the exact closed support. -/
@[simp] theorem CompactlySupported.tsupport_conjCLE
    (φ : compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    let _ := compactlySupportedTopology (I := I) (n := n) e U hU
    let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    (CompactlySupported.conjCLE (n := n) (I := I) e U hU φ).val.tsupport = φ.val.tsupport
      := by
  simpa only [CompactlySupported.conjCLE, ContinuousLinearEquiv.coe_mk] using
    CompactlySupported.tsupport_conjEquiv (n := n) (I := I) (F := F) (V := V) φ

/-- The quarter-turn preserves the exact closed support. -/
@[simp] theorem CompactlySupported.tsupport_smulICLE
    (φ : compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    let _ := compactlySupportedTopology (I := I) (n := n) e U hU
    let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    (CompactlySupported.smulICLE (n := n) (I := I) e U hU φ).val.tsupport = φ.val.tsupport
      := by
  simpa only [CompactlySupported.smulICLE, ContinuousLinearEquiv.coe_mk] using
    CompactlySupported.tsupport_smulIEquiv (n := n) (I := I) (F := F) (V := V) φ

/-- Conjugation of native compact tests is involutive. -/
theorem CompactlySupported.conjCLE_involutive :
    let _ := compactlySupportedTopology (I := I) (n := n) e U hU
    let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    Function.Involutive (CompactlySupported.conjCLE (n := n) (I := I) e U hU) := by
  dsimp only
  intro φ
  simpa only [CompactlySupported.conjCLE, ContinuousLinearEquiv.coe_mk] using
    CompactlySupported.conjEquiv_conjEquiv (n := n) (I := I) (F := F) (V := V) φ

/-- The square of the quarter-turn is negation. -/
@[simp] theorem CompactlySupported.smulICLE_smulICLE
    (φ : compactlySupported I (Complexification F) n (fun x ↦ ℂ ⊗[ℝ] V x)) :
    let _ := compactlySupportedTopology (I := I) (n := n) e U hU
    let _ := compactlySupportedTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (by simpa only [Trivialization.baseSet_complexification] using hU)
    CompactlySupported.smulICLE (n := n) (I := I) e U hU (CompactlySupported.smulICLE (n :=
      n) (I := I) e U hU φ) = -φ := by
  simpa only [CompactlySupported.smulICLE, ContinuousLinearEquiv.coe_mk] using
    CompactlySupported.smulIEquiv_smulIEquiv (n := n) (I := I) (F := F) (V := V) φ

end Topology

end ContMDiffSection

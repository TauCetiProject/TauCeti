/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import Mathlib.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Restriction
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.CLMApply
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Independence of the frame cover for the native section topology

The compact derivative topology on native sections is independent of the covering smooth
frame system. Changes of frame act by the actual smooth transition matrix, including its
higher derivatives. Open-cover locality is taken in the existing weak Whitney topology.
-/

public noncomputable section

open Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney

namespace Bundle.Trivialization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  (e e' : Trivialization F (π F V)) [MemTrivializationAtlas e] [MemTrivializationAtlas e']
  {U : Opens M} (hU : (U : Set M) ⊆ e.baseSet) (hU' : (U : Set M) ⊆ e'.baseSet)

/-- A fixed smooth change of frame preserves continuity of section coefficient families.
The fibres may be infinite dimensional and the transition matrix need not be globally bounded. -/
theorem continuous_frameCoordinates_of_change {P : Type*} [TopologicalSpace P]
    {s : P → Cₛ^n⟮I; F, V⟯} (hs : Continuous (fun p ↦ e.frameCoordinates hU (s p))) :
    Continuous (fun p ↦ e'.frameCoordinates hU' (s p)) := by
  have h := (ContMDiffMap.continuous_clmApplyLinearMap
    (frameTransitionMap (I := I) (n := n) e e' hU hU')).comp hs
  simpa only [Function.comp_def, ← frameCoordinates_eq_clmApply] using h

end Bundle.Trivialization


namespace ContMDiffSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  [LocallyCompactSpace E]
  {ι : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- Coefficients in any smooth frame depend continuously on sections in a covering frame
topology. The comparison uses the actual transition multiplier on each overlap. -/
theorem continuous_frameCoordinates_of_cover (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (e' : Trivialization F (π F V)) [MemTrivializationAtlas e']
    (U' : Opens M) (hU' : (U' : Set M) ⊆ e'.baseSet) :
    let _ := frameTopology (I := I) (n := n) e U hU
    Continuous (e'.frameCoordinates (I := I) (n := n) hU') := by
  let _ := frameTopology (I := I) (n := n) e U hU
  let W (i : ι) : Opens U' := Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ (U i)
  have hW : ∀ x : U', ∃ i, x ∈ W i := fun x ↦ hcover x
  apply ContMDiffMap.continuous_of_forall_continuous_restrict W hW
  intro i
  let j : C^n⟮I, W i; I, U i⟯ :=
    ⟨fun x ↦ ⟨((x : U') : M), x.2⟩,
      (TauCeti.ContMDiff.subtypeVal_comp_iff (U i) _).mp (by
        -- The target-subtype criterion leaves composition through two inclusions. Normalize
        -- their nested subtype coercions, which are bundled by different open carriers.
        change ContMDiff I I n (fun x : W i ↦ ((x : U') : M))
        exact (contMDiff_subtype_val (U := U')).comp
          (contMDiff_subtype_val (U := W i)))⟩
  let A : C^n⟮I, W i; 𝓘(𝕜, F →L[𝕜] F), F →L[𝕜] F⟯ :=
    ⟨fun x ↦ ((e i).coordChangeL 𝕜 e' ((x : U') : M) : F →L[𝕜] F), fun x ↦
      (contMDiffAt_coordChangeL (e := e i) (e' := e')
        (hU i x.2) (hU' (x : U').2)).comp x
          (contMDiff_subtype_val.comp contMDiff_subtype_val).contMDiffAt⟩
  have hc : Continuous (fun s : Cₛ^n⟮I; F, V⟯ ↦
      ((e i).frameCoordinates (hU i) s).comp j) :=
    ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp
      ((continuous_frameCoordinates e U hU i).prodMk continuous_const)
  have h := (ContMDiffMap.continuous_clmApplyLinearMap A).comp hc
  convert h using 1
  funext s
  ext x
  simp only [Function.comp_apply, ContMDiffMap.restrict_apply,
    ContMDiffMap.clmApplyLinearMap_apply, ContMDiffMap.comp_apply,
    Bundle.Trivialization.frameCoordinates_apply]
  exact (((e i).coordChangeL_apply (R := 𝕜) e'
    ⟨hU i x.2, hU' (x : U').2⟩) ((e i) ⟨((x : U') : M), s x⟩).2).trans
      (congrArg (fun v ↦ (e' ⟨((x : U') : M), v⟩).2)
        ((e i).symm_apply_apply_mk (hU i x.2) (s ((x : U') : M)))) |>.symm

/-- A covering frame system induces a finer topology than any other specified frame system. -/
theorem frameTopology_le_of_cover (hcover : ∀ x : M, ∃ i, x ∈ U i)
    {κ : Type*} (e' : κ → Trivialization F (π F V))
    [∀ j, MemTrivializationAtlas (e' j)]
    (U' : κ → Opens M) (hU' : ∀ j, (U' j : Set M) ⊆ (e' j).baseSet) :
    frameTopology (I := I) (n := n) e U hU ≤ frameTopology (I := I) (n := n) e' U' hU' := by
  apply continuous_id_iff_le.mp
  let _ := frameTopology (I := I) (n := n) e U hU
  apply (continuous_frameTopology_iff_frameCoordinates e' U' hU').mpr
  intro j
  exact continuous_frameCoordinates_of_cover e U hU hcover (e' j) (U' j) (hU' j)

/-- The existing compact derivative topology on sections is independent of any choice of
covering smooth frames. This includes empty bases and empty covering index types. -/
theorem frameTopology_eq_of_covers (hcover : ∀ x : M, ∃ i, x ∈ U i)
    {κ : Type*} (e' : κ → Trivialization F (π F V))
    [∀ j, MemTrivializationAtlas (e' j)]
    (U' : κ → Opens M) (hU' : ∀ j, (U' j : Set M) ⊆ (e' j).baseSet)
    (hcover' : ∀ x : M, ∃ j, x ∈ U' j) :
    frameTopology (I := I) (n := n) e U hU = frameTopology (I := I) (n := n) e' U' hU' :=
  le_antisymm (frameTopology_le_of_cover e U hU hcover e' U' hU')
    (frameTopology_le_of_cover e' U' hU' hcover' e U hU)

/-- Restricting and changing each frame along a refinement gives a continuous comparison of
the induced topologies, even when the original frame domains do not cover the base. -/
theorem frameTopology_le_of_refinement {κ : Type*}
    (e' : κ → Trivialization F (π F V)) [∀ j, MemTrivializationAtlas (e' j)]
    (U' : κ → Opens M) (hU' : ∀ j, (U' j : Set M) ⊆ (e' j).baseSet)
    (r : κ → ι) (hr : ∀ j, U' j ≤ U (r j)) :
    frameTopology (I := I) (n := n) e U hU ≤ frameTopology (I := I) (n := n) e' U' hU' := by
  apply continuous_id_iff_le.mp
  let _ := frameTopology (I := I) (n := n) e U hU
  apply (continuous_frameTopology_iff_frameCoordinates e' U' hU').mpr
  intro j
  have hsub : (U' j : Set M) ⊆ (e (r j)).baseSet := fun x hx ↦ hU (r j) (hr j hx)
  apply (e (r j)).continuous_frameCoordinates_of_change (e' j) hsub (hU' j)
  let inc : C^n⟮I, U' j; I, U (r j)⟯ := ⟨Opens.inclusion (hr j), contMDiff_inclusion (hr j)⟩
  have h := ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp
    ((continuous_frameCoordinates e U hU (r j)).prodMk (continuous_const (y := inc)))
  convert h using 1
  funext s
  ext x
  simp only [Function.comp_apply, ContMDiffMap.comp_apply,
    Bundle.Trivialization.frameCoordinates_apply]
  rfl

/-- Restriction of native sections is continuous into the topology induced by the pulled-back
frames and the restricted frame domains. No global covering hypothesis is needed. -/
theorem continuous_restrict_frameTopology (W : Opens M) :
    let c : C(W, M) := ⟨Subtype.val, continuous_subtype_val⟩
    let _ : ContMDiffVectorBundle n F (c *ᵖ V) I :=
      ContMDiffVectorBundle.pullback F V I
        (⟨Subtype.val, contMDiff_subtype_val⟩ : C^n⟮I, W; I, M⟯)
    let eW := fun i ↦ (e i).pullback c
    let UW := fun i ↦ Opens.comap c (U i)
    let hUW : ∀ i, (UW i : Set W) ⊆ (eW i).baseSet := fun i _ hx ↦ hU i hx
    let _ := frameTopology (I := I) (n := n) e U hU
    let _ := frameTopology (I := I) (n := n) eW UW hUW
    Continuous (fun s : Cₛ^n⟮I; F, V⟯ ↦ s.restrict W) := by
  let c : C(W, M) := ⟨Subtype.val, continuous_subtype_val⟩
  let _ : ContMDiffVectorBundle n F (c *ᵖ V) I :=
    ContMDiffVectorBundle.pullback F V I
      (⟨Subtype.val, contMDiff_subtype_val⟩ : C^n⟮I, W; I, M⟯)
  let eW := fun i ↦ (e i).pullback c
  let UW := fun i ↦ Opens.comap c (U i)
  let hUW : ∀ i, (UW i : Set W) ⊆ (eW i).baseSet := fun i _ hx ↦ hU i hx
  let _ := frameTopology (I := I) (n := n) e U hU
  let _ := frameTopology (I := I) (n := n) eW UW hUW
  apply (continuous_frameTopology_iff_frameCoordinates eW UW hUW).mpr
  intro i
  let j : C^n⟮I, UW i; I, U i⟯ :=
    ⟨fun x ↦ ⟨((x : W) : M), x.2⟩,
      (TauCeti.ContMDiff.subtypeVal_comp_iff (U i) _).mp (by
        -- Normalize the composite of the two open inclusions after the target-subtype
        -- criterion; rewriting cannot identify their distinct bundled membership proofs.
        change ContMDiff I I n (fun x : UW i ↦ ((x : W) : M))
        exact (contMDiff_subtype_val (U := W)).comp
          (contMDiff_subtype_val (U := UW i)))⟩
  have h := ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp
    ((continuous_frameCoordinates e U hU i).prodMk (continuous_const (y := j)))
  apply h.congr
  intro s
  ext x
  simp only [Function.comp_apply, ContMDiffMap.comp_apply,
    Bundle.Trivialization.frameCoordinates_apply]
  erw [Bundle.Trivialization.frameCoordinates_apply,
    Bundle.Trivialization.pullback_apply, ContMDiffSection.restrict_apply]
  rfl

end ContMDiffSection

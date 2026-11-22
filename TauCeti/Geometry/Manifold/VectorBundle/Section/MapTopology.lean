/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Map
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution

/-!
# Continuous transport of supported sections and native bundle tests

A smooth fibrewise linear equivalence whose expressions in common frame domains are fixed
continuous linear maps in both directions transports fixed-support stages, their final locally
convex compact-support topologies, and native smooth bundle tests. The frames and domains are
arbitrary. Only the comparison with native bundle tests needs a covering family and a locally
compact base model. No completeness or finite-dimensionality of the fibre models is required.
-/

public noncomputable section

open Bundle Set TopologicalSpace Topology
open scoped ContDiff Manifold

namespace ContMDiffSection

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {n : ℕ∞ω}
  {V W : M → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [∀ x, TopologicalSpace (W x)]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle 𝕜 G W]
  (φ : ∀ x, V x ≃ₗ[𝕜] W x)
  (hφ : ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, G)) n
    (fun p : TotalSpace F V ↦ (⟨p.proj, φ p.proj p.snd⟩ : TotalSpace G W)))
  (hφ' : ContMDiff (I.prod 𝓘(𝕜, G)) (I.prod 𝓘(𝕜, F)) n
    (fun p : TotalSpace G W ↦ (⟨p.proj, (φ p.proj).symm p.snd⟩ : TotalSpace F V)))

/-- Fibre transport commutes with the inclusion of a fixed-compact support stage. -/
@[simp]
theorem mapCompactlySupportedEquiv_ofSupportedIn (K : Compacts M)
    (s : supportedIn I F n V K) :
    mapCompactlySupportedEquiv φ hφ hφ' (ofSupportedIn K s) =
      ofSupportedIn K (mapSupportedInEquiv φ hφ hφ' K s) := by
  apply Subtype.ext
  rw [coe_mapCompactlySupportedEquiv, ofSupportedIn_apply, ofSupportedIn_apply,
    coe_mapSupportedInEquiv]

/-- Inverse transport also commutes with the inclusion of a fixed-compact support stage. -/
theorem mapCompactlySupportedEquiv_symm_ofSupportedIn (K : Compacts M)
    (s : supportedIn I G n W K) :
    (mapCompactlySupportedEquiv φ hφ hφ').symm (ofSupportedIn K s) =
      ofSupportedIn K ((mapSupportedInEquiv φ hφ hφ' K).symm s) := by
  apply (mapCompactlySupportedEquiv φ hφ hφ').injective
  rw [LinearEquiv.apply_symm_apply, mapCompactlySupportedEquiv_ofSupportedIn,
    LinearEquiv.apply_symm_apply]

/-- Inverting the fibre equivalences inverts transport of compactly supported sections. -/
@[simp]
theorem mapCompactlySupportedEquiv_symm :
    (mapCompactlySupportedEquiv φ hφ hφ').symm =
      mapCompactlySupportedEquiv (fun x ↦ (φ x).symm) hφ'
        (by simpa only [LinearEquiv.symm_symm] using hφ) := by
  apply LinearEquiv.ext
  intro s
  apply Subtype.ext
  rw [coe_mapCompactlySupportedEquiv_symm, coe_mapCompactlySupportedEquiv]
  exact congrArg (fun l ↦ l s.val) (mapEquiv_symm φ hφ hφ')

section Frames

variable [ContMDiffVectorBundle n F V I] [ContMDiffVectorBundle n G W I] [IsManifold I n M]
  {ι : Type*} (e : ι → Trivialization F (π F V)) (d : ι → Trivialization G (π G W))
  [∀ i, MemTrivializationAtlas (e i)] [∀ i, MemTrivializationAtlas (d i)]
  (U : ι → Opens M) (he : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  (hd : ∀ i, (U i : Set M) ⊆ (d i).baseSet)
  (A : ι → F →L[𝕜] G) (B : ι → G →L[𝕜] F)
  (hA : ∀ i s (x : U i), (d i).frameCoordinates (hd i) (mapEquiv φ hφ hφ' s) x =
    A i ((e i).frameCoordinates (he i) s x))
  (hB : ∀ i s (x : U i), (e i).frameCoordinates (he i) ((mapEquiv φ hφ hφ').symm s) x =
    B i ((d i).frameCoordinates (hd i) s x))

include A hA in
/-- Fixed linear frame expressions make fibre transport continuous for the frame topologies. -/
theorem continuous_mapEquiv_frameTopology :
    let _ := frameTopology (I := I) (n := n) e U he
    let _ := frameTopology (I := I) (n := n) d U hd
    Continuous (mapEquiv φ hφ hφ') :=
  continuous_frameTopology_of_frameCoordinates_eq_clm_apply e U he d hd A hA

include B hB in
/-- The inverse frame expressions make inverse transport continuous for the frame topologies. -/
theorem continuous_mapEquiv_symm_frameTopology :
    let _ := frameTopology (I := I) (n := n) e U he
    let _ := frameTopology (I := I) (n := n) d U hd
    Continuous (mapEquiv φ hφ hφ').symm :=
  continuous_frameTopology_of_frameCoordinates_eq_clm_apply d U hd e he B hB

include A B hA hB in
/-- Smooth fibre transport as a continuous linear equivalence on any support stage, computed in
arbitrary common frame domains. No covering assumption on the domains is required. -/
def mapSupportedInCLE (K : Set M) :
    let _ := frameTopology (I := I) (n := n) e U he
    let _ := frameTopology (I := I) (n := n) d U hd
    supportedIn I F n V K ≃L[𝕜] supportedIn I G n W K := by
  let _ := frameTopology (I := I) (n := n) e U he
  let _ := frameTopology (I := I) (n := n) d U hd
  refine ContinuousLinearEquiv.mk (mapSupportedInEquiv φ hφ hφ' K) ?_ ?_
  · apply continuous_induced_rng.2
    exact ((continuous_mapEquiv_frameTopology φ hφ hφ' e d U he hd A hA).comp
      continuous_subtypeVal).congr fun s ↦ (coe_mapSupportedInEquiv φ hφ hφ' K s).symm
  · apply continuous_induced_rng.2
    exact ((continuous_mapEquiv_symm_frameTopology φ hφ hφ' e d U he hd B hB).comp
      continuous_subtypeVal).congr fun s ↦ (coe_mapSupportedInEquiv_symm φ hφ hφ' K s).symm

/-- The support-stage continuous equivalence has exactly the existing algebraic transport. -/
@[simp]
theorem mapSupportedInCLE_toLinearEquiv (K : Set M) :
    let _ := frameTopology (I := I) (n := n) e U he
    let _ := frameTopology (I := I) (n := n) d U hd
    (mapSupportedInCLE φ hφ hφ' e d U he hd A B hA hB K).toLinearEquiv =
      mapSupportedInEquiv φ hφ hφ' K := by
  unfold mapSupportedInCLE
  rfl

/-- Forward evaluation of continuous support-stage transport is the original fibre map. -/
@[simp]
theorem mapSupportedInCLE_apply (K : Set M) (s : supportedIn I F n V K) (x : M) :
    let _ := frameTopology (I := I) (n := n) e U he
    let _ := frameTopology (I := I) (n := n) d U hd
    (mapSupportedInCLE φ hφ hφ' e d U he hd A B hA hB K s).val x = φ x (s.val x) := by
  let _ := frameTopology (I := I) (n := n) e U he
  let _ := frameTopology (I := I) (n := n) d U hd
  simpa only [mapSupportedInCLE, ContinuousLinearEquiv.coe_mk, mapEquiv_apply] using
    congrFun (congrArg DFunLike.coe (coe_mapSupportedInEquiv φ hφ hφ' K s)) x

/-- Inverse evaluation of continuous support-stage transport is the inverse fibre map. -/
@[simp]
theorem mapSupportedInCLE_symm_apply (K : Set M) (s : supportedIn I G n W K) (x : M) :
    let _ := frameTopology (I := I) (n := n) e U he
    let _ := frameTopology (I := I) (n := n) d U hd
    ((mapSupportedInCLE φ hφ hφ' e d U he hd A B hA hB K).symm s).val x = (φ x).symm (s.val x) := by
  let _ := frameTopology (I := I) (n := n) e U he
  let _ := frameTopology (I := I) (n := n) d U hd
  have h := mapSupportedInCLE_toLinearEquiv φ hφ hφ' e d U he hd A B hA hB K
  rw [← ContinuousLinearEquiv.coe_symm_toLinearEquiv, h]
  simpa only [mapEquiv_symm, mapEquiv_apply] using
    congrFun (congrArg DFunLike.coe (coe_mapSupportedInEquiv_symm φ hφ hφ' K s)) x

end Frames
end ContMDiffSection


namespace ContMDiffSection

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {n : ℕ∞ω} {V W : M → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle ℝ G W]
  [ContMDiffVectorBundle n F V I] [ContMDiffVectorBundle n G W I] [IsManifold I n M]
  (φ : ∀ x, V x ≃ₗ[ℝ] W x)
  (hφ : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, G)) n
    (fun p : TotalSpace F V ↦ (⟨p.proj, φ p.proj p.snd⟩ : TotalSpace G W)))
  (hφ' : ContMDiff (I.prod 𝓘(ℝ, G)) (I.prod 𝓘(ℝ, F)) n
    (fun p : TotalSpace G W ↦ (⟨p.proj, (φ p.proj).symm p.snd⟩ : TotalSpace F V)))
  {ι : Type*} (e : ι → Trivialization F (π F V)) (d : ι → Trivialization G (π G W))
  [∀ i, MemTrivializationAtlas (e i)] [∀ i, MemTrivializationAtlas (d i)]
  (U : ι → Opens M) (he : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  (hd : ∀ i, (U i : Set M) ⊆ (d i).baseSet)
  (A : ι → F →L[ℝ] G) (B : ι → G →L[ℝ] F)
  (hA : ∀ i s (x : U i), (d i).frameCoordinates (hd i) (mapEquiv φ hφ hφ' s) x =
    A i ((e i).frameCoordinates (he i) s x))
  (hB : ∀ i s (x : U i), (e i).frameCoordinates (he i) ((mapEquiv φ hφ hφ').symm s) x =
    B i ((d i).frameCoordinates (hd i) s x))

include A hA in
/-- Fixed linear expressions in common frames make compact-support transport continuous for the
existing final locally convex topologies. This follows from continuity on every compact stage. -/
theorem continuous_mapCompactlySupportedEquiv :
    let _ := compactlySupportedTopology (I := I) (n := n) e U he
    let _ := compactlySupportedTopology (I := I) (n := n) d U hd
    Continuous (mapCompactlySupportedEquiv φ hφ hφ') := by
  let _ := frameTopology (I := I) (n := n) e U he
  let _ := frameTopology (I := I) (n := n) d U hd
  let _ := compactlySupportedTopology (I := I) (n := n) e U he
  let _ := compactlySupportedTopology (I := I) (n := n) d U hd
  let _ := isTopologicalAddGroup_compactlySupportedTopology (I := I) (n := n) d U hd
  let _ := continuousSMul_compactlySupportedTopology (I := I) (n := n) d U hd
  let _ := locallyConvexSpace_compactlySupportedTopology (I := I) (n := n) d U hd
  apply (continuous_compactlySupportedTopology_iff e U he
    (mapCompactlySupportedEquiv φ hφ hφ').toLinearMap).2
  intro K
  have hc : Continuous (mapSupportedInEquiv φ hφ hφ' (K : Set M)) :=
    continuous_induced_rng.2 <|
      ((continuous_mapEquiv_frameTopology φ hφ hφ' e d U he hd A hA).comp
        continuous_subtypeVal).congr fun s ↦ (coe_mapSupportedInEquiv φ hφ hφ' K s).symm
  exact ((continuous_ofSupportedIn (I := I) (n := n) d U hd K).comp hc).congr fun s ↦
    (mapCompactlySupportedEquiv_ofSupportedIn φ hφ hφ' K s).symm

include B hB in
/-- The inverse fixed frame expressions give continuous inverse compact-support transport. -/
theorem continuous_mapCompactlySupportedEquiv_symm :
    let _ := compactlySupportedTopology (I := I) (n := n) e U he
    let _ := compactlySupportedTopology (I := I) (n := n) d U hd
    Continuous (mapCompactlySupportedEquiv φ hφ hφ').symm := by
  rw [mapCompactlySupportedEquiv_symm]
  apply continuous_mapCompactlySupportedEquiv (fun x ↦ (φ x).symm) hφ'
    (by simpa only [LinearEquiv.symm_symm] using hφ) d e U hd he B
  intro i s x
  simpa only [mapEquiv_symm] using hB i s x

include A B hA hB in
/-- Fibre transport as a continuous linear equivalence for the existing final locally convex
compact-support topologies, in arbitrary common frame domains and at every order. -/
def mapCompactlySupportedCLE :
    let _ := compactlySupportedTopology (I := I) (n := n) e U he
    let _ := compactlySupportedTopology (I := I) (n := n) d U hd
    compactlySupported I F n V ≃L[ℝ] compactlySupported I G n W := by
  let _ := compactlySupportedTopology (I := I) (n := n) e U he
  let _ := compactlySupportedTopology (I := I) (n := n) d U hd
  exact ContinuousLinearEquiv.mk (mapCompactlySupportedEquiv φ hφ hφ')
    (continuous_mapCompactlySupportedEquiv φ hφ hφ' e d U he hd A hA)
    (continuous_mapCompactlySupportedEquiv_symm φ hφ hφ' e d U he hd B hB)

/-- The continuous compact-support equivalence has exactly the original algebraic transport. -/
@[simp]
theorem mapCompactlySupportedCLE_toLinearEquiv :
    let _ := compactlySupportedTopology (I := I) (n := n) e U he
    let _ := compactlySupportedTopology (I := I) (n := n) d U hd
    (mapCompactlySupportedCLE φ hφ hφ' e d U he hd A B hA hB).toLinearEquiv =
      mapCompactlySupportedEquiv φ hφ hφ' := by
  unfold mapCompactlySupportedCLE
  rfl

/-- Forward compact-support evaluation is the original fibrewise linear equivalence. -/
@[simp]
theorem mapCompactlySupportedCLE_apply (s : compactlySupported I F n V) (x : M) :
    let _ := compactlySupportedTopology (I := I) (n := n) e U he
    let _ := compactlySupportedTopology (I := I) (n := n) d U hd
    (mapCompactlySupportedCLE φ hφ hφ' e d U he hd A B hA hB s).val x = φ x (s.val x) := by
  let _ := compactlySupportedTopology (I := I) (n := n) e U he
  let _ := compactlySupportedTopology (I := I) (n := n) d U hd
  simpa only [mapCompactlySupportedCLE, ContinuousLinearEquiv.coe_mk, mapEquiv_apply] using
    congrFun (congrArg DFunLike.coe (coe_mapCompactlySupportedEquiv φ hφ hφ' s)) x

/-- Inverse compact-support evaluation is the original inverse fibrewise equivalence. -/
@[simp]
theorem mapCompactlySupportedCLE_symm_apply (s : compactlySupported I G n W) (x : M) :
    let _ := compactlySupportedTopology (I := I) (n := n) e U he
    let _ := compactlySupportedTopology (I := I) (n := n) d U hd
    ((mapCompactlySupportedCLE φ hφ hφ' e d U he hd A B hA hB).symm s).val x =
      (φ x).symm (s.val x) := by
  let _ := compactlySupportedTopology (I := I) (n := n) e U he
  let _ := compactlySupportedTopology (I := I) (n := n) d U hd
  have h := mapCompactlySupportedCLE_toLinearEquiv φ hφ hφ' e d U he hd A B hA hB
  rw [← ContinuousLinearEquiv.coe_symm_toLinearEquiv, h]
  simpa only [mapEquiv_symm, mapEquiv_apply] using
    congrFun (congrArg DFunLike.coe (coe_mapCompactlySupportedEquiv_symm φ hφ hφ' s)) x

/-- Continuous compact transport commutes with the existing fixed-compact stage inclusion. -/
@[simp]
theorem mapCompactlySupportedCLE_ofSupportedIn (K : Compacts M)
    (s : supportedIn I F n V K) :
    let _ := frameTopology (I := I) (n := n) e U he
    let _ := frameTopology (I := I) (n := n) d U hd
    let _ := compactlySupportedTopology (I := I) (n := n) e U he
    let _ := compactlySupportedTopology (I := I) (n := n) d U hd
    mapCompactlySupportedCLE φ hφ hφ' e d U he hd A B hA hB (ofSupportedIn K s) =
      ofSupportedIn K (mapSupportedInCLE φ hφ hφ' e d U he hd A B hA hB K s) := by
  let _ := frameTopology (I := I) (n := n) e U he
  let _ := frameTopology (I := I) (n := n) d U hd
  let _ := compactlySupportedTopology (I := I) (n := n) e U he
  let _ := compactlySupportedTopology (I := I) (n := n) d U hd
  simpa only [mapCompactlySupportedCLE, mapSupportedInCLE, ContinuousLinearEquiv.coe_mk] using
    mapCompactlySupportedEquiv_ofSupportedIn φ hφ hφ' K s

end ContMDiffSection


namespace TauCeti.BundleTest

open ContMDiffSection

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [LocallyCompactSpace E] [IsManifold I ∞ M]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {V W : M → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle ℝ G W]
  [ContMDiffVectorBundle ∞ F V I] [ContMDiffVectorBundle ∞ G W I]
  {ι : Type*} (e : ι → Trivialization F (π F V)) (d : ι → Trivialization G (π G W))
  [∀ i, MemTrivializationAtlas (e i)] [∀ i, MemTrivializationAtlas (d i)]
  (U : ι → Opens M) (he : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  (hd : ∀ i, (U i : Set M) ⊆ (d i).baseSet)
  (hcover : ∀ x : M, ∃ i, x ∈ U i)

/-- The existing algebraic wrapper from compactly supported sections to native bundle tests is a
continuous linear equivalence for any covering smooth atlas's final locally convex topology. -/
def ofCompactlySupportedCLE :
    let _ := compactlySupportedTopology (I := I) (n := ∞) e U he
    compactlySupported I F ∞ V ≃L[ℝ] BundleTest I F V := by
  let _ := compactlySupportedTopology (I := I) (n := ∞) e U he
  have ht := instTopologicalSpace_eq_compactlySupportedTopology (I := I) e U he hcover
  refine ContinuousLinearEquiv.mk (ofCompactlySupported I F V) ?_ ?_
  -- The native wrapper is the identity linear equivalence on the existing type synonym.
  -- Once the public topology comparison is rewritten, both continuity goals are continuity of id.
  · rw [ht]
    exact @continuous_id (compactlySupported I F ∞ V)
      (compactlySupportedTopology (I := I) (n := ∞) e U he)
  · rw [ht]
    exact @continuous_id (compactlySupported I F ∞ V)
      (compactlySupportedTopology (I := I) (n := ∞) e U he)

/-- The continuous native wrapper retains exactly the original algebraic wrapper. -/
@[simp]
theorem ofCompactlySupportedCLE_toLinearEquiv :
    let _ := compactlySupportedTopology (I := I) (n := ∞) e U he
    (ofCompactlySupportedCLE e U he hcover).toLinearEquiv = ofCompactlySupported I F V := by
  unfold ofCompactlySupportedCLE
  rfl

/-- Passing through the continuous native wrapper preserves every fibre value. -/
@[simp]
theorem ofCompactlySupportedCLE_apply (s : compactlySupported I F ∞ V) (x : M) :
    let _ := compactlySupportedTopology (I := I) (n := ∞) e U he
    ofCompactlySupportedCLE e U he hcover s x = s.val x := by
  simpa only [ofCompactlySupportedCLE, ContinuousLinearEquiv.coe_mk] using
    congrFun (coe_ofCompactlySupported s) x

/-- The inverse continuous native wrapper also preserves every fibre value. -/
@[simp]
theorem ofCompactlySupportedCLE_symm_apply (s : BundleTest I F V) (x : M) :
    let _ := compactlySupportedTopology (I := I) (n := ∞) e U he
    ((ofCompactlySupportedCLE e U he hcover).symm s).val x = s x := by
  let _ := compactlySupportedTopology (I := I) (n := ∞) e U he
  -- Native test evaluation is evaluation after the inverse original algebraic wrapper.
  rw [← ContinuousLinearEquiv.coe_symm_toLinearEquiv, ofCompactlySupportedCLE_toLinearEquiv]

variable (φ : ∀ x, V x ≃ₗ[ℝ] W x)
  (hφ : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, G)) ∞
    (fun p : TotalSpace F V ↦ (⟨p.proj, φ p.proj p.snd⟩ : TotalSpace G W)))
  (hφ' : ContMDiff (I.prod 𝓘(ℝ, G)) (I.prod 𝓘(ℝ, F)) ∞
    (fun p : TotalSpace G W ↦ (⟨p.proj, (φ p.proj).symm p.snd⟩ : TotalSpace F V)))
  (A : ι → F →L[ℝ] G) (B : ι → G →L[ℝ] F)
  (hA : ∀ i s (x : U i), (d i).frameCoordinates (hd i) (mapEquiv φ hφ hφ' s) x =
    A i ((e i).frameCoordinates (he i) s x))
  (hB : ∀ i s (x : U i), (e i).frameCoordinates (he i) ((mapEquiv φ hφ hφ').symm s) x =
    B i ((d i).frameCoordinates (hd i) s x))

include A B hA hB in
/-- Smooth fibre transport with fixed continuous linear frame expressions in both directions is a
real continuous linear equivalence on the existing native bundle-test spaces. -/
def mapCLE : BundleTest I F V ≃L[ℝ] BundleTest I G W := by
  let _ := compactlySupportedTopology (I := I) (n := ∞) e U he
  let _ := compactlySupportedTopology (I := I) (n := ∞) d U hd
  exact ((ofCompactlySupportedCLE (I := I) e U he hcover).symm.trans
    (mapCompactlySupportedCLE (I := I) (n := ∞) φ hφ hφ' e d U he hd A B hA hB)).trans
      (ofCompactlySupportedCLE (I := I) d U hd hcover)

/-- Native transport retains the original algebraic maps and the original carrier wrappers. -/
@[simp]
theorem mapCLE_toLinearEquiv :
    (mapCLE e d U he hd hcover φ hφ hφ' A B hA hB).toLinearEquiv =
      (((ofCompactlySupported I F V).symm.trans (mapCompactlySupportedEquiv φ hφ hφ')).trans
        (ofCompactlySupported I G W)) := by
  simp only [mapCLE, ContinuousLinearEquiv.trans_toLinearEquiv,
    ContinuousLinearEquiv.toLinearEquiv_symm, ofCompactlySupportedCLE_toLinearEquiv,
    mapCompactlySupportedCLE_toLinearEquiv]

/-- Native transport evaluates by the given fibrewise linear equivalence. -/
@[simp]
theorem mapCLE_apply (s : BundleTest I F V) (x : M) :
    mapCLE e d U he hd hcover φ hφ hφ' A B hA hB s x = φ x (s x) := by
  simp only [mapCLE, ContinuousLinearEquiv.trans_apply, ofCompactlySupportedCLE_apply,
    mapCompactlySupportedCLE_apply, ofCompactlySupportedCLE_symm_apply]

/-- Inverse native transport evaluates by the inverse fibrewise linear equivalence. -/
@[simp]
theorem mapCLE_symm_apply (s : BundleTest I G W) (x : M) :
    (mapCLE e d U he hd hcover φ hφ hφ' A B hA hB).symm s x = (φ x).symm (s x) := by
  simp only [mapCLE, ContinuousLinearEquiv.symm_trans_apply, ofCompactlySupportedCLE_apply,
    ContinuousLinearEquiv.symm_symm, mapCompactlySupportedCLE_symm_apply,
    ofCompactlySupportedCLE_symm_apply]

/-- Native fibrewise equivalence transport preserves closed support exactly. -/
theorem tsupport_mapCLE (s : BundleTest I F V) :
    closure {x | mapCLE e d U he hd hcover φ hφ hφ' A B hA hB s x ≠ 0} =
      closure {x | s x ≠ 0} := by
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, mapCLE_apply, LinearEquiv.map_ne_zero_iff]

end TauCeti.BundleTest

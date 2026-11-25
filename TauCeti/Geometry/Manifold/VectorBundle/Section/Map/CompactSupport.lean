/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Map.Topology
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution

/-!
# Continuous transport of compactly supported sections and native bundle tests

A smooth fibrewise linear equivalence whose expressions in common frame domains are fixed
continuous linear maps in both directions is continuous on every fixed-support stage
(`ContMDiffSection.mapSupportedInCLE`). It therefore transports the final locally convex
compact-support topologies (`ContMDiffSection.mapCompactlySupportedCLE`) and native smooth bundle
tests (`TauCeti.BundleTest.mapCLE`). The frames and domains are arbitrary. Only the comparison
with native bundle tests needs a covering family and a locally compact base model. No
completeness or finite-dimensionality of the fibre models is required.
-/

public noncomputable section

open Bundle Set TopologicalSpace Topology
open scoped ContDiff Manifold

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
existing final locally convex topologies. -/
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
  exact ((continuous_ofSupportedIn (I := I) (n := n) d U hd K).comp
    (continuous_mapSupportedInEquiv φ hφ hφ' e d U he hd A hA K)).congr fun s ↦
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
  rw [← ContinuousLinearEquiv.coe_toLinearEquiv, mapCompactlySupportedCLE_toLinearEquiv,
    ← ContinuousLinearEquiv.coe_toLinearEquiv, mapSupportedInCLE_toLinearEquiv]
  exact mapCompactlySupportedEquiv_ofSupportedIn φ hφ hφ' K s

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

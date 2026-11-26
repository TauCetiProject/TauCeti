/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Map.Basic
import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
import TauCeti.Geometry.Manifold.ContMDiffMap.CLMApply
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Prod
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Comp
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Restriction
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Continuity of smooth fibrewise operations on sections

A family of fibre maps `ϕ x : V x → W x` over the identity of the base, smooth as a map of
total spaces, acts on smooth sections by `s ↦ (x ↦ ϕ x (s x))` (`ContMDiffSection.map`). The
fibre maps need not be linear: pointwise polynomial operations on sections of endomorphism
bundles, such as `J ↦ J ∘ J` or `J ↦ J ∘ J₀ ∘ J`, are of this form.

This action is continuous for the compact derivative topologies on sections
(`ContMDiffSection.continuous_map_frameTopology`), for any covering frame system of the source
bundle and any frame system of the target bundle. The source model of the base is locally
compact, as for finite-dimensional manifolds; the fibres may be infinite-dimensional.

On the overlap of a source frame domain with a target frame domain, the target coefficients of
the image section are a fixed smooth map of the base point and the source coefficients. Pairing
(`ContMDiffMap.continuous_prodMk_manifoldWeakWhitney`), composition
(`ContMDiffMap.continuous_comp_manifoldWeakWhitney`) and postcomposition with a fixed map
(`ContMDiffMap.continuous_postcomp_manifoldWeakWhitney`) are continuous in the weak Whitney
topology, and continuity is local on the target frame domain
(`ContMDiffMap.continuous_of_forall_continuous_restrict`).

A smooth fibrewise linear equivalence whose expressions in common frame domains are smooth
families of continuous linear maps in both directions is a homeomorphism for the frame topologies,
with no covering or local compactness assumption. It is therefore a continuous linear equivalence
on every fixed-support stage (`ContMDiffSection.mapSupportedInCLE`).

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1, for continuity of composition
  in the compact-open `C^∞` topology.
-/

public noncomputable section

open Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {n : ℕ∞ω}
  {V W : M → Type*}
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]
  [∀ x, TopologicalSpace (W x)]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W]

variable (ϕ : ∀ x, V x → W x)
  (hϕ : ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, G)) n
    (fun p : TotalSpace F V ↦ (⟨p.proj, ϕ p.proj p.snd⟩ : TotalSpace G W)))

variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [VectorBundle 𝕜 G W]
  [ContMDiffVectorBundle n F V I] [ContMDiffVectorBundle n G W I] [IsManifold I n M]
  [LocallyCompactSpace E]
  {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  {κ : Type*} (e' : κ → Trivialization G (π G W)) [∀ j, MemTrivializationAtlas (e' j)]
  (U' : κ → Opens M) (hU' : ∀ j, (U' j : Set M) ⊆ (e' j).baseSet)

/-- A smooth family of fibre maps acts continuously on sections for the compact derivative
topologies, given a covering frame system of the source bundle and any frame system of the
target bundle. -/
theorem continuous_map_frameTopology (hcover : ∀ x : M, ∃ i, x ∈ U i) :
    let _ := frameTopology (I := I) (n := n) e U hU
    let _ := frameTopology (I := I) (n := n) e' U' hU'
    Continuous (ContMDiffSection.map ϕ hϕ) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  let _ := frameTopology (I := I) (n := n) e' U' hU'
  apply (continuous_frameTopology_iff_frameCoordinates e' U' hU').mpr
  intro j
  -- Continuity is local on the target frame domain; cover it by the source frame domains.
  let D (i : ι) : Opens (U' j) := Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ (U i)
  apply ContMDiffMap.continuous_of_forall_continuous_restrict D fun x ↦ hcover x
  intro i
  have hval : ContMDiff I I n (fun y : D i ↦ ((y : U' j) : M)) :=
    (contMDiff_subtypeVal (U := U' j)).comp (contMDiff_subtypeVal (U := D i))
  let incl : C^n⟮I, D i; I, U i⟯ :=
    ⟨fun x ↦ ⟨((x : U' j) : M), x.property⟩,
      (TauCeti.ContMDiff.subtypeVal_comp_iff (U i) _).mp hval⟩
  -- On the overlap, target coefficients are a fixed smooth map of the point and the source
  -- coefficients.
  let σ : D i × F → TotalSpace F V := fun p ↦ ⟨((p.1 : U' j) : M), (e i).symm _ p.2⟩
  have hσ : ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F)) n σ := by
    convert (e i).contMDiffOn_symm.comp_contMDiff (hval.prodMap contMDiff_id)
      (fun p ↦ (e i).mem_target.mpr (hU i p.1.property)) using 1
    exact funext fun p ↦ (e i).mk_symm (hU i p.1.property) p.2
  let g : C^n⟮I.prod 𝓘(𝕜, F), D i × F; 𝓘(𝕜, G), G⟯ :=
    ⟨fun p ↦ ((e' j) ⟨((p.1 : U' j) : M), ϕ _ ((e i).symm _ p.2)⟩).2, fun p ↦
      (((e' j).contMDiffAt_iff ((e' j).mem_source.mpr (hU' j (p.1 : U' j).property))).mp
        ((hϕ.comp hσ) p)).2⟩
  have hc : Continuous (fun s : Cₛ^n⟮I; F, V⟯ ↦
      g.comp (ContMDiffMap.id.prodMk (((e i).frameCoordinates (hU i) s).comp incl))) :=
    (ContMDiffMap.continuous_postcomp_manifoldWeakWhitney g).comp
      (ContMDiffMap.continuous_prodMk_manifoldWeakWhitney.comp (continuous_const.prodMk
        (ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp
          ((continuous_frameCoordinates e U hU i).prodMk continuous_const))))
  -- The bundled maps evaluate by their defining formulas.
  have hg (p : D i × F) : g p = ((e' j) ⟨((p.1 : U' j) : M), ϕ _ ((e i).symm _ p.2)⟩).2 := rfl
  have hincl (x : D i) : incl x = ⟨((x : U' j) : M), x.property⟩ := rfl
  refine hc.congr fun s ↦ ?_
  ext x
  simp only [ContMDiffMap.restrict_apply, ContMDiffMap.comp_apply, ContMDiffMap.prodMk_apply,
    ContMDiffMap.id_apply, Bundle.Trivialization.frameCoordinates_apply, map_apply, hg, hincl]
  have hx : ((x : U' j) : M) ∈ (e i).baseSet := hU i x.property
  rw [(e i).symm_apply_apply_mk hx]

end ContMDiffSection

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
  [ContMDiffVectorBundle n F V I] [ContMDiffVectorBundle n G W I] [IsManifold I n M]
  {ι : Type*} (e : ι → Trivialization F (π F V)) (d : ι → Trivialization G (π G W))
  [∀ i, MemTrivializationAtlas (e i)] [∀ i, MemTrivializationAtlas (d i)]
  (U : ι → Opens M) (he : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  (hd : ∀ i, (U i : Set M) ⊆ (d i).baseSet)
  (A : ∀ i, C^n⟮I, U i; 𝓘(𝕜, F →L[𝕜] G), F →L[𝕜] G⟯)
  (B : ∀ i, C^n⟮I, U i; 𝓘(𝕜, G →L[𝕜] F), G →L[𝕜] F⟯)
  (hA : ∀ i s (x : U i), (d i).frameCoordinates (hd i) (mapEquiv φ hφ hφ' s) x =
    A i x ((e i).frameCoordinates (he i) s x))
  (hB : ∀ i s (x : U i), (e i).frameCoordinates (he i) ((mapEquiv φ hφ hφ').symm s) x =
    B i x ((d i).frameCoordinates (hd i) s x))

include A hA in
/-- Smooth linear frame expressions make fibre transport continuous for the frame topologies.
Unlike `continuous_map_frameTopology`, the frame domains need not cover the base. -/
theorem continuous_mapEquiv_frameTopology :
    let _ := frameTopology (I := I) (n := n) e U he
    let _ := frameTopology (I := I) (n := n) d U hd
    Continuous (mapEquiv φ hφ hφ') :=
  continuous_frameTopology_of_frameCoordinates_eq_clmApplyLinearMap e U he d hd A fun i s ↦
    ContMDiffMap.ext fun x ↦ by
      rw [ContMDiffMap.clmApplyLinearMap_apply]
      exact hA i s x

include B hB in
/-- The inverse frame expressions make inverse transport continuous for the frame topologies. -/
theorem continuous_mapEquiv_symm_frameTopology :
    let _ := frameTopology (I := I) (n := n) e U he
    let _ := frameTopology (I := I) (n := n) d U hd
    Continuous (mapEquiv φ hφ hφ').symm :=
  continuous_frameTopology_of_frameCoordinates_eq_clmApplyLinearMap d U hd e he B fun i s ↦
    ContMDiffMap.ext fun x ↦ by
      rw [ContMDiffMap.clmApplyLinearMap_apply]
      exact hB i s x

include A hA in
/-- Smooth linear frame expressions make fibre transport continuous on every support stage, for
the subspace topologies of the frame topologies. -/
theorem continuous_mapSupportedInEquiv (K : Set M) :
    let _ := frameTopology (I := I) (n := n) e U he
    let _ := frameTopology (I := I) (n := n) d U hd
    Continuous (mapSupportedInEquiv φ hφ hφ' K) := by
  let _ := frameTopology (I := I) (n := n) e U he
  let _ := frameTopology (I := I) (n := n) d U hd
  exact continuous_induced_rng.2 <|
    ((continuous_mapEquiv_frameTopology φ hφ hφ' e d U he hd A hA).comp
      continuous_subtypeVal).congr fun s ↦ (coe_mapSupportedInEquiv φ hφ hφ' K s).symm

include A B hA hB in
/-- Smooth fibre transport as a continuous linear equivalence on any support stage, computed in
arbitrary common frame domains. No covering assumption on the domains is required. -/
def mapSupportedInCLE (K : Set M) :
    let _ := frameTopology (I := I) (n := n) e U he
    let _ := frameTopology (I := I) (n := n) d U hd
    supportedIn I F n V K ≃L[𝕜] supportedIn I G n W K := by
  let _ := frameTopology (I := I) (n := n) e U he
  let _ := frameTopology (I := I) (n := n) d U hd
  refine ContinuousLinearEquiv.mk (mapSupportedInEquiv φ hφ hφ' K)
    (continuous_mapSupportedInEquiv φ hφ hφ' e d U he hd A hA K) ?_
  apply continuous_induced_rng.2
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

end ContMDiffSection

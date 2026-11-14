/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Sphere
public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar

/-!
# Irreducible manifold predicate

This file packages the tame sphere-bounds-a-ball condition used as the irreducibility
hypothesis for Haken 3-manifolds. The disk and its boundary are Mathlib's standard `𝔻 3`
and `𝕊 2` objects, so the predicate quantifies over closed locally flat embedded spheres
and embedded balls extending them.

## Main definitions

* `TauCeti.IsSphereBoundsBall`: every closed locally flat embedded 2-sphere bounds an embedded
  3-ball.

## Main results

* `TauCeti.isSphereBoundsBall_iff`: the defining characterization of `IsSphereBoundsBall`.
* `Homeomorph.isSphereBoundsBall` and `Homeomorph.isSphereBoundsBall_iff`: homeomorphism
  invariance of `IsSphereBoundsBall`, across arbitrary universes.
-/

public section

open Set Topology

open scoped TopCat

namespace TauCeti

universe u

/-- A space satisfies the sphere-bounds-a-ball condition when every closed locally flat embedded
2-sphere extends across an embedded 3-ball. The disk and its boundary are Mathlib's standard
`𝔻 3` and `𝕊 2` objects, so this is the usual tame condition used in irreducible 3-manifolds. -/
def IsSphereBoundsBall (M : Type u) [TopologicalSpace M] : Prop :=
  ∀ f : C((TopCat.sphere 2 : TopCat.{u}), M), IsClosedEmbedding f →
    IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ f →
    ∃ g : C((TopCat.disk 3 : TopCat.{u}), M), IsClosedEmbedding g ∧
      g.comp (TopCat.diskBoundaryInclusion 3).hom = f

/-- The sphere-bounds-a-ball condition defining `IsSphereBoundsBall`. -/
@[simp]
theorem isSphereBoundsBall_iff (M : Type u) [TopologicalSpace M] :
    IsSphereBoundsBall M ↔
      ∀ f : C((TopCat.sphere 2 : TopCat.{u}), M), IsClosedEmbedding f →
        IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ f →
        ∃ g : C((TopCat.disk 3 : TopCat.{u}), M), IsClosedEmbedding g ∧
          g.comp (TopCat.diskBoundaryInclusion 3).hom = f :=
  Iff.rfl

end TauCeti

namespace Homeomorph

universe u v

/-- A homeomorphism transports `TauCeti.IsSphereBoundsBall` from its source to its target,
including across different universes. -/
theorem isSphereBoundsBall {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (e : M ≃ₜ N) (h : TauCeti.IsSphereBoundsBall M) : TauCeti.IsSphereBoundsBall N := by
  rw [TauCeti.isSphereBoundsBall_iff] at h ⊢
  -- Re-lift the standard 2-sphere and 3-disk between universes `u` and `v`.
  let eS : (TopCat.sphere 2 : TopCat.{u}) ≃ₜ (TopCat.sphere 2 : TopCat.{v}) :=
    Homeomorph.ulift.trans Homeomorph.ulift.symm
  let eD : (TopCat.disk 3 : TopCat.{v}) ≃ₜ (TopCat.disk 3 : TopCat.{u}) :=
    Homeomorph.ulift.trans Homeomorph.ulift.symm
  intro f hf_emb hf_flat
  let fM : C((TopCat.sphere 2 : TopCat.{u}), M) :=
    ⟨e.symm ∘ f ∘ eS, by fun_prop⟩
  have hfM_emb : IsClosedEmbedding fM :=
    e.symm.isClosedEmbedding.comp (hf_emb.comp eS.isClosedEmbedding)
  have hfM_flat : TauCeti.IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ fM :=
    (hf_flat.comp_homeomorph eS).homeomorph_comp e.symm
  obtain ⟨gM, hgM_emb, hgM_bdry⟩ := h fM hfM_emb hfM_flat
  refine ⟨⟨e ∘ gM ∘ eD, by fun_prop⟩,
    e.isClosedEmbedding.comp (hgM_emb.comp eD.isClosedEmbedding), ?_⟩
  -- Neither `TopCat.diskBoundaryInclusion` nor `Homeomorph.ulift` has an evaluation lemma in
  -- Mathlib; both preserve the underlying `EuclideanSpace ℝ (Fin 3)` vector by definition.
  have hs (s : TopCat.sphere.{v} 2) : eD ((TopCat.diskBoundaryInclusion 3).hom s) =
      (TopCat.diskBoundaryInclusion 3).hom (eS.symm s) :=
    ULift.ext (Subtype.ext rfl)
  ext s
  have key : gM ((TopCat.diskBoundaryInclusion 3).hom (eS.symm s)) = fM (eS.symm s) :=
    ContinuousMap.congr_fun hgM_bdry (eS.symm s)
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Function.comp_apply, hs s, key, fM,
    Homeomorph.apply_symm_apply]
  exact congrArg f (eS.apply_symm_apply s)

/-- `TauCeti.IsSphereBoundsBall` is invariant under homeomorphism, including across universes. -/
theorem isSphereBoundsBall_iff {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (e : M ≃ₜ N) : TauCeti.IsSphereBoundsBall M ↔ TauCeti.IsSphereBoundsBall N :=
  ⟨e.isSphereBoundsBall, e.symm.isSphereBoundsBall⟩

end Homeomorph

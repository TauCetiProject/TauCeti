/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.Stein.Basic
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Biholomorphic invariance of Stein manifolds

Holomorphic maps send the holomorphic hull of a set into the hull of its image.
For a biholomorphism this inclusion is an equality, so holomorphic convexity is
preserved. Global holomorphic functions separating points transport by composition
with the inverse. The same composition transports global coordinates; the differential
of the biholomorphism identifies the two model spaces when they differ.

`Diffeomorph.isSteinManifold_iff` expresses the resulting invariance of Steinness.
A biholomorphism is represented by a complex `C¹` diffeomorphism: this supplies precisely
the holomorphic maps in both directions needed here. Neither compactness nor
finite-dimensionality of the model spaces is needed for the transport statements.
-/

public section

open Set Function
open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℂ F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- A holomorphic map sends the holomorphic hull of a set into the hull of its image. -/
theorem MDifferentiable.mapsTo_mholomorphicHull {f : M → N}
    (hf : MDifferentiable I J f) (K : Set M) :
    MapsTo f (TauCeti.mholomorphicHull I K) (TauCeti.mholomorphicHull J (f '' K)) := by
  intro x hx
  rw [TauCeti.mem_mholomorphicHull_iff] at hx ⊢
  intro g hg B hB
  exact hx (g ∘ f) (hg.comp hf) B fun y hy ↦ hB (f y) (mem_image_of_mem f hy)

namespace Diffeomorph

/-- Biholomorphisms transport holomorphic hulls exactly, for arbitrary sets. -/
@[simp]
theorem image_mholomorphicHull (e : M ≃ₘ^1⟮I, J⟯ N) (K : Set M) :
    e '' TauCeti.mholomorphicHull I K = TauCeti.mholomorphicHull J (e '' K) := by
  refine subset_antisymm ((e.mdifferentiable one_ne_zero).mapsTo_mholomorphicHull K).image_subset
    (fun y hy ↦ ?_)
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  have h := (e.symm.mdifferentiable one_ne_zero).mapsTo_mholomorphicHull (e '' K) hy
  simpa only [e.symm_image_image] using h

/-- A manifold biholomorphic to a Stein manifold is Stein, even when the model spaces differ. -/
theorem isSteinManifold (e : M ≃ₘ^1⟮I, J⟯ N) [TauCeti.IsSteinManifold I M] :
    TauCeti.IsSteinManifold J N where
  isCompact_mholomorphicHull {K} hK := by
    have h := TauCeti.IsSteinManifold.isCompact_mholomorphicHull (I := I)
      (hK.image e.symm.continuous)
    have himage := h.image e.continuous
    simpa only [e.image_mholomorphicHull, e.image_symm_image] using himage
  exists_mdifferentiable_apply_ne {x y} hxy := by
    obtain ⟨f, hf, hne⟩ := TauCeti.IsSteinManifold.exists_mdifferentiable_apply_ne
      (I := I) (e.symm.injective.ne hxy)
    exact ⟨f ∘ e.symm, hf.comp (e.symm.mdifferentiable one_ne_zero), hne⟩
  exists_mdifferentiable_injective_mfderiv y := by
    obtain ⟨f, hf, hinj⟩ := TauCeti.IsSteinManifold.exists_mdifferentiable_injective_mfderiv
      (I := I) (e.symm y)
    -- Tangent spaces are the model spaces as normed spaces. At this fixed point, the
    -- differential therefore gives the continuous linear identification of the two models.
    let A : E ≃L[ℂ] F := e.mfderivToContinuousLinearEquiv one_ne_zero (e.symm y)
    refine ⟨A ∘ f ∘ e.symm, A.mdifferentiable.comp (hf.comp
      (e.symm.mdifferentiable one_ne_zero)), ?_⟩
    apply (A.toDiffeomorph.mfderiv_diffeomorph_comp_injective_iff (by simp)).2
    exact (e.symm.mfderiv_comp_diffeomorph_injective_iff one_ne_zero).2 hinj

/-- Steinness is invariant under biholomorphisms. -/
theorem isSteinManifold_iff (e : M ≃ₘ^1⟮I, J⟯ N) :
    TauCeti.IsSteinManifold I M ↔ TauCeti.IsSteinManifold J N :=
  ⟨fun _ ↦ e.isSteinManifold, fun _ ↦ e.symm.isSteinManifold⟩

end Diffeomorph

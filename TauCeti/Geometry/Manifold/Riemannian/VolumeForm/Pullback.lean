/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm

/-!
# Pullbacks of Riemannian volume forms

Pulling the Riemannian volume form back along an orientation-preserving map whose differential
preserves tangent inner products recovers the source Riemannian volume form
(`TauCeti.mpullback_riemannianVolumeForm_of_isOrientationPreservingAt`); an orientation-reversing
map with the same inner-product property negates it
(`TauCeti.mpullback_riemannianVolumeForm_of_isOrientationReversingAt`).
-/

public section

noncomputable section

open Bundle
open scoped Manifold

namespace TauCeti

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' 1 N] [RiemannianBundle (fun x : N ↦ TangentSpace I' x)] {k : ℕ}

/-- Pulling the Riemannian volume form back along a map that preserves orientations and tangent
inner products gives the source Riemannian volume form, in every dimension `k ≥ 0`. -/
theorem mpullback_riemannianVolumeForm_of_isOrientationPreservingAt
    {E'' H'' N'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
    [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    [TopologicalSpace N''] [ChartedSpace H'' N''] [IsManifold I'' 1 N'']
    [RiemannianBundle (fun x : N'' ↦ TangentSpace I'' x)]
    {o'' : Manifold.Orientation I'' N'' (Fin k)} {o : Manifold.Orientation I' N (Fin k)}
    {Φ : N'' → N} (ho : ∀ x, Manifold.Orientation.IsOrientationPreservingAt o'' o Φ x)
    (hinner : ∀ x (v w : TangentSpace I'' x),
      Inner.inner ℝ (mfderiv I'' I' Φ x v) (mfderiv I'' I' Φ x w) = Inner.inner ℝ v w) :
    mpullback I'' I' Φ (riemannianVolumeForm o) = riemannianVolumeForm o'' := by
  funext x; ext v
  let := o''.fact_finrank_tangentSpace x; let := o.fact_finrank_tangentSpace (Φ x)
  obtain ⟨e, he, hmap⟩ := (Manifold.Orientation.isOrientationPreservingAt_iff _ _ _ _).1 (ho x)
  let L : TangentSpace I'' x ≃ₗᵢ[ℝ] TangentSpace I' (Φ x) :=
    { e.toLinearEquiv with
      norm_map' := fun u ↦ by
        have hu := hinner x u u
        rw [← he, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hu
        exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hu }
  have hL : (fun i ↦ mfderiv I'' I' Φ x (v i)) = L ∘ v :=
    funext fun i ↦ (congrArg (fun T : _ →L[ℝ] _ ↦ T (v i)) he).symm
  rw [mpullback_apply, riemannianVolumeForm_apply, riemannianVolumeForm_apply, hL,
    ← (hmap : Orientation.map (Fin k) L.toLinearEquiv _ = o.orientationAt (Φ x)),
    (o''.orientationAt x).volumeForm_map L (L ∘ v)]
  exact congrArg _ (funext fun i ↦ L.symm_apply_apply (v i))

/-- Pulling the Riemannian volume form back along an orientation-reversing map that preserves
tangent inner products negates the source Riemannian volume form, in every dimension `k ≥ 0`. -/
theorem mpullback_riemannianVolumeForm_of_isOrientationReversingAt
    {E'' H'' N'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
    [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    [TopologicalSpace N''] [ChartedSpace H'' N''] [IsManifold I'' 1 N'']
    [RiemannianBundle (fun x : N'' ↦ TangentSpace I'' x)]
    {o'' : Manifold.Orientation I'' N'' (Fin k)} {o : Manifold.Orientation I' N (Fin k)}
    {Φ : N'' → N} (ho : ∀ x, Manifold.Orientation.IsOrientationReversingAt o'' o Φ x)
    (hinner : ∀ x (v w : TangentSpace I'' x),
      Inner.inner ℝ (mfderiv I'' I' Φ x v) (mfderiv I'' I' Φ x w) = Inner.inner ℝ v w) :
    mpullback I'' I' Φ (riemannianVolumeForm o) = -riemannianVolumeForm o'' := by
  have ho' : ∀ x, Manifold.Orientation.IsOrientationPreservingAt (-o'') o Φ x := fun x ↦
    (Manifold.Orientation.isOrientationPreservingAt_neg_left o'' o Φ x).2 (ho x)
  rw [mpullback_riemannianVolumeForm_of_isOrientationPreservingAt ho' hinner,
    riemannianVolumeForm_neg]

end TauCeti

end

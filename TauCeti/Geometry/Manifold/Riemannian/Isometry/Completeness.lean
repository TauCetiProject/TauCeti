/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Exponential

/-!
# Geodesic completeness under Riemannian isometries

A smooth Riemannian isometry preserves maximal geodesic intervals, and its differential at a
point is a bijection between the tangent spaces. Consequently an isometry preserves geodesic
completeness, both at corresponding base points and globally, as well as the property that the
exponential map has its full tangent space as domain.

These statements are purely geodesic: unlike the Hopf–Rinow theorem, they need neither a metric on
the manifolds, nor their Hausdorffness, nor boundarylessness.
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.RiemannianIsometry

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [FiniteDimensional ℝ F]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

/-- A smooth Riemannian isometry preserves geodesic completeness at corresponding base points. -/
theorem isGeodesicallyCompleteAt_iff (Φ : RiemannianIsometry I J M N) (p : M) :
    IsGeodesicallyCompleteAt I M p ↔ IsGeodesicallyCompleteAt J N (Φ p) := by
  rw [isGeodesicallyCompleteAt_iff_forall_one_mem_geodesicInterval,
    isGeodesicallyCompleteAt_iff_forall_one_mem_geodesicInterval]
  constructor
  · intro h w
    obtain ⟨v, rfl⟩ := Φ.mfderiv_surjective p w
    rw [Φ.geodesicInterval_mfderiv]
    exact h v
  · intro h v
    rw [← Φ.geodesicInterval_mfderiv]
    exact h _

/-- Geodesic completeness of a Riemannian manifold is invariant under a smooth Riemannian
isometry. -/
theorem forall_isGeodesicallyCompleteAt_iff (Φ : RiemannianIsometry I J M N) :
    (∀ p : M, IsGeodesicallyCompleteAt I M p) ↔
      ∀ q : N, IsGeodesicallyCompleteAt J N q := by
  constructor
  · intro h q
    obtain ⟨p, rfl⟩ := Φ.surjective q
    exact (Φ.isGeodesicallyCompleteAt_iff p).mp (h p)
  · intro h p
    exact (Φ.isGeodesicallyCompleteAt_iff p).mpr (h (Φ p))

/-- The exponential map is defined on every tangent vector at `p` if and only if the same holds
at the corresponding point under a smooth Riemannian isometry. -/
theorem expDomain_eq_univ_iff (Φ : RiemannianIsometry I J M N) (p : M) :
    Manifold.expDomain I M p = Set.univ ↔
      Manifold.expDomain J N (Φ p) = Set.univ :=
  (Manifold.expDomain_eq_univ_iff (I := I) (M := M) (p := p)).trans <|
    (Φ.isGeodesicallyCompleteAt_iff p).trans
      (Manifold.expDomain_eq_univ_iff (I := J) (M := N) (p := Φ p)).symm

end TauCeti.RiemannianIsometry

end

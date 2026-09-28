/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.HopfRinow

/-!
# Geodesic completeness under Riemannian isometries

A smooth Riemannian isometry preserves the Riemannian distance and hence metric completeness.
The Hopf–Rinow theorem identifies metric completeness with geodesic completeness at each point.
Consequently an isometry preserves geodesic completeness, both at corresponding base points and
globally, as well as the property that the exponential map has its full tangent space as domain.

These statements require the ambient metrics to be the Riemannian metrics. They concern the
domains of exponential maps; preservation of their values requires naturality of the geodesic
equation under the isometry.
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.RiemannianIsometry

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [T2Space (TangentBundle I M)] [IsRiemannianManifold I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [MetricSpace N] [ChartedSpace H' N]
  [FiniteDimensional ℝ F] [J.Boundaryless]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  [T2Space (TangentBundle J N)] [IsRiemannianManifold J N]

/-- A smooth Riemannian isometry preserves geodesic completeness at corresponding base points. -/
theorem isGeodesicallyCompleteAt_iff (Φ : RiemannianIsometry I J M N) (p : M) :
    IsGeodesicallyCompleteAt I M p ↔ IsGeodesicallyCompleteAt J N (Φ p) :=
  (Manifold.completeSpace_iff_isGeodesicallyCompleteAt (I := I) p).symm.trans <|
    ((Φ : M ≃ᵢ N).completeSpace_iff.trans
      (Manifold.completeSpace_iff_isGeodesicallyCompleteAt (I := J) (Φ p)))

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

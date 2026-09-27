/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Examples.OpenUnitBall
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.HopfRinow
import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# Geodesic incompleteness of the real open unit ball

The Euclidean metric restricted to the open unit ball in `ℝ` is an example where every point
can be joined to the centre by a distance-realizing smooth path, but geodesics cannot all be
continued indefinitely. In fact, some initial velocity at the centre has a maximal geodesic
whose domain does not contain time `1`. This follows from the Hopf–Rinow equivalence and the
failure of metric completeness proved in `Examples.OpenUnitBall`.

This is the geodesic incompleteness half of the open-ball example in do Carmo,
*Riemannian Geometry*, Chapter 7, §2.
-/

public section

open Bundle Manifold Set
open scoped Manifold

noncomputable section

namespace TauCeti.RealOpenUnitBall

local instance : RiemannianBundle
    (fun x : realOpenUnitBall ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
  Manifold.instRiemannianBundleOpen realOpenUnitBall

local instance : IsRiemannianManifold 𝓘(ℝ, ℝ) realOpenUnitBall :=
  isRiemannianManifold

local instance : T2Space (TangentBundle 𝓘(ℝ, ℝ) realOpenUnitBall) := by
  let _ : T2Space (ModelProd ℝ ℝ) := Prod.t2Space
  let _ : T2Space (TangentBundle 𝓘(ℝ, ℝ) ℝ) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.t2Space
  exact Manifold.t2Space_tangentBundle_open realOpenUnitBall

/-- The open unit ball is not geodesically complete at its centre: an initial velocity there
has a maximal geodesic that cannot be extended to all real times. -/
theorem not_isGeodesicallyCompleteAt_center :
    ¬ Manifold.IsGeodesicallyCompleteAt 𝓘(ℝ, ℝ) realOpenUnitBall center := by
  intro h
  exact not_completeSpace
    ((Manifold.completeSpace_iff_isGeodesicallyCompleteAt (I := 𝓘(ℝ, ℝ)) center).2 h)

/-- Some maximal geodesic starting at the centre of the open unit ball is undefined at time
`1`. -/
theorem exists_velocity_one_not_mem_geodesicInterval :
    ∃ v : TangentSpace 𝓘(ℝ, ℝ) center,
      (1 : ℝ) ∉ Manifold.geodesicInterval 𝓘(ℝ, ℝ) realOpenUnitBall center v := by
  have h : Manifold.expDomain 𝓘(ℝ, ℝ) realOpenUnitBall center ≠ univ := by
    intro hu
    exact not_isGeodesicallyCompleteAt_center
      ((Manifold.expDomain_eq_univ_iff (I := 𝓘(ℝ, ℝ))).1 hu)
  obtain ⟨v, hv⟩ := (Set.ne_univ_iff_exists_notMem _).mp h
  exact ⟨v, (Manifold.mem_expDomain_iff (I := 𝓘(ℝ, ℝ))).not.mp hv⟩

end TauCeti.RealOpenUnitBall

end

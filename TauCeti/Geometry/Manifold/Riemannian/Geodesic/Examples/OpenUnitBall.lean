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
can be joined to the centre by a distance-realizing C¹ path, but geodesics cannot all be
continued indefinitely. In fact, some initial velocity at each point has a maximal geodesic
whose domain does not contain time `1`. This follows from the Hopf–Rinow equivalence and the
failure of metric completeness proved in `TauCeti.RealOpenUnitBall.not_completeSpace`.

This is the geodesic incompleteness half of the open-ball example in do Carmo,
*Riemannian Geometry*, Chapter 7, §2.
-/

public section

open Bundle Manifold Set
open scoped Manifold TauCeti

noncomputable section

namespace TauCeti.RealOpenUnitBall

/-- The open unit ball is not geodesically complete at any point: an initial velocity there
has a maximal geodesic that cannot be extended to all real times. -/
theorem not_isGeodesicallyCompleteAt (p : realOpenUnitBall) :
    ¬ Manifold.IsGeodesicallyCompleteAt 𝓘(ℝ, ℝ) realOpenUnitBall p := by
  intro h
  exact not_completeSpace
    ((Manifold.completeSpace_iff_isGeodesicallyCompleteAt (I := 𝓘(ℝ, ℝ)) p).2 h)

/-- Some maximal geodesic starting at any point of the open unit ball is undefined at time
`1`. -/
theorem exists_one_notMem_geodesicInterval (p : realOpenUnitBall) :
    ∃ v : TangentSpace 𝓘(ℝ, ℝ) p,
      (1 : ℝ) ∉ Manifold.geodesicInterval 𝓘(ℝ, ℝ) realOpenUnitBall p v := by
  exact (Manifold.not_isGeodesicallyCompleteAt_iff_exists_one_notMem_geodesicInterval
    (I := 𝓘(ℝ, ℝ)) (M := realOpenUnitBall)).mp (not_isGeodesicallyCompleteAt p)

end TauCeti.RealOpenUnitBall

end

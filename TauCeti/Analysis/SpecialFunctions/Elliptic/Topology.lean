/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.Uniformization
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Topology

/-!
# Continuity of the Weierstrass point map

The map `z ↦ (℘(z), ℘'(z)/2)`, extended to the identity at lattice points, is continuous into
the native projective points with their analytic topology. The local holomorphic homogeneous
coordinates already constructed at ordinary points and at infinity establish continuity in
both charts. In particular the junk values of the affine Weierstrass functions on the lattice
do not introduce discontinuities into the projective point map.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, VI.3.
-/

public section

open WeierstrassCurve
open scoped Topology

namespace PeriodPair

/-- The Weierstrass point map, including its extension at lattice points, is continuous in the
analytic topology on the native projective curve. -/
theorem continuous_weierstrassPoint_toProjective (L : PeriodPair) :
    Continuous (fun z ↦ (L.weierstrassPoint z).toProjective) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro z₀
  obtain ⟨P, hP, h⟩ := L.exists_analyticAt_toAffine_eq_weierstrassPoint z₀
  apply Projective.Point.continuousAt_of_eventually_eq_mk hP.continuousAt
  filter_upwards [h] with z hz
  refine ⟨hz.1, ?_⟩
  apply (Projective.Point.toAffineAddEquiv L.weierstrassCurve.toProjective).injective
  rw [Projective.Point.toAffineAddEquiv_apply, Projective.Point.toAffineLift_eq, hz.2]
  simpa only [Projective.Point.toAffineAddEquiv_symm_apply] using
    ((Projective.Point.toAffineAddEquiv L.weierstrassCurve.toProjective).apply_symm_apply
      (L.weierstrassPoint z)).symm

end PeriodPair

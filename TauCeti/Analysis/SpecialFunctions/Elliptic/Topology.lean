/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.LatticeClassification
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.TopologicalAddGroup
import TauCeti.Algebra.Module.ZLattice.Quotient

/-!
# Complex elliptic curves as topological groups

The map `z ↦ (℘(z), ℘'(z)/2)`, extended to the identity at lattice points, is continuous into
the native projective points with their analytic topology. The local holomorphic homogeneous
coordinates already constructed at ordinary points and at infinity establish continuity in
both charts. In particular the junk values of the affine Weierstrass functions on the lattice
do not introduce discontinuities into the projective point map.

The point map descends to a continuous group isomorphism from the compact torus `ℂ / Λ` to the
Hausdorff space `E_Λ(ℂ)`, which is therefore an isomorphism of topological groups. Since every
complex elliptic curve is a change of variables of some `E_Λ`, and changes of variables are
homeomorphisms, the points of every complex elliptic curve form a compact connected Hausdorff
topological group.

## Main results

* `PeriodPair.continuous_weierstrassPoint_toProjective`: the point map is continuous.
* `PeriodPair.weierstrassPointContinuousAddEquiv`: `ℂ / Λ ≃ₜ+ E_Λ(ℂ)`.
* `WeierstrassCurve.Projective.Point.instConnectedSpace`: the points of a complex elliptic curve
  form a connected space.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, VI.3 and VI.5.
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

open Classical in
/-- **Complex uniformization as topological groups**: the Weierstrass point map induces an
isomorphism of topological groups `ℂ / Λ ≃ₜ+ E_Λ(ℂ)` onto the projective points of the
Weierstrass curve of `Λ`, with their analytic topology. -/
noncomputable def weierstrassPointContinuousAddEquiv (L : PeriodPair) :
    ℂ ⧸ L.lattice.toAddSubgroup ≃ₜ+ L.weierstrassCurve.toProjective.Point :=
  let e := L.weierstrassPointEquiv.trans
    (Projective.Point.toAffineAddEquiv L.weierstrassCurve.toProjective).symm
  -- A continuous bijection from the compact torus to the Hausdorff curve is a homeomorphism.
  have hc : Continuous e := (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr <| by
    convert L.continuous_weierstrassPoint_toProjective using 1
    ext z
    simp [e, weierstrassPointEquiv_mk]
  { e with
    continuous_toFun := hc
    continuous_invFun := hc.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) }

/-- The isomorphism `ℂ / Λ ≃ₜ+ E_Λ(ℂ)` sends the class of `z` to the point
`(℘(z), ℘'(z) / 2)`, and the class of a lattice point to the point at infinity. -/
@[simp]
theorem weierstrassPointContinuousAddEquiv_mk (L : PeriodPair) (z : ℂ) :
    L.weierstrassPointContinuousAddEquiv z = (L.weierstrassPoint z).toProjective := by
  rw [weierstrassPointContinuousAddEquiv, ContinuousAddEquiv.coe_mk, AddEquiv.trans_apply,
    weierstrassPointEquiv_mk, Projective.Point.toAffineAddEquiv_symm_apply]

/-- The inverse of `ℂ / Λ ≃ₜ+ E_Λ(ℂ)` sends the point `(℘(z), ℘'(z) / 2)` to the class of `z`. -/
@[simp]
theorem weierstrassPointContinuousAddEquiv_symm_weierstrassPoint (L : PeriodPair) (z : ℂ) :
    L.weierstrassPointContinuousAddEquiv.symm (L.weierstrassPoint z).toProjective = z :=
  (ContinuousAddEquiv.symm_apply_eq _).mpr (L.weierstrassPointContinuousAddEquiv_mk z).symm

end PeriodPair

namespace WeierstrassCurve.Projective.Point

/-- **The points of a complex elliptic curve form a connected space** in their analytic
topology. -/
instance instConnectedSpace (W : Projective ℂ) [W.IsElliptic] : ConnectedSpace W.Point := by
  obtain ⟨τ, C, rfl⟩ := exists_variableChange_smul_weierstrassCurve_periodPair_eq W
  have : ConnectedSpace τ.periodPair.weierstrassCurve.toProjective.Point :=
    (τ.periodPair.weierstrassPointContinuousAddEquiv.surjective.comp
      QuotientAddGroup.mk_surjective).connectedSpace
      ((map_continuous _).comp QuotientAddGroup.continuous_mk)
  exact (continuousAddEquivVariableChange _ C).symm.surjective.connectedSpace (map_continuous _)

end WeierstrassCurve.Projective.Point

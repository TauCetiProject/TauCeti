/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapEquiv

/-!
# Galois actions on elliptic-curve points

Let `W` be a Weierstrass curve over a field `F`, and `K` an extension of `F`. An `F`-automorphism
of `K` acts on the coordinates of the points of `W` over `K`, through the transport
`WeierstrassCurve.Affine.Point.mapEquiv`. This file packages that as the Galois action on points
and, restricting to the subgroup killed by `N : ℤ`, as the action on `N`-torsion. Both actions
are bundled as monoid homomorphisms into the additive automorphism group, viewed
multiplicatively so composition has the usual action order.

For `N ≠ 0` the torsion action is the input needed to state Galois equivariance of the Weil
pairing. When `F` is finite and `K` is an algebraic extension of `F`, the `#F`-power Frobenius
is an `F`-automorphism of `K`, so the same action also supplies the point-side representation
used in the Hasse-bound argument.

## Main definitions

* `WeierstrassCurve.pointGaloisAction`: the Galois action on points.
* `WeierstrassCurve.torsionGaloisAction`: its restriction to `N`-torsion.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8 and V.1.
-/

public section

open scoped WeierstrassCurve

namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] [DecidableEq K] [Algebra F K]
  (W : WeierstrassCurve F) [W.IsElliptic]

/-- **The Galois action on the points of an elliptic curve.** An `F`-automorphism of
`K` acts by applying it to both affine coordinates and fixes the point at infinity. -/
noncomputable def pointGaloisAction :
    (K ≃ₐ[F] K) →* Multiplicative (AddAut ((W⁄K).toAffine.Point)) where
  toFun e := Multiplicative.ofAdd (Affine.Point.mapEquiv W e)
  -- In Mathlib's automorphism groups, `1` is `refl` and `e * f` is `f.trans e` by definition.
  map_one' := congrArg Multiplicative.ofAdd (Affine.Point.mapEquiv_refl W)
  map_mul' e f := congrArg Multiplicative.ofAdd (Affine.Point.mapEquiv_trans W f e)

omit [W.IsElliptic] in
/-- The Galois action of `e` on points is Mathlib's point map along `e`. -/
@[simp]
theorem pointGaloisAction_apply (e : K ≃ₐ[F] K)
    (P : (W⁄K).toAffine.Point) :
    Multiplicative.toAdd (W.pointGaloisAction e) P = Affine.Point.map e.toAlgHom P := by
  simp [pointGaloisAction]

/-- **The Galois action on `N`-torsion.** This is the restriction of
`pointGaloisAction` to the subgroup killed by `N`. -/
noncomputable def torsionGaloisAction (N : ℤ) :
    (K ≃ₐ[F] K) →*
      Multiplicative (AddAut (AddSubgroup.torsionBy ((W⁄K).toAffine.Point) N)) where
  toFun e := Multiplicative.ofAdd ((Affine.Point.mapEquiv W e).torsionByCongr N)
  -- As for `pointGaloisAction`, `1` and `e * f` unfold to `refl` and `f.trans e`.
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext P
    rw [toAdd_ofAdd, AddEquiv.torsionByCongr_apply_coe, toAdd_one, AddAut.zero_apply]
    exact DFunLike.congr_fun (Affine.Point.mapEquiv_refl W) P.1
  map_mul' e f := by
    apply Multiplicative.toAdd.injective
    ext P
    rw [toAdd_mul, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd, AddAut.add_apply,
      AddEquiv.torsionByCongr_apply_coe, AddEquiv.torsionByCongr_apply_coe,
      AddEquiv.torsionByCongr_apply_coe]
    exact DFunLike.congr_fun (Affine.Point.mapEquiv_trans W f e) P.1

omit [W.IsElliptic] in
/-- The Galois action on `N`-torsion agrees with the Galois action on points. -/
@[simp]
theorem torsionGaloisAction_apply_coe (N : ℤ) (e : K ≃ₐ[F] K)
    (P : AddSubgroup.torsionBy (W⁄K).toAffine.Point N) :
    ((Multiplicative.toAdd (W.torsionGaloisAction N e) P :
      AddSubgroup.torsionBy (W⁄K).toAffine.Point N) : (W⁄K).toAffine.Point) =
      Multiplicative.toAdd (W.pointGaloisAction e) P := by
  simp [torsionGaloisAction]

end WeierstrassCurve

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Degree
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Divisor.Class
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Finrank
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Place
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PicZero
public import TauCeti.FieldTheory.FunctionField.Divisor.Equiv

/-!
# `Pic⁰` of the projective model of an elliptic curve

Let `W` be an elliptic Weierstrass curve over a field `K` and let `E = projModel W` be its
projective model, a smooth proper curve over `K`. This file identifies the group of points
`W.toAffine.Point` of Mathlib, with its chord-and-tangent group law, with the degree-zero part
`Pic⁰ E` of the Picard group of `E`, the group of isomorphism classes of line bundles of degree
zero under tensor product (`LineBundleClass.picZero`).

The identification is assembled from three isomorphisms of groups:

* the points of `W` are the degree-zero divisor classes `Cl⁰(K(W))` of the function field of the
  affine equation, a point `P` going to the class of `(P) - (O)`
  (`WeierstrassCurve.Affine.pointEquivDegreeZeroDivisorClass`);
* the function field of `E` is `K(W)` (`WeierstrassCurve.projModelFunctionFieldEquiv`), and this
  isomorphism respects the constants, so it identifies `Cl⁰(K(E))` with `Cl⁰(K(W))`
  (`Divisor.degreeZeroClassGroupEquivOfRingEquiv`);
* on a proper curve, `Pic⁰ E ≅ Cl⁰(K(E))` (`SchemeWeilDivisor.picZeroAddEquivDegreeZeroClassGroup`).

The codimension-one points of `E` are identified with the places of `K(W)` in
`TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Place`
(`WeierstrassCurve.projModelCodimensionOnePointEquivPlace`). Through this identification the
isomorphism sends an affine point `P` to the class of the line bundle `𝒪_E(x_P - x_O)`, where
`x_P` and `x_O` are the points of `E` corresponding to the place of `P` and to the place at
infinity (`WeierstrassCurve.coe_pointAddEquivPicZero_some`).

## Main declarations

* `WeierstrassCurve.projModelPicZeroAddEquiv`: `Pic⁰ (projModel W) ≃+ Cl⁰(K(W))`;
* `WeierstrassCurve.pointAddEquivPicZero`: `W.toAffine.Point ≃+ Pic⁰ (projModel W)`.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer, 2009,
  Proposition III.3.4.
* R. Hartshorne, *Algebraic Geometry*, Chapter II, Section 6, and Chapter IV, Section 4.
-/

public section

open CategoryTheory AlgebraicGeometry TauCeti TauCeti.AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {K : Type u} [Field K] (W : WeierstrassCurve K)

-- The function field of the projective model carries two `K`-algebra structures: the one defined
-- by its structure morphism, `Scheme.functionFieldBaseAlgebra`, which the divisor theory of
-- schemes uses, and the one transported from the affine function field,
-- `projModelFunctionFieldAlgebra`. They agree
-- (`projModelFunctionFieldEquiv_baseRingToFunctionField`), but not definitionally; this file
-- works with the first one throughout.
attribute [local instance high] Scheme.functionFieldBaseAlgebra

variable [W.IsElliptic]

/-- The coordinate ring of an elliptic curve is a Dedekind domain. -/
local instance : IsDedekindDomain W.toAffine.CoordinateRing :=
  have := WeierstrassCurve.Affine.isIntegrallyClosed_coordinateRing W.toAffine
  W.toAffine.isDedekindDomain_coordinateRing_of_isIntegrallyClosed

/-- The first cohomology of the structure sheaf of the projective model of an elliptic curve is
finite-dimensional. -/
instance finiteDimensional_cohomology_one_projModel :
    FiniteDimensional K
      (Scheme.Modules.Cohomology (InvertibleSheaf.trivial W.projModel).obj 1) :=
  finiteDimensional_cohomology_one_trivial_of_isProper K (topologicalKrullDim_projModel W)

/-! ### `Pic⁰` of the projective model -/

/-- **`Pic⁰` of the projective model is the degree-zero divisor class group of `K(W)`.** It is the
composite of `Pic⁰ E ≅ Cl⁰(K(E))` with the identification of `K(E)` with `K(W)`. -/
noncomputable def projModelPicZeroAddEquiv :
    LineBundleClass.picZero K W.projModel ≃+ (Divisor.degreeClass W.toAffine.isFunctionField).ker :=
  (SchemeWeilDivisor.picZeroAddEquivDegreeZeroClassGroup K
      (isFunctionField_functionField_projModel W)).trans
    (Divisor.degreeZeroClassGroupEquivOfRingEquiv (RingEquiv.refl K)
      W.projModelFunctionFieldEquiv (projModelFunctionFieldEquiv_algebraMap W)
      (isFunctionField_functionField_projModel W) W.toAffine.isFunctionField)

/-- The inverse of `projModelPicZeroAddEquiv` sends the class of a degree-zero divisor `E` of
`K(W)` to the class of the line bundle `𝒪(D)` on `projModel W`, where `D` is the divisor on
`projModel W` with the same coefficients at corresponding points and places. -/
theorem coe_projModelPicZeroAddEquiv_symm_apply
    {c : (Divisor.degreeClass W.toAffine.isFunctionField).ker}
    {E : Divisor K W.toAffine.FunctionField}
    (hc : (c : (Place.orderSystem W.toAffine.isFunctionField).ClassGroup) =
      (Place.orderSystem W.toAffine.isFunctionField).divisorClass E) :
    ((projModelPicZeroAddEquiv W).symm c : Additive (LineBundleClass W.projModel)) =
      Additive.ofMul (SchemeWeilDivisor.toLineBundleClass Fact.out
        (Finsupp.domCongr (projModelCodimensionOnePointEquivPlace W).symm E)) := by
  rw [projModelPicZeroAddEquiv, AddEquiv.symm_trans_apply,
    SchemeWeilDivisor.coe_picZeroAddEquivDegreeZeroClassGroup_symm_apply K _
      (valuativeCriterionExistence_projModel W)
      (by rw [Divisor.coe_degreeZeroClassGroupEquivOfRingEquiv_symm_apply, hc,
        Divisor.classGroupEquivOfRingEquiv_symm_divisorClass])]
  congr 2
  refine AlgebraicGeometry.WeilDivisor.ext fun x ↦ ?_
  rw [SchemeWeilDivisor.coeff_equivFunctionFieldDivisor_symm]
  simp only [AlgebraicGeometry.WeilDivisor.coeff, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_apply, Equiv.symm_symm, projModelCodimensionOnePointEquivPlace_apply]

/-- **The points of an elliptic curve form `Pic⁰` of its projective model.** For an elliptic
curve `W` over a field `K`, the group `W.toAffine.Point` of Mathlib, with its chord-and-tangent
group law, is isomorphic to the group `Pic⁰ (projModel W)` of degree-zero line bundles on the
projective model. The point at infinity goes to the trivial bundle, and an affine point `P` to the
class of `𝒪(x_P - x_O)` (`coe_pointAddEquivPicZero_some`). -/
noncomputable def pointAddEquivPicZero [DecidableEq K] :
    W.toAffine.Point ≃+ LineBundleClass.picZero K W.projModel :=
  W.toAffine.pointEquivDegreeZeroDivisorClass.trans (projModelPicZeroAddEquiv W).symm

/-- **An affine point goes to the class of `𝒪(x_P - x_O)`.** The line bundle attached by
`pointAddEquivPicZero` to an affine point `P` is that of the divisor `x_P - x_O`, where `x_P` and
`x_O` are the codimension-one points of `projModel W` corresponding to the place of `K(W)` at `P`
and to the place at infinity. -/
theorem coe_pointAddEquivPicZero_some [DecidableEq K] {x y : K}
    (h : W.toAffine.Nonsingular x y) :
    (pointAddEquivPicZero W (.some x y h) : Additive (LineBundleClass W.projModel)) =
      Additive.ofMul (SchemeWeilDivisor.toLineBundleClass Fact.out
        (AlgebraicGeometry.WeilDivisor.ofPoint ((projModelCodimensionOnePointEquivPlace W).symm
            (Place.ofPrime K W.toAffine.FunctionField
              (Affine.CoordinateRing.pointPlace h.left))) -
          AlgebraicGeometry.WeilDivisor.ofPoint
            ((projModelCodimensionOnePointEquivPlace W).symm (Place.infinity W.toAffine)))) := by
  rw [pointAddEquivPicZero, AddEquiv.trans_apply,
    coe_projModelPicZeroAddEquiv_symm_apply W
      (W.toAffine.val_pointEquivDegreeZeroDivisorClass_some h),
    map_sub, Finsupp.domCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_eq_mapDomain,
    ← AlgebraicGeometry.WeilDivisor.pushforward_apply,
    ← AlgebraicGeometry.WeilDivisor.pushforward_apply,
    AlgebraicGeometry.WeilDivisor.pushforward_ofPoint,
    AlgebraicGeometry.WeilDivisor.pushforward_ofPoint]

end WeierstrassCurve

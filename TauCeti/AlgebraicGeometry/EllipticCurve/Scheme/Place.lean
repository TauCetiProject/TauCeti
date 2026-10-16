/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.FunctionField
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Smooth
public import TauCeti.AlgebraicGeometry.Scheme.FunctionField
public import TauCeti.AlgebraicGeometry.Scheme.Place.Proper
public import TauCeti.FieldTheory.FunctionField.Place.Equiv

/-!
# Points of the projective model and places of the function field

Let `W` be an elliptic Weierstrass curve over a field `K` and let `E = projModel W` be its
projective model, a smooth proper curve over `K`. This file shows that the function field of `E`
is an algebraic function field of one variable over `K`, and identifies the codimension-one points
of `E` with the places of the function field `K(W)` of the affine equation: a point goes to the
place whose valuation ring is its local ring, transported along
`WeierstrassCurve.projModelFunctionFieldEquiv`.

## Main declarations

* `WeierstrassCurve.isFunctionField_functionField_projModel`: `K(E)` is a function field over
  `K`;
* `WeierstrassCurve.projModelCodimensionOnePointEquivPlace`: the codimension-one points of
  `projModel W` are the places of `K(W)`;
* `WeierstrassCurve.mem_integers_projModelCodimensionOnePointEquivPlace_iff`: the valuation ring
  of the place of a point is its local ring;
* `WeierstrassCurve.degree_projModelCodimensionOnePointEquivPlace`: the degree of the place of a
  point is its residue degree.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter I, Section 6, and Chapter II, Section 6.
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

/-- The function-field comparison `projModelFunctionFieldEquiv` respects the constants, for the
algebra structure on `K(E)` defined by the structure morphism. It is stated in the form of the
compatibility hypothesis of `Place.equivOfRingEquiv` for the identity of `K`. -/
theorem projModelFunctionFieldEquiv_algebraMap (c : K) :
    W.projModelFunctionFieldEquiv (algebraMap K W.projModel.functionField c) =
      algebraMap K W.toAffine.FunctionField (RingEquiv.refl K c) := by
  rw [Scheme.algebraMap_functionField_eq_baseRingToFunctionField,
    projModelFunctionFieldEquiv_baseRingToFunctionField, RingEquiv.refl_apply]

variable [W.IsElliptic]

/-- The function field of the projective model of an elliptic curve is an algebraic function
field of one variable over the base field. -/
theorem isFunctionField_functionField_projModel :
    IsFunctionField K W.projModel.functionField :=
  (isFunctionField_functionField_iff K).mpr (topologicalKrullDim_projModel W)

/-- **The codimension-one points of the projective model are the places of `K(W)`.** A
codimension-one point of `E = projModel W` goes to the place of `K(E)` whose valuation ring is its
local ring, transported to `K(W)` along `projModelFunctionFieldEquiv`. -/
noncomputable def projModelCodimensionOnePointEquivPlace :
    CodimensionOnePoint W.projModel ≃ Place K W.toAffine.FunctionField :=
  (CodimensionOnePoint.equivPlace (valuativeCriterionExistence_projModel W) Fact.out).trans
    (Place.equivOfRingEquiv (RingEquiv.refl K) W.projModelFunctionFieldEquiv
      (projModelFunctionFieldEquiv_algebraMap W))

/-- The place attached to a codimension-one point `y` of `projModel W` is the transport along
`projModelFunctionFieldEquiv` of the place of `K(E)` at `y`. -/
theorem projModelCodimensionOnePointEquivPlace_apply (y : CodimensionOnePoint W.projModel) :
    projModelCodimensionOnePointEquivPlace W y =
      Place.equivOfRingEquiv (RingEquiv.refl K) W.projModelFunctionFieldEquiv
        (projModelFunctionFieldEquiv_algebraMap W) (W.projModel.toPlace (k := K) (y : W.projModel))
    := by
  rw [projModelCodimensionOnePointEquivPlace, Equiv.trans_apply,
    CodimensionOnePoint.equivPlace_apply]

/-- **The valuation ring of the place of a point is its local ring**: a function of `K(W)` is
integral at the place attached to a codimension-one point `y` of `projModel W` exactly when it
comes from the local ring of `projModel W` at `y`. -/
theorem mem_integers_projModelCodimensionOnePointEquivPlace_iff
    (y : CodimensionOnePoint W.projModel) (z : W.toAffine.FunctionField) :
    z ∈ (projModelCodimensionOnePointEquivPlace W y).integers ↔
      ∃ a : W.projModel.presheaf.stalk (y : W.projModel),
        W.projModelFunctionFieldEquiv
          (algebraMap (W.projModel.presheaf.stalk (y : W.projModel)) W.projModel.functionField a) =
            z := by
  rw [projModelCodimensionOnePointEquivPlace_apply, Place.mem_integers_iff,
    Place.valuation_equivOfRingEquiv, ← Place.mem_integers_iff,
    Scheme.mem_toPlace_integers_iff_exists_stalk]
  exact exists_congr fun a ↦ W.projModelFunctionFieldEquiv.eq_symm_apply

/-- The degree of the place attached to a codimension-one point of `projModel W` is the residue
degree of the point over the base field. -/
@[simp]
theorem degree_projModelCodimensionOnePointEquivPlace (y : CodimensionOnePoint W.projModel) :
    (projModelCodimensionOnePointEquivPlace W y).degree =
      (W.projModel ↘ Spec (.of K)).residueDegree (y : W.projModel) := by
  rw [projModelCodimensionOnePointEquivPlace_apply, Place.degree_equivOfRingEquiv,
    Scheme.toPlace_degree_eq_residueDegree]

end WeierstrassCurve

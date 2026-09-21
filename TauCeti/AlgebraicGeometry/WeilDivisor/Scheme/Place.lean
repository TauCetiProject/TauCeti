/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order
public import TauCeti.FieldTheory.FunctionField.AffineModel.Prime
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Places attached to codimension-one points

Let `X` be an integral scheme over a field `k`. When the local ring at a codimension-one point
`x` is a discrete valuation ring, its normalized valuation on the function field of `X` is a
place of `X.functionField / k`. This file constructs that place and identifies its order with
the scheme-theoretic order of vanishing at `x`.

The construction uses the canonical `k`-algebra structures on the function field and the stalks
of a scheme over `Spec k`, recorded in `TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra`. The place
is then `TauCeti.Place.ofPrime` for the maximal ideal of the discrete valuation ring at `x`.

This provides the local bridge used to transport divisor and differential constructions between
scheme-theoretic codimension-one points and abstract function-field places.

## Main definitions and results

* `Scheme.baseRingToFunctionField`: the canonical map from the base ring to the function field.
* `Scheme.baseRingToStalk`: the canonical map from the base ring to a stalk.
* `Scheme.toPlace`: the normalized place attached to a point with discrete valuation ring stalk.
* `CodimensionOnePoint.toPlace_ord`: its order is the scheme-theoretic order of vanishing.
* `CodimensionOnePoint.toPlace_ordAddMonoidHom`: the corresponding additive order homomorphisms
  agree.
* `Scheme.toPlaceResidueFieldAlgEquiv`: the residue field of the scheme point is
  the residue field of its place.
-/

public section

open _root_.AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (.of k))]

/-- The normalized place of the function field attached to a point with discrete valuation ring
as its stalk. -/
def toPlace (X : Scheme.{u}) (x : X)
    [IsIntegral X] [X.Over (Spec (.of k))]
    [IsDiscreteValuationRing (X.presheaf.stalk x)] : Place k X.functionField :=
  Place.ofPrime k X.functionField
    (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk x))

/-- The valuation of the place attached to `x` is the normalized valuation of the maximal ideal
of the discrete valuation ring `𝒪_{X,x}`. -/
@[simp]
lemma toPlace_valuation (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (.of k))] (x : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    (toPlace (k := k) X x).valuation =
      (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk x)).valuation X.functionField :=
  Place.valuation_ofPrime k X.functionField _

/-- A rational function is integral at the place attached to `x` exactly when it comes from the
stalk `𝒪_{X,x}`. Thus the valuation ring of `x.toPlace` is the image of the local ring in the
function field. -/
theorem mem_toPlace_integers_iff_exists_stalk (X : Scheme.{u}) [IsIntegral X]
    [X.Over (Spec (.of k))] (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (f : X.functionField) :
    f ∈ (toPlace (k := k) X x).integers ↔
      ∃ a : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField a = f := by
  rw [Place.mem_integers_iff, toPlace_valuation]
  constructor
  · exact IsDiscreteValuationRing.exists_lift_of_le_one
  · rintro ⟨a, rfl⟩
    exact (IsDiscreteValuationRing.maximalIdeal
      (X.presheaf.stalk (x : X))).valuation_le_one a

/-- The canonical inclusion of the stalk into the function field lands in the valuation ring of
the place attached to the point. -/
theorem algebraMap_stalk_mem_toPlace_integers (X : Scheme.{u}) [IsIntegral X]
    [X.Over (Spec (.of k))] (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    ∀ a : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField a ∈
      (toPlace (k := k) X x).integers := by
  simpa only [toPlace] using
    (Place.algebraMap_mem_integers_ofPrime k X.functionField
      (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk x)))

/-- The valuation ring defining the place is the valuation subring of the normalized maximal-ideal
valuation of the stalk. -/
theorem toPlace_integers (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (.of k))]
    (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    (toPlace (k := k) X x).integers =
      ((IsDiscreteValuationRing.maximalIdeal
        (X.presheaf.stalk x)).valuation X.functionField).valuationSubring := by
  ext f
  rw [Place.mem_integers_iff, toPlace_valuation, Valuation.mem_valuationSubring_iff]

/-- The stalk at a point with discrete valuation ring stalk is canonically the valuation ring of
its associated place. -/
def stalkToPlaceIntegersAlgEquiv (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (.of k))]
    (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    X.presheaf.stalk x ≃ₐ[k] (toPlace (k := k) X x).integers :=
  AlgEquiv.ofRingEquiv
    (f := (IsDiscreteValuationRing.equivValuationSubring
      (A := X.presheaf.stalk x) (K := X.functionField)).trans
        (RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
          (toPlace_integers (k := k) X x).symm))) fun c ↦
        Subtype.ext (IsScalarTower.algebraMap_apply k (X.presheaf.stalk x) X.functionField c).symm

/-- The stalk-to-valuation-ring equivalence is the canonical inclusion into the function field. -/
@[simp]
theorem coe_stalkToPlaceIntegersAlgEquiv (X : Scheme.{u}) [IsIntegral X]
    [X.Over (Spec (.of k))] (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (a : X.presheaf.stalk x) :
    ((stalkToPlaceIntegersAlgEquiv (k := k) X x a :
      (toPlace (k := k) X x).integers) : X.functionField) =
      algebraMap (X.presheaf.stalk x) X.functionField a := by
  change algebraMap (X.presheaf.stalk x) X.functionField a = _
  rfl

/-- The residue field of a codimension-one point is canonically the residue field of its place.
Both are the stalk modulo its maximal ideal; the right-hand description is the general residue
field computation for `Place.ofPrime`. -/
def toPlaceResidueFieldAlgEquiv (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (.of k))]
    (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    X.residueField x ≃ₐ[k] (toPlace (k := k) X x).ResidueField :=
  Place.quotientAlgEquivResidueFieldOfPrime k X.functionField
    (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk x))

/-- The residue-field equivalence sends the residue class of a stalk element to its residue at
the associated place. -/
@[simp]
theorem toPlaceResidueFieldAlgEquiv_mk (X : Scheme.{u}) [IsIntegral X]
    [X.Over (Spec (.of k))] (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (a : X.presheaf.stalk x) :
    toPlaceResidueFieldAlgEquiv (k := k) X x
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a) =
      (toPlace (k := k) X x).residueHom
        (algebraMap_stalk_mem_toPlace_integers (k := k) X x) a :=
  Place.quotientAlgEquivResidueFieldOfPrime_mk k X.functionField _ a

/-- The degree of the place attached to `x` is the degree of the scheme-theoretic residue field
`κ(x)` over the base field. -/
theorem toPlace_degree (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (.of k))] (x : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    (toPlace (k := k) X x).degree = Module.finrank k (X.residueField x) :=
  Place.degree_ofPrime k X.functionField
    (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk x))

/-- The degree of the place attached to `x` is the scheme-theoretic residue degree of `x` over
the base field. -/
@[simp]
theorem toPlace_degree_eq_residueDegree (X : Scheme.{u}) [IsIntegral X]
    [X.Over (Spec (.of k))] (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    (toPlace (k := k) X x).degree = (X ↘ Spec (.of k)).residueDegree x := by
  rw [toPlace_degree, finrank_residueField_eq_residueDegree]

end Scheme

namespace CodimensionOnePoint

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (.of k))]
  [IsLocallyNoetherian X]

/-- The order at the place attached to a codimension-one point is its scheme-theoretic order of
vanishing. -/
@[simp]
theorem toPlace_ord (x : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] (f : X.functionField) :
    (Scheme.toPlace (k := k) X (x : X)).ord f = X.ord f (x : X) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [(Scheme.toPlace (k := k) X (x : X)).ord_eq_iff_valuation_eq_exp_neg hf,
      Scheme.toPlace_valuation]
    have hord := (X.ord_eq_iff x.property hf).mp rfl
    simp only [_root_.AlgebraicGeometry.Scheme.ordHom,
      Ring.ordFrac_eq_valuation_inv] at hord
    rw [← inv_inj, hord]
    rw [WithZero.exp_neg, inv_inv, WithZero.exp_eq_coe_ofAdd]

/-- The additive order homomorphism of the place attached to `x` is the scheme-theoretic order
homomorphism at `x`. -/
theorem toPlace_ordAddMonoidHom (x : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] :
    (Scheme.toPlace (k := k) X (x : X)).ordAddMonoidHom = SchemeWeilDivisor.orderAt x := by
  apply AddMonoidHom.ext
  intro f
  rw [← ofMul_toMul f, Place.ordAddMonoidHom_apply, SchemeWeilDivisor.orderAt_apply,
    toPlace_ord, toMul_ofMul]

end CodimensionOnePoint

end

end AlgebraicGeometry

end TauCeti

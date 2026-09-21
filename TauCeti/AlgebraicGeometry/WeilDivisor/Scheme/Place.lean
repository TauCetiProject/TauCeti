/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order
public import TauCeti.FieldTheory.FunctionField.AffineModel.Prime
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Places attached to codimension-one points

Let `X` be an integral scheme over a field `k`. When the local ring at a codimension-one point
`x` is a discrete valuation ring, its normalized valuation on the function field of `X` is a
place of `X.functionField / k`. This file constructs that place and identifies its order with
the scheme-theoretic order of vanishing at `x`.

The construction first records the canonical `k`-algebra structures on the function field and
the stalks of a scheme over `Spec k`. These structures are compatible with the canonical map
from a stalk to the function field. The place is then `TauCeti.Place.ofPrime` for the maximal
ideal of the discrete valuation ring `𝒪_{X,x}`.

This provides the local bridge between the scheme-theoretic divisors used in the Jacobian
development and the abstract function-field places and differentials already available in
Tau Ceti.

## Main definitions and results

* `Scheme.baseRingToFunctionField`: the canonical map from the base ring to the function field.
* `Scheme.baseRingToStalk`: the canonical map from the base ring to a stalk.
* `CodimensionOnePoint.toPlace`: the normalized place attached to a codimension-one point.
* `CodimensionOnePoint.toPlace_ord`: its order is the scheme-theoretic order of vanishing.
* `CodimensionOnePoint.toPlace_ordAddMonoidHom`: the corresponding additive order homomorphisms
  agree.
* `CodimensionOnePoint.toPlaceResidueFieldAlgEquiv`: the residue field of the scheme point is
  the residue field of its place.
-/

public section

open _root_.AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The canonical map from the base ring of a scheme to its function field. It is the pullback
to global sections followed by the inclusion of global functions into rational functions. -/
def baseRingToFunctionField [IsIntegral X] : k →+* X.functionField :=
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  (X.germToFunctionField ⊤).hom.comp (Scheme.Modules.baseRingToGlobalSections k X)

/-- The function field of an integral scheme over `Spec k` is canonically a `k`-algebra. -/
instance (priority := 900) functionFieldBaseAlgebra [IsIntegral X] : Algebra k X.functionField :=
  (baseRingToFunctionField k X).toAlgebra

/-- The canonical map from the base ring of a scheme to its stalk at `x`. -/
def baseRingToStalk (x : X) : k →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x trivial).hom.comp (Scheme.Modules.baseRingToGlobalSections k X)

/-- Every stalk of a scheme over `Spec k` is canonically a `k`-algebra. -/
instance (priority := 900) stalkBaseAlgebra (x : X) : Algebra k (X.presheaf.stalk x) :=
  (baseRingToStalk k X x).toAlgebra

/-- The residue field at a point of a scheme over `Spec k` is canonically a `k`-algebra. -/
instance (priority := 900) residueFieldBaseAlgebra (x : X) : Algebra k (X.residueField x) :=
  ((X.residue x).hom.comp (baseRingToStalk k X x)).toAlgebra

/-- The canonical maps from the base ring through a stalk to the function field form a scalar
tower. -/
instance baseStalkFunctionFieldIsScalarTower [IsIntegral X] (x : X) :
    IsScalarTower k (X.presheaf.stalk x) X.functionField := by
  let _ : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  apply IsScalarTower.of_algebraMap_eq'
  rw [show algebraMap k X.functionField = baseRingToFunctionField k X from rfl,
    show algebraMap k (X.presheaf.stalk x) = baseRingToStalk k X x from rfl]
  ext c
  simp only [baseRingToFunctionField, baseRingToStalk, RingHom.comp_apply]
  exact (X.algebraMap_germ_eq_germToFunctionField (U := ⊤) (x := x) trivial _).symm

end Scheme

namespace CodimensionOnePoint

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (.of k))]

/-- The normalized place of the function field attached to a codimension-one point with discrete
valuation ring as its stalk. -/
def toPlace (x : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] : Place k X.functionField :=
  Place.ofPrime k X.functionField
    (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk (x : X)))

/-- The valuation of the place attached to `x` is the normalized valuation of the maximal ideal
of the discrete valuation ring `𝒪_{X,x}`. -/
@[simp]
lemma toPlace_valuation (x : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] :
    (x.toPlace (k := k)).valuation =
      (IsDiscreteValuationRing.maximalIdeal
        (X.presheaf.stalk (x : X))).valuation X.functionField :=
  Place.valuation_ofPrime k X.functionField _

/-- A rational function is integral at the place attached to `x` exactly when it comes from the
stalk `𝒪_{X,x}`. Thus the valuation ring of `x.toPlace` is the image of the local ring in the
function field. -/
theorem mem_toPlace_integers_iff_exists_stalk (x : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] (f : X.functionField) :
    f ∈ (x.toPlace (k := k)).integers ↔
      ∃ a : X.presheaf.stalk (x : X),
        algebraMap (X.presheaf.stalk (x : X)) X.functionField a = f := by
  rw [Place.mem_integers_iff, toPlace_valuation]
  constructor
  · exact IsDiscreteValuationRing.exists_lift_of_le_one
  · rintro ⟨a, rfl⟩
    exact (IsDiscreteValuationRing.maximalIdeal
      (X.presheaf.stalk (x : X))).valuation_le_one a

/-- The canonical inclusion of the stalk into the function field lands in the valuation ring of
the place attached to the point. -/
theorem algebraMap_stalk_mem_toPlace_integers (x : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] :
    ∀ a : X.presheaf.stalk (x : X),
      algebraMap (X.presheaf.stalk (x : X)) X.functionField a ∈
        (x.toPlace (k := k)).integers := by
  simpa only [toPlace] using
    (Place.algebraMap_mem_integers_ofPrime k X.functionField
      (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk (x : X))))

/-- The residue field of a codimension-one point is canonically the residue field of its place.
Both are the stalk modulo its maximal ideal; the right-hand description is the general residue
field computation for `Place.ofPrime`. -/
def toPlaceResidueFieldAlgEquiv (x : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] :
    X.residueField (x : X) ≃ₐ[k] (x.toPlace (k := k)).ResidueField :=
  Place.quotientAlgEquivResidueFieldOfPrime k X.functionField
    (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk (x : X)))

/-- The residue-field equivalence sends the residue class of a stalk element to its residue at
the associated place. -/
@[simp]
theorem toPlaceResidueFieldAlgEquiv_mk (x : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    (a : X.presheaf.stalk (x : X)) :
    toPlaceResidueFieldAlgEquiv x
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk (x : X))) a) =
      (x.toPlace (k := k)).residueHom
        (algebraMap_stalk_mem_toPlace_integers x) a := by
  change (Place.quotientAlgEquivResidueFieldOfPrime k X.functionField
      (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk (x : X))))
      (Ideal.Quotient.mk
        (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk (x : X))).asIdeal a) = _
  change _ = (Place.ofPrime k X.functionField
    (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk (x : X)))).residueHom _ a
  exact Place.quotientAlgEquivResidueFieldOfPrime_mk k X.functionField _ a

/-- The degree of the place attached to `x` is the degree of the scheme-theoretic residue field
`κ(x)` over the base field. -/
@[simp]
theorem toPlace_degree (x : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] :
    (x.toPlace (k := k)).degree = Module.finrank k (X.residueField (x : X)) :=
  Place.degree_ofPrime k X.functionField
    (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk (x : X)))

variable [IsLocallyNoetherian X]

/-- The order at the place attached to a codimension-one point is its scheme-theoretic order of
vanishing. -/
@[simp]
theorem toPlace_ord (x : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] (f : X.functionField) :
    (x.toPlace (k := k)).ord f = X.ord f (x : X) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [(x.toPlace (k := k)).ord_eq_iff_valuation_eq_exp_neg hf, toPlace_valuation]
    have hord := (X.ord_eq_iff x.property hf).mp rfl
    simp only [_root_.AlgebraicGeometry.Scheme.ordHom,
      Ring.ordFrac_eq_valuation_inv] at hord
    rw [← inv_inj, hord]
    rw [WithZero.exp_neg, inv_inv, WithZero.exp_eq_coe_ofAdd]

/-- The additive order homomorphism of the place attached to `x` is the scheme-theoretic order
homomorphism at `x`. -/
theorem toPlace_ordAddMonoidHom (x : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] :
    (x.toPlace (k := k)).ordAddMonoidHom = SchemeWeilDivisor.orderAt x := by
  apply AddMonoidHom.ext
  intro f
  rw [← ofMul_toMul f, Place.ordAddMonoidHom_apply, SchemeWeilDivisor.orderAt_apply,
    toPlace_ord, toMul_ofMul]

end CodimensionOnePoint

end

end AlgebraicGeometry

end TauCeti

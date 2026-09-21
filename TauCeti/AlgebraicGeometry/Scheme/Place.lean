/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.FieldTheory.FunctionField.AffineModel.Prime

/-!
# Places attached to points with discrete valuation ring stalks

Let `X` be an integral scheme over a field `k`. When the local ring at a point `x` is a discrete
valuation ring, its normalized valuation on the function field of `X` is a place of
`X.functionField / k`. This file constructs that place and identifies its valuation ring, residue
field, and degree with the scheme-theoretic local ring, residue field, and residue degree at `x`.

The construction uses the canonical `k`-algebra structures on the function field and the stalks
of a scheme over `Spec k`, recorded in `TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra`. The place
is then `TauCeti.Place.ofPrime` for the maximal ideal of the discrete valuation ring at `x`, so
its valuation, residue field and degree are read off from `TauCeti.Place.valuation_ofPrime`,
`TauCeti.Place.quotientAlgEquivResidueFieldOfPrime` and `TauCeti.Place.degree_ofPrime`, together
with Mathlib's `IsDiscreteValuationRing.equivValuationSubring`. No external formalization is
vendored.

## Main definitions and results

* `Scheme.toPlace`: the normalized place attached to a point with discrete valuation ring stalk.
* `Scheme.stalkToPlaceIntegersAlgEquiv`: the stalk at `x` is the valuation ring of that place.
* `Scheme.toPlaceResidueFieldAlgEquiv`: the residue field of the scheme point is the residue
  field of its place.
* `Scheme.toPlace_degree_eq_residueDegree`: the degree of the place is the scheme-theoretic
  residue degree of `x`.
-/

public section

open _root_.AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (.of k))]

/-- The normalized place of the function field attached to a point with discrete valuation ring
as its stalk. -/
def _root_.AlgebraicGeometry.Scheme.toPlace (X : Scheme.{u}) (x : X)
    [IsIntegral X] [X.Over (Spec (.of k))]
    [IsDiscreteValuationRing (X.presheaf.stalk x)] : Place k X.functionField :=
  Place.ofPrime k X.functionField
    (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk x))

/-- The valuation of the place attached to `x` is the normalized valuation of the maximal ideal
of the discrete valuation ring `𝒪_{X,x}`. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.toPlace_valuation (X : Scheme.{u}) [IsIntegral X]
    [X.Over (Spec (.of k))] (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    (X.toPlace (k := k) x).valuation =
      (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk x)).valuation X.functionField :=
  Place.valuation_ofPrime k X.functionField _

/-- A rational function is integral at the place attached to `x` exactly when it comes from the
stalk `𝒪_{X,x}`. Thus the valuation ring of `X.toPlace x` is the image of the local ring in the
function field. -/
theorem _root_.AlgebraicGeometry.Scheme.mem_toPlace_integers_iff_exists_stalk (X : Scheme.{u})
    [IsIntegral X] [X.Over (Spec (.of k))] (x : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] (f : X.functionField) :
    f ∈ (X.toPlace (k := k) x).integers ↔
      ∃ a : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField a = f := by
  rw [Place.mem_integers_iff, Scheme.toPlace_valuation]
  constructor
  · exact IsDiscreteValuationRing.exists_lift_of_le_one
  · rintro ⟨a, rfl⟩
    exact (IsDiscreteValuationRing.maximalIdeal
      (X.presheaf.stalk (x : X))).valuation_le_one a

/-- The canonical inclusion of the stalk into the function field lands in the valuation ring of
the place attached to the point. -/
theorem _root_.AlgebraicGeometry.Scheme.algebraMap_stalk_mem_toPlace_integers (X : Scheme.{u})
    [IsIntegral X] [X.Over (Spec (.of k))] (x : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    ∀ a : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField a ∈
      (X.toPlace (k := k) x).integers := by
  simpa only [Scheme.toPlace] using
    (Place.algebraMap_mem_integers_ofPrime k X.functionField
      (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk x)))

/-- The valuation ring defining the place is the valuation subring of the normalized maximal-ideal
valuation of the stalk. -/
theorem _root_.AlgebraicGeometry.Scheme.toPlace_integers (X : Scheme.{u}) [IsIntegral X]
    [X.Over (Spec (.of k))] (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    (X.toPlace (k := k) x).integers =
      ((IsDiscreteValuationRing.maximalIdeal
        (X.presheaf.stalk x)).valuation X.functionField).valuationSubring := by
  ext f
  rw [Place.mem_integers_iff, Scheme.toPlace_valuation, Valuation.mem_valuationSubring_iff]

/-- The stalk at a point with discrete valuation ring stalk is canonically the valuation ring of
its associated place. -/
def _root_.AlgebraicGeometry.Scheme.stalkToPlaceIntegersAlgEquiv (X : Scheme.{u}) [IsIntegral X]
    [X.Over (Spec (.of k))] (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    X.presheaf.stalk x ≃ₐ[k] (X.toPlace (k := k) x).integers :=
  AlgEquiv.ofRingEquiv
    (f := (IsDiscreteValuationRing.equivValuationSubring
      (A := X.presheaf.stalk x) (K := X.functionField)).trans
        (RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
          (Scheme.toPlace_integers (k := k) X x).symm))) fun c ↦
        Subtype.ext (IsScalarTower.algebraMap_apply k (X.presheaf.stalk x) X.functionField c).symm

/-- The stalk-to-valuation-ring equivalence is the canonical inclusion into the function field. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.coe_stalkToPlaceIntegersAlgEquiv (X : Scheme.{u})
    [IsIntegral X] [X.Over (Spec (.of k))] (x : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] (a : X.presheaf.stalk x) :
    ((X.stalkToPlaceIntegersAlgEquiv (k := k) x a :
      (X.toPlace (k := k) x).integers) : X.functionField) =
      algebraMap (X.presheaf.stalk x) X.functionField a := by
  -- Mathlib has no coercion lemma for `IsDiscreteValuationRing.equivValuationSubring`, so it is
  -- unfolded into its constituent equivalences, each of which has one.
  simp only [Scheme.stalkToPlaceIntegersAlgEquiv, AlgEquiv.ofRingEquiv_apply,
    RingEquiv.trans_apply, IsDiscreteValuationRing.equivValuationSubring]
  rw [RingEquiv.coe_subringCongr_apply, RingEquiv.coe_subringCongr_apply,
    Subring.coe_equivMapOfInjective_apply, Subring.topEquiv_symm_apply_coe]

/-- The residue field of a point with discrete valuation ring stalk is canonically the residue
field of its place. Both are the stalk modulo its maximal ideal; the right-hand description is
the general residue field computation for `Place.ofPrime`. -/
def _root_.AlgebraicGeometry.Scheme.toPlaceResidueFieldAlgEquiv (X : Scheme.{u}) [IsIntegral X]
    [X.Over (Spec (.of k))] (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    X.residueField x ≃ₐ[k] (X.toPlace (k := k) x).ResidueField :=
  Place.quotientAlgEquivResidueFieldOfPrime k X.functionField
    (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk x))

/-- The residue-field equivalence sends the residue class of a stalk element to its residue at
the associated place. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.toPlaceResidueFieldAlgEquiv_mk (X : Scheme.{u})
    [IsIntegral X] [X.Over (Spec (.of k))] (x : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] (a : X.presheaf.stalk x) :
    X.toPlaceResidueFieldAlgEquiv (k := k) x
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a) =
      (X.toPlace (k := k) x).residueHom
        (X.algebraMap_stalk_mem_toPlace_integers (k := k) x) a :=
  Place.quotientAlgEquivResidueFieldOfPrime_mk k X.functionField _ a

/-- The degree of the place attached to `x` is the degree of the scheme-theoretic residue field
`κ(x)` over the base field. -/
theorem _root_.AlgebraicGeometry.Scheme.toPlace_degree (X : Scheme.{u}) [IsIntegral X]
    [X.Over (Spec (.of k))] (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    (X.toPlace (k := k) x).degree = Module.finrank k (X.residueField x) :=
  Place.degree_ofPrime k X.functionField
    (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk x))

/-- The degree of the place attached to `x` is the scheme-theoretic residue degree of `x` over
the base field. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.toPlace_degree_eq_residueDegree (X : Scheme.{u})
    [IsIntegral X] [X.Over (Spec (.of k))] (x : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    (X.toPlace (k := k) x).degree = (X ↘ Spec (.of k)).residueDegree x := by
  rw [Scheme.toPlace_degree, Scheme.finrank_residueField_eq_residueDegree]

end

end AlgebraicGeometry

end TauCeti

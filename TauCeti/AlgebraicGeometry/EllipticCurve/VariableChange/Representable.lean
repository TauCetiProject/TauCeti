/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# The coordinate algebra of Weierstrass changes of variables

The group-valued functor `R ↦ WeierstrassCurve.VariableChange R` has underlying functor
corepresented by `ℤ[u,r,s,t][u⁻¹]`. The equivalence here uses the native change of variables,
including over rings with nilpotents and the zero ring; it is not a classification on field
points. This supplies the coordinate algebra for the group acting on Weierstrass equations.

`WeierstrassCurve.VariableChange.specialize` classifies a change of variables and
`Universal.change` is the universal one. Their two inverse laws, together with naturality,
give `pointsCorepresentableBy`.
The functor takes values in groups using Mathlib's `VariableChange.mapHom`, so its product
is the native, noncommutative product, not addition on three translation coordinates.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, §3, for the
  Weierstrass coordinate-change group. The native multiplication convention is retained here.
-/

public section

noncomputable section

universe u

open WeierstrassCurve WeierstrassCurve.VariableChange

namespace TauCeti.WeierstrassChange

namespace Universal

open MvPolynomial

/-- The coordinate algebra `ℤ[u,r,s,t][u⁻¹]`, with indices `0,1,2,3` for `u,r,s,t`. -/
abbrev CoordinateRing := Localization.Away (X (0 : Fin 4) : MvPolynomial (Fin 4) ℤ)

/-- The four coordinate functions on the scheme of changes of variables. -/
def coordinate (i : Fin 4) : CoordinateRing :=
  algebraMap (MvPolynomial (Fin 4) ℤ) CoordinateRing (X i)

@[simp]
theorem algebraMap_X (i : Fin 4) :
    algebraMap (MvPolynomial (Fin 4) ℤ) CoordinateRing (X i) = coordinate i := (rfl)

/-- The scaling coordinate is invertible in the coordinate algebra. -/
theorem isUnit_coordinate_zero : IsUnit (coordinate 0) :=
  IsLocalization.Away.algebraMap_isUnit (X (0 : Fin 4) : MvPolynomial (Fin 4) ℤ)

/-- The universal admissible change of variables over `ℤ[u,r,s,t][u⁻¹]`. -/
def change : VariableChange CoordinateRing :=
  ⟨isUnit_coordinate_zero.unit, coordinate 1, coordinate 2, coordinate 3⟩

@[simp] theorem change_u : (change.u : CoordinateRing) = coordinate 0 :=
  isUnit_coordinate_zero.unit_spec

@[simp] theorem change_r : change.r = coordinate 1 := (rfl)

@[simp] theorem change_s : change.s = coordinate 2 := (rfl)

@[simp] theorem change_t : change.t = coordinate 3 := (rfl)

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A map from the coordinate algebra is determined by the four coordinate functions;
the inverse of the scaling coordinate requires no extra datum. -/
@[ext]
theorem ringHom_ext {f g : CoordinateRing →+* R}
    (h : ∀ i, f (coordinate i) = g (coordinate i)) : f = g := by
  apply IsLocalization.ringHom_ext (.powers (X (0 : Fin 4) : MvPolynomial (Fin 4) ℤ))
  exact MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) h

end Universal

end TauCeti.WeierstrassChange

namespace WeierstrassCurve.VariableChange

open MvPolynomial TauCeti.WeierstrassChange.Universal

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The classifying homomorphism of a change of variables: send `u,r,s,t` to its coefficients. -/
def specialize (C : VariableChange R) : CoordinateRing →+* R :=
  IsLocalization.Away.lift (X (0 : Fin 4) : MvPolynomial (Fin 4) ℤ)
    (g := eval₂Hom (Int.castRingHom R) ![(C.u : R), C.r, C.s, C.t]) (by simp)

/-- Specialization evaluates the four coordinates at the four native coefficients. -/
@[simp]
theorem specialize_coordinate (C : VariableChange R) (i : Fin 4) :
    specialize C (coordinate i) = ![(C.u : R), C.r, C.s, C.t] i := by
  simp [specialize, coordinate, IsLocalization.Away.lift_eq, -algebraMap_X]

/-- Every change of variables is the image of the universal one under its classifying map. -/
@[simp]
theorem map_specialize (C : VariableChange R) : change.map (specialize C) = C := by
  ext <;> simp

/-- Classifying maps commute with coefficient extension. -/
@[simp]
theorem specialize_map (C : VariableChange R) (f : R →+* S) :
    specialize (C.map f) = f.comp (specialize C) := by
  apply TauCeti.WeierstrassChange.Universal.ringHom_ext
  intro i
  fin_cases i <;> simp

end WeierstrassCurve.VariableChange

namespace TauCeti.WeierstrassChange

namespace Universal

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The universal change is classified by the identity on its coordinate algebra. -/
@[simp]
theorem specialize_change : specialize change = RingHom.id CoordinateRing := by
  apply ringHom_ext
  intro i
  fin_cases i <;> simp

/-- Ring homomorphisms from the coordinate algebra classify native changes of variables. -/
def ringHomEquiv (R : Type*) [CommRing R] : (CoordinateRing →+* R) ≃ VariableChange R where
  toFun f := change.map f
  invFun := specialize
  left_inv f := by simp
  right_inv := map_specialize

@[simp]
theorem ringHomEquiv_apply (f : CoordinateRing →+* R) : ringHomEquiv R f = change.map f := (rfl)

@[simp]
theorem ringHomEquiv_symm_apply (C : VariableChange R) :
    (ringHomEquiv R).symm C = specialize C := (rfl)

/-- The represented point associated to a composite is obtained by mapping the original
point along the second ring homomorphism. -/
theorem ringHomEquiv_comp (f : CoordinateRing →+* R) (g : R →+* S) :
    ringHomEquiv S (g.comp f) = (ringHomEquiv R f).map g :=
  (change.map_map f g).symm

end Universal

open CategoryTheory

/-- Changes of variables, with their native noncommutative group law, form a group-valued
functor of the coefficient ring. Its body is exposed so that its value types are the native
groups `VariableChange R`, without transporting points across object equalities. -/
@[expose] def pointsFunctor : CommRingCat.{u} ⥤ GrpCat.{u} where
  obj R := GrpCat.of (VariableChange R)
  map f := GrpCat.ofHom (mapHom f.hom)
  map_id _ := GrpCat.hom_ext (MonoidHom.ext fun C ↦ C.map_id)
  map_comp f g := GrpCat.hom_ext (MonoidHom.ext fun C ↦ (C.map_map f.hom g.hom).symm)

/-- The points functor acts by the native coefficient map. -/
@[simp]
theorem pointsFunctor_map_apply {R S : CommRingCat.{u}} (f : R ⟶ S)
    (C : VariableChange R) : pointsFunctor.map f C = C.map f.hom := (rfl)

/-- The underlying type-valued functor of Weierstrass changes of variables is corepresented
by `ℤ[u,r,s,t][u⁻¹]`. The group-scheme structure is not constructed here. -/
def pointsCorepresentableBy :
    (pointsFunctor.{u} ⋙ forget GrpCat).CorepresentableBy
      (CommRingCat.of (ULift.{u} Universal.CoordinateRing)) where
  homEquiv {R} := (ConcreteCategory.homEquiv (C := CommRingCat)).trans <|
    ({ toFun f := f.comp ULift.ringEquiv.symm.toRingHom
       invFun f := f.comp ULift.ringEquiv.toRingHom
       left_inv f := by ext x; rfl
       right_inv f := by ext x; rfl } :
      (ULift.{u} Universal.CoordinateRing →+* R) ≃ (Universal.CoordinateRing →+* R)).trans
        (Universal.ringHomEquiv R)
  homEquiv_comp g f := by
    -- Unwrap coefficient extension and use naturality of the ring-level classification.
    dsimp [ConcreteCategory.homEquiv, pointsFunctor]
    exact Universal.ringHomEquiv_comp (f.hom.comp ULift.ringEquiv.symm.toRingHom) g.hom

/-- The representing equivalence evaluates the universal change along the given ring map. -/
-- Not a simp lemma: the composite functor's object type is not in simp normal form.
theorem pointsCorepresentableBy_homEquiv {R : CommRingCat.{u}}
    (f : CommRingCat.of (ULift.{u} Universal.CoordinateRing) ⟶ R) :
    pointsCorepresentableBy.homEquiv f =
      Universal.change.map (f.hom.comp ULift.ringEquiv.symm.toRingHom) := (rfl)

/-- The inverse representing equivalence is the classifying homomorphism. -/
-- As above, the composite functor's object type prevents a simp-normal-form statement.
theorem pointsCorepresentableBy_homEquiv_symm {R : CommRingCat.{u}}
    (C : VariableChange R) :
    pointsCorepresentableBy.homEquiv.symm C =
      CommRingCat.ofHom (C.specialize.comp ULift.ringEquiv.toRingHom) := (rfl)

/-- The underlying functor of changes of variables is corepresentable by its coordinate
algebra; the representing equivalence is `pointsCorepresentableBy`. -/
instance : (pointsFunctor.{u} ⋙ forget GrpCat).IsCorepresentable :=
  pointsCorepresentableBy.isCorepresentable

end TauCeti.WeierstrassChange

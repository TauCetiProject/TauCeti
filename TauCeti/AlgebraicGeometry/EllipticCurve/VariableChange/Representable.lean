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
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# The coordinate algebra of Weierstrass changes of variables

The group-valued functor `R ↦ WeierstrassCurve.VariableChange R` has underlying functor
corepresented by `ℤ[u,r,s,t][u⁻¹]`. The equivalence here uses the native change of variables,
including over rings with nilpotents and the zero ring; it is not a classification on field
points. This supplies the coordinate algebra for the group acting on Weierstrass equations.

`Universal.specialize` classifies a change of variables and `Universal.change` is the universal
one. Their two inverse laws, together with naturality, give `pointsCorepresentableBy`.
The functor takes values in groups using Mathlib's `VariableChange.mapHom`, so its product
is the native, noncommutative product, not addition on three translation coordinates.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, §3, for the
  Weierstrass coordinate-change group. The native multiplication convention is retained here.
-/

public section

noncomputable section

namespace WeierstrassCurve.VariableChange

namespace Universal

open MvPolynomial

/-- The coordinate algebra `ℤ[u,r,s,t][u⁻¹]`, with indices `0,1,2,3` for `u,r,s,t`. -/
abbrev Ring := Localization.Away (X (0 : Fin 4) : MvPolynomial (Fin 4) ℤ)

/-- The four coordinate functions on the scheme of changes of variables. -/
def coordinate (i : Fin 4) : Ring :=
  algebraMap (MvPolynomial (Fin 4) ℤ) Ring (X i)

/-- The scaling coordinate is invertible in the coordinate algebra. -/
theorem isUnit_coordinate_zero : IsUnit (coordinate 0) :=
  IsLocalization.Away.algebraMap_isUnit (X (0 : Fin 4) : MvPolynomial (Fin 4) ℤ)

/-- The universal admissible change of variables over `ℤ[u,r,s,t][u⁻¹]`. -/
def change : VariableChange Ring :=
  ⟨isUnit_coordinate_zero.unit, coordinate 1, coordinate 2, coordinate 3⟩

@[simp] theorem change_u : (change.u : Ring) = coordinate 0 :=
  isUnit_coordinate_zero.unit_spec

@[simp] theorem change_r : change.r = coordinate 1 := (rfl)

@[simp] theorem change_s : change.s = coordinate 2 := (rfl)

@[simp] theorem change_t : change.t = coordinate 3 := (rfl)

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A map from the coordinate algebra is determined by the four coordinate functions;
the inverse of the scaling coordinate requires no extra datum. -/
@[ext]
theorem ringHom_ext {f g : Ring →+* R}
    (h : ∀ i, f (coordinate i) = g (coordinate i)) : f = g := by
  apply IsLocalization.ringHom_ext (.powers (X (0 : Fin 4) : MvPolynomial (Fin 4) ℤ))
  exact MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) h

/-- The classifying homomorphism of a change of variables: send `u,r,s,t` to its coefficients. -/
def specialize (C : VariableChange R) : Ring →+* R :=
  IsLocalization.Away.lift (X (0 : Fin 4) : MvPolynomial (Fin 4) ℤ)
    (g := eval₂Hom (Int.castRingHom R) ![(C.u : R), C.r, C.s, C.t]) (by simp)

/-- Specialization evaluates the four coordinates at the four native coefficients. -/
@[simp]
theorem specialize_coordinate (C : VariableChange R) (i : Fin 4) :
    specialize C (coordinate i) = ![(C.u : R), C.r, C.s, C.t] i := by
  simp [specialize, coordinate, IsLocalization.Away.lift_eq]

/-- Every change of variables is the image of the universal one under its classifying map. -/
@[simp]
theorem map_specialize (C : VariableChange R) : change.map (specialize C) = C := by
  ext <;> simp

/-- A homomorphism from the coordinate algebra is the classifying map of the change of
variables that it produces. This is the uniqueness part of the universal property. -/
@[simp]
theorem specialize_map_change (f : Ring →+* R) : specialize (change.map f) = f := by
  apply ringHom_ext
  intro i
  fin_cases i <;> simp

/-- Ring homomorphisms from `ℤ[u,r,s,t][u⁻¹]` classify native changes of variables. -/
def ringHomEquiv (R : Type*) [CommRing R] : (Ring →+* R) ≃ VariableChange R where
  toFun f := change.map f
  invFun := specialize
  left_inv := specialize_map_change
  right_inv := map_specialize

@[simp]
theorem ringHomEquiv_apply (f : Ring →+* R) : ringHomEquiv R f = change.map f := (rfl)

@[simp]
theorem ringHomEquiv_symm_apply (C : VariableChange R) :
    (ringHomEquiv R).symm C = specialize C := (rfl)

/-- Classifying maps commute with coefficient extension. -/
theorem specialize_map (C : VariableChange R) (f : R →+* S) :
    specialize (C.map f) = f.comp (specialize C) := by
  apply ringHom_ext
  intro i
  fin_cases i <;> simp

/-- The represented point associated to a composite is obtained by mapping the original
point along the second ring homomorphism. -/
theorem ringHomEquiv_comp (f : Ring →+* R) (g : R →+* S) :
    ringHomEquiv S (g.comp f) = (ringHomEquiv R f).map g :=
  (change.map_map f g).symm

end Universal

open CategoryTheory

/-- Changes of variables, with their native noncommutative group law, form a group-valued
functor of the coefficient ring. Its body is exposed so that its value types are the native
groups `VariableChange R`, without transporting points across object equalities. -/
@[expose] def pointsFunctor : CommRingCat.{0} ⥤ GrpCat.{0} where
  obj R := GrpCat.of (VariableChange R)
  map f := GrpCat.ofHom (mapHom f.hom)
  map_id _ := GrpCat.hom_ext (MonoidHom.ext fun C ↦ C.map_id)
  map_comp f g := GrpCat.hom_ext (MonoidHom.ext fun C ↦ (C.map_map f.hom g.hom).symm)

/-- The points functor acts by the native coefficient map. -/
@[simp]
theorem pointsFunctor_map_apply {R S : CommRingCat.{0}} (f : R ⟶ S)
    (C : VariableChange R) : pointsFunctor.map f C = C.map f.hom := (rfl)

/-- The group functor of Weierstrass changes of variables is represented on affine test
schemes by `Spec ℤ[u,r,s,t][u⁻¹]`, expressed as corepresentability on commutative rings. -/
def pointsCorepresentableBy :
    (pointsFunctor ⋙ forget GrpCat).CorepresentableBy (CommRingCat.of Universal.Ring) where
  homEquiv {R} := (ConcreteCategory.homEquiv (C := CommRingCat)).trans
    (Universal.ringHomEquiv R)
  homEquiv_comp g f := by
    -- Unwrap the concrete-category equivalence and the underlying type-valued functor.
    dsimp [ConcreteCategory.homEquiv, pointsFunctor]
    exact Universal.ringHomEquiv_comp f.hom g.hom

/-- The representing equivalence evaluates the universal change along the given ring map. -/
-- Not a simp lemma: the composite functor's object type is not in simp normal form.
theorem pointsCorepresentableBy_homEquiv {R : CommRingCat.{0}}
    (f : CommRingCat.of Universal.Ring ⟶ R) :
    pointsCorepresentableBy.homEquiv f = Universal.change.map f.hom := (rfl)

/-- The inverse representing equivalence is the classifying homomorphism. -/
-- As above, the composite functor's object type prevents a simp-normal-form statement.
theorem pointsCorepresentableBy_homEquiv_symm {R : CommRingCat.{0}}
    (C : VariableChange R) :
    pointsCorepresentableBy.homEquiv.symm C = CommRingCat.ofHom (Universal.specialize C) := (rfl)

/-- The underlying functor of changes of variables is corepresentable by its coordinate
algebra; the representing equivalence is `pointsCorepresentableBy`. -/
instance : (pointsFunctor ⋙ forget GrpCat).IsCorepresentable :=
  pointsCorepresentableBy.isCorepresentable

end WeierstrassCurve.VariableChange

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Opposite
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Representability
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

/-!
# Representability of dynamic Levi subgroups

For a cocharacter `λ` of an affine group scheme, its dynamic Levi `Z(λ)` is represented by
the quotient by the sum of the defining Hopf ideals of `P(λ)` and `P(−λ)`. Thus it is the
scheme-theoretic intersection of the two opposite dynamic parabolics. The natural representing
isomorphism identifies quotient points with their ambient points, over every commutative value
algebra, including nonreduced ones.

No field, smoothness, reductivity, or finite-type hypothesis is needed. When the ambient
coordinate algebra is of finite type, its Levi quotient is of finite type by the existing
Hopf-ideal quotient API. This supplies the affine subgroup needed for the scheme-theoretic
Levi decomposition; it makes no claim that a dynamic parabolic has proper homogeneous quotient.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

The representing isomorphism uses the same quotient-points construction as
`TauCeti.Cocharacter.parabolicPointsIso`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.Cocharacter

universe u v w

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]

/-- The Hopf ideal cutting out the dynamic Levi, the scheme-theoretic intersection of the
parabolics of a cocharacter and its opposite. -/
noncomputable def leviDefiningHopfIdeal (l : H →ₐc[R] LaurentPolynomial R) :
    HopfIdeal R H :=
  parabolicDefiningHopfIdeal l ⊔ parabolicDefiningHopfIdeal l.oppositeCocharacter

/-- The Levi defining ideal is the sum of the two opposite parabolic defining ideals. -/
theorem leviDefiningHopfIdeal_def (l : H →ₐc[R] LaurentPolynomial R) :
    leviDefiningHopfIdeal l =
      parabolicDefiningHopfIdeal l ⊔ parabolicDefiningHopfIdeal l.oppositeCocharacter := (rfl)

/-- Opposite cocharacters define the same closed Levi subgroup scheme. -/
@[simp]
theorem leviDefiningHopfIdeal_oppositeCocharacter (l : H →ₐc[R] LaurentPolynomial R) :
    leviDefiningHopfIdeal l.oppositeCocharacter = leviDefiningHopfIdeal l := by
  simp only [leviDefiningHopfIdeal_def, BialgHom.oppositeCocharacter_oppositeCocharacter,
    sup_comm]

/-- The subgroup cut out by the Levi ideal is exactly the dynamic Levi, over every value
algebra. -/
@[simp]
theorem quotientPointsSubgroup_leviDefiningHopfIdeal (l : H →ₐc[R] LaurentPolynomial R)
    (A : CommAlgCat.{w} R) :
    CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H)
      (leviDefiningHopfIdeal l) A = levi A l := by
  rw [leviDefiningHopfIdeal_def, CommHopfAlgCat.quotientPointsSubgroup_sup,
    quotientPointsSubgroup_parabolicDefiningHopfIdeal,
    quotientPointsSubgroup_parabolicDefiningHopfIdeal, parabolic_inf_oppositeCocharacter]

/-- The quotient by the Levi defining Hopf ideal represents the dynamic Levi functor. -/
noncomputable def leviPointsIso (l : H →ₐc[R] LaurentPolynomial R) :
    HopfAlgebra.pointsFunctor (R := R)
        (H := CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
          (leviDefiningHopfIdeal l)) ≅ leviFunctor.{u, v, w} l :=
  CommHopfAlgCat.quotientPointsSubgroupRepresentingIso (_root_.CommHopfAlgCat.of R H)
    (leviDefiningHopfIdeal l) (fun A ↦ levi A l)
    (fun A _ ↦ by rw [quotientPointsSubgroup_leviDefiningHopfIdeal])

/-- The representing isomorphism sends a quotient point to its ambient point. -/
@[simp]
theorem coe_leviPointsIso_hom_app_apply (l : H →ₐc[R] LaurentPolynomial R)
    (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R)
      (H := CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
        (leviDefiningHopfIdeal l)) A) :
    ((ConcreteCategory.hom
      (X := HopfAlgebra.pointsFunctor (R := R)
        (H := CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
          (leviDefiningHopfIdeal l)) |>.obj A)
      (Y := GrpCat.of (levi A l))
      ((leviPointsIso l).hom.app A) f : levi A l) : WithConv (H →ₐ[R] A)) =
      CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H)
        (leviDefiningHopfIdeal l) A f := by
  unfold leviPointsIso
  exact CommHopfAlgCat.coe_quotientPointsSubgroupRepresentingIso_hom_app_apply
    (_root_.CommHopfAlgCat.of R H) (leviDefiningHopfIdeal l) _ _ A f

/-- Factoring a Levi point through the representing quotient recovers its ambient point. -/
@[simp]
theorem quotientPointsHom_leviPointsIso_inv_app_apply
    (l : H →ₐc[R] LaurentPolynomial R) (A : CommAlgCat.{w} R) (g : levi A l) :
    CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H)
        (leviDefiningHopfIdeal l) A ((leviPointsIso l).inv.app A g) = g.1 := by
  unfold leviPointsIso
  exact CommHopfAlgCat.quotientPointsHom_quotientPointsSubgroupRepresentingIso_inv_app_apply
    (_root_.CommHopfAlgCat.of R H) (leviDefiningHopfIdeal l) (fun A ↦ levi A l) _ A g

end TauCeti.Cocharacter

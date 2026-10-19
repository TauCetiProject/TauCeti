/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.Basic
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Representability
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality

/-!
# Representability of dynamic weight parabolics

The weight-parabolic subgroup scheme of `GL_N` represents the dynamic parabolic attached to the
cocharacter `t ↦ diag(t ^ w i)`. On points, both descriptions say exactly that the `(i,j)` entry
vanishes whenever `w i < w j`.

The dynamic defining Hopf ideal equals the explicit matrix ideal, so the comparison
also identifies the infinitesimal subgroup structure.

## Main declarations

* `TauCeti.GeneralLinear.Dynamic.mem_weightParabolicDefiningPointsSubgroup_iff`: membership in
  the Hopf-ideal cut-out agrees with dynamic-parabolic membership.
* `TauCeti.GeneralLinear.Dynamic.weightParabolicPointsIso`: the natural representing
  isomorphism.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear.Dynamic

universe u v

variable (R : Type u) [CommRing R] {N : ℕ}

private theorem mem_weightParabolicSubgroup_iff (w : Fin N → ℤ)
    (A : CommAlgCat.{v} R)
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N) A) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R N)
        (weightParabolicDefiningHopfIdeal R w) A ↔
      g ∈ Cocharacter.parabolic A (weightCocharacter (R := R) w) := by
  rw [mem_weightParabolicDefiningPointsSubgroup_iff_blockTriangular,
    mem_parabolic_weightCocharacter_iff]

section Points

variable {A : Type v} [CommRing A] [Algebra R A]

/-- The Hopf-ideal cut-out is exactly the dynamic parabolic of the weight cocharacter. -/
theorem mem_weightParabolicDefiningPointsSubgroup_iff (w : Fin N → ℤ)
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N)
      (CommAlgCat.of R A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R N)
        (weightParabolicDefiningHopfIdeal R w) (CommAlgCat.of R A) ↔
      g ∈ Cocharacter.parabolic (CommAlgCat.of R A) (weightCocharacter (R := R) w) := by
  rw [mem_weightParabolicDefiningPointsSubgroup_iff_blockTriangular,
    mem_parabolic_weightCocharacter_iff]

end Points

/-- The weight-parabolic coordinate Hopf algebra represents the dynamic parabolic functor of the
weight cocharacter, naturally in the commutative value algebra. -/
noncomputable def weightParabolicPointsIso (w : Fin N → ℤ) :
    HopfAlgebra.pointsFunctor (R := R) (H := weightParabolicCoordinateHopfAlgebra R w) ≅
      Cocharacter.parabolicFunctor (weightCocharacter (R := R) w) :=
  CommHopfAlgCat.quotientPointsSubgroupRepresentingIso
    (coordinateHopfAlgebra R N) (weightParabolicDefiningHopfIdeal R w)
    (fun A ↦ Cocharacter.parabolic A (weightCocharacter (R := R) w))
    (mem_weightParabolicSubgroup_iff R w)

/-- The ambient point underlying the represented dynamic-parabolic point is induced by the
quotient coordinate map. -/
@[simp]
theorem coe_weightParabolicPointsIso_hom_app_apply (w : Fin N → ℤ)
    {A : Type v} [CommRing A] [Algebra R A]
    (f : HopfAlgebra.points
      (R := R) (H := weightParabolicCoordinateHopfAlgebra R w) (CommAlgCat.of R A)) :
    (((eqToHom (Cocharacter.parabolicFunctor_obj
        (weightCocharacter (R := R) w) (CommAlgCat.of R A)))
      ((weightParabolicPointsIso R w).hom.app (CommAlgCat.of R A) f) :
        Cocharacter.parabolic (CommAlgCat.of R A) (weightCocharacter (R := R) w)) :
      HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N) (CommAlgCat.of R A)) =
      CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
        (weightParabolicDefiningHopfIdeal R w) (CommAlgCat.of R A) f := by
  unfold weightParabolicPointsIso
  convert
    (CommHopfAlgCat.coe_quotientPointsSubgroupRepresentingIso_hom_app_apply
      (coordinateHopfAlgebra R N) (weightParabolicDefiningHopfIdeal R w)
      (fun B ↦ Cocharacter.parabolic B (weightCocharacter (R := R) w))
      (mem_weightParabolicSubgroup_iff R w)
      (CommAlgCat.of R A) f) using 1
  rfl

/-- Applying the quotient inclusion to the inverse representing isomorphism recovers the ambient
dynamic-parabolic point. -/
@[simp]
theorem quotientPointsHom_weightParabolicPointsIso_inv_app_apply (w : Fin N → ℤ)
    {A : Type v} [CommRing A] [Algebra R A]
    (g : Cocharacter.parabolic (CommAlgCat.of R A) (weightCocharacter (R := R) w)) :
    CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
        (weightParabolicDefiningHopfIdeal R w) (CommAlgCat.of R A)
        ((weightParabolicPointsIso R w).inv.app (CommAlgCat.of R A) g) = g.1 := by
  unfold weightParabolicPointsIso
  convert
    (CommHopfAlgCat.quotientPointsHom_quotientPointsSubgroupRepresentingIso_inv_app_apply
      (coordinateHopfAlgebra R N) (weightParabolicDefiningHopfIdeal R w)
      (fun B ↦ Cocharacter.parabolic B (weightCocharacter (R := R) w))
      (mem_weightParabolicSubgroup_iff R w)
      (CommAlgCat.of R A) g) using 1

/-- The dynamic parabolic ideal of a diagonal weight cocharacter equals the explicit
weight-parabolic matrix ideal, including its scheme structure. -/
@[simp]
theorem parabolicDefiningHopfIdeal_weightCocharacter (w : Fin N → ℤ) :
    Cocharacter.parabolicDefiningHopfIdeal (weightCocharacter (R := R) w) =
      weightParabolicDefiningHopfIdeal R w := by
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq
    (H := coordinateHopfAlgebra R N)
  intro A
  ext g
  rw [Cocharacter.quotientPointsSubgroup_parabolicDefiningHopfIdeal]
  exact (mem_weightParabolicDefiningPointsSubgroup_iff R w g).symm

end TauCeti.GeneralLinear.Dynamic

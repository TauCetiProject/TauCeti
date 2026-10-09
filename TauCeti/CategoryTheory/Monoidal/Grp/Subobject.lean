/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Group structures on subobjects

A subobject of a group object inherits a unique group structure if the identity,
multiplication, and inversion factor through it. The group axioms follow by cancellation
of the monomorphism; no axioms need to be assumed for the lifted operations.

This is the categorical form of the closed-subgroup criterion for group schemes.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.3.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace TauCeti

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {H G : C} [GrpObj G]

/-- The group structure induced on a subobject by lifts of identity, multiplication and inversion.
Only the compatibility of the operations with the inclusion is required. -/
@[instance_reducible]
def grpObjOfMono (i : H ⟶ G) [Mono i]
    (e : 𝟙_ C ⟶ H) (m : H ⊗ H ⟶ H) (j : H ⟶ H)
    (he : e ≫ i = η[G]) (hm : m ≫ i = (i ⊗ₘ i) ≫ μ[G])
    (hj : j ≫ i = i ≫ ι[G]) : GrpObj H where
  one := e
  mul := m
  inv := j
  one_mul := by
    apply (cancel_mono i).1
    rw [← lift_fst_comp_snd_comp] at hm
    simp [hm, comp_lift_assoc, he, leftUnitor_hom, -lift_fst_comp_snd_comp]
  mul_one := by
    apply (cancel_mono i).1
    rw [← lift_fst_comp_snd_comp] at hm
    simp [hm, comp_lift_assoc, he, rightUnitor_hom, -lift_fst_comp_snd_comp]
  mul_assoc := by
    apply (cancel_mono i).1
    rw [← lift_fst_comp_snd_comp] at hm
    simp [hm, comp_lift_assoc, MonObj.lift_lift_assoc, -lift_fst_comp_snd_comp]
  left_inv := by
    apply (cancel_mono i).1
    simp [hm, he, hj]
  right_inv := by
    apply (cancel_mono i).1
    simp [hm, he, hj]

/-- The inclusion of the induced group object is a homomorphism. -/
theorem isMonHom_grpObjOfMono (i : H ⟶ G) [Mono i]
    (e : 𝟙_ C ⟶ H) (m : H ⊗ H ⟶ H) (j : H ⟶ H)
    (he : e ≫ i = η[G]) (hm : m ≫ i = (i ⊗ₘ i) ≫ μ[G])
    (hj : j ≫ i = i ≫ ι[G]) :
    letI := grpObjOfMono i e m j he hm hj
    IsMonHom i := by
  let := grpObjOfMono i e m j he hm hj
  exact ⟨he, hm⟩

/-- A monomorphism into a group object admits at most one compatible group structure. -/
theorem grpObj_eq_of_mono (i : H ⟶ G) [Mono i] (a b : GrpObj H)
    (ha : @IsMonHom _ _ _ H G a.toMonObj inferInstance i)
    (hb : @IsMonHom _ _ _ H G b.toMonObj inferInstance i) : a = b := by
  apply GrpObj.ext
  apply MonObj.ext
  apply (cancel_mono i).1
  exact ha.mul_hom.trans hb.mul_hom.symm

/-- The unit of the induced group object is the specified lift. -/
@[simp]
theorem grpObjOfMono_one (i : H ⟶ G) [Mono i]
    (e : 𝟙_ C ⟶ H) (m : H ⊗ H ⟶ H) (j : H ⟶ H)
    (he : e ≫ i = η[G]) (hm : m ≫ i = (i ⊗ₘ i) ≫ μ[G])
    (hj : j ≫ i = i ≫ ι[G]) :
    (grpObjOfMono i e m j he hm hj).one = e := (rfl)

/-- The multiplication of the induced group object is the specified lift. -/
@[simp]
theorem grpObjOfMono_mul (i : H ⟶ G) [Mono i]
    (e : 𝟙_ C ⟶ H) (m : H ⊗ H ⟶ H) (j : H ⟶ H)
    (he : e ≫ i = η[G]) (hm : m ≫ i = (i ⊗ₘ i) ≫ μ[G])
    (hj : j ≫ i = i ≫ ι[G]) :
    (grpObjOfMono i e m j he hm hj).mul = m := (rfl)

/-- The inversion of the induced group object is the specified lift. -/
@[simp]
theorem grpObjOfMono_inv (i : H ⟶ G) [Mono i]
    (e : 𝟙_ C ⟶ H) (m : H ⊗ H ⟶ H) (j : H ⟶ H)
    (he : e ≫ i = η[G]) (hm : m ≫ i = (i ⊗ₘ i) ≫ μ[G])
    (hj : j ≫ i = i ≫ ι[G]) :
    (grpObjOfMono i e m j he hm hj).inv = j := (rfl)

end TauCeti

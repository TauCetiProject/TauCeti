/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Grp

/-!
# Monoid and group objects along faithful monoidal functors

Let `F : C ⥤ D` be a faithful monoidal functor and `X : C`. Mathlib pulls a monoid object
structure on `F.obj X` back to `X` when `F` is fully faithful
(`CategoryTheory.Functor.FullyFaithful.monObj`). If `F` is only faithful, the same works as soon as
the unit and the multiplication of `F.obj X` are images under `F` of morphisms `𝟙_ C ⟶ X` and
`X ⊗ X ⟶ X`, and similarly for the inverse of a group object: the axioms hold on `X` because they
hold after applying `F`. The construction and its proofs follow Mathlib's
`CategoryTheory.Functor.FullyFaithful.monObj` and `CategoryTheory.Functor.FullyFaithful.grpObj`.
Faithfulness also makes the structure on `X` unique, and it reflects commutativity and
homomorphisms.

This is the formal part of descent of group objects: for a base change functor along a morphism
of effective descent, the morphism-descent theorem supplies the required morphisms.

## Main declarations

* `CategoryTheory.Functor.monObjOfFaithful`, `CategoryTheory.Functor.grpObjOfFaithful`: the monoid
  (group) object structure on `X` whose structure morphisms are given lifts of those of `F.obj X`.
* `CategoryTheory.Functor.monObjObj_monObjOfFaithful`,
  `CategoryTheory.Functor.grpObjObj_grpObjOfFaithful`: its image under `F` is the given structure.
* `CategoryTheory.Functor.monObjObj_injective`, `CategoryTheory.Functor.grpObjObj_injective`: a
  faithful monoidal functor is injective on monoid (group) object structures.
* `CategoryTheory.Functor.isMonHom_map_iff`, `CategoryTheory.Functor.isCommMonObj_obj_iff`:
  a faithful monoidal functor reflects homomorphisms and commutativity.
-/

public section

namespace CategoryTheory.Functor

open MonoidalCategory MonObj OplaxMonoidal LaxMonoidal
open scoped Obj

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section Monoidal

variable [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)

section OplaxMonoidal

variable [F.OplaxMonoidal] [F.Faithful]

/-- Pull back a monoid object along a faithful oplax monoidal functor `F`, given lifts `one` and
`mul` of the unit and the multiplication of `F.obj X`. -/
@[simps]
abbrev monObjOfFaithful (X : C) [MonObj (F.obj X)] (one : 𝟙_ C ⟶ X) (mul : X ⊗ X ⟶ X)
    (h_one : F.map one = OplaxMonoidal.η F ≫ η[F.obj X])
    (h_mul : F.map mul = δ F X X ≫ μ[F.obj X]) : MonObj X where
  one := one
  mul := mul
  one_mul := F.map_injective <| by simp [h_one, h_mul, ← δ_natural_left_assoc]
  mul_one := F.map_injective <| by simp [h_one, h_mul, ← δ_natural_right_assoc]
  mul_assoc := F.map_injective <| by
    simp [h_mul, ← δ_natural_left_assoc, ← δ_natural_right_assoc]

end OplaxMonoidal

variable [F.Monoidal]

/-- The image under `F` of the monoid object structure `F.monObjOfFaithful X one mul _ _` is the
monoid object structure of `F.obj X` it was built from. -/
theorem monObjObj_monObjOfFaithful [F.Faithful] (X : C) [MonObj (F.obj X)] (one : 𝟙_ C ⟶ X)
    (mul : X ⊗ X ⟶ X) (h_one : F.map one = OplaxMonoidal.η F ≫ η[F.obj X])
    (h_mul : F.map mul = δ F X X ≫ μ[F.obj X]) :
    letI := F.monObjOfFaithful X one mul h_one h_mul
    monObjObj (F := F) X = ‹MonObj (F.obj X)› :=
  MonObj.ext _ _ (by simp [h_mul])

/-- A faithful monoidal functor is injective on monoid object structures. -/
theorem monObjObj_injective [F.Faithful] (X : C) :
    Function.Injective fun _ : MonObj X ↦ monObjObj (F := F) X := by
  intro h₁ h₂ e
  refine MonObj.ext _ _ (F.map_injective ?_)
  have := congr(($e).mul)
  simpa [← cancel_epi (LaxMonoidal.μ F X X)] using this

/-- A faithful monoidal functor reflects monoid homomorphisms. -/
theorem isMonHom_map_iff [F.Faithful] {X Y : C} [MonObj X] [MonObj Y] (f : X ⟶ Y) :
    IsMonHom (F.map f) ↔ IsMonHom f := by
  refine ⟨fun h ↦ ⟨F.map_injective ?_, F.map_injective ?_⟩, fun _ ↦ inferInstance⟩
  · simpa [← cancel_epi (ε F)] using h.one_hom
  · simpa [← cancel_epi (LaxMonoidal.μ F X X)] using h.mul_hom

end Monoidal

section Braided

variable [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
  (F : C ⥤ D) [F.Braided] [F.Faithful]

/-- A faithful braided functor reflects commutativity of monoid objects. -/
theorem isCommMonObj_obj_iff (X : C) [MonObj X] : IsCommMonObj (F.obj X) ↔ IsCommMonObj X := by
  refine ⟨fun h ↦ ⟨F.map_injective ?_⟩, fun _ ↦ inferInstance⟩
  simpa [Functor.map_braiding, ← cancel_epi (LaxMonoidal.μ F X X)] using h.mul_comm

end Braided

section Cartesian

variable [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
  [F.Faithful]

/-- Pull back a group object along a faithful monoidal functor `F`, given lifts `one`, `mul` and
`inv` of the unit, the multiplication and the inverse of `F.obj X`. -/
@[simps]
abbrev grpObjOfFaithful (X : C) [GrpObj (F.obj X)] (one : 𝟙_ C ⟶ X) (mul : X ⊗ X ⟶ X)
    (inv : X ⟶ X) (h_one : F.map one = OplaxMonoidal.η F ≫ η[F.obj X])
    (h_mul : F.map mul = δ F X X ≫ μ[F.obj X]) (h_inv : F.map inv = ι[F.obj X]) :
    GrpObj X where
  __ := F.monObjOfFaithful X one mul h_one h_mul
  inv := inv
  left_inv := F.map_injective <| by
    rw [F.map_comp, F.map_comp, ← Monoidal.lift_μ, F.map_id, h_inv]
    simp [h_mul, h_one, OplaxMonoidal.η_of_cartesianMonoidalCategory]
  right_inv := F.map_injective <| by
    rw [F.map_comp, F.map_comp, ← Monoidal.lift_μ, F.map_id, h_inv]
    simp [h_mul, h_one, OplaxMonoidal.η_of_cartesianMonoidalCategory]

/-- The image under `F` of the group object structure `F.grpObjOfFaithful X one mul inv _ _ _` is
the group object structure of `F.obj X` it was built from. -/
theorem grpObjObj_grpObjOfFaithful (X : C) [GrpObj (F.obj X)] (one : 𝟙_ C ⟶ X)
    (mul : X ⊗ X ⟶ X) (inv : X ⟶ X) (h_one : F.map one = OplaxMonoidal.η F ≫ η[F.obj X])
    (h_mul : F.map mul = δ F X X ≫ μ[F.obj X]) (h_inv : F.map inv = ι[F.obj X]) :
    letI := F.grpObjOfFaithful X one mul inv h_one h_mul h_inv
    grpObjObj (F := F) (G := X) = ‹GrpObj (F.obj X)› :=
  GrpObj.ext _ _ (F.monObjObj_monObjOfFaithful X one mul h_one h_mul)

/-- A faithful monoidal functor is injective on group object structures. -/
theorem grpObjObj_injective (X : C) :
    Function.Injective fun _ : GrpObj X ↦ grpObjObj (F := F) (G := X) := by
  intro h₁ h₂ e
  exact GrpObj.ext _ _ <| F.monObjObj_injective X congr(($e).toMonObj)

end Cartesian

end CategoryTheory.Functor

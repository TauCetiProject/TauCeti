/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Monoid objects

This file provides general-purpose facts about monoid objects and their commutativity.

## Main declarations

* `TauCeti.isCommMonObj_of_grp_iso`: commutativity of a group object is preserved by isomorphism.
* `TauCeti.isCommMonObj_of_mono`: a monoid subobject of a commutative monoid object is commutative.
* `TauCeti.monObj_eq_of_mono`: a monomorphism admits at most one compatible monoid structure.
* `CategoryTheory.MonObj.isMonHom_one`: the unit of a monoid object is a monoid homomorphism
  from the trivial monoid on the tensor unit.
* `CategoryTheory.MonObj.isMonHom_mul`: the multiplication of a commutative monoid object is a
  monoid homomorphism.
-/

public section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti

universe u v

/-- A monomorphism into a monoid object admits at most one compatible monoid structure. -/
theorem monObj_eq_of_mono
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {H G : C} [MonObj G] (i : H ⟶ G) [Mono i] (a b : MonObj H)
    (ha : @IsMonHom _ _ _ H G a inferInstance i)
    (hb : @IsMonHom _ _ _ H G b inferInstance i) : a = b := by
  apply MonObj.ext
  apply (cancel_mono i).1
  exact ha.mul_hom.trans hb.mul_hom.symm

/-- Commutativity of a group object is preserved under isomorphism. -/
theorem isCommMonObj_of_grp_iso
    {C : Type u} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
    {G H : Grp C} (e : G ≅ H) (hG : IsCommMonObj G.X) : IsCommMonObj H.X := by
  let _ := hG
  constructor
  apply (cancel_mono e.inv.hom.hom).1
  simp only [Category.assoc, IsMonHom.mul_hom]
  rw [← Category.assoc, ← BraidedCategory.braiding_naturality]
  simp only [Category.assoc, IsCommMonObj.mul_comm]

/-- A subobject of a commutative monoid object is commutative whenever its inclusion is a
homomorphism. -/
theorem isCommMonObj_of_mono
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    {A B : C} [MonObj A] [MonObj B] [IsCommMonObj B]
    (i : A ⟶ B) [Mono i] [IsMonHom i] : IsCommMonObj A where
  mul_comm := by
    apply (cancel_mono i).1
    simp [IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc]

end TauCeti

namespace CategoryTheory.MonObj

open MonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (M : C) [MonObj M]

/-- The unit `𝟙_ C ⟶ M` of a monoid object is a monoid homomorphism, for the trivial monoid
structure on the tensor unit. -/
instance isMonHom_one : IsMonHom η[M] where
  mul_hom := by
    rw [MonObj.mul_def, tensorHom_def', Category.assoc, one_mul, leftUnitor_naturality]

/-- The multiplication `M ⊗ M ⟶ M` of a commutative monoid object is a monoid homomorphism. -/
instance isMonHom_mul [BraidedCategory C] [IsCommMonObj M] : IsMonHom μ[M] where
  one_hom := by
    have h := IsMonHom.mul_hom η[M]
    simp only [MonObj.mul_def] at h
    rw [tensorObj.one_def, Category.assoc, ← h, Iso.inv_hom_id_assoc]
  mul_hom := by
    rw [tensorObj.mul_def, Category.assoc, mul_mul_mul_comm]

end CategoryTheory.MonObj

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Pointwise characterization of monoid-object homomorphisms

In a cartesian monoidal category `C`, every hom-set `X ⟶ M` into a monoid object `M` carries the
pointwise monoid structure (`CategoryTheory.Hom.monoid`). A morphism `f : M ⟶ N` between monoid
objects is a monoid-object homomorphism (`CategoryTheory.IsMonHom f`) if and only if
postcomposition by `f` preserves the unit and multiplication on `X`-points for every `X : C`.
When `N` is a group object, preservation of multiplication on all `X`-points already implies
preservation of the unit (and, when `M` is also a group object, of inverses).

This is the Yoneda criterion corresponding to `CategoryTheory.isCommMonObj_iff_isMulCommutative`.

## Main results

* `CategoryTheory.isMonHom_iff_one_comp_and_mul_comp` (and its additive version
  `CategoryTheory.isAddMonHom_iff_zero_comp_and_add_comp`): `IsMonHom f` holds if and only if
  postcomposition by `f` preserves the unit and multiplication on `X`-points for every `X : C`.
* `CategoryTheory.GrpObj.isMonHom_iff_mul_comp` (and its additive version
  `CategoryTheory.AddGrpObj.isAddMonHom_iff_add_comp`): when the target is a group object,
  preservation of multiplication on `X`-points for every `X : C` already suffices.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

open scoped CategoryTheory.MonObj

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- A morphism `f : M ⟶ N` between monoid objects in a cartesian monoidal category is a
monoid-object homomorphism if and only if postcomposition by `f` preserves the unit and
multiplication on `X`-points for every `X : C`. -/
@[to_additive
/-- A morphism `f : M ⟶ N` between additive monoid objects in a cartesian monoidal category is an
additive monoid-object homomorphism if and only if postcomposition by `f` preserves zero and
addition on `X`-points for every `X : C`. -/]
theorem isMonHom_iff_one_comp_and_mul_comp {M N : C} [MonObj M] [MonObj N] (f : M ⟶ N) :
    IsMonHom f ↔
      (∀ X : C, (1 : X ⟶ M) ≫ f = 1) ∧
      (∀ (X : C) (x y : X ⟶ M), (x * y) ≫ f = x ≫ f * y ≫ f) := by
  refine ⟨fun _ ↦ ⟨fun _ ↦ MonObj.one_comp f, fun _ _ _ ↦ MonObj.mul_comp _ _ f⟩,
    fun ⟨h1, hmul⟩ ↦ ⟨?_, ?_⟩⟩
  · simpa only [MonObj.one_eq_one] using h1 (𝟙_ C)
  · simpa only [MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd] using
      hmul (M ⊗ M) (fst M M) (snd M M)

/-- A morphism `f : G ⟶ H` from a monoid object to a group object in a cartesian monoidal
category is a monoid-object homomorphism if and only if postcomposition by `f` preserves
multiplication on `X`-points for every `X : C`. -/
@[to_additive
/-- A morphism `f : G ⟶ H` from an additive monoid object to an additive group object in a
cartesian monoidal category is an additive monoid-object homomorphism if and only if
postcomposition by `f` preserves addition on `X`-points for every `X : C`. -/]
theorem GrpObj.isMonHom_iff_mul_comp {G H : C} [MonObj G] [GrpObj H] (f : G ⟶ H) :
    IsMonHom f ↔ ∀ (X : C) (x y : X ⟶ G), (x * y) ≫ f = x ≫ f * y ≫ f := by
  rw [isMonHom_iff_one_comp_and_mul_comp]
  refine ⟨fun h ↦ h.2, fun hmul ↦ ⟨fun X ↦ ?_, hmul⟩⟩
  have h1 : ((1 : X ⟶ G) ≫ f) * ((1 : X ⟶ G) ≫ f) = (1 : X ⟶ G) ≫ f := by
    rw [← hmul X 1 1, _root_.mul_one]
  exact mul_left_cancel (h1.trans (_root_.mul_one _).symm)

end CategoryTheory

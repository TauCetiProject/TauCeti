/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-!
# Monoid homomorphisms detected on points

In a cartesian monoidal category every hom-set `X ⟶ M` into a monoid object `M` is a monoid
(`CategoryTheory.MonObj.Hom.monoid`). A morphism `f : M ⟶ N` of monoid objects is a monoid
homomorphism (`IsMonHom f`) exactly when postcomposition with `f` preserves the unit and the
multiplication of these point monoids for every test object `X`. Mathlib proves the forward
direction as `MonObj.one_comp` and `MonObj.mul_comp`; this file adds the converse, which tests the
unit on the tensor unit and the multiplication on the universal pair of points
`fst M M, snd M M : M ⊗ M ⟶ M`.

For group schemes over a base `S` this is the statement that a morphism in `Over S` is a
homomorphism exactly when it is one on `T`-valued points for every `S`-scheme `T`.

## Main declarations

* `CategoryTheory.isMonHom_iff_forall_one_comp_mul_comp`: `IsMonHom f` holds exactly when
  postcomposition with `f` preserves the unit and multiplication of all point monoids. Its
  additive form is `CategoryTheory.isAddMonHom_iff_forall_zero_comp_add_comp`.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.AddMonObj

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- A morphism of monoid objects in a cartesian monoidal category is a monoid homomorphism exactly
when, for every test object `X`, postcomposition with it preserves the unit and the multiplication
of the monoid `X ⟶ M` of `X`-valued points. -/
@[to_additive /-- A morphism of additive monoid objects in a cartesian monoidal category is an
additive monoid homomorphism exactly when, for every test object `X`, postcomposition with it
preserves the zero and the addition of the additive monoid `X ⟶ M` of `X`-valued points. -/]
theorem isMonHom_iff_forall_one_comp_mul_comp {M N : C} [MonObj M] [MonObj N] (f : M ⟶ N) :
    IsMonHom f ↔ ∀ X : C, (1 : X ⟶ M) ≫ f = 1 ∧
      ∀ x y : X ⟶ M, (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
  refine ⟨fun _ X ↦ ⟨MonObj.one_comp f, fun x y ↦ MonObj.mul_comp x y f⟩, fun h ↦ ⟨?_, ?_⟩⟩
  · -- The unit is the unit point over the tensor unit.
    simpa [Hom.one_def, toUnit_unique (toUnit (𝟙_ C)) (𝟙 _)] using (h (𝟙_ C)).1
  · -- The multiplication is the product of the two universal points `fst` and `snd`.
    simpa [Hom.mul_def, lift_fst_snd, lift_fst_comp_snd_comp] using
      (h (M ⊗ M)).2 (fst M M) (snd M M)

end CategoryTheory

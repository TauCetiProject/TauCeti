/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Rigid monoidal structure on the delooping of a commutative monoid

For a commutative monoid `M`, the single-object category `CategoryTheory.SingleObj M` carries a
rigid monoidal structure in which tensoring morphisms is multiplication in `M`, the structural
isomorphisms are identities, and the unique object `SingleObj.star M` is both its own right dual
and its own left dual with unit evaluation and coevaluation.

Because `SingleObj M` does not carry a canonical global monoidal structure for arbitrary monoids,
these instances are `scoped` under `CategoryTheory.SingleObj`. They are useful for constructing
monoidal and rigid invariants by lifting into `SingleObj (Multiplicative ℕ)` or `SingleObj M`.

## Main declarations

* `CategoryTheory.SingleObj.monoidalCategory`: the monoidal structure on `SingleObj M` for a
  commutative monoid `M`.
* `CategoryTheory.SingleObj.rightRigidCategory`, `CategoryTheory.SingleObj.leftRigidCategory`,
  and `CategoryTheory.SingleObj.rigidCategory`: the rigid structure with trivial duality
  pairings on `SingleObj.star M`.
* `CategoryTheory.SingleObj.whiskerLeft_eq`, `CategoryTheory.SingleObj.whiskerRight_eq`, and
  `CategoryTheory.SingleObj.tensorHom_as_mul`: basic computation rules for whiskering and tensor
  products of morphisms.
-/

@[expose] public section

universe u

namespace CategoryTheory.SingleObj

open MonoidalCategory

variable {M : Type u} [CommMonoid M]

/-- The monoidal structure on the single-object category `SingleObj M` of a commutative monoid
`M`, with tensor product of morphisms given by multiplication in `M`. -/
scoped instance monoidalCategory : MonoidalCategory (SingleObj M) where
  tensorObj _ _ := star M
  whiskerLeft _ _ _ f := f
  whiskerRight f _ := f
  tensorHom f g := ((f : M) * (g : M) : M)
  tensorUnit := star M
  associator _ _ _ := Iso.refl _
  leftUnitor _ := Iso.refl _
  rightUnitor _ := Iso.refl _
  tensorHom_def _ _ := mul_comm _ _
  id_tensorHom_id _ _ := one_mul (1 : M)
  tensorHom_comp_tensorHom _ _ _ _ := by
    simp only [comp_as_mul]
    exact mul_mul_mul_comm _ _ _ _
  associator_naturality _ _ _ := by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact mul_assoc _ _ _
  leftUnitor_naturality _ := by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  rightUnitor_naturality _ := by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  pentagon _ _ _ _ := by
    simp only [Iso.refl_hom, Category.comp_id]
  triangle _ _ := by
    simp only [Iso.refl_hom, id_as_one, comp_as_mul]
    exact one_mul (1 : M)

open scoped CategoryTheory.SingleObj

/-- The tensor unit of `SingleObj M` is `SingleObj.star M`. -/
@[simp]
theorem tensorUnit_eq : (𝟙_ (SingleObj M)) = star M := rfl

/-- Every tensor product of objects in `SingleObj M` is `SingleObj.star M`. -/
@[simp]
theorem tensorObj_eq (X Y : SingleObj M) : X ⊗ Y = star M := rfl

/-- Left whiskering in `SingleObj M` acts as the identity on morphisms. -/
@[simp]
theorem whiskerLeft_eq (X : SingleObj M) {Y₁ Y₂ : SingleObj M} (f : Y₁ ⟶ Y₂) :
    X ◁ f = f := rfl

/-- Right whiskering in `SingleObj M` acts as the identity on morphisms. -/
@[simp]
theorem whiskerRight_eq {X₁ X₂ : SingleObj M} (f : X₁ ⟶ X₂) (Y : SingleObj M) :
    f ▷ Y = f := rfl

/-- Tensoring morphisms in `SingleObj M` is multiplication in `M`. -/
theorem tensorHom_as_mul {X₁ Y₁ X₂ Y₂ : SingleObj M} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ₘ g = (f : M) * (g : M) := rfl

/-- The associator in `SingleObj M` is the identity isomorphism. -/
@[simp]
theorem associator_eq_refl (X Y Z : SingleObj M) : α_ X Y Z = Iso.refl _ := rfl

/-- The left unitor in `SingleObj M` is the identity isomorphism. -/
@[simp]
theorem leftUnitor_eq_refl (X : SingleObj M) : λ_ X = Iso.refl _ := rfl

/-- The right unitor in `SingleObj M` is the identity isomorphism. -/
@[simp]
theorem rightUnitor_eq_refl (X : SingleObj M) : ρ_ X = Iso.refl _ := rfl

/-- The right-rigid structure on `SingleObj M`, with `SingleObj.star M` self-dual and unit
evaluation and coevaluation. -/
scoped instance rightRigidCategory : RightRigidCategory (SingleObj M) where
  rightDual _ :=
    { rightDual := star M
      exact :=
        { coevaluation' := (1 : M)
          evaluation' := (1 : M)
          coevaluation_evaluation' := by
            simp [id_as_one, comp_as_mul]
          evaluation_coevaluation' := by
            simp [id_as_one, comp_as_mul] } }

/-- The left-rigid structure on `SingleObj M`, with `SingleObj.star M` self-dual and unit
evaluation and coevaluation. -/
scoped instance leftRigidCategory : LeftRigidCategory (SingleObj M) where
  leftDual _ :=
    { leftDual := star M
      exact :=
        { coevaluation' := (1 : M)
          evaluation' := (1 : M)
          coevaluation_evaluation' := by
            simp [id_as_one, comp_as_mul]
          evaluation_coevaluation' := by
            simp [id_as_one, comp_as_mul] } }

/-- The rigid structure on `SingleObj M`. -/
scoped instance rigidCategory : RigidCategory (SingleObj M) where

/-- Right coevaluation in `SingleObj M` is `1 : M`. -/
@[simp]
theorem coevaluation_right_as_one (X : SingleObj M) :
    @ExactPairing.coevaluation (SingleObj M) _ _ X _ (RightRigidCategory.rightDual X).exact =
      (1 : M) := rfl

/-- Right evaluation in `SingleObj M` is `1 : M`. -/
@[simp]
theorem evaluation_right_as_one (X : SingleObj M) :
    @ExactPairing.evaluation (SingleObj M) _ _ X _ (RightRigidCategory.rightDual X).exact =
      (1 : M) := rfl

/-- Left coevaluation in `SingleObj M` is `1 : M`. -/
@[simp]
theorem coevaluation_left_as_one (X : SingleObj M) :
    @ExactPairing.coevaluation (SingleObj M) _ _ _ X (LeftRigidCategory.leftDual X).exact =
      (1 : M) := rfl

/-- Left evaluation in `SingleObj M` is `1 : M`. -/
@[simp]
theorem evaluation_left_as_one (X : SingleObj M) :
    @ExactPairing.evaluation (SingleObj M) _ _ _ X (LeftRigidCategory.leftDual X).exact =
      (1 : M) := rfl

end CategoryTheory.SingleObj

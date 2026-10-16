/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Functor
public import TauCeti.CategoryTheory.Monoidal.Rigid.Mate

/-!
# The right dual functor is monoidal

Mathlib's `CategoryTheory.rightDualFunctor C : C ⥤ (Cᵒᵖ)ᴹᵒᵖ` sends an object `X` of a right rigid
monoidal category to its right dual `Xᘁ` and a morphism `f` to its right adjoint mate `fᘁ`. Its
target is the monoidal opposite of the opposite category: the functor is contravariant, and it
reverses the order of tensor products, since `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ` (Mathlib's
`CategoryTheory.rightDualTensorIso`).

This file makes `rightDualFunctor C` a strong monoidal functor. Its tensor comparison is
`rightDualTensorIso` and its unit comparison is the identification `(𝟙_ C)ᘁ ≅ 𝟙_ C` of the
right dual of the unit with the unit, through the self-pairing `exactPairingUnit`. The
coherence conditions are first proved in `C`, for arbitrary objects with right duals, as
identities between mates; there the comparisons are mates of identities and every coherence
morphism is a mate of a coherence morphism (`TauCeti.CategoryTheory.Monoidal.Rigid.Mate`).

## Main declarations

* `TauCeti.rightDualTensorIso_hom_naturality`: naturality of `rightDualTensorIso`;
* `TauCeti.rightDualTensorIso_associativity`, `TauCeti.rightDualTensorIso_leftUnitality` and
  `TauCeti.rightDualTensorIso_rightUnitality`: its compatibility with the associator and the
  unitors;
* `TauCeti.rightDualFunctorCoreMonoidal` and the instance `TauCeti.rightDualFunctorMonoidal`: the
  strong monoidal structure on `rightDualFunctor C`, with structure morphisms given by
  `TauCeti.rightDualFunctor_ε`, `TauCeti.rightDualFunctor_η`, `TauCeti.rightDualFunctor_μ` and
  `TauCeti.rightDualFunctor_δ`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §2.10
-/

public section

open CategoryTheory MonoidalCategory MonoidalOpposite Opposite ExactPairing

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The comparison `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ` is natural in `X` and `Y`. -/
@[reassoc]
theorem rightDualTensorIso_hom_naturality {X X' Y Y' : C} [HasRightDual X] [HasRightDual X']
    [HasRightDual Y] [HasRightDual Y'] [HasRightDual (X ⊗ Y)] [HasRightDual (X' ⊗ Y')]
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g)ᘁ ≫ (rightDualTensorIso X Y).hom = (rightDualTensorIso X' Y').hom ≫ (gᘁ ⊗ₘ fᘁ) := by
  simp only [rightDualTensorIso, rightDualIso_hom, rightAdjointMate_eq_rightMate,
    ← rightMate_tensorHom, ← comp_rightMate, Category.id_comp, Category.comp_id]

/-- The comparison `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ` is compatible with the associators: the two ways of
identifying `(X ⊗ Y ⊗ Z)ᘁ` with `Zᘁ ⊗ Yᘁ ⊗ Xᘁ` agree. -/
@[reassoc]
theorem rightDualTensorIso_associativity (X Y Z : C) [HasRightDual X] [HasRightDual Y]
    [HasRightDual Z] [HasRightDual (X ⊗ Y)] [HasRightDual (Y ⊗ Z)] [HasRightDual ((X ⊗ Y) ⊗ Z)]
    [HasRightDual (X ⊗ Y ⊗ Z)] :
    ((α_ X Y Z).hom)ᘁ ≫ (rightDualTensorIso (X ⊗ Y) Z).hom ≫ Zᘁ ◁ (rightDualTensorIso X Y).hom =
      (rightDualTensorIso X (Y ⊗ Z)).hom ≫ (rightDualTensorIso Y Z).hom ▷ Xᘁ ≫
        (α_ Zᘁ Yᘁ Xᘁ).hom := by
  simp only [rightDualTensorIso, rightDualIso_hom, rightAdjointMate_eq_rightMate]
  rw [← rightMate_whiskerRight _ _ (HasRightDual.exact (X := Z)),
    ← rightMate_whiskerLeft _ _ (HasRightDual.exact (X := X)),
    ← rightMate_associator_hom (HasRightDual.exact (X := X)) (HasRightDual.exact (X := Y))
      (HasRightDual.exact (X := Z)),
    ← comp_rightMate, ← comp_rightMate, ← comp_rightMate, ← comp_rightMate]
  simp

/-- The mate `Xᘁ ⟶ (𝟙_ C ⊗ X)ᘁ` of the left unitor of `X`, followed by the comparison
`(𝟙_ C ⊗ X)ᘁ ≅ Xᘁ ⊗ (𝟙_ C)ᘁ` and the identification of `(𝟙_ C)ᘁ` with `𝟙_ C`, is the inverse
right unitor `Xᘁ ⟶ Xᘁ ⊗ 𝟙_ C` of `Xᘁ`. -/
theorem rightDualTensorIso_leftUnitality (X : C) [HasRightDual X] [HasRightDual (𝟙_ C)]
    [HasRightDual (𝟙_ C ⊗ X)] :
    (ρ_ Xᘁ).inv = ((λ_ X).hom)ᘁ ≫ (rightDualTensorIso (𝟙_ C) X).hom ≫
      Xᘁ ◁ (rightDualIso HasRightDual.exact exactPairingUnit).hom := by
  simp only [rightDualTensorIso, rightDualIso_hom, rightAdjointMate_eq_rightMate]
  rw [← rightMate_whiskerRight _ _ (HasRightDual.exact (X := X)),
    ← rightMate_leftUnitor_hom (HasRightDual.exact (X := X)), ← comp_rightMate, ← comp_rightMate]
  simp

/-- The mate `Xᘁ ⟶ (X ⊗ 𝟙_ C)ᘁ` of the right unitor of `X`, followed by the comparison
`(X ⊗ 𝟙_ C)ᘁ ≅ (𝟙_ C)ᘁ ⊗ Xᘁ` and the identification of `(𝟙_ C)ᘁ` with `𝟙_ C`, is the inverse
left unitor `Xᘁ ⟶ 𝟙_ C ⊗ Xᘁ` of `Xᘁ`. -/
theorem rightDualTensorIso_rightUnitality (X : C) [HasRightDual X] [HasRightDual (𝟙_ C)]
    [HasRightDual (X ⊗ 𝟙_ C)] :
    (λ_ Xᘁ).inv = ((ρ_ X).hom)ᘁ ≫ (rightDualTensorIso X (𝟙_ C)).hom ≫
      (rightDualIso HasRightDual.exact exactPairingUnit).hom ▷ Xᘁ := by
  simp only [rightDualTensorIso, rightDualIso_hom, rightAdjointMate_eq_rightMate]
  rw [← rightMate_whiskerLeft _ _ (HasRightDual.exact (X := X)),
    ← rightMate_rightUnitor_hom (HasRightDual.exact (X := X)), ← comp_rightMate, ← comp_rightMate]
  simp

variable (C) [RightRigidCategory C]

/-! In `(Cᵒᵖ)ᴹᵒᵖ`, composition and tensor products are those of `C` in the reverse order, by
definition. So after `Quiver.Hom.unmop_inj` and `Quiver.Hom.unop_inj`, each coherence condition
for `rightDualFunctor C` is definitionally the corresponding identity in `C` proved above, up to
reassociating the composites. -/

/-- The right dual functor `C ⥤ (Cᵒᵖ)ᴹᵒᵖ` of a right rigid monoidal category is strong
monoidal: the tensor comparison is `rightDualTensorIso` and the unit comparison identifies the
right dual of the unit with the unit. -/
noncomputable def rightDualFunctorCoreMonoidal : (rightDualFunctor C).CoreMonoidal where
  εIso := (mopFunctor _).mapIso
    (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).op
  μIso X Y := (mopFunctor _).mapIso (rightDualTensorIso X Y).op
  μIso_hom_natural_left f X' := by
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    have h : (rightDualTensorIso _ X').hom ≫ (X'ᘁ : C) ◁ fᘁ =
        (f ▷ X')ᘁ ≫ (rightDualTensorIso _ X').hom := by
      simpa using (rightDualTensorIso_hom_naturality f (𝟙 X')).symm
    exact h
  μIso_hom_natural_right X' f := by
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    have h : (rightDualTensorIso X' _).hom ≫ fᘁ ▷ (X'ᘁ : C) =
        (X' ◁ f)ᘁ ≫ (rightDualTensorIso X' _).hom := by
      simpa using (rightDualTensorIso_hom_naturality (𝟙 X') f).symm
    exact h
  associativity X Y Z := by
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    exact (Category.assoc _ _ _).trans
      ((rightDualTensorIso_associativity X Y Z).trans (Category.assoc _ _ _).symm)
  left_unitality X := by
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    -- The unit comparison uses the rigid structure's right dual of `𝟙_ C`, not `hasRightDualUnit`.
    exact (@rightDualTensorIso_leftUnitality C _ _ X _ (RightRigidCategory.rightDual _) _).trans
      (Category.assoc _ _ _).symm
  right_unitality X := by
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    -- The unit comparison uses the rigid structure's right dual of `𝟙_ C`, not `hasRightDualUnit`.
    exact (@rightDualTensorIso_rightUnitality C _ _ X _ (RightRigidCategory.rightDual _) _).trans
      (Category.assoc _ _ _).symm

/-- The right dual functor of a right rigid monoidal category is strong monoidal. -/
noncomputable instance rightDualFunctorMonoidal : (rightDualFunctor C).Monoidal :=
  (rightDualFunctorCoreMonoidal C).toMonoidal

open Functor.LaxMonoidal Functor.OplaxMonoidal

/-- The unit comparison of the right dual functor is the identification of the right dual of the
unit with the unit. -/
@[simp]
theorem rightDualFunctor_ε :
    ε (rightDualFunctor C) =
      (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).hom.op.mop :=
  (rfl)

/-- The inverse unit comparison of the right dual functor. -/
@[simp]
theorem rightDualFunctor_η :
    η (rightDualFunctor C) =
      (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).inv.op.mop :=
  (rfl)

/-- The tensor comparison of the right dual functor is `rightDualTensorIso`. -/
@[simp]
theorem rightDualFunctor_μ (X Y : C) :
    μ (rightDualFunctor C) X Y = (rightDualTensorIso X Y).hom.op.mop :=
  (rfl)

/-- The inverse tensor comparison of the right dual functor. -/
@[simp]
theorem rightDualFunctor_δ (X Y : C) :
    δ (rightDualFunctor C) X Y = (rightDualTensorIso X Y).inv.op.mop :=
  (rfl)

end TauCeti

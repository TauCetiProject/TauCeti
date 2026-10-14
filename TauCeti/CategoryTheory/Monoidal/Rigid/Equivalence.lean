/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Rigid.DualFunctor

/-!
# Duality as a monoidal equivalence

In a rigid monoidal category, taking right adjoint mates gives an equivalence from the category to
the monoidal opposite of its opposite. Full faithfulness follows because taking a left adjoint mate
undoes taking a right adjoint mate, while essential surjectivity follows because every object is the
right dual of its left dual.

Together with the strong monoidal structure on `CategoryTheory.rightDualFunctor`, this packages
right duality as a monoidal equivalence. The mixed double-mate identities are also useful directly:
they express the inverse relationship between left and right duality without choosing a pivotal
structure.

## Main declarations

* `CategoryTheory.leftAdjointMate_rightAdjointMate` and
  `CategoryTheory.rightAdjointMate_leftAdjointMate`: taking the opposite-handed mate recovers the
  original morphism;
* `TauCeti.rightDualFunctorFullyFaithful`: the explicit full-faithfulness structure whose preimage
  operation takes left adjoint mates;
* `TauCeti.rightDualFunctorIsEquivalence`: right duality is an equivalence; together with its
  existing `Functor.Monoidal` instance, it is a monoidal equivalence.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §2.10
-/

public section

open CategoryTheory MonoidalCategory MonoidalOpposite Opposite

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Taking the left adjoint mate of a right adjoint mate recovers the original morphism. -/
@[simp]
theorem leftAdjointMate_rightAdjointMate {X Y : C} [HasRightDual X] [HasRightDual Y]
    (f : X ⟶ Y) : leftAdjointMate (fᘁ) = f := by
  apply @ExactPairing.leftHom_ext C _ _ X (Xᘁ) Y HasRightDual.exact
  calc
    _ = η_ Y Yᘁ ≫ Y ◁ fᘁ :=
      @coevaluation_comp_leftAdjointMate C _ _ (Yᘁ) (Xᘁ)
        hasLeftDualRightDual hasLeftDualRightDual (fᘁ)
    _ = _ := coevaluation_comp_rightAdjointMate f

/-- Taking the right adjoint mate of a left adjoint mate recovers the original morphism. -/
@[simp]
theorem rightAdjointMate_leftAdjointMate {X Y : C} [HasLeftDual X] [HasLeftDual Y]
    (f : X ⟶ Y) : rightAdjointMate (leftAdjointMate f) = f := by
  apply @ExactPairing.rightHom_ext C _ _ (ᘁY) Y X HasLeftDual.exact
  calc
    _ = X ◁ leftAdjointMate f ≫ ε_ (ᘁX) X :=
      @rightAdjointMate_comp_evaluation C _ _ (ᘁY) (ᘁX)
        hasRightDualLeftDual hasRightDualLeftDual (leftAdjointMate f)
    _ = _ := leftAdjointMate_comp_evaluation f

end CategoryTheory

namespace TauCeti

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

section RightRigid

variable [RightRigidCategory C]

/-- The right dual functor is fully faithful. Its inverse on each hom-set takes left adjoint
mates. -/
def rightDualFunctorFullyFaithful : (rightDualFunctor C).FullyFaithful where
  preimage {X Y} f := by
    -- Expose the object formula through the two opposite-category wrappers so the left mate has
    -- the original objects `X` and `Y` as its endpoints.
    change mop (op Xᘁ) ⟶ mop (op Yᘁ) at f
    exact leftAdjointMate f.unmop.unop
  map_preimage {X Y} f := by
    -- Expose both the object and morphism formulas before cancelling the wrapper constructors.
    change mop (op Xᘁ) ⟶ mop (op Yᘁ) at f
    simp only [rightDualFunctor_map]
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    exact rightAdjointMate_leftAdjointMate f.unmop.unop
  preimage_map f := leftAdjointMate_rightAdjointMate f

/-- The right dual functor of a right rigid monoidal category is faithful. -/
instance rightDualFunctorFaithful : (rightDualFunctor C).Faithful :=
  (rightDualFunctorFullyFaithful C).faithful

/-- The right dual functor of a right rigid monoidal category is full. -/
instance rightDualFunctorFull : (rightDualFunctor C).Full :=
  (rightDualFunctorFullyFaithful C).full

end RightRigid

section Rigid

variable [RigidCategory C]

/-- The right dual functor of a rigid monoidal category is an equivalence of categories. -/
instance rightDualFunctorIsEquivalence : (rightDualFunctor C).IsEquivalence where
  essSurj :=
    { mem_essImage := fun X =>
        ⟨ᘁ(X.unmop.unop),
          ⟨(mopFunctor (Cᵒᵖ)).mapIso
            (rightDualIso (RightRigidCategory.rightDual (ᘁ(X.unmop.unop))).exact
              (LeftRigidCategory.leftDual (X.unmop.unop)).exact).symm.op⟩⟩ }

end Rigid

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Linear

/-!
# Tensoring with a self-inverse object

Let `L` be an object of a monoidal category `C` together with an isomorphism
`e : L ⊗ L ≅ 𝟙_ C`.  Tensoring on the right with `L` is then its own inverse up to the natural
isomorphism `(X ⊗ L) ⊗ L ≅ X ⊗ (L ⊗ L) ≅ X ⊗ 𝟙_ C ≅ X`, so it is an autoequivalence of `C`.  In
particular `L` can be moved across a morphism: `(X ⟶ Y ⊗ L) ≃ (X ⊗ L ⟶ Y)`, and this bijection is
`R`-linear when `C` is a monoidal `R`-linear category.

The typical example is a one-dimensional representation whose character squares to the trivial
character, such as the sign representation of a symmetric group: twisting by the sign moves
between the two sides of a space of intertwiners.

No compatibility between `e` and the associator is needed: `CategoryTheory.Equivalence.mk`
corrects the unit so that the triangle identities hold.  This is what distinguishes the bijection
from Mathlib's `CategoryTheory.tensorRightHomEquiv`, which needs an exact pairing
of `L` with itself, that is, evaluation and coevaluation satisfying the zigzag identities.

## Main definitions

* `CategoryTheory.MonoidalCategory.tensorRightEquivalenceOfIso`: the autoequivalence `- ⊗ L`,
  with inverse `- ⊗ L`.
* `CategoryTheory.MonoidalCategory.tensorRightHomEquivOfIso`: the bijection
  `(X ⟶ Y ⊗ L) ≃ (X ⊗ L ⟶ Y)`.
* `CategoryTheory.MonoidalCategory.tensorRightHomLinearEquivOfIso`: the same bijection, as an
  `R`-linear equivalence.
-/

public section

namespace CategoryTheory

namespace MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C] {L : C}

/-- **Tensoring on the right with an object `L` with `L ⊗ L ≅ 𝟙_ C` is an autoequivalence of `C`,
with inverse again `- ⊗ L`.**  The counit is `(X ⊗ L) ⊗ L ≅ X ⊗ (L ⊗ L) ≅ X ⊗ 𝟙_ C ≅ X`. -/
noncomputable def tensorRightEquivalenceOfIso (e : L ⊗ L ≅ 𝟙_ C) : C ≌ C :=
  Equivalence.mk (tensorRight L) (tensorRight L)
    ((tensorRightTensor L L).symm ≪≫ (tensoringRight C).mapIso e ≪≫ rightUnitorNatIso C).symm
    ((tensorRightTensor L L).symm ≪≫ (tensoringRight C).mapIso e ≪≫ rightUnitorNatIso C)

@[simp]
theorem tensorRightEquivalenceOfIso_functor (e : L ⊗ L ≅ 𝟙_ C) :
    (tensorRightEquivalenceOfIso e).functor = tensorRight L :=
  (rfl)

@[simp]
theorem tensorRightEquivalenceOfIso_inverse (e : L ⊗ L ≅ 𝟙_ C) :
    (tensorRightEquivalenceOfIso e).inverse = tensorRight L :=
  (rfl)

/-- **An object `L` with `L ⊗ L ≅ 𝟙_ C` moves across a morphism**: `f : X ⟶ Y ⊗ L` corresponds to
`f ▷ L` followed by `(Y ⊗ L) ⊗ L ≅ Y`. -/
noncomputable def tensorRightHomEquivOfIso (e : L ⊗ L ≅ 𝟙_ C) (X Y : C) :
    (X ⟶ Y ⊗ L) ≃ (X ⊗ L ⟶ Y) :=
  ((tensorRightEquivalenceOfIso e).fullyFaithfulFunctor.homEquiv).trans
    (((tensorRightEquivalenceOfIso e).counitIso.app Y).homToEquiv)

theorem tensorRightHomEquivOfIso_apply (e : L ⊗ L ≅ 𝟙_ C) {X Y : C} (f : X ⟶ Y ⊗ L) :
    tensorRightHomEquivOfIso e X Y f = f ▷ L ≫ (α_ Y L L).hom ≫ Y ◁ e.hom ≫ (ρ_ Y).hom := by
  simp [tensorRightHomEquivOfIso, Iso.homToEquiv, tensorRightEquivalenceOfIso,
    Functor.FullyFaithful.homEquiv, Equivalence.mk]

section Linear

variable (R : Type*) [Semiring R] [Preadditive C] [Linear R C] [MonoidalPreadditive C]
  [MonoidalLinear R C]

/-- **The bijection `(X ⟶ Y ⊗ L) ≃ (X ⊗ L ⟶ Y)` of `tensorRightHomEquivOfIso` is `R`-linear** in a
monoidal `R`-linear category. -/
noncomputable def tensorRightHomLinearEquivOfIso (e : L ⊗ L ≅ 𝟙_ C) (X Y : C) :
    (X ⟶ Y ⊗ L) ≃ₗ[R] (X ⊗ L ⟶ Y) where
  __ := tensorRightHomEquivOfIso e X Y
  map_add' f g := by simp [tensorRightHomEquivOfIso_apply]
  map_smul' r f := by simp [tensorRightHomEquivOfIso_apply]

@[simp]
theorem coe_tensorRightHomLinearEquivOfIso (e : L ⊗ L ≅ 𝟙_ C) (X Y : C) :
    ⇑(tensorRightHomLinearEquivOfIso R e X Y) = tensorRightHomEquivOfIso e X Y :=
  (rfl)

theorem tensorRightHomLinearEquivOfIso_apply (e : L ⊗ L ≅ 𝟙_ C) {X Y : C} (f : X ⟶ Y ⊗ L) :
    tensorRightHomLinearEquivOfIso R e X Y f =
      f ▷ L ≫ (α_ Y L L).hom ≫ Y ◁ e.hom ≫ (ρ_ Y).hom :=
  tensorRightHomEquivOfIso_apply e f

end Linear

end MonoidalCategory

end CategoryTheory

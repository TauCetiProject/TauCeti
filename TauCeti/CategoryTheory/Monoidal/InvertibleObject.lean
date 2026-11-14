/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Linear

/-!
# Tensoring with an invertible object

Let `L` and `M` be objects of a monoidal category `C` together with isomorphisms
`e₁ : L ⊗ M ≅ 𝟙_ C` and `e₂ : M ⊗ L ≅ 𝟙_ C`.  Tensoring on the right with `L` is then inverse to
tensoring on the right with `M`, up to the natural isomorphisms
`X ≅ X ⊗ 𝟙_ C ≅ X ⊗ (L ⊗ M) ≅ (X ⊗ L) ⊗ M` and `(X ⊗ M) ⊗ L ≅ X ⊗ (M ⊗ L) ≅ X ⊗ 𝟙_ C ≅ X`, so it
is an autoequivalence of `C`.  In particular `L` can be moved across a morphism:
`(X ⟶ Y ⊗ M) ≃ (X ⊗ L ⟶ Y)`, and this bijection is `R`-linear when `C` is a monoidal `R`-linear
category.

The typical example is a pair of one-dimensional representations whose characters multiply to the
trivial character, such as the sign representation of a symmetric group paired with itself:
twisting by the sign moves between the two sides of a space of intertwiners.

No compatibility between `e₁`, `e₂` and the associator is needed:
`CategoryTheory.Equivalence.mk` corrects the unit so that the triangle identities hold.  This is
what distinguishes the bijection from Mathlib's `CategoryTheory.tensorRightHomEquiv`, which needs
an exact pairing of `L` with `M`, that is, evaluation and coevaluation satisfying the zigzag
identities.  For the same reason only the counit has a closed form; the unit is Mathlib's
`CategoryTheory.Equivalence.adjointifyη` of `e₁`, and the inverse bijection is read through it
(`CategoryTheory.MonoidalCategory.tensorRightHomEquivOfIso_symm_apply`).

## Main definitions

* `CategoryTheory.MonoidalCategory.tensorRightEquivalenceOfIso`: the autoequivalence `- ⊗ L`,
  with inverse `- ⊗ M`.
* `CategoryTheory.MonoidalCategory.tensorRightHomEquivOfIso`: the bijection
  `(X ⟶ Y ⊗ M) ≃ (X ⊗ L ⟶ Y)`.
* `CategoryTheory.MonoidalCategory.tensorRightHomLinearEquivOfIso`: the same bijection, as an
  `R`-linear equivalence.
-/

public section

namespace CategoryTheory

namespace MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C] {L M : C}

/-- **Tensoring on the right with an object `L` with inverse `M` is an autoequivalence of `C`,
with inverse `- ⊗ M`.**  The counit is `(X ⊗ M) ⊗ L ≅ X ⊗ (M ⊗ L) ≅ X ⊗ 𝟙_ C ≅ X`, and the unit
is the adjointification of `X ≅ X ⊗ 𝟙_ C ≅ X ⊗ (L ⊗ M) ≅ (X ⊗ L) ⊗ M`.

The body is exposed so that `functor` and `inverse` reduce to `tensorRight L` and
`tensorRight M` outside this file: the unit and counit lemmas below only typecheck after that
reduction. -/
@[expose]
noncomputable def tensorRightEquivalenceOfIso (e₁ : L ⊗ M ≅ 𝟙_ C) (e₂ : M ⊗ L ≅ 𝟙_ C) : C ≌ C :=
  Equivalence.mk (tensorRight L) (tensorRight M)
    ((tensorRightTensor L M).symm ≪≫ (tensoringRight C).mapIso e₁ ≪≫ rightUnitorNatIso C).symm
    ((tensorRightTensor M L).symm ≪≫ (tensoringRight C).mapIso e₂ ≪≫ rightUnitorNatIso C)

@[simp]
theorem tensorRightEquivalenceOfIso_functor (e₁ : L ⊗ M ≅ 𝟙_ C) (e₂ : M ⊗ L ≅ 𝟙_ C) :
    (tensorRightEquivalenceOfIso e₁ e₂).functor = tensorRight L :=
  (rfl)

@[simp]
theorem tensorRightEquivalenceOfIso_inverse (e₁ : L ⊗ M ≅ 𝟙_ C) (e₂ : M ⊗ L ≅ 𝟙_ C) :
    (tensorRightEquivalenceOfIso e₁ e₂).inverse = tensorRight M :=
  (rfl)

/-- The counit of `tensorRightEquivalenceOfIso` is `(X ⊗ M) ⊗ L ≅ X ⊗ (M ⊗ L) ≅ X ⊗ 𝟙_ C ≅ X`. -/
@[simp]
theorem tensorRightEquivalenceOfIso_counitIso_hom_app (e₁ : L ⊗ M ≅ 𝟙_ C) (e₂ : M ⊗ L ≅ 𝟙_ C)
    (X : C) :
    (tensorRightEquivalenceOfIso e₁ e₂).counitIso.hom.app X =
      (α_ X M L).hom ≫ X ◁ e₂.hom ≫ (ρ_ X).hom := by
  simp [tensorRightEquivalenceOfIso, Equivalence.mk]

/-- The inverse counit of `tensorRightEquivalenceOfIso` is
`X ≅ X ⊗ 𝟙_ C ≅ X ⊗ (M ⊗ L) ≅ (X ⊗ M) ⊗ L`. -/
@[simp]
theorem tensorRightEquivalenceOfIso_counitIso_inv_app (e₁ : L ⊗ M ≅ 𝟙_ C) (e₂ : M ⊗ L ≅ 𝟙_ C)
    (X : C) :
    (tensorRightEquivalenceOfIso e₁ e₂).counitIso.inv.app X =
      (ρ_ X).inv ≫ X ◁ e₂.inv ≫ (α_ X M L).inv := by
  simp [tensorRightEquivalenceOfIso, Equivalence.mk]

/-- **An invertible object `L` with inverse `M` moves across a morphism**: `f : X ⟶ Y ⊗ M`
corresponds to `f ▷ L` followed by `(Y ⊗ M) ⊗ L ≅ Y`. -/
noncomputable def tensorRightHomEquivOfIso (e₁ : L ⊗ M ≅ 𝟙_ C) (e₂ : M ⊗ L ≅ 𝟙_ C) (X Y : C) :
    (X ⟶ Y ⊗ M) ≃ (X ⊗ L ⟶ Y) :=
  ((tensorRightEquivalenceOfIso e₁ e₂).fullyFaithfulFunctor.homEquiv).trans
    (((tensorRightEquivalenceOfIso e₁ e₂).counitIso.app Y).homToEquiv)

theorem tensorRightHomEquivOfIso_apply (e₁ : L ⊗ M ≅ 𝟙_ C) (e₂ : M ⊗ L ≅ 𝟙_ C) {X Y : C}
    (f : X ⟶ Y ⊗ M) :
    tensorRightHomEquivOfIso e₁ e₂ X Y f = f ▷ L ≫ (α_ Y M L).hom ≫ Y ◁ e₂.hom ≫ (ρ_ Y).hom := by
  simp [tensorRightHomEquivOfIso, Iso.homToEquiv, tensorRightEquivalenceOfIso,
    Functor.FullyFaithful.homEquiv, Equivalence.mk]

/-- The inverse of `tensorRightHomEquivOfIso` sends `g : X ⊗ L ⟶ Y` to the preimage under
`- ⊗ L` of `g` followed by the inverse counit `Y ≅ (Y ⊗ M) ⊗ L`, read through the unit of
`tensorRightEquivalenceOfIso`. -/
theorem tensorRightHomEquivOfIso_symm_apply (e₁ : L ⊗ M ≅ 𝟙_ C) (e₂ : M ⊗ L ≅ 𝟙_ C) {X Y : C}
    (g : X ⊗ L ⟶ Y) :
    (tensorRightHomEquivOfIso e₁ e₂ X Y).symm g =
      (tensorRightEquivalenceOfIso e₁ e₂).unitIso.hom.app X ≫
        (g ≫ (ρ_ Y).inv ≫ Y ◁ e₂.inv ≫ (α_ Y M L).inv) ▷ M ≫
          (tensorRightEquivalenceOfIso e₁ e₂).unitIso.inv.app (Y ⊗ M) := by
  simp [tensorRightHomEquivOfIso, Iso.homToEquiv, tensorRightEquivalenceOfIso,
    Functor.FullyFaithful.homEquiv, Equivalence.mk, Equivalence.fullyFaithfulFunctor]

section Linear

variable (R : Type*) [Semiring R] [Preadditive C] [Linear R C] [MonoidalPreadditive C]
  [MonoidalLinear R C]

/-- **The bijection `(X ⟶ Y ⊗ M) ≃ (X ⊗ L ⟶ Y)` of `tensorRightHomEquivOfIso` is `R`-linear** in a
monoidal `R`-linear category. -/
noncomputable def tensorRightHomLinearEquivOfIso (e₁ : L ⊗ M ≅ 𝟙_ C) (e₂ : M ⊗ L ≅ 𝟙_ C)
    (X Y : C) : (X ⟶ Y ⊗ M) ≃ₗ[R] (X ⊗ L ⟶ Y) where
  __ := tensorRightHomEquivOfIso e₁ e₂ X Y
  map_add' f g := by simp [tensorRightHomEquivOfIso_apply]
  map_smul' r f := by simp [tensorRightHomEquivOfIso_apply]

@[simp]
theorem coe_tensorRightHomLinearEquivOfIso (e₁ : L ⊗ M ≅ 𝟙_ C) (e₂ : M ⊗ L ≅ 𝟙_ C) (X Y : C) :
    ⇑(tensorRightHomLinearEquivOfIso R e₁ e₂ X Y) = tensorRightHomEquivOfIso e₁ e₂ X Y :=
  (rfl)

@[simp]
theorem coe_tensorRightHomLinearEquivOfIso_symm (e₁ : L ⊗ M ≅ 𝟙_ C) (e₂ : M ⊗ L ≅ 𝟙_ C)
    (X Y : C) :
    ⇑(tensorRightHomLinearEquivOfIso R e₁ e₂ X Y).symm =
      (tensorRightHomEquivOfIso e₁ e₂ X Y).symm :=
  (rfl)

@[simp]
theorem toEquiv_tensorRightHomLinearEquivOfIso (e₁ : L ⊗ M ≅ 𝟙_ C) (e₂ : M ⊗ L ≅ 𝟙_ C)
    (X Y : C) :
    (tensorRightHomLinearEquivOfIso R e₁ e₂ X Y).toEquiv = tensorRightHomEquivOfIso e₁ e₂ X Y :=
  (rfl)

theorem tensorRightHomLinearEquivOfIso_apply (e₁ : L ⊗ M ≅ 𝟙_ C) (e₂ : M ⊗ L ≅ 𝟙_ C) {X Y : C}
    (f : X ⟶ Y ⊗ M) :
    tensorRightHomLinearEquivOfIso R e₁ e₂ X Y f =
      f ▷ L ≫ (α_ Y M L).hom ≫ Y ◁ e₂.hom ≫ (ρ_ Y).hom :=
  tensorRightHomEquivOfIso_apply e₁ e₂ f

theorem tensorRightHomLinearEquivOfIso_symm_apply (e₁ : L ⊗ M ≅ 𝟙_ C) (e₂ : M ⊗ L ≅ 𝟙_ C)
    {X Y : C} (g : X ⊗ L ⟶ Y) :
    (tensorRightHomLinearEquivOfIso R e₁ e₂ X Y).symm g =
      (tensorRightEquivalenceOfIso e₁ e₂).unitIso.hom.app X ≫
        (g ≫ (ρ_ Y).inv ≫ Y ◁ e₂.inv ≫ (α_ Y M L).inv) ▷ M ≫
          (tensorRightEquivalenceOfIso e₁ e₂).unitIso.inv.app (Y ⊗ M) :=
  tensorRightHomEquivOfIso_symm_apply e₁ e₂ g

end Linear

end MonoidalCategory

end CategoryTheory

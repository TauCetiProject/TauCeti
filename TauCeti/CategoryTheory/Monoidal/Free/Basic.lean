/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Free.Basic

/-!
# Evaluation and substitution of formal tensor words

Basic injectivity, evaluation, congruence, identity, and composition lemmas for
`CategoryTheory.FreeMonoidalCategory.projectObj`, which evaluates formal parenthesized tensor words
in an arbitrary (not necessarily strict) monoidal category (and in particular substitutes tensor
words for letters when the target is another free monoidal category).

## Main results

* `CategoryTheory.FreeMonoidalCategory.of_injective` and
  `CategoryTheory.FreeMonoidalCategory.of_inj`: the generator inclusion `FreeMonoidalCategory.of`
  is injective.
* `CategoryTheory.FreeMonoidalCategory.tensor_injective` and
  `CategoryTheory.FreeMonoidalCategory.tensorObj_inj`: formal tensor product of words is injective
  in both factors.
* `CategoryTheory.FreeMonoidalCategory.projectObj_tensorUnit` and
  `CategoryTheory.FreeMonoidalCategory.projectObj_tensorObj`: `@[simp]` evaluation rules on the
  monoidal unit and tensor products.
* `CategoryTheory.FreeMonoidalCategory.projectObj_congr`: pointwise equal generator maps evaluate
  identically on every tensor word.
* `CategoryTheory.FreeMonoidalCategory.projectObj_of`: interpreting a word by its own letters
  recovers the word.
* `CategoryTheory.FreeMonoidalCategory.projectObj_projectObj` and
  `CategoryTheory.FreeMonoidalCategory.projectObj_projectObj_of_comp`: interpreting a word after
  replacing its letters by words agrees with interpreting directly along the evaluated generator
  map, without requiring strictness of `D`.
-/

public section

universe u u' u'' v''

namespace CategoryTheory.FreeMonoidalCategory

open MonoidalCategory

section Injectivity

variable {C : Type u}

/-- The inclusion of generators into formal tensor words is injective. -/
theorem of_injective : Function.Injective (@FreeMonoidalCategory.of C) := by
  intro a b h
  cases h
  rfl

@[simp]
theorem of_inj {a b : C} : FreeMonoidalCategory.of a = FreeMonoidalCategory.of b ↔ a = b :=
  of_injective.eq_iff

/-- Formal tensor product of words is injective in both factors. -/
theorem tensor_injective : Function.Injective2 (@FreeMonoidalCategory.tensor C) := by
  intro X₁ Y₁ X₂ Y₂ h
  cases h
  exact ⟨rfl, rfl⟩

@[simp]
theorem tensorObj_inj {X₁ Y₁ X₂ Y₂ : FreeMonoidalCategory C} :
    X₁ ⊗ Y₁ = X₂ ⊗ Y₂ ↔ X₁ = X₂ ∧ Y₁ = Y₂ :=
  ⟨fun h ↦ tensor_injective h, fun ⟨hX, hY⟩ ↦ by rw [hX, hY]⟩

end Injectivity

section ProjectObj

variable {C : Type u} {C' : Type u'} {D : Type u''} [Category.{v''} D] [MonoidalCategory D]

@[simp]
theorem projectObj_tensorUnit (f : C → D) : projectObj f (𝟙_ (FreeMonoidalCategory C)) = 𝟙_ D :=
  rfl

@[simp]
theorem projectObj_tensorObj (f : C → D) (X Y : FreeMonoidalCategory C) :
    projectObj f (X ⊗ Y) = projectObj f X ⊗ projectObj f Y :=
  rfl

/-- Pointwise equal generator maps evaluate identically on every formal tensor word. -/
theorem projectObj_congr {f g : C → D} (h : ∀ a, f a = g a) (X : FreeMonoidalCategory C) :
    projectObj f X = projectObj g X := by
  induction X with
  | of a => exact h a
  | unit => rfl
  | tensor X Y ihX ihY => exact congrArg₂ (· ⊗ ·) ihX ihY

/-- Interpreting a tensor word by its own letters recovers the word. -/
@[simp]
theorem projectObj_of (X : FreeMonoidalCategory C) : projectObj of X = X := by
  induction X with
  | of a => rfl
  | unit => rfl
  | tensor X Y hX hY => exact congrArg₂ tensor hX hY

/-- Interpreting a tensor word after replacing its letters by tensor words `h` is interpreting it
by the interpretations of those words. -/
theorem projectObj_projectObj (f : C' → D) (h : C → FreeMonoidalCategory C')
    (X : FreeMonoidalCategory C) :
    projectObj f (projectObj h X) = projectObj (fun a ↦ projectObj f (h a)) X := by
  induction X with
  | of a => rfl
  | unit => rfl
  | tensor X Y hX hY => exact congrArg₂ (· ⊗ ·) hX hY

/-- Evaluating after renaming generators by `h : C → C'` agrees with precomposing `f` with `h`. -/
theorem projectObj_projectObj_of_comp (f : C' → D) (h : C → C') (X : FreeMonoidalCategory C) :
    projectObj f (projectObj (.of ∘ h) X) = projectObj (f ∘ h) X :=
  projectObj_projectObj f (.of ∘ h) X

end ProjectObj

end CategoryTheory.FreeMonoidalCategory

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Free.Basic

/-!
# Evaluation of formal tensor words

Basic injectivity, computation, congruence, identity, and composition lemmas for
`CategoryTheory.FreeMonoidalCategory.projectObj`, which evaluates formal parenthesized tensor words
in an arbitrary (not necessarily strict) monoidal category.

## Main results

* `CategoryTheory.FreeMonoidalCategory.of_injective` and
  `CategoryTheory.FreeMonoidalCategory.of_inj`: the generator inclusion `FreeMonoidalCategory.of`
  is injective.
* `CategoryTheory.FreeMonoidalCategory.tensor_injective` and
  `CategoryTheory.FreeMonoidalCategory.tensorObj_inj`: formal tensor product of words is injective
  in both factors.
* `CategoryTheory.FreeMonoidalCategory.projectObj_of`,
  `CategoryTheory.FreeMonoidalCategory.projectObj_tensorUnit`,
  `CategoryTheory.FreeMonoidalCategory.projectObj_tensorObj`: `@[simp]` evaluation rules on
  generators, the monoidal unit, and tensor products.
* `CategoryTheory.FreeMonoidalCategory.projectObj_of_self`: evaluating along
  `FreeMonoidalCategory.of` is the identity on formal tensor words.
* `CategoryTheory.FreeMonoidalCategory.projectObj_projectObj` and
  `CategoryTheory.FreeMonoidalCategory.projectObj_projectObj_of_comp`: evaluating a substituted
  tensor word in a monoidal category `D` agrees with evaluating directly along the composite
  generator map, without requiring strictness of `D`.
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
theorem projectObj_of (f : C → D) (a : C) : projectObj f (.of a) = f a :=
  rfl

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

/-- Evaluating a formal tensor word along `FreeMonoidalCategory.of` returns the same word. -/
@[simp]
theorem projectObj_of_self (X : FreeMonoidalCategory C) :
    projectObj FreeMonoidalCategory.of X = X := by
  induction X with
  | of _ => rfl
  | unit => rfl
  | tensor _ _ ihX ihY => exact congrArg₂ tensor ihX ihY

/-- Evaluating a formal tensor word obtained by replacing generators with formal tensor words in
`C'` agrees with evaluating directly along the evaluated generator map, in any (not necessarily
strict) monoidal category `D`. -/
theorem projectObj_projectObj (f : C' → D) (g : C → FreeMonoidalCategory C')
    (X : FreeMonoidalCategory C) :
    projectObj f (projectObj g X) = projectObj (fun a ↦ projectObj f (g a)) X := by
  induction X with
  | of _ => rfl
  | unit => rfl
  | tensor _ _ ihX ihY => exact congrArg₂ (· ⊗ ·) ihX ihY

/-- Evaluating after renaming generators by `h : C → C'` agrees with precomposing `f` with `h`. -/
theorem projectObj_projectObj_of_comp (f : C' → D) (h : C → C') (X : FreeMonoidalCategory C) :
    projectObj f (projectObj (.of ∘ h) X) = projectObj (f ∘ h) X :=
  projectObj_projectObj f (.of ∘ h) X

end ProjectObj

end CategoryTheory.FreeMonoidalCategory

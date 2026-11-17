/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Quotient

/-!
# Iterated quotient categories

Given two morphism relations `r₁ r₂ : HomRel C` on a category `C`, forming the quotient
`CategoryTheory.Quotient r₁` and then quotienting by the image relation `r₁.mapQuotient r₂`
yields a category isomorphic (and in particular equivalent) to the single quotient
`CategoryTheory.Quotient (r₁.sup r₂)` by the union `r₁ ∨ r₂`.

## Main definitions and results

* `HomRel.sup r₁ r₂`: the pointwise disjunction of two morphism relations on a quiver.
* `HomRel.mapQuotient r₁ r₂`: the image of `r₂` in `CategoryTheory.Quotient r₁`, relating the
  classes of `r₂`-related morphisms.
* `CategoryTheory.Quotient.iteratedToSup r₁ r₂` and `CategoryTheory.Quotient.supToIterated r₁ r₂`:
  mutually inverse functors between `Quotient (r₁.mapQuotient r₂)` and `Quotient (r₁.sup r₂)`
  (`iteratedToSup_comp_supToIterated`, `supToIterated_comp_iteratedToSup`), packaged as an
  equivalence `CategoryTheory.Quotient.iteratedEquiv r₁ r₂`.
-/

public section

universe v u

open CategoryTheory

namespace HomRel

/-- The pointwise union (disjunction) of two morphism relations on a quiver. -/
@[expose] def sup {C : Type u} [Quiver.{v} C] (r₁ r₂ : HomRel C) : HomRel C :=
  fun _ _ f g ↦ r₁ f g ∨ r₂ f g

@[simp]
theorem sup_iff {C : Type u} [Quiver.{v} C] (r₁ r₂ : HomRel C) {X Y : C} (f g : X ⟶ Y) :
    r₁.sup r₂ f g ↔ r₁ f g ∨ r₂ f g :=
  Iff.rfl

/-- The image of a morphism relation `r₂` on `C` in the quotient category `Quotient r₁`: two
morphisms in `Quotient r₁` are related when they are the classes of `r₂`-related morphisms in
`C`. -/
@[expose] def mapQuotient {C : Type u} [Category.{v} C] (r₁ r₂ : HomRel C) :
    HomRel (CategoryTheory.Quotient r₁) :=
  fun X Y f g ↦ ∃ f' g' : X.as ⟶ Y.as,
    (CategoryTheory.Quotient.functor r₁).map f' = f ∧
      (CategoryTheory.Quotient.functor r₁).map g' = g ∧ r₂ f' g'

@[simp]
theorem mapQuotient_iff {C : Type u} [Category.{v} C] (r₁ r₂ : HomRel C)
    {X Y : CategoryTheory.Quotient r₁} (f g : X ⟶ Y) :
    r₁.mapQuotient r₂ f g ↔
      ∃ f' g' : X.as ⟶ Y.as,
        (CategoryTheory.Quotient.functor r₁).map f' = f ∧
          (CategoryTheory.Quotient.functor r₁).map g' = g ∧ r₂ f' g' :=
  Iff.rfl

/-- Related morphisms in `C` have related classes in `Quotient r₁`. -/
theorem mapQuotient_of {C : Type u} [Category.{v} C] (r₁ : HomRel C) {r₂ : HomRel C}
    {X Y : C} {f g : X ⟶ Y} (h : r₂ f g) :
    r₁.mapQuotient r₂ ((CategoryTheory.Quotient.functor r₁).map f)
      ((CategoryTheory.Quotient.functor r₁).map g) :=
  ⟨f, g, rfl, rfl, h⟩

end HomRel

namespace CategoryTheory.Quotient

variable {C : Type u} [Category.{v} C] (r₁ r₂ : HomRel C)

/-- The canonical functor from the iterated quotient `Quotient (r₁.mapQuotient r₂)` to the single
quotient `Quotient (r₁.sup r₂)`. -/
-- Exposed so monoidal and braided structures on `lift` descend directly to this functor.
@[expose] def iteratedToSup : Quotient (r₁.mapQuotient r₂) ⥤ Quotient (r₁.sup r₂) :=
  lift (r₁.mapQuotient r₂)
    (lift r₁ (functor (r₁.sup r₂)) fun _ _ _ _ h ↦ Quotient.sound _ (.inl h))
    fun _ _ _ _ ⟨_, _, hf, hg, h⟩ ↦ by
      rw [← hf, ← hg]
      exact Quotient.sound _ (.inr h)

/-- The canonical functor from the single quotient `Quotient (r₁.sup r₂)` to the iterated quotient
`Quotient (r₁.mapQuotient r₂)`. -/
@[expose] def supToIterated : Quotient (r₁.sup r₂) ⥤ Quotient (r₁.mapQuotient r₂) :=
  lift (r₁.sup r₂) (functor r₁ ⋙ functor (r₁.mapQuotient r₂)) fun _ _ _ _ h ↦ by
    rcases h with h₁ | h₂
    · exact congrArg (functor (r₁.mapQuotient r₂)).map (Quotient.sound r₁ h₁)
    · exact Quotient.sound (r₁.mapQuotient r₂) (HomRel.mapQuotient_of r₁ h₂)

theorem functor_comp_iteratedToSup :
    functor r₁ ⋙ functor (r₁.mapQuotient r₂) ⋙ iteratedToSup r₁ r₂ = functor (r₁.sup r₂) :=
  rfl

theorem functor_comp_supToIterated :
    functor (r₁.sup r₂) ⋙ supToIterated r₁ r₂ = functor r₁ ⋙ functor (r₁.mapQuotient r₂) :=
  rfl

@[simp]
theorem iteratedToSup_obj (X : C) :
    (iteratedToSup r₁ r₂).obj ((functor (r₁.mapQuotient r₂)).obj ((functor r₁).obj X)) =
      (functor (r₁.sup r₂)).obj X :=
  rfl

@[simp]
theorem iteratedToSup_map {X Y : C} (f : X ⟶ Y) :
    (iteratedToSup r₁ r₂).map ((functor (r₁.mapQuotient r₂)).map ((functor r₁).map f)) =
      (functor (r₁.sup r₂)).map f :=
  rfl

@[simp]
theorem supToIterated_obj (X : C) :
    (supToIterated r₁ r₂).obj ((functor (r₁.sup r₂)).obj X) =
      (functor (r₁.mapQuotient r₂)).obj ((functor r₁).obj X) :=
  rfl

@[simp]
theorem supToIterated_map {X Y : C} (f : X ⟶ Y) :
    (supToIterated r₁ r₂).map ((functor (r₁.sup r₂)).map f) =
      (functor (r₁.mapQuotient r₂)).map ((functor r₁).map f) :=
  rfl

/-- Passing from the iterated quotient to the combined quotient and back is the identity functor. -/
theorem iteratedToSup_comp_supToIterated :
    iteratedToSup r₁ r₂ ⋙ supToIterated r₁ r₂ = 𝟭 _ := by
  apply lift_unique' (r₁.mapQuotient r₂)
  apply lift_unique' r₁
  rfl

/-- Passing from the combined quotient to the iterated quotient and back is the identity functor. -/
theorem supToIterated_comp_iteratedToSup :
    supToIterated r₁ r₂ ⋙ iteratedToSup r₁ r₂ = 𝟭 _ := by
  apply lift_unique' (r₁.sup r₂)
  rfl

/-- Quotienting first by `r₁` and then by the image of `r₂` is equivalent to quotienting by
`r₁.sup r₂`. -/
@[expose] def iteratedEquiv : Quotient (r₁.mapQuotient r₂) ≌ Quotient (r₁.sup r₂) where
  functor := iteratedToSup r₁ r₂
  inverse := supToIterated r₁ r₂
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) fun {X Y} f ↦ by
    obtain ⟨f, rfl⟩ := (functor (r₁.mapQuotient r₂)).map_surjective f
    obtain ⟨f, rfl⟩ := (functor r₁).map_surjective f
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) fun {X Y} f ↦ by
    obtain ⟨f, rfl⟩ := (functor (r₁.sup r₂)).map_surjective f
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  functor_unitIso_comp _ := Category.comp_id _

end CategoryTheory.Quotient

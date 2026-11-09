/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Basic
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Effective epimorphic families of types

A family of functions `π a : X a → B` is an effective epimorphic family in the category of types
exactly when it is jointly surjective (`CategoryTheory.Types.effectiveEpiFamily_iff`).

A jointly surjective family is effective: a family `e a : X a → W` compatible with the relations
`π a₁ x₁ = π a₂ x₂` descends to `B` by evaluating `e` at any preimage. Conversely, an effective
epimorphic family is jointly epimorphic, and the two maps from `B` to propositions, constantly
true and membership in the joint image, agree after composing with every `π a`.
-/

public section

universe u

namespace CategoryTheory.Types

variable {α : Type*} {B : Type u} (X : α → Type u) (π : (a : α) → X a ⟶ B)

/-- The descent data of a jointly surjective family of functions: a compatible family is
evaluated at a chosen preimage. -/
noncomputable def effectiveEpiFamilyStructOfSurjective (hπ : ∀ b, ∃ a x, π a x = b) :
    EffectiveEpiFamilyStruct X π where
  desc {W} e _ := TypeCat.ofHom fun b ↦ e (hπ b).choose (hπ b).choose_spec.choose
  fac {W} e h a := by
    ext x
    have hb := (hπ (π a x)).choose_spec.choose_spec
    exact ConcreteCategory.congr_hom (h _ _ (homOfElement (hπ (π a x)).choose_spec.choose)
      (homOfElement x) (ConcreteCategory.hom_ext _ _ fun _ ↦ hb)) PUnit.unit
  uniq {W} e h m hm := by
    ext b
    have hb := (hπ b).choose_spec.choose_spec
    simp only [← hm]
    exact congrArg m hb.symm

/-- In the category of types, a family of functions is effective epimorphic if and only if it is
jointly surjective. -/
theorem effectiveEpiFamily_iff : EffectiveEpiFamily X π ↔ ∀ b, ∃ a x, π a x = b := by
  refine ⟨fun _ ↦ ?_, fun hπ ↦ ⟨⟨effectiveEpiFamilyStructOfSurjective X π hπ⟩⟩⟩
  have h := EffectiveEpiFamily.hom_ext X π (W := ULift.{u} Prop)
    (TypeCat.ofHom fun _ ↦ ULift.up True) (TypeCat.ofHom fun b ↦ ULift.up (∃ a x, π a x = b))
    (fun a ↦ ConcreteCategory.hom_ext _ _ fun x ↦ by simpa using ⟨a, x, rfl⟩)
  intro b
  simpa using congrArg ULift.down (ConcreteCategory.congr_hom h b)

end CategoryTheory.Types

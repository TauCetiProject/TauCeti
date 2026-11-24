/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Properties holding eventually in a cofiltered category

In a cofiltered category, a property of morphisms into a fixed object `i` which is stable under
precomposition holds *eventually* once it holds for some morphism into `i`. Two such properties
which each hold eventually hold together eventually
(`CategoryTheory.IsCofiltered.exists_and_of_stable`), so finitely many conditions, each realised
along some morphism into `i`, are realised along a common one. This is how statements about a
cofiltered limit, each of which holds at some member of the diagram, are combined at a single
member.
-/

public section

namespace CategoryTheory.IsCofiltered

variable {I : Type*} [Category* I] [IsCofiltered I]

/-- In a cofiltered category, two properties of morphisms to `i` which are stable under
precomposition and each hold for some morphism to `i` hold together for some morphism to `i`. -/
theorem exists_and_of_stable {i : I} {R₁ R₂ : ∀ {k : I}, (k ⟶ i) → Prop}
    (hR₁ : ∀ {k l : I} {g : k ⟶ i} (h : l ⟶ k), R₁ g → R₁ (h ≫ g))
    (hR₂ : ∀ {k l : I} {g : k ⟶ i} (h : l ⟶ k), R₂ g → R₂ (h ≫ g))
    (h₁ : ∃ (k : I) (g : k ⟶ i), R₁ g) (h₂ : ∃ (k : I) (g : k ⟶ i), R₂ g) :
    ∃ (k : I) (g : k ⟶ i), R₁ g ∧ R₂ g := by
  obtain ⟨k₁, g₁, r₁⟩ := h₁
  obtain ⟨k₂, g₂, r₂⟩ := h₂
  obtain ⟨l, a₁, a₂, ha⟩ := cospan g₁ g₂
  exact ⟨l, a₁ ≫ g₁, hR₁ a₁ r₁, ha ▸ hR₂ a₂ r₂⟩

end CategoryTheory.IsCofiltered

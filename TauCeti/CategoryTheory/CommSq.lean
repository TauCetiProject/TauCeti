/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.CommSq

/-!
# Commutative squares over a base object

If the cospan `X ⟶ Z ⟵ Y` of a commutative square lies over a base object `S`, then the two
projections out of the apex induce the same morphism to `S`.
-/

public section

namespace CategoryTheory.CommSq

variable {C : Type*} [Category* C] {P X Y Z S : C} {p₁ : P ⟶ X} {p₂ : P ⟶ Y} {g₁ : X ⟶ Z}
  {g₂ : Y ⟶ Z} {fX : X ⟶ S} {fY : Y ⟶ S} {fZ : Z ⟶ S} {fP : P ⟶ S}

/-- In a commutative square over a cospan `X ⟶ Z ⟵ Y` lying over `S`, the second projection is a
morphism over `S` whenever the first one is. -/
theorem snd_comp_eq_of_fst_comp_eq (h : CommSq p₁ p₂ g₁ g₂) (hg₁ : g₁ ≫ fZ = fX)
    (hg₂ : g₂ ≫ fZ = fY) (hp₁ : p₁ ≫ fX = fP) : p₂ ≫ fY = fP := by
  rw [← hp₁, ← hg₁, ← hg₂, h.w_assoc]

end CategoryTheory.CommSq

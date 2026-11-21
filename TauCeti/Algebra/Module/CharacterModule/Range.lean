/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.CharacterModule

/-!
# Characters detect the range of a homomorphism

An element of an abelian group lies in the image of a homomorphism exactly when every character
vanishing on the image vanishes on it: this is
`AddMonoidHom.mem_range_iff_forall_characterModule`. It is how one shows that a linear system over a
noncommutative ring is solvable by passing to character modules.
-/

public section

/-- Characters detect the image of a homomorphism of abelian groups: an element lies in the image
exactly when every character vanishing on the image vanishes on it. -/
theorem AddMonoidHom.mem_range_iff_forall_characterModule {X Y : Type*} [AddCommGroup X]
    [AddCommGroup Y] (f : X →+ Y) (y : Y) :
    y ∈ f.range ↔ ∀ χ : CharacterModule Y, (∀ x, χ (f x) = 0) → χ y = 0 := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨x, rfl⟩ χ hχ
    exact hχ x
  rw [← QuotientAddGroup.eq_zero_iff]
  refine CharacterModule.eq_zero_of_character_apply fun c ↦ ?_
  exact h (AddMonoidHom.comp c (QuotientAddGroup.mk' f.range)) fun x ↦
    (congrArg c ((QuotientAddGroup.eq_zero_iff (f x)).mpr
      (AddMonoidHom.mem_range.mpr ⟨x, rfl⟩))).trans (map_zero c)

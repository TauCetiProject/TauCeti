/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.GroupPresentation
public import TauCeti.GroupTheory.IsPerfect

/-!
# Perfectness of two-generator presentations

A two-generator presentation defines a perfect group if its transcribed relations include
power relations on both generators and their product with pairwise coprime exponents.
Additional relations are allowed, so the criterion applies without checking the rest of the
presentation or assuming finiteness.
-/

public section

namespace TauCeti.GroupPresentation

/-- A two-generator presentation containing pairwise coprime power relations on the generators
and their product defines a perfect group. -/
theorem isPerfect_of_coprime (P : GroupPresentation) (hP : P.generatorCount = 2)
    {a b c : ℕ}
    (ha : .pow (.gen ⟨0, by omega⟩) a ∈ P.transcribed)
    (hb : .pow (.gen ⟨1, by omega⟩) b ∈ P.transcribed)
    (hc : .pow (.mul (.gen ⟨0, by omega⟩) (.gen ⟨1, by omega⟩)) c ∈ P.transcribed)
    (hab : a.Coprime b) (hac : a.Coprime c) (hbc : b.Coprime c) :
    Group.IsPerfect P.Group := by
  let x : P.Group := PresentedGroup.of ⟨0, by omega⟩
  let y : P.Group := PresentedGroup.of ⟨1, by omega⟩
  have hgen : Subgroup.closure ({x, y} : Set P.Group) = ⊤ := by
    apply top_unique
    rw [← PresentedGroup.closure_range_of]
    apply Subgroup.closure_mono
    rintro _ ⟨i, rfl⟩
    have hi : i = ⟨0, by omega⟩ ∨ i = ⟨1, by omega⟩ := by
      rcases (by omega : i.val = 0 ∨ i.val = 1) with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases hi with rfl | rfl <;> simp [x, y]
  apply isPerfect_of_coprime_pow_eq_one hgen (a := a) (b := b) (c := c)
  · simpa only [Relator.eval_pow, Relator.eval_gen] using P.eval_of_eq_one _ ha
  · simpa only [Relator.eval_pow, Relator.eval_gen] using P.eval_of_eq_one _ hb
  · simpa only [Relator.eval_pow, Relator.eval_mul, Relator.eval_gen] using P.eval_of_eq_one _ hc
  · exact hab
  · exact hac
  · exact hbc

end TauCeti.GroupPresentation

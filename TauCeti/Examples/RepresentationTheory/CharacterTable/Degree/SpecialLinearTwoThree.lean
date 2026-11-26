/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Degree.Center
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.SpecialLinearTwoThree

/-!
# Degrees of `SL(2, 3)` and the index of its centre

`Representation.finrank_dvd_index_of_le_center` says that the degree of an irreducible complex
representation of a finite group divides the index of every central subgroup. For
`H = SL(2, 3)` and `Z = {±1}`, its centre, the index is `24 / 2 = 12`. These checks read the
degrees `1, 1, 1, 3, 2, 2, 2` off the certified character table
(`TauCeti.irreducibleCharacters_specialLinearTwoThree`), check that each divides `12`, as the
theorem predicts, and show that the stronger variant `χ(1)² ∣ |H : Z|` is false: the character of
degree `3` has `3² = 9`, which does not divide `12`.
-/

public section

namespace TauCeti.Examples.RepresentationTheory.DegreeSpecialLinearTwoThree

open Matrix

/-- The centre `{±1}` of `SL(2, 3)` has index `12`. -/
theorem index_center : (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod 3))).index = 12 := by
  have h := (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod 3))).card_mul_index
  rw [natCard_center_sl2_zmod_three, natCard_sl2_zmod_three] at h
  omega

/-- The value at `1` of an irreducible character of `SL(2, 3)` is the degree attached to its row
of the certified table. -/
private theorem exists_apply_one_eq {χ : SpecialLinearGroup (Fin 2) (ZMod 3) → ℂ}
    (hχ : χ ∈ irreducibleCharacters ℂ (SpecialLinearGroup (Fin 2) (ZMod 3))) :
    ∃ i, χ 1 = specialLinearTwoThreeCharacterDegrees i := by
  rw [irreducibleCharacters_specialLinearTwoThree] at hχ
  obtain ⟨i, rfl⟩ := hχ
  exact ⟨i, specialLinearTwoThreeCharacter_one i⟩

/-- **The degrees of `SL(2, 3)` are `1`, `2` and `3`.** -/
theorem apply_one_eq_one_or_eq_two_or_eq_three {χ : SpecialLinearGroup (Fin 2) (ZMod 3) → ℂ}
    (hχ : χ ∈ irreducibleCharacters ℂ (SpecialLinearGroup (Fin 2) (ZMod 3))) :
    χ 1 = 1 ∨ χ 1 = 2 ∨ χ 1 = 3 := by
  obtain ⟨i, hi⟩ := exists_apply_one_eq hχ
  have hdeg : ∀ j, specialLinearTwoThreeCharacterDegrees j = 1 ∨
      specialLinearTwoThreeCharacterDegrees j = 2 ∨
        specialLinearTwoThreeCharacterDegrees j = 3 := by
    intro j
    rw [specialLinearTwoThreeCharacterDegrees_apply]
    fin_cases j <;> decide
  rcases hdeg i with h | h | h <;> rw [hi, h] <;> norm_num

/-- Every degree `1`, `2`, `3` of `SL(2, 3)` divides `|H : Z| = 12`. -/
example {χ : SpecialLinearGroup (Fin 2) (ZMod 3) → ℂ}
    (hχ : χ ∈ irreducibleCharacters ℂ (SpecialLinearGroup (Fin 2) (ZMod 3))) :
    ∃ d : ℕ, χ 1 = d ∧ d ∣ (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod 3))).index := by
  rw [index_center]
  rcases apply_one_eq_one_or_eq_two_or_eq_three hχ with h | h | h
  · exact ⟨1, by simp [h], by norm_num⟩
  · exact ⟨2, by simp [h], by norm_num⟩
  · exact ⟨3, by simp [h], by norm_num⟩

/-- The same divisibility, from `Representation.finrank_dvd_index_of_le_center` applied to a
representation affording `χ`. -/
example {χ : SpecialLinearGroup (Fin 2) (ZMod 3) → ℂ}
    (hχ : χ ∈ irreducibleCharacters ℂ (SpecialLinearGroup (Fin 2) (ZMod 3))) :
    ∃ d : ℕ, χ 1 = d ∧ d ∣ (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod 3))).index := by
  obtain ⟨n, ρ, hρ, rfl⟩ := mem_irreducibleCharacters_iff.1 hχ
  exact ⟨_, ρ.char_one, ρ.finrank_dvd_index_of_le_center _ le_rfl⟩

/-- **The square of a degree need not divide `|H : Z|`**: `SL(2, 3)` has an irreducible character
of degree `3`, and `3² = 9` does not divide `|SL(2, 3) : {±1}| = 12`. -/
example : ∃ χ ∈ irreducibleCharacters ℂ (SpecialLinearGroup (Fin 2) (ZMod 3)), χ 1 = 3 ∧
    ¬ 3 ^ 2 ∣ (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod 3))).index := by
  refine ⟨specialLinearTwoThreeCharacter ⟨3, by decide⟩,
    specialLinearTwoThreeCharacter_mem_irreducibleCharacters _, ?_, ?_⟩
  · have h3 : specialLinearTwoThreeCharacterDegrees ⟨3, by decide⟩ = 3 := by
      rw [specialLinearTwoThreeCharacterDegrees_apply]
      decide
    rw [specialLinearTwoThreeCharacter_one, h3, Nat.cast_ofNat]
  · rw [index_center]
    norm_num

end TauCeti.Examples.RepresentationTheory.DegreeSpecialLinearTwoThree

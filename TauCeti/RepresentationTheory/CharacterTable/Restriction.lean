/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Table

/-!
# Constituents of restricted characters

The restriction of an irreducible character to a finite subgroup has an irreducible constituent.
-/

public section

namespace TauCeti

variable {k G : Type*} [Field k] [IsAlgClosed k] [CharZero k] [Group G]
  {N : Subgroup G} [Finite N]

/-- Every irreducible character lies over some irreducible constituent of its restriction to a
finite subgroup. -/
theorem exists_mem_irreducibleCharactersOver {χ : G → k} (hχ : χ ∈ irreducibleCharacters k G) :
    ∃ θ ∈ irreducibleCharacters k N, χ ∈ irreducibleCharactersOver k N θ := by
  classical
  let := Fintype.ofFinite N
  let : Invertible (Nat.card N : k) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨d, ρ, -, rfl⟩ := mem_irreducibleCharacters_iff.mp hχ
  let f := ClassFunction.comap N.subtype (ClassFunction.ofCharacter ρ)
  have h := ClassFunction.apply_eq_sum_characterPairing_mul_character
    (irreducibleRepresentation k) (pairwise_isEmpty_equiv_irreducibleRepresentation k)
    (by simp) f 1
  have hf : (f : N → k) 1 ≠ 0 := by
    simpa [f, ClassFunction.comap_apply] using apply_one_ne_zero_of_mem_irreducibleCharacters hχ
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h ▸ hf)
  refine ⟨_, irreducibleCharacter_mem k i, mem_irreducibleCharactersOver_iff_sum.mpr ⟨hχ, ?_⟩⟩
  rw [ClassFunction.characterPairing_symm, ClassFunction.characterPairing_apply] at hi
  simp only [f, ClassFunction.comap_apply, Subgroup.subtype_apply, ClassFunction.ofCharacter_apply,
    character_irreducibleRepresentation] at hi
  exact fun hz => hi (by rw [hz, mul_zero, zero_mul])

end TauCeti

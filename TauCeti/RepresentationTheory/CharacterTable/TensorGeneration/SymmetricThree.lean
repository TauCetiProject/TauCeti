/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.TensorGeneration
public import TauCeti.RepresentationTheory.FDRep.Basic
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
public import TauCeti.RepresentationTheory.Symmetric.SignCharacter
public import TauCeti.RepresentationTheory.Symmetric.Standard
import TauCeti.RepresentationTheory.CharacterTable.Determined

/-!
# Tensor powers of the two-dimensional representation of `S₃`

This file works out the faithful-tensor-generation theory of
`TauCeti.RepresentationTheory.CharacterTable.TensorGeneration` for the symmetric group
`S₃ = Equiv.Perm (Fin 3)` and its two-dimensional irreducible representation `U`, the standard
representation `TauCeti.standardRepresentation` on the vectors of `k[Fin 3]` whose coefficients sum
to zero, over a field `k`.

The character of `U` is `2` at the identity, `0` at the three transpositions and `-1` at the two
three-cycles (`TauCeti.char_standardRepresentation_fin_three`), so it takes `r_U = 3` values when
`6 ≠ 0` in `k`. Since `U` is faithful, the Burnside–Brauer theorem
`FDRep.exists_pos_finrank_hom_tensorPower` puts every irreducible complex representation of `S₃`
into some `U^⊗n` with `n < 3`. Summing over the group computes every multiplicity: the trivial
representation, the sign representation `sgn` and `U` occur in `U^⊗n` with multiplicities

`(2ⁿ + 3·0ⁿ + 2(-1)ⁿ)/6`, `(2ⁿ - 3·0ⁿ + 2(-1)ⁿ)/6` and `(2ⁿ - (-1)ⁿ)/3`,

with `0⁰ = 1`, as elements of `k` whenever `6 ≠ 0` in `k`. In characteristic zero
`U^⊗2 ≅ 1 ⊕ sgn ⊕ U`, and the sign representation occurs in neither `U^⊗0` nor `U^⊗1`: the bound
`n < r_U` is attained.

## Main statements

* `TauCeti.characterValues_standardRepresentation_fin_three`,
  `TauCeti.characterValueCount_standardRepresentation_fin_three`: the character values `2, 0, -1`.
* `TauCeti.finrank_hom_tensorPower_standardRepresentation_fin_three`: the multiplicity of an
  arbitrary representation `X` in `U^⊗n`, from three values of the character of `X`.
* `TauCeti.finrank_hom_trivial_tensorPower_standardRepresentation_fin_three`,
  `TauCeti.finrank_hom_sign_tensorPower_standardRepresentation_fin_three`,
  `TauCeti.finrank_hom_standardRepresentation_fin_three_tensorPower`: the multiplicities of the
  three irreducible representations in `U^⊗n`.
* `TauCeti.nonempty_iso_tensorPower_two_standardRepresentation_fin_three`: `U^⊗2 ≅ 1 ⊕ sgn ⊕ U`.
* `TauCeti.exists_lt_three_pos_finrank_hom_tensorPower_standardRepresentation_fin_three`: every
  nonzero complex representation maps nontrivially into some `U^⊗n` with `n < 3`, and
  `TauCeti.finrank_hom_sign_tensorPower_standardRepresentation_fin_three_of_lt_two` shows that the
  sign representation needs `n = 2`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Theorem 4.3.
* B. Steinberg, *On the Burnside–Brauer–Steinberg theorem*, arXiv:1409.7632, Introduction.
-/

public section

open CategoryTheory Equiv

namespace TauCeti

universe u

/-- The character values of the standard representation of `S₃` are `2`, `0` and `-1`. -/
theorem characterValues_standardRepresentation_fin_three (k : Type u) [Field k] [DecidableEq k] :
    (FDRep.of (standardRepresentation k (Fin 3))).characterValues = {2, 0, -1} := by
  ext z
  simp only [FDRep.mem_characterValues, FDRep.character_of, char_standardRepresentation_fin_three,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨σ, rfl⟩
    split_ifs <;> simp only [true_or, or_true]
  · have h₁ : swap (0 : Fin 3) 1 ≠ 1 ∧ Perm.sign (swap (0 : Fin 3) 1) = -1 := by decide
    have h₂ : finRotate 3 ≠ 1 ∧ Perm.sign (finRotate 3) ≠ -1 := by decide
    rintro (rfl | rfl | rfl)
    exacts [⟨1, by simp⟩, ⟨swap 0 1, by simp [h₁]⟩, ⟨finRotate 3, by simp [h₂]⟩]

section NeZero

variable (k : Type u) [Field k] [NeZero ((6 : ℕ) : k)]

/-- The standard representation of `S₃` has three distinct character values. -/
theorem characterValueCount_standardRepresentation_fin_three :
    (FDRep.of (standardRepresentation k (Fin 3))).characterValueCount = 3 := by
  classical
  have h₆ : (6 : k) ≠ 0 := by exact_mod_cast NeZero.ne ((6 : ℕ) : k)
  have h₂ : (2 : k) ≠ 0 := fun h ↦ h₆ (by linear_combination 3 * h)
  have h₃ : (3 : k) ≠ 0 := fun h ↦ h₆ (by linear_combination 2 * h)
  rw [← FDRep.card_characterValues, characterValues_standardRepresentation_fin_three,
    Finset.card_insert_of_notMem, Finset.card_pair_eq_two_iff.mpr (by simp)]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨h₂, fun h ↦ h₃ (by linear_combination h)⟩

variable {k} in
/-- The multiplicity of a representation `X` in `U^⊗n`, for `U` the standard representation of
`S₃`, from the values `a`, `b`, `c` of the character of `X` at the identity, the transpositions and
the three-cycles. -/
private theorem finrank_hom_tensorPower_standardRepresentation_fin_three_eq
    (X : FDRep k (Perm (Fin 3))) (a b c : k)
    (hX : ∀ σ, X.character σ = if σ = 1 then a else if Perm.sign σ = -1 then b else c) (n : ℕ) :
    (Module.finrank k (X ⟶ (FDRep.of (standardRepresentation k (Fin 3))).tensorPower n) : k) =
      (2 ^ n * a + 3 * 0 ^ n * b + 2 * (-1) ^ n * c) / 6 := by
  have : Invertible (Nat.card (Perm (Fin 3)) : k) := invertibleOfNonzero <| by
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using
      NeZero.ne ((6 : ℕ) : k)
  rw [← FDRep.scalar_product_char_eq_finrank_equivariant]
  have hsum : ∑ σ : Perm (Fin 3),
      ((FDRep.of (standardRepresentation k (Fin 3))).tensorPower n).character σ *
        X.character σ⁻¹ =
      ∑ σ : Perm (Fin 3), if σ = 1 then 2 ^ n * a else
        if Perm.sign σ = -1 then 0 ^ n * b else (-1) ^ n * c := by
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [FDRep.char_tensorPower, FDRep.character_of, char_standardRepresentation_fin_three, hX]
    simp only [inv_eq_one, Perm.sign_inv]
    split_ifs <;> rfl
  have h₁ : (Finset.univ.filter fun σ : Perm (Fin 3) ↦ σ = 1).card = 1 := by decide
  have h₂ : ((Finset.univ.filter fun σ : Perm (Fin 3) ↦ ¬σ = 1).filter
      fun σ ↦ Perm.sign σ = -1).card = 3 := by decide
  have h₃ : ((Finset.univ.filter fun σ : Perm (Fin 3) ↦ ¬σ = 1).filter
      fun σ ↦ ¬Perm.sign σ = -1).card = 2 := by decide
  rw [hsum, Finset.sum_ite, Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.sum_const,
    h₁, h₂, h₃, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  simp only [Nat.factorial, nsmul_eq_mul]
  push_cast
  ring

variable {k} in
/-- **The multiplicity of a representation `X` in `U^⊗n`**, for `U` the standard representation of
`S₃`, from the values of the character of `X` at the identity, the transposition `(0 1)` and the
three-cycle `finRotate 3`. -/
theorem finrank_hom_tensorPower_standardRepresentation_fin_three (X : FDRep k (Perm (Fin 3)))
    (n : ℕ) :
    (Module.finrank k (X ⟶ (FDRep.of (standardRepresentation k (Fin 3))).tensorPower n) : k) =
      (2 ^ n * X.character 1 + 3 * 0 ^ n * X.character (swap 0 1) +
        2 * (-1) ^ n * X.character (finRotate 3)) / 6 := by
  refine finrank_hom_tensorPower_standardRepresentation_fin_three_eq X _ _ _ (fun σ ↦ ?_) n
  obtain ⟨g, hg⟩ : ∃ g : Perm (Fin 3), g * (if σ = 1 then 1 else
      if Perm.sign σ = -1 then swap 0 1 else finRotate 3) * g⁻¹ = σ := by
    revert σ
    decide
  conv_lhs => rw [← hg]
  rw [FDRep.char_conj]
  split_ifs <;> rfl

/-- **The multiplicity of the trivial representation in `U^⊗n`**, for `U` the standard
representation of `S₃`, is `(2ⁿ + 3·0ⁿ + 2(-1)ⁿ)/6`, with `0⁰ = 1`. -/
theorem finrank_hom_trivial_tensorPower_standardRepresentation_fin_three (n : ℕ) :
    (Module.finrank k (FDRep.ofLinearCharacter 1 ⟶
        (FDRep.of (standardRepresentation k (Fin 3))).tensorPower n) : k) =
      (2 ^ n + 3 * 0 ^ n + 2 * (-1) ^ n) / 6 := by
  rw [finrank_hom_tensorPower_standardRepresentation_fin_three_eq _ 1 1 1 (fun σ ↦ by simp)]
  ring

/-- **The multiplicity of the sign representation in `U^⊗n`**, for `U` the standard
representation of `S₃`, is `(2ⁿ - 3·0ⁿ + 2(-1)ⁿ)/6`, with `0⁰ = 1`. -/
theorem finrank_hom_sign_tensorPower_standardRepresentation_fin_three (n : ℕ) :
    (Module.finrank k (FDRep.ofLinearCharacter (signLinearCharacter k (Fin 3)) ⟶
        (FDRep.of (standardRepresentation k (Fin 3))).tensorPower n) : k) =
      (2 ^ n - 3 * 0 ^ n + 2 * (-1) ^ n) / 6 := by
  rw [finrank_hom_tensorPower_standardRepresentation_fin_three_eq _ 1 (-1) 1 (fun σ ↦ ?_)]
  · ring
  · rw [FDRep.char_ofLinearCharacter, coe_signLinearCharacter_apply]
    rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> split_ifs <;> simp_all

/-- **The multiplicity of `U` in `U^⊗n`**, for `U` the standard representation of `S₃`, is
`(2ⁿ - (-1)ⁿ)/3`. -/
theorem finrank_hom_standardRepresentation_fin_three_tensorPower (n : ℕ) :
    (Module.finrank k (FDRep.of (standardRepresentation k (Fin 3)) ⟶
        (FDRep.of (standardRepresentation k (Fin 3))).tensorPower n) : k) =
      (2 ^ n - (-1) ^ n) / 3 := by
  have h₆ : (6 : k) ≠ 0 := by exact_mod_cast NeZero.ne ((6 : ℕ) : k)
  have h₃ : (3 : k) ≠ 0 := fun h ↦ h₆ (by linear_combination 2 * h)
  rw [finrank_hom_tensorPower_standardRepresentation_fin_three_eq _ 2 0 (-1)
    (fun σ ↦ by rw [FDRep.character_of, char_standardRepresentation_fin_three])]
  field_simp
  ring

end NeZero

section CharZero

variable (k : Type u) [Field k] [CharZero k]

/-- **The tensor square of the standard representation `U` of `S₃`** is `1 ⊕ sgn ⊕ U`. -/
theorem nonempty_iso_tensorPower_two_standardRepresentation_fin_three :
    Nonempty ((FDRep.of (standardRepresentation k (Fin 3))).tensorPower 2 ≅
      FDRep.ofLinearCharacter 1 ⊞ FDRep.ofLinearCharacter (signLinearCharacter k (Fin 3)) ⊞
        FDRep.of (standardRepresentation k (Fin 3))) := by
  refine FDRep.nonempty_iso_of_character_eq _ _ (funext fun σ ↦ ?_)
  rw [FDRep.char_tensorPower, FDRep.char_biprod, FDRep.char_biprod, Pi.add_apply, Pi.add_apply,
    FDRep.char_ofLinearCharacter, FDRep.char_ofLinearCharacter, coe_signLinearCharacter_apply,
    FDRep.character_of, char_standardRepresentation_fin_three]
  by_cases h₁ : σ = 1
  · subst h₁
    norm_num
  · rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> norm_num [h₁, h]

/-- **The sign representation of `S₃` occurs in neither `U^⊗0` nor `U^⊗1`**, for `U` the standard
representation: the exponent `n < 3` of the Burnside–Brauer theorem cannot be lowered. -/
theorem finrank_hom_sign_tensorPower_standardRepresentation_fin_three_of_lt_two {n : ℕ}
    (hn : n < 2) :
    Module.finrank k (FDRep.ofLinearCharacter (signLinearCharacter k (Fin 3)) ⟶
      (FDRep.of (standardRepresentation k (Fin 3))).tensorPower n) = 0 := by
  have h := finrank_hom_sign_tensorPower_standardRepresentation_fin_three k n
  interval_cases n <;> norm_num at h <;> exact_mod_cast h

/-- The sign representation of `S₃` occurs exactly once in `U^⊗2`, for `U` the standard
representation. -/
theorem finrank_hom_sign_tensorPower_two_standardRepresentation_fin_three :
    Module.finrank k (FDRep.ofLinearCharacter (signLinearCharacter k (Fin 3)) ⟶
      (FDRep.of (standardRepresentation k (Fin 3))).tensorPower 2) = 1 := by
  have h := finrank_hom_sign_tensorPower_standardRepresentation_fin_three k 2
  norm_num at h
  exact_mod_cast h

end CharZero

/-- **Burnside–Brauer for the standard representation `U` of `S₃`.** Every nonzero
finite-dimensional complex representation of `S₃` has a nonzero map into `U^⊗n` for some `n < 3`,
the number of character values of `U`. The bound is attained by the sign representation
(`TauCeti.finrank_hom_sign_tensorPower_standardRepresentation_fin_three_of_lt_two`). -/
theorem exists_lt_three_pos_finrank_hom_tensorPower_standardRepresentation_fin_three
    (X : FDRep ℂ (Perm (Fin 3))) (hX : 0 < Module.finrank ℂ X) :
    ∃ n < 3,
      0 < Module.finrank ℂ (X ⟶ (FDRep.of (standardRepresentation ℂ (Fin 3))).tensorPower n) := by
  have hU : Function.Injective (FDRep.of (standardRepresentation ℂ (Fin 3))).ρ := by
    rw [FDRep.of_ρ']
    exact standardRepresentation_injective (by simp)
  obtain ⟨n, hn, h⟩ := FDRep.exists_pos_finrank_hom_tensorPower _ X hU hX
  rw [characterValueCount_standardRepresentation_fin_three] at hn
  exact ⟨n, hn, h⟩

end TauCeti

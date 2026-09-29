/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.GL2.Classification

import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.FieldTheory.Finite.Extension
-- Non-public: `TauCeti.primitiveChar_to_Complex_ne_one` supplies the nontrivial
-- additive character that the classification theorem needs.
import TauCeti.NumberTheory.LegendreSymbol.Complex

/-!
# Degrees of the irreducible characters of `GL₂(𝔽_q)`

Let `F` be a finite field with `q ≥ 3` elements and let `E/F` be a degree-two extension. The
classification of the irreducible complex characters of `GL₂(F)` separates them into four
families. This file identifies each family intrinsically by its degree and counts the characters
of each degree:

* `q - 1` characters have degree `1`;
* `q - 1` characters have degree `q`;
* `(q - 1)(q - 2)/2` characters have degree `q + 1`;
* `q(q - 1)/2` characters have degree `q - 1`.

The lower bound `q ≥ 3` is necessary: for `q = 2`, the linear and cuspidal degrees both equal
one, while the principal-series family is empty. The final theorem verifies that the squares of
the four degrees, with these multiplicities, sum to the order of `GL₂(F)`.

## Main results

* `TauCeti.irreducibleCharacters_GL2_degree_one_eq_range` and its three companions identify the
  irreducible characters of each degree with the corresponding constructed family.
* `TauCeti.ncard_irreducibleCharacters_GL2_degree_one` and its three companions count those sets.
* `TauCeti.GL2_sum_characterDegrees_sq_eq_natCard` is the degree-squared identity for the four
  families.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, Section 5.2.
* I. Piatetski-Shapiro, *Complex Representations of GL(2, K) for Finite Fields K*,
  Contemporary Mathematics 16, AMS (1983), Sections 4--5.
-/

public section

open Matrix

namespace TauCeti

variable (F : Type) [Field F]

private theorem character_degree_eq_of_mem_linear {chi : GL (Fin 2) F → ℂ}
    (hchi : chi ∈ Set.range fun alpha : Fˣ →* ℂˣ => (GL2Linear F alpha).character) :
    chi 1 = 1 := by
  obtain ⟨alpha, hchi⟩ := hchi
  rw [← hchi]
  simp only [FDRep.char_one, finrank_GL2Linear]
  norm_num

private local instance [Finite F] : Fact (Nat.Prime (ringChar F)) :=
  ⟨CharP.char_is_prime F (ringChar F)⟩

private abbrev gl2QuadraticExtension [Finite F] := FiniteField.Extension F (ringChar F) 2

private local instance [Finite F] :
    Algebra.IsQuadraticExtension F (gl2QuadraticExtension F) :=
  ⟨FiniteField.finrank_extension F (ringChar F) 2⟩

variable [Fintype F] (E : Type*) [Field E] [Algebra F E]
  [hE : Algebra.IsQuadraticExtension F E] {psi : AddChar F ℂ} (hpsi : psi ≠ 1)

private theorem character_degree_eq_of_mem_steinberg {chi : GL (Fin 2) F → ℂ}
    (hchi : chi ∈ Set.range fun alpha : Fˣ →* ℂˣ => (GL2SteinbergTwist F alpha).character) :
    chi 1 = Fintype.card F := by
  obtain ⟨alpha, hchi⟩ := hchi
  rw [← hchi]
  simp only [FDRep.char_one, finrank_GL2SteinbergTwist]

private theorem character_degree_eq_of_mem_principalSeries {chi : GL (Fin 2) F → ℂ}
    (hchi : chi ∈ (fun p : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) =>
      (GL2PrincipalSeries F p.1 p.2).character) '' {p | p.1 ≠ p.2}) :
    chi 1 = Fintype.card F + 1 := by
  obtain ⟨p, -, hchi⟩ := hchi
  rw [← hchi]
  simpa only using character_one_GL2PrincipalSeries F p.1 p.2

private theorem character_degree_eq_of_mem_cuspidal {chi : GL (Fin 2) F → ℂ}
    (hchi : chi ∈
      (fun theta : Eˣ →* ℂˣ => (GL2CuspidalVirtualCharacter F E theta psi).1) ''
        {theta | theta.comp (powMonoidHom (Fintype.card F)) ≠ theta}) :
    chi 1 = ((Fintype.card F - 1 : ℕ) : ℂ) := by
  obtain ⟨theta, -, hchi⟩ := hchi
  rw [← hchi]
  simp only
  rw [GL2CuspidalVirtualCharacter_apply_one theta psi,
    Nat.cast_sub Fintype.card_pos, Nat.cast_one]

omit E hE hpsi

/-- The degree-one irreducible characters of `GL₂(F)` are exactly the linear characters. -/
theorem irreducibleCharacters_GL2_degree_one_eq_range (hq : 3 ≤ Fintype.card F) :
    {chi ∈ irreducibleCharacters ℂ (GL (Fin 2) F) | chi 1 = 1} =
      Set.range fun alpha : Fˣ →* ℂˣ => (GL2Linear F alpha).character := by
  rw [irreducibleCharacters_GL2_eq_union F (gl2QuadraticExtension F)
    (primitiveChar_to_Complex_ne_one F)]
  ext chi
  constructor
  · rintro ⟨(((hlin | hstein) | hprincipal) | hcuspidal), hdegree⟩
    · exact hlin
    · rw [character_degree_eq_of_mem_steinberg F hstein] at hdegree
      have : Fintype.card F = 1 := by exact_mod_cast hdegree
      omega
    · rw [character_degree_eq_of_mem_principalSeries F hprincipal] at hdegree
      have : Fintype.card F + 1 = 1 := by exact_mod_cast hdegree
      omega
    · rw [character_degree_eq_of_mem_cuspidal F (gl2QuadraticExtension F) hcuspidal] at hdegree
      have : Fintype.card F - 1 = 1 := by exact_mod_cast hdegree
      omega
  · intro hlin
    exact ⟨Or.inl (Or.inl (Or.inl hlin)), character_degree_eq_of_mem_linear F hlin⟩

/-- The irreducible characters of `GL₂(F)` of degree `q` are exactly the Steinberg twists. -/
theorem irreducibleCharacters_GL2_degree_card_eq_range :
    {chi ∈ irreducibleCharacters ℂ (GL (Fin 2) F) | chi 1 = Fintype.card F} =
      Set.range fun alpha : Fˣ →* ℂˣ => (GL2SteinbergTwist F alpha).character := by
  rw [irreducibleCharacters_GL2_eq_union F (gl2QuadraticExtension F)
    (primitiveChar_to_Complex_ne_one F)]
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  ext chi
  constructor
  · rintro ⟨(((hlin | hstein) | hprincipal) | hcuspidal), hdegree⟩
    · rw [character_degree_eq_of_mem_linear F hlin] at hdegree
      have : 1 = Fintype.card F := by exact_mod_cast hdegree
      omega
    · exact hstein
    · rw [character_degree_eq_of_mem_principalSeries F hprincipal] at hdegree
      have : Fintype.card F + 1 = Fintype.card F := by exact_mod_cast hdegree
      omega
    · rw [character_degree_eq_of_mem_cuspidal F (gl2QuadraticExtension F) hcuspidal] at hdegree
      have : Fintype.card F - 1 = Fintype.card F := by exact_mod_cast hdegree
      omega
  · intro hstein
    exact ⟨Or.inl (Or.inl (Or.inr hstein)), character_degree_eq_of_mem_steinberg F hstein⟩

/-- The irreducible characters of `GL₂(F)` of degree `q + 1` are exactly the principal-series
characters. -/
theorem irreducibleCharacters_GL2_degree_card_add_one_eq_image :
    {chi ∈ irreducibleCharacters ℂ (GL (Fin 2) F) | chi 1 = Fintype.card F + 1} =
      (fun p : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) =>
        (GL2PrincipalSeries F p.1 p.2).character) '' {p | p.1 ≠ p.2} := by
  rw [irreducibleCharacters_GL2_eq_union F (gl2QuadraticExtension F)
    (primitiveChar_to_Complex_ne_one F)]
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  ext chi
  constructor
  · rintro ⟨(((hlin | hstein) | hprincipal) | hcuspidal), hdegree⟩
    · rw [character_degree_eq_of_mem_linear F hlin] at hdegree
      have : 1 = Fintype.card F + 1 := by exact_mod_cast hdegree
      omega
    · rw [character_degree_eq_of_mem_steinberg F hstein] at hdegree
      have : Fintype.card F = Fintype.card F + 1 := by exact_mod_cast hdegree
      omega
    · exact hprincipal
    · rw [character_degree_eq_of_mem_cuspidal F (gl2QuadraticExtension F) hcuspidal] at hdegree
      have : Fintype.card F - 1 = Fintype.card F + 1 := by exact_mod_cast hdegree
      omega
  · intro hprincipal
    exact ⟨Or.inl (Or.inr hprincipal), character_degree_eq_of_mem_principalSeries F hprincipal⟩

include E hE hpsi

/-- The irreducible characters of `GL₂(F)` of degree `q - 1` are exactly the cuspidal
characters. -/
theorem irreducibleCharacters_GL2_degree_card_sub_one_eq_image (hq : 3 ≤ Fintype.card F) :
    {chi ∈ irreducibleCharacters ℂ (GL (Fin 2) F) |
      chi 1 = ((Fintype.card F - 1 : ℕ) : ℂ)} =
      (fun theta : Eˣ →* ℂˣ => (GL2CuspidalVirtualCharacter F E theta psi).1) ''
        {theta | theta.comp (powMonoidHom (Fintype.card F)) ≠ theta} := by
  rw [irreducibleCharacters_GL2_eq_union F E hpsi]
  ext chi
  constructor
  · rintro ⟨(((hlin | hstein) | hprincipal) | hcuspidal), hdegree⟩
    · rw [character_degree_eq_of_mem_linear F hlin] at hdegree
      have : 1 = Fintype.card F - 1 := by exact_mod_cast hdegree
      omega
    · rw [character_degree_eq_of_mem_steinberg F hstein] at hdegree
      have : Fintype.card F = Fintype.card F - 1 := by exact_mod_cast hdegree
      omega
    · rw [character_degree_eq_of_mem_principalSeries F hprincipal] at hdegree
      have : Fintype.card F + 1 = Fintype.card F - 1 := by exact_mod_cast hdegree
      omega
    · exact hcuspidal
  · intro hcuspidal
    exact ⟨Or.inr hcuspidal, character_degree_eq_of_mem_cuspidal F E hcuspidal⟩

omit E hE hpsi

/-- There are `q - 1` irreducible characters of `GL₂(F)` of degree one. -/
@[simp]
theorem ncard_irreducibleCharacters_GL2_degree_one (hq : 3 ≤ Fintype.card F) :
    {chi ∈ irreducibleCharacters ℂ (GL (Fin 2) F) | chi 1 = 1}.ncard =
      Fintype.card F - 1 := by
  rw [irreducibleCharacters_GL2_degree_one_eq_range F hq,
    ncard_range_character_GL2Linear]

/-- There are `q - 1` irreducible characters of `GL₂(F)` of degree `q`. -/
@[simp]
theorem ncard_irreducibleCharacters_GL2_degree_card :
    {chi ∈ irreducibleCharacters ℂ (GL (Fin 2) F) |
      chi 1 = Fintype.card F}.ncard = Fintype.card F - 1 := by
  rw [irreducibleCharacters_GL2_degree_card_eq_range F,
    ncard_range_character_GL2SteinbergTwist]

/-- There are `(q - 1)(q - 2)/2` irreducible characters of `GL₂(F)` of degree `q + 1`. -/
@[simp]
theorem ncard_irreducibleCharacters_GL2_degree_card_add_one :
    {chi ∈ irreducibleCharacters ℂ (GL (Fin 2) F) |
      chi 1 = Fintype.card F + 1}.ncard =
      (Fintype.card F - 1) * (Fintype.card F - 2) / 2 := by
  rw [irreducibleCharacters_GL2_degree_card_add_one_eq_image F,
    ncard_image_character_GL2PrincipalSeries]

/-- There are `q(q - 1)/2` irreducible characters of `GL₂(F)` of degree `q - 1`. -/
@[simp]
theorem ncard_irreducibleCharacters_GL2_degree_card_sub_one (hq : 3 ≤ Fintype.card F) :
    {chi ∈ irreducibleCharacters ℂ (GL (Fin 2) F) |
      chi 1 = ((Fintype.card F - 1 : ℕ) : ℂ)}.ncard =
      Fintype.card F * (Fintype.card F - 1) / 2 := by
  rw [irreducibleCharacters_GL2_degree_card_sub_one_eq_image F (gl2QuadraticExtension F)
      (primitiveChar_to_Complex_ne_one F) hq,
    ncard_image_GL2CuspidalVirtualCharacter F (gl2QuadraticExtension F)
      (primitiveChar_to_Complex_ne_one F)]

/-- The four irreducible degree families satisfy the degree-squared formula for `GL₂(F)`. -/
theorem GL2_sum_characterDegrees_sq_eq_natCard :
    (Fintype.card F - 1) * 1 ^ 2 +
          (Fintype.card F - 1) * Fintype.card F ^ 2 +
          ((Fintype.card F - 1) * (Fintype.card F - 2) / 2) *
            (Fintype.card F + 1) ^ 2 +
          (Fintype.card F * (Fintype.card F - 1) / 2) *
            (Fintype.card F - 1) ^ 2 =
      Nat.card (GL (Fin 2) F) := by
  rw [natCard_GL_fin_two_eq_sq_sub_one_mul]
  have hq := Fintype.one_lt_card (α := F)
  have hq_one : 1 ≤ Fintype.card F := by omega
  have hq_two : 2 ≤ Fintype.card F := by omega
  have hq_sq : 1 ≤ Fintype.card F ^ 2 := by nlinarith
  have hprincipal : 2 ∣ (Fintype.card F - 1) * (Fintype.card F - 2) := by
    simpa [Nat.sub_sub] using Nat.two_dvd_mul_sub_one (Fintype.card F - 1)
  have hcuspidal : 2 ∣ Fintype.card F * (Fintype.card F - 1) :=
    Nat.two_dvd_mul_sub_one (Fintype.card F)
  rw [← Nat.cast_inj (R := ℚ)]
  push_cast [Nat.cast_sub hq_one, Nat.cast_sub hq_two, Nat.cast_sub hq_sq,
    Nat.cast_div_charZero hprincipal, Nat.cast_div_charZero hcuspidal]
  ring

end TauCeti

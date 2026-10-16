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

`TauCeti.GL2_sum_degreeCount_mul_degree_sq_eq_natCard` verifies that the squares of the four
degrees, with these multiplicities, sum to the order of `GL₂(F)`; it needs no lower bound on `q`.

The lower bound `q ≥ 3` is necessary for the degree-`1` and degree-`(q - 1)` identifications, since
at `q = 2` those two degrees coincide. A separate section treats that degenerate case: over the
field with two elements the principal series is empty and the three irreducible characters of
`GL₂(𝔽₂)` have degrees `1`, `1` and `2`, which are the degrees of `S₃`. The last section specializes
the counts to the smallest uniform case `q = 3`, where all four families occur: the eight
irreducible characters of `GL₂(𝔽₃)` have degrees `1, 1, 2, 2, 2, 3, 3, 4`.

## Main results

* `TauCeti.irreducibleCharacters_GL2_degree_one_eq_range` and its three companions identify the
  irreducible characters of each degree with the corresponding constructed family.
* `TauCeti.ncard_irreducibleCharacters_GL2_degree_one` and its three companions count those sets.
* `TauCeti.image_degree_irreducibleCharacters_GL2`: for `q ≥ 3` the irreducible characters have
  exactly the four degrees `1`, `q - 1`, `q` and `q + 1`.
* `TauCeti.GL2_sum_degreeCount_mul_degree_sq_eq_natCard` adds the four degree counts, each
  weighted by the square of the degree it counts.
* `TauCeti.image_character_GL2PrincipalSeries_eq_empty_of_card_eq_two`: the principal series of
  `GL₂(𝔽₂)` is empty.
* `TauCeti.image_degree_irreducibleCharacters_GL2_of_card_eq_two`,
  `TauCeti.ncard_irreducibleCharacters_GL2_degree_one_of_card_eq_two` and
  `TauCeti.ncard_irreducibleCharacters_GL2_degree_two_of_card_eq_two`: `GL₂(𝔽₂)` has two
  irreducible characters of degree `1` and one of degree `2`, and no others.
* `TauCeti.image_degree_irreducibleCharacters_GL2_of_card_eq_three` and
  `TauCeti.ncard_irreducibleCharacters_GL2_degree_one_of_card_eq_three` with its three companions:
  `GL₂(𝔽₃)` has two irreducible characters of degree `1`, three of degree `2`, two of degree `3`
  and one of degree `4`, and no others.

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

/-- The four degree counts `q - 1`, `q - 1`, `(q - 1)(q - 2)/2`, and `q(q - 1)/2`, weighted by
the squares of the degrees `1`, `q`, `q + 1`, and `q - 1` they count, add up to `|GL₂(F)|`. -/
theorem GL2_sum_degreeCount_mul_degree_sq_eq_natCard :
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

/-- **The degrees of the irreducible characters of `GL₂(F)` are `1`, `q - 1`, `q` and `q + 1`**
for `q ≥ 3`: the linear characters have degree `1`, the cuspidal ones `q - 1`, the Steinberg twists
`q` and the principal series `q + 1`, and each family is nonempty. -/
theorem image_degree_irreducibleCharacters_GL2 (hq : 3 ≤ Fintype.card F) :
    (fun chi => chi 1) '' irreducibleCharacters ℂ (GL (Fin 2) F) =
      {1, ((Fintype.card F - 1 : ℕ) : ℂ), (Fintype.card F : ℂ), (Fintype.card F : ℂ) + 1} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro - ⟨chi, hchi, rfl⟩
    rw [irreducibleCharacters_GL2_eq_union F (gl2QuadraticExtension F)
      (primitiveChar_to_Complex_ne_one F)] at hchi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hchi with (((hlin | hstein) | hprincipal) | hcuspidal)
    · exact .inl (character_degree_eq_of_mem_linear F hlin)
    · exact .inr (.inr (.inl (character_degree_eq_of_mem_steinberg F hstein)))
    · exact .inr (.inr (.inr (character_degree_eq_of_mem_principalSeries F hprincipal)))
    · exact .inr (.inl
        (character_degree_eq_of_mem_cuspidal F (gl2QuadraticExtension F) hcuspidal))
  · -- each degree is attained, its set of characters having positive cardinality
    have hne {d : ℂ} (h : {chi ∈ irreducibleCharacters ℂ (GL (Fin 2) F) | chi 1 = d}.ncard ≠ 0) :
        d ∈ (fun chi => chi 1) '' irreducibleCharacters ℂ (GL (Fin 2) F) := by
      obtain ⟨chi, hchi, hd⟩ := Set.nonempty_of_ncard_ne_zero h
      exact ⟨chi, hchi, hd⟩
    rintro x (rfl | rfl | rfl | rfl) <;> refine hne ?_
    · rw [ncard_irreducibleCharacters_GL2_degree_one F hq]
      omega
    · rw [ncard_irreducibleCharacters_GL2_degree_card_sub_one F hq]
      exact (Nat.div_pos (Nat.mul_le_mul (by omega : 2 ≤ _) (by omega : 1 ≤ _)) two_pos).ne'
    · rw [ncard_irreducibleCharacters_GL2_degree_card F]
      omega
    · rw [ncard_irreducibleCharacters_GL2_degree_card_add_one F]
      exact (Nat.div_pos (Nat.mul_le_mul (by omega : 2 ≤ _) (by omega : 1 ≤ _)) two_pos).ne'

/-! ### The degenerate case `q = 2`

Over the field with two elements the four families of the classification degenerate: there is one
linear character and one Steinberg twist, the principal series is empty because `Fˣ` carries only
the trivial character, and the single cuspidal character has degree `q - 1 = 1`, the same degree as
the linear one. So the three irreducible characters of `GL₂(𝔽₂)` have degrees `1`, `1` and `2`,
which are the degrees of `S₃`; the isomorphism `GL₂(𝔽₂) ≅ S₃` itself is proved in
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/SymmetricGroup.lean`. -/

section CardTwo

/-- **There are no principal-series characters of `GL₂(𝔽₂)`**: a principal series needs two
distinct characters of `Fˣ`, and `Fˣ` is trivial. -/
theorem image_character_GL2PrincipalSeries_eq_empty_of_card_eq_two (hq : Fintype.card F = 2) :
    (fun p : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) => (GL2PrincipalSeries F p.1 p.2).character) ''
      {p | p.1 ≠ p.2} = ∅ := by
  have : Subsingleton Fˣ := by
    rw [← Finite.card_le_one_iff_subsingleton, Nat.card_units, Nat.card_eq_fintype_card, hq]
  rw [Set.image_eq_empty, Set.eq_empty_iff_forall_notMem]
  exact fun p hp => hp (Subsingleton.elim p.1 p.2)

/-- **Every irreducible character of `GL₂(𝔽₂)` has degree `1` or `2`**: the linear and cuspidal
characters have degree `1`, the Steinberg twist has degree `q = 2`, and the principal series, whose
degree would be `3`, is empty. -/
theorem character_degree_eq_one_or_two_of_card_eq_two (hq : Fintype.card F = 2)
    {chi : GL (Fin 2) F → ℂ} (hchi : chi ∈ irreducibleCharacters ℂ (GL (Fin 2) F)) :
    chi 1 = 1 ∨ chi 1 = 2 := by
  rw [irreducibleCharacters_GL2_eq_union F (gl2QuadraticExtension F)
    (primitiveChar_to_Complex_ne_one F)] at hchi
  rcases hchi with (((hlin | hstein) | hprincipal) | hcuspidal)
  · exact .inl (character_degree_eq_of_mem_linear F hlin)
  · refine .inr ?_
    rw [character_degree_eq_of_mem_steinberg F hstein, hq]
    norm_num
  · rw [image_character_GL2PrincipalSeries_eq_empty_of_card_eq_two F hq] at hprincipal
    exact absurd hprincipal (Set.notMem_empty chi)
  · refine .inl ?_
    rw [character_degree_eq_of_mem_cuspidal F (gl2QuadraticExtension F) hcuspidal, hq]
    norm_num

/-- **The degrees of the irreducible characters of `GL₂(𝔽₂)` are `1` and `2`**: both occur, the
first on the linear character and the second on the Steinberg character. -/
theorem image_degree_irreducibleCharacters_GL2_of_card_eq_two (hq : Fintype.card F = 2) :
    (fun chi => chi 1) '' irreducibleCharacters ℂ (GL (Fin 2) F) = {1, 2} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro - ⟨chi, hchi, rfl⟩
    exact character_degree_eq_one_or_two_of_card_eq_two F hq hchi
  · have hsteinberg : (GL2SteinbergTwist F 1).character 1 = 2 := by
      rw [character_degree_eq_of_mem_steinberg F
        (chi := (GL2SteinbergTwist F 1).character) ⟨1, rfl⟩, hq]
      norm_num
    rintro x (rfl | rfl)
    · exact ⟨_, character_GL2Linear_mem_irreducibleCharacters (F := F) 1,
        character_degree_eq_of_mem_linear F ⟨1, rfl⟩⟩
    · exact ⟨_, character_GL2SteinbergTwist_mem_irreducibleCharacters F 1, hsteinberg⟩

/-- **`GL₂(𝔽₂)` has one irreducible character of degree `2`**, the Steinberg character. -/
@[simp]
theorem ncard_irreducibleCharacters_GL2_degree_two_of_card_eq_two (hq : Fintype.card F = 2) :
    {chi ∈ irreducibleCharacters ℂ (GL (Fin 2) F) | chi 1 = 2}.ncard = 1 := by
  -- rewrite the degree `2` back into `q`, where the general count applies
  have h2 : ((Fintype.card F : ℕ) : ℂ) = 2 := by rw [hq]; norm_num
  rw [← h2, ncard_irreducibleCharacters_GL2_degree_card F, hq]

/-- **`GL₂(𝔽₂)` has no irreducible character of degree `3`**: the degree `q + 1` belongs to the
principal series, which is empty. -/
theorem irreducibleCharacters_GL2_degree_three_eq_empty_of_card_eq_two
    (hq : Fintype.card F = 2) :
    {chi ∈ irreducibleCharacters ℂ (GL (Fin 2) F) | chi 1 = 3} = ∅ := by
  -- rewrite the degree `3` back into `q + 1`, where the general identification applies
  have h3 : ((Fintype.card F : ℕ) : ℂ) + 1 = 3 := by rw [hq]; norm_num
  rw [← h3, irreducibleCharacters_GL2_degree_card_add_one_eq_image F,
    image_character_GL2PrincipalSeries_eq_empty_of_card_eq_two F hq]

/-- **`GL₂(𝔽₂)` has two irreducible characters of degree `1`**, the trivial character and the
cuspidal one: there are `q² - 1 = 3` irreducible characters in all, and one of them has
degree `2`. -/
@[simp]
theorem ncard_irreducibleCharacters_GL2_degree_one_of_card_eq_two (hq : Fintype.card F = 2) :
    {chi ∈ irreducibleCharacters ℂ (GL (Fin 2) F) | chi 1 = 1}.ncard = 2 := by
  have htotal : (irreducibleCharacters ℂ (GL (Fin 2) F)).ncard = 3 := by
    rw [← Nat.card_coe_set_eq, card_irreducibleCharacters, card_conjClasses_GL2,
      Nat.card_eq_fintype_card, hq]
    norm_num
  have hunion : {chi ∈ irreducibleCharacters ℂ (GL (Fin 2) F) | chi 1 = 1} ∪
      {chi ∈ irreducibleCharacters ℂ (GL (Fin 2) F) | chi 1 = 2} =
      irreducibleCharacters ℂ (GL (Fin 2) F) := by
    refine Set.Subset.antisymm (Set.union_subset (fun _ h => h.1) fun _ h => h.1) fun chi hchi => ?_
    rcases character_degree_eq_one_or_two_of_card_eq_two F hq hchi with h | h
    · exact .inl ⟨hchi, h⟩
    · exact .inr ⟨hchi, h⟩
  have hdisj : Disjoint {chi ∈ irreducibleCharacters ℂ (GL (Fin 2) F) | chi 1 = 1}
      {chi ∈ irreducibleCharacters ℂ (GL (Fin 2) F) | chi 1 = 2} := by
    rw [Set.disjoint_left]
    intro chi h1 h2
    have : (1 : ℂ) = 2 := h1.2.symm.trans h2.2
    norm_num at this
  have hadd := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  rw [hunion, htotal, ncard_irreducibleCharacters_GL2_degree_two_of_card_eq_two F hq] at hadd
  omega

end CardTwo

/-! ### The uniform case `q = 3`

Over the field with three elements all four families are present, and the degrees `1`, `q`,
`q + 1` and `q - 1` are the four distinct numbers `1`, `3`, `4` and `2`. The general counts give
two linear characters, two Steinberg twists, one principal series and three cuspidal characters,
so `GL₂(𝔽₃)` has eight irreducible characters, of degrees `1, 1, 2, 2, 2, 3, 3, 4`; their squares
add up to `48`, the order of the group. The eight conjugacy classes they are evaluated on, of sizes
`1, 1, 6, 6, 6, 8, 8, 12`, are listed in
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/ClassSize.lean`. -/

section CardThree

-- Unlike its three companions this is not a `@[simp]` lemma: its left-hand side is that of the
-- general `@[simp]` lemma `ncard_irreducibleCharacters_GL2_degree_one`, so `simp [hq]` already
-- proves it, and the `simpNF` linter rejects the attribute.
/-- **`GL₂(𝔽₃)` has two irreducible characters of degree `1`**, the characters `α ∘ det` for the
two characters `α` of `𝔽₃ˣ`. -/
theorem ncard_irreducibleCharacters_GL2_degree_one_of_card_eq_three (hq : Fintype.card F = 3) :
    {chi ∈ irreducibleCharacters ℂ (GL (Fin 2) F) | chi 1 = 1}.ncard = 2 := by
  rw [ncard_irreducibleCharacters_GL2_degree_one F hq.ge, hq]

/-- **`GL₂(𝔽₃)` has three irreducible characters of degree `2`**, the cuspidal characters: the
degree `q - 1` is `2`, and there are `q (q - 1) / 2 = 3` of them. -/
@[simp]
theorem ncard_irreducibleCharacters_GL2_degree_two_of_card_eq_three (hq : Fintype.card F = 3) :
    {chi ∈ irreducibleCharacters ℂ (GL (Fin 2) F) | chi 1 = 2}.ncard = 3 := by
  -- rewrite the degree `2` back into `q - 1`, where the general count applies
  have h2 : ((Fintype.card F - 1 : ℕ) : ℂ) = 2 := by rw [hq]; norm_num
  rw [← h2, ncard_irreducibleCharacters_GL2_degree_card_sub_one F hq.ge, hq]

/-- **`GL₂(𝔽₃)` has two irreducible characters of degree `3`**, the Steinberg twists. -/
@[simp]
theorem ncard_irreducibleCharacters_GL2_degree_three_of_card_eq_three (hq : Fintype.card F = 3) :
    {chi ∈ irreducibleCharacters ℂ (GL (Fin 2) F) | chi 1 = 3}.ncard = 2 := by
  -- rewrite the degree `3` back into `q`, where the general count applies
  have h3 : ((Fintype.card F : ℕ) : ℂ) = 3 := by rw [hq]; norm_num
  rw [← h3, ncard_irreducibleCharacters_GL2_degree_card F, hq]

/-- **`GL₂(𝔽₃)` has one irreducible character of degree `4`**, the principal series attached to
the two distinct characters of `𝔽₃ˣ`. -/
@[simp]
theorem ncard_irreducibleCharacters_GL2_degree_four_of_card_eq_three (hq : Fintype.card F = 3) :
    {chi ∈ irreducibleCharacters ℂ (GL (Fin 2) F) | chi 1 = 4}.ncard = 1 := by
  -- rewrite the degree `4` back into `q + 1`, where the general count applies
  have h4 : ((Fintype.card F : ℕ) : ℂ) + 1 = 4 := by rw [hq]; norm_num
  rw [← h4, ncard_irreducibleCharacters_GL2_degree_card_add_one F, hq]

/-- **The degrees of the irreducible characters of `GL₂(𝔽₃)` are `1`, `2`, `3` and `4`**: the
linear characters have degree `1`, the cuspidal ones `q - 1 = 2`, the Steinberg twists `q = 3` and
the principal series `q + 1 = 4`, and each family is nonempty. -/
theorem image_degree_irreducibleCharacters_GL2_of_card_eq_three (hq : Fintype.card F = 3) :
    (fun chi => chi 1) '' irreducibleCharacters ℂ (GL (Fin 2) F) = {1, 2, 3, 4} := by
  rw [image_degree_irreducibleCharacters_GL2 F hq.ge, hq]
  norm_num

end CardThree

end TauCeti

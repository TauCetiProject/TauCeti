/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Specification
public import TauCeti.RepresentationTheory.Symmetric.ClassSize
public import TauCeti.RepresentationTheory.Symmetric.Specht.Complex

/-!
# The character table of `Sₙ` is a character table, and its orthogonality relations

This file identifies the integer matrix `TauCeti.symmetricCharacterTable n`, whose `(μ, ν)` entry
is the value `χ^μ(ν)` of the character of the Specht module `S^μ` on the class of cycle type `ν`,
with the library's complex character table `TauCeti.characterTable ℂ (Equiv.Perm (Fin n))`. It then
proves the specification `TauCeti.IsCharacterTableSpec` and the row and column orthogonality
relations for the table.

The bridge is that the complex Specht modules are exactly the irreducible complex representations
of `Sₙ` (`TauCeti.existsUnique_character_eq_spechtChar`), so each `χ^μ`, read in `ℂ`, is one of the
enumerated irreducible characters, and `μ ↦ (its index)` is a bijection onto the row index of the
complex character table. Both index sets have as many elements as `Sₙ` has conjugacy classes, so
injectivity — which is the distinctness of the complex Specht modules — already gives the
bijection. Reindexing the rows by that bijection and the columns by
`TauCeti.partitionEquivConjClasses` turns the integer table into `characterTable ℂ Sₙ` on the nose,
whence the specification and, entry by entry, the two orthogonality relations.

The orthogonality relations are stated over `ℤ`, where the values live: division by class sizes is
avoided by weighting with the class size `n ! / z_ν` itself, which is exact by
`TauCeti.zPart_dvd_factorial`. The rational form with the classical weights `1 / z_ν`,
`TauCeti.sum_symmetricCharacterTable_mul_div_zPart`, is the shape the Hall inner product of
symmetric-function theory uses, and follows by dividing by `n !`. Complex conjugation, which is
what the general relations over `ℂ` carry, disappears here: the entries are integers, so a row and
its conjugate coincide.

## Main definitions

* `TauCeti.partitionEquivIrreducibleIndex`: the bijection sending `μ` to the row of the complex
  character table of `Sₙ` carrying `χ^μ`.
* `TauCeti.symmetricCharacterTableℂ`: the integer character table of `Sₙ` read in `ℂ` and
  reindexed on both sides into the shape `TauCeti.IsCharacterTableSpec` asks for.

## Main results

* `TauCeti.characterTable_partitionEquivIrreducibleIndex`: the entries of the complex character
  table of `Sₙ` are the entries of `TauCeti.symmetricCharacterTable`.
* `TauCeti.symmetricCharacterTableℂ_eq_characterTable` and
  `TauCeti.isCharacterTableSpec_symmetricCharacterTableℂ`: **the character table of `Sₙ` is the
  complex character table of `Sₙ`, and satisfies the character-table specification.**
* `TauCeti.symmetricCharacterTable_column_orthogonality`: **second (column) orthogonality**,
  `∑_μ χ^μ(ν) χ^μ(ν') = z_ν` when `ν = ν'` and `0` otherwise.
* `TauCeti.symmetricCharacterTable_row_orthogonality`: **first (row) orthogonality**,
  `∑_ν (n !/z_ν) χ^μ(ν) χ^μ'(ν) = n !` when `μ = μ'` and `0` otherwise, with
  `TauCeti.sum_symmetricCharacterTable_mul_div_zPart` its rational form `∑_ν χ^μ(ν) χ^μ'(ν)/z_ν`.
* `TauCeti.sum_finrank_spechtModule_sq`: **`∑_{μ ⊢ n} (f^μ)² = n !`**, column orthogonality at the
  identity class.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 6.
* B. E. Sagan, *The Symmetric Group*, 2nd ed. (2001), Sections 1.9 and 4.7.
-/

public section

open Nat

namespace TauCeti

open Module

variable {n : ℕ}

/-! ### The Specht character as an enumerated irreducible character -/

/-- **The integer character `χ^μ`, read in `ℂ`, is an irreducible character of `Sₙ`.** The complex
Specht module is simple (`TauCeti.instSimpleSpechtModuleℂ`) and its character is `χ^μ`. -/
theorem spechtChar_mem_irreducibleCharacters (μ : n.Partition) :
    (fun σ ↦ ((spechtChar μ σ : ℤ) : ℂ)) ∈ irreducibleCharacters ℂ (Equiv.Perm (Fin n)) := by
  have := FDRep.isIrreducible_of_simple (spechtModuleℂ μ)
  have h := character_mem_irreducibleCharacters (spechtModuleℂ μ).ρ
  have hcharacter : Representation.character (spechtModuleℂ μ).ρ =
      fun σ ↦ ((spechtChar μ σ : ℤ) : ℂ) :=
    funext (character_spechtModuleℂ_intCast μ)
  rw [hcharacter] at h
  exact h

/-- The row of the complex character table of `Sₙ` carrying `χ^μ`. The enumeration
`TauCeti.irreducibleCharacter` of the irreducible characters is an arbitrary one, so this index is
found rather than computed; only the bijection it defines,
`TauCeti.partitionEquivIrreducibleIndex`, is part of the API. -/
private noncomputable def spechtCharIndex (μ : n.Partition) :
    Fin (Nat.card (ConjClasses (Equiv.Perm (Fin n)))) :=
  (exists_irreducibleCharacter_eq ℂ (spechtChar_mem_irreducibleCharacters μ)).choose

/-- The character enumerated at `spechtCharIndex μ` is `χ^μ`. -/
private theorem irreducibleCharacter_spechtCharIndex (μ : n.Partition)
    (σ : Equiv.Perm (Fin n)) :
    irreducibleCharacter ℂ (spechtCharIndex μ) σ = (spechtChar μ σ : ℂ) :=
  congrFun (exists_irreducibleCharacter_eq ℂ (spechtChar_mem_irreducibleCharacters μ)).choose_spec σ

/-- **Distinct partitions occupy distinct rows**: a complex Specht module is determined by its
character. -/
private theorem spechtCharIndex_injective : Function.Injective (spechtCharIndex (n := n)) := by
  intro μ ν h
  have hchar : (spechtModuleℂ μ).character = (spechtModuleℂ ν).character := funext fun σ ↦ by
    rw [character_spechtModuleℂ_intCast, character_spechtModuleℂ_intCast]
    exact (irreducibleCharacter_spechtCharIndex μ σ).symm.trans
      (h ▸ irreducibleCharacter_spechtCharIndex ν σ)
  exact spechtModuleℂ_character_injective hchar

/-- **Every row is occupied**: there are as many partitions of `n` as conjugacy classes of `Sₙ`,
so the injection `spechtCharIndex_injective` is a bijection. -/
private theorem spechtCharIndex_bijective : Function.Bijective (spechtCharIndex (n := n)) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨spechtCharIndex_injective, ?_⟩
  rw [Fintype.card_fin, Fintype.card_eq_nat_card]
  exact Nat.card_congr (partitionEquivConjClasses n)

/-- **The partitions of `n` index the rows of the complex character table of `Sₙ`**, by
`μ ↦ χ^μ`: the row `partitionEquivIrreducibleIndex n μ` carries the character `χ^μ`
(`TauCeti.irreducibleCharacter_partitionEquivIrreducibleIndex`), and every row is of this form
exactly once. -/
noncomputable def partitionEquivIrreducibleIndex (n : ℕ) :
    n.Partition ≃ Fin (Nat.card (ConjClasses (Equiv.Perm (Fin n)))) :=
  Equiv.ofBijective _ spechtCharIndex_bijective

/-- **The character enumerated at the row `TauCeti.partitionEquivIrreducibleIndex n μ` is
`χ^μ`**, the character of the complex Specht module `S^μ`. -/
@[simp]
theorem irreducibleCharacter_partitionEquivIrreducibleIndex (μ : n.Partition)
    (σ : Equiv.Perm (Fin n)) :
    irreducibleCharacter ℂ (partitionEquivIrreducibleIndex n μ) σ = (spechtChar μ σ : ℂ) :=
  irreducibleCharacter_spechtCharIndex μ σ

/-! ### The integer table is the complex character table -/

/-- **The complex character table of `Sₙ` has the entries of `TauCeti.symmetricCharacterTable`**,
once its rows are indexed by `TauCeti.partitionEquivIrreducibleIndex` and its columns by
`TauCeti.partitionEquivConjClasses`. The entry at a representative `σ` of the class,
`χ^μ(σ)`, is `TauCeti.characterTable_apply` followed by
`TauCeti.irreducibleCharacter_partitionEquivIrreducibleIndex`. -/
@[simp]
theorem characterTable_partitionEquivIrreducibleIndex (μ ν : n.Partition) :
    characterTable ℂ (Equiv.Perm (Fin n)) (partitionEquivIrreducibleIndex n μ)
        (partitionEquivConjClasses n ν)
      = (symmetricCharacterTable n μ ν : ℂ) := by
  obtain ⟨σ, hσ⟩ := ConjClasses.exists_rep (partitionEquivConjClasses n ν)
  rw [← hσ, characterTable_apply, irreducibleCharacter_partitionEquivIrreducibleIndex,
    symmetricCharacterTable_apply, spechtCharValue_eq_spechtChar μ ν hσ]

/-- **The character table of `Sₙ` in the shape the specification asks for**: the integer entries
of `TauCeti.symmetricCharacterTable` read in `ℂ`, with the rows indexed by
`Fin (Nat.card (ConjClasses (Equiv.Perm (Fin n))))` and the columns by the conjugacy classes
themselves. It is the complex character table
(`TauCeti.symmetricCharacterTableℂ_eq_characterTable`). -/
noncomputable def symmetricCharacterTableℂ (n : ℕ) :
    Matrix (Fin (Nat.card (ConjClasses (Equiv.Perm (Fin n)))))
      (ConjClasses (Equiv.Perm (Fin n))) ℂ :=
  Matrix.of fun i C ↦ (symmetricCharacterTable n ((partitionEquivIrreducibleIndex n).symm i)
    ((partitionEquivConjClasses n).symm C) : ℂ)

/-- The entries of the reindexed complex character table are the integer Specht character values
read in `ℂ`. -/
@[simp]
theorem symmetricCharacterTableℂ_apply (n : ℕ)
    (i : Fin (Nat.card (ConjClasses (Equiv.Perm (Fin n)))))
    (C : ConjClasses (Equiv.Perm (Fin n))) :
    symmetricCharacterTableℂ n i C =
      (symmetricCharacterTable n ((partitionEquivIrreducibleIndex n).symm i)
        ((partitionEquivConjClasses n).symm C) : ℂ) := by
  simp [symmetricCharacterTableℂ]

/-- **The reindexed integer character table of `Sₙ` is the complex character table of `Sₙ`.** -/
theorem symmetricCharacterTableℂ_eq_characterTable (n : ℕ) :
    symmetricCharacterTableℂ n = characterTable ℂ (Equiv.Perm (Fin n)) := by
  ext i C
  rw [symmetricCharacterTableℂ_apply, ← characterTable_partitionEquivIrreducibleIndex,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **The character table of `Sₙ` satisfies the character-table specification**: its identity
column consists of positive divisors of `n !` whose squares sum to `n !`, its rows are orthonormal
for the class-size weighted Hermitian pairing, and its normalized rows are common left eigenrows of
the class-multiplication matrices. By `TauCeti.characterTable_unique_rows` this pins the table down
up to a permutation of its rows. -/
theorem isCharacterTableSpec_symmetricCharacterTableℂ (n : ℕ) :
    IsCharacterTableSpec (Equiv.Perm (Fin n)) (symmetricCharacterTableℂ n) := by
  rw [symmetricCharacterTableℂ_eq_characterTable]
  exact isCharacterTableSpec_characterTable (Equiv.Perm (Fin n))

/-! ### The orthogonality relations -/

/-- A column pairing of `TauCeti.symmetricCharacterTable`, read in `ℂ` as the corresponding
pairing of the complex character table. Conjugation is invisible: the entries are integers. -/
private theorem intCast_sum_symmetricCharacterTable (ν ν' : n.Partition) :
    ((∑ μ : n.Partition, symmetricCharacterTable n μ ν *
        symmetricCharacterTable n μ ν' : ℤ) : ℂ)
      = ∑ i, characterTable ℂ (Equiv.Perm (Fin n)) i (partitionEquivConjClasses n ν) *
          (starRingEnd ℂ) (characterTable ℂ (Equiv.Perm (Fin n)) i
            (partitionEquivConjClasses n ν')) := by
  rw [← Equiv.sum_comp (partitionEquivIrreducibleIndex n)]
  push_cast
  exact Finset.sum_congr rfl fun μ _ ↦ by
    rw [characterTable_partitionEquivIrreducibleIndex,
      characterTable_partitionEquivIrreducibleIndex, map_intCast]

/-- **Second (column) orthogonality for `Sₙ`**: two columns of the character table pair to the
weight `z_ν` of their common cycle type, and to `0` when the cycle types differ. The weight is the
order of the centralizer of a permutation of that cycle type
(`TauCeti.nat_card_centralizer_eq_zPart`), which is `n !` divided by the size of the class. -/
theorem symmetricCharacterTable_column_orthogonality (ν ν' : n.Partition) :
    ∑ μ : n.Partition, symmetricCharacterTable n μ ν * symmetricCharacterTable n μ ν'
      = if ν = ν' then (zPart ν : ℤ) else 0 := by
  rcases eq_or_ne ν ν' with rfl | hne
  · rw [ite_eq_left rfl]
    refine Int.cast_injective (α := ℂ) ?_
    rw [intCast_sum_symmetricCharacterTable, sum_characterTable_mul_conj, ite_eq_left rfl,
      Nat.card_perm, Nat.card_fin]
    have hmul := card_carrier_partitionEquivConjClasses_mul_zPart ν
    have hne0 : (Nat.card (partitionEquivConjClasses n ν).carrier : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (ConjClasses.card_carrier_pos _).ne'
    rw [div_eq_iff hne0, mul_comm]
    exact_mod_cast hmul.symm
  · rw [ite_eq_right hne]
    refine Int.cast_injective (α := ℂ) ?_
    rw [intCast_sum_symmetricCharacterTable, sum_characterTable_mul_conj,
      ite_eq_right fun h ↦ hne ((partitionEquivConjClasses n).injective h), Int.cast_zero]

/-- **First (row) orthogonality for `Sₙ`**, in a form free of division: two rows of the character
table, paired with the class sizes `n !/z_ν` as weights, give `n !` on the diagonal and `0` off
it. -/
theorem symmetricCharacterTable_row_orthogonality (μ μ' : n.Partition) :
    ∑ ν : n.Partition, ((n ! / zPart ν : ℕ) : ℤ) * symmetricCharacterTable n μ ν *
        symmetricCharacterTable n μ' ν = if μ = μ' then (n ! : ℤ) else 0 := by
  have hfac : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
  have key := card_inv_mul_sum_card_conjClass_mul_characterTable_mul_conj
    (partitionEquivIrreducibleIndex n μ) (partitionEquivIrreducibleIndex n μ')
  rw [← Equiv.sum_comp (partitionEquivConjClasses n)] at key
  simp only [characterTable_partitionEquivIrreducibleIndex, map_intCast,
    card_carrier_partitionEquivConjClasses] at key
  rw [Nat.card_perm, Nat.card_fin, inv_mul_eq_iff_eq_mul₀ hfac] at key
  rcases eq_or_ne μ μ' with rfl | hne
  · rw [ite_eq_left rfl, mul_one] at key
    rw [ite_eq_left rfl]
    refine Int.cast_injective (α := ℂ) ?_
    push_cast
    exact key
  · rw [ite_eq_right fun h ↦ hne ((partitionEquivIrreducibleIndex n).injective h), mul_zero] at key
    rw [ite_eq_right hne]
    refine Int.cast_injective (α := ℂ) ?_
    push_cast
    exact key

/-- **First (row) orthogonality for `Sₙ` in its classical rational form**: the characters are
orthonormal for the pairing `⟨f, g⟩ = ∑_ν f(ν) g(ν) / z_ν`. This is
`TauCeti.symmetricCharacterTable_row_orthogonality` divided by `n !`, the divisions being exact by
`TauCeti.zPart_dvd_factorial`. -/
theorem sum_symmetricCharacterTable_mul_div_zPart (μ μ' : n.Partition) :
    ∑ ν : n.Partition,
        (symmetricCharacterTable n μ ν * symmetricCharacterTable n μ' ν : ℚ) / zPart ν
      = if μ = μ' then 1 else 0 := by
  have hfac : (n ! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
  refine mul_left_cancel₀ hfac ?_
  have h1 : (n ! : ℚ) * ∑ ν : n.Partition,
      (symmetricCharacterTable n μ ν * symmetricCharacterTable n μ' ν : ℚ) / zPart ν
      = ((∑ ν : n.Partition, ((n ! / zPart ν : ℕ) : ℤ) * symmetricCharacterTable n μ ν *
        symmetricCharacterTable n μ' ν : ℤ) : ℚ) := by
    rw [Finset.mul_sum, Int.cast_sum]
    refine Finset.sum_congr rfl fun ν _ ↦ ?_
    rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast,
      Nat.cast_div (zPart_dvd_factorial ν) (Nat.cast_ne_zero.mpr (zPart_pos ν).ne')]
    ring
  rw [h1, symmetricCharacterTable_row_orthogonality]
  rcases eq_or_ne μ μ' with rfl | hne
  · rw [ite_eq_left rfl, ite_eq_left rfl, mul_one, Int.cast_natCast]
  · rw [ite_eq_right hne, ite_eq_right hne, mul_zero, Int.cast_zero]

/-- **The dimensions of the Specht modules square-sum to `n !`.** This is column orthogonality at
the class of the identity, whose weight `z` is the order of `Sₙ` and whose column holds the
degrees `f^μ = dim_ℚ S^μ`. -/
theorem sum_finrank_spechtModule_sq (n : ℕ) :
    ∑ μ : n.Partition, finrank ℚ (spechtModule μ) ^ 2 = n ! := by
  have hz : zPart ((partitionEquivConjClasses n).symm (ConjClasses.mk 1)) = n ! := by
    rw [zPart_partitionEquivConjClasses_symm_mk, zPart_partition_one, Fintype.card_fin]
  have hcol := symmetricCharacterTable_column_orthogonality
    ((partitionEquivConjClasses n).symm (ConjClasses.mk 1))
    ((partitionEquivConjClasses n).symm (ConjClasses.mk 1))
  rw [ite_eq_left rfl, hz] at hcol
  refine Nat.cast_injective (R := ℤ) ?_
  push_cast
  rw [← hcol]
  exact Finset.sum_congr rfl fun μ _ ↦ by rw [symmetricCharacterTable_one]; ring

end TauCeti

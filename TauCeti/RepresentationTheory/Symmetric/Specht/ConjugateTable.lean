/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.Specht.Extremes
public import TauCeti.RepresentationTheory.Symmetric.Specht.Orthogonality
public import TauCeti.RepresentationTheory.Symmetric.Specht.SignTranspose

/-!
# Conjugating the shape multiplies a row of the character table of `Sₙ` by the signs

Tensoring with the sign representation sends the Specht module `S^μ` to `S^(μᵗ)`
(`TauCeti.spechtModule_tensor_sign_iso`), so `χ^(μᵗ)(σ) = sgn(σ) χ^μ(σ)`
(`TauCeti.spechtChar_conjugate`). This file reads that identity on the character table of `Sₙ`.

On the integer table `TauCeti.symmetricCharacterTable n`, whose columns are the cycle types `ν`,
the sign of the class of cycle type `ν` is `(-1) ^ (n + ℓ(ν))`, where `ℓ(ν)` is the number of parts
of `ν` (the fixed points count as parts), equivalently `(-1) ^ (n - ℓ(ν))`. Hence
`X(μᵗ, ν) = (-1) ^ (n + ℓ(ν)) X(μ, ν)`: the row of `μᵗ` is the row of `μ` multiplied entrywise by
the row of signs `X((1ⁿ), ·)`. In particular a self-conjugate shape has a character vanishing on
every odd permutation.

On the complex table, whose rows are an arbitrary enumeration of the irreducible characters,
conjugation of partitions becomes a row involution `TauCeti.conjugateIrreducibleIndex n`, carried
across by `TauCeti.partitionEquivIrreducibleIndex`. The same identity then holds for
`TauCeti.irreducibleCharacter` and for the table `TauCeti.symmetricCharacterTableℂ n`, which is the
complex character table of `Sₙ` and satisfies the character-table specification
`TauCeti.IsCharacterTableSpec` (`TauCeti.isCharacterTableSpec_symmetricCharacterTableℂ`).

## Main definitions

* `TauCeti.conjugateIrreducibleIndex`: the involution of the rows of the complex character table
  of `Sₙ` induced by `Nat.Partition.conjugate`.

## Main results

* `TauCeti.spechtCharValue_conjugate`, `TauCeti.symmetricCharacterTable_conjugate`:
  `X(μᵗ, ν) = (-1) ^ (n + ℓ(ν)) X(μ, ν)`.
* `TauCeti.spechtChar_eq_zero_of_conjugate_eq`, `TauCeti.spechtCharValue_eq_zero_of_conjugate_eq`:
  the character of a self-conjugate shape vanishes on the odd permutations.
* `TauCeti.irreducibleCharacter_conjugateIrreducibleIndex`,
  `TauCeti.symmetricCharacterTableℂ_conjugateIrreducibleIndex`: the same identity on the complex
  character table of `Sₙ`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 4, Exercise 4.4.
* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Theorem 8.15.
-/

public section

namespace TauCeti

variable {n : ℕ}

/-! ### The integer table -/

/-- **Conjugating the shape multiplies a character value by the sign of the class**:
`χ^(μᵗ)(ν) = (-1) ^ (n + ℓ(ν)) χ^μ(ν)`, where `ℓ(ν)` is the number of parts of the cycle type
`ν`. -/
@[simp]
theorem spechtCharValue_conjugate (μ ν : n.Partition) :
    spechtCharValue μ.conjugate ν = (-1) ^ (n + Multiset.card ν.parts) * spechtCharValue μ ν := by
  obtain ⟨σ, hσ⟩ := ConjClasses.mk_surjective (partitionEquivConjClasses n ν)
  rw [← spechtCharValue_ones, spechtCharValue_eq_spechtChar _ _ hσ,
    spechtCharValue_eq_spechtChar _ _ hσ, spechtCharValue_eq_spechtChar _ _ hσ,
    spechtChar_conjugate, spechtChar_ones]

/-- **The row of `μᵗ` in the character table of `Sₙ` is the row of `μ` times the row of signs**:
`X(μᵗ, ν) = (-1) ^ (n + ℓ(ν)) X(μ, ν)`, the signs being the row `X((1ⁿ), ·)`
(`TauCeti.symmetricCharacterTable_ones`).

This is not a `simp` lemma, for the reason given at
`TauCeti.symmetricCharacterTable_indiscrete`. -/
theorem symmetricCharacterTable_conjugate (μ ν : n.Partition) :
    symmetricCharacterTable n μ.conjugate ν =
      (-1) ^ (n + Multiset.card ν.parts) * symmetricCharacterTable n μ ν := by
  rw [symmetricCharacterTable_apply, symmetricCharacterTable_apply, spechtCharValue_conjugate]

/-- **The character of a self-conjugate shape vanishes on the odd permutations**: if `μᵗ = μ` and
`sgn σ = -1`, then `χ^μ(σ) = 0`. -/
theorem spechtChar_eq_zero_of_conjugate_eq {μ : n.Partition} (hμ : μ.conjugate = μ)
    {σ : Equiv.Perm (Fin n)} (hσ : Equiv.Perm.sign σ = -1) : spechtChar μ σ = 0 := by
  have h := spechtChar_conjugate μ σ
  rw [hμ, hσ, Units.val_neg, Units.val_one] at h
  omega

/-- **The character value of a self-conjugate shape vanishes on the odd classes**: if `μᵗ = μ`
and `n + ℓ(ν)` is odd, then `χ^μ(ν) = 0`. -/
theorem spechtCharValue_eq_zero_of_conjugate_eq {μ : n.Partition} (hμ : μ.conjugate = μ)
    {ν : n.Partition} (hν : Odd (n + Multiset.card ν.parts)) : spechtCharValue μ ν = 0 := by
  have h := spechtCharValue_conjugate μ ν
  rw [hμ, hν.neg_one_pow] at h
  omega

/-! ### The complex table -/

/-- The involution of the rows of the complex character table of `Sₙ` induced by conjugating
partitions: it sends the row of `χ^μ` to the row of `χ^(μᵗ)`
(`TauCeti.conjugateIrreducibleIndex_partitionEquivIrreducibleIndex`), and multiplies each
irreducible character by the sign (`TauCeti.irreducibleCharacter_conjugateIrreducibleIndex`). -/
noncomputable def conjugateIrreducibleIndex (n : ℕ) :
    Equiv.Perm (Fin (Nat.card (ConjClasses (Equiv.Perm (Fin n))))) :=
  (partitionEquivIrreducibleIndex n).permCongr
    ⟨Nat.Partition.conjugate, Nat.Partition.conjugate, Nat.Partition.conjugate_conjugate,
      Nat.Partition.conjugate_conjugate⟩

/-- The row involution sends the row of `χ^μ` to the row of `χ^(μᵗ)`. -/
@[simp]
theorem conjugateIrreducibleIndex_partitionEquivIrreducibleIndex (μ : n.Partition) :
    conjugateIrreducibleIndex n (partitionEquivIrreducibleIndex n μ) =
      partitionEquivIrreducibleIndex n μ.conjugate := by
  simp [conjugateIrreducibleIndex, Equiv.permCongr_apply]

/-- The row involution read through the labelling of the rows by partitions. -/
theorem conjugateIrreducibleIndex_apply (i : Fin (Nat.card (ConjClasses (Equiv.Perm (Fin n))))) :
    conjugateIrreducibleIndex n i =
      partitionEquivIrreducibleIndex n ((partitionEquivIrreducibleIndex n).symm i).conjugate := by
  rw [← conjugateIrreducibleIndex_partitionEquivIrreducibleIndex, Equiv.apply_symm_apply]

/-- The row involution is an involution. -/
@[simp]
theorem conjugateIrreducibleIndex_conjugateIrreducibleIndex
    (i : Fin (Nat.card (ConjClasses (Equiv.Perm (Fin n))))) :
    conjugateIrreducibleIndex n (conjugateIrreducibleIndex n i) = i := by
  simp [conjugateIrreducibleIndex_apply]

/-- The row involution is its own inverse. -/
@[simp]
theorem conjugateIrreducibleIndex_symm :
    (conjugateIrreducibleIndex n).symm = conjugateIrreducibleIndex n :=
  Equiv.ext fun i ↦ by
    rw [Equiv.symm_apply_eq, conjugateIrreducibleIndex_conjugateIrreducibleIndex]

/-- **Conjugating the shape multiplies an irreducible character of `Sₙ` by the sign**: the
character enumerated at the row `conjugateIrreducibleIndex n i` is `σ ↦ sgn(σ) χᵢ(σ)`. -/
@[simp]
theorem irreducibleCharacter_conjugateIrreducibleIndex
    (i : Fin (Nat.card (ConjClasses (Equiv.Perm (Fin n))))) (σ : Equiv.Perm (Fin n)) :
    irreducibleCharacter ℂ (conjugateIrreducibleIndex n i) σ =
      (Equiv.Perm.sign σ : ℤ) * irreducibleCharacter ℂ i σ := by
  obtain ⟨μ, rfl⟩ := (partitionEquivIrreducibleIndex n).surjective i
  rw [conjugateIrreducibleIndex_partitionEquivIrreducibleIndex,
    irreducibleCharacter_partitionEquivIrreducibleIndex,
    irreducibleCharacter_partitionEquivIrreducibleIndex, spechtChar_conjugate]
  norm_cast

/-- **The sign-transpose identity on the character table of `Sₙ` in the shape of the
specification**: in `TauCeti.symmetricCharacterTableℂ n`, the row `conjugateIrreducibleIndex n i`
is the row `i` multiplied by the sign `(-1) ^ (n + ℓ(ν))` of each class, `ν` being the cycle type
of the class. -/
theorem symmetricCharacterTableℂ_conjugateIrreducibleIndex
    (i : Fin (Nat.card (ConjClasses (Equiv.Perm (Fin n))))) (C : ConjClasses (Equiv.Perm (Fin n))) :
    symmetricCharacterTableℂ n (conjugateIrreducibleIndex n i) C =
      (-1) ^ (n + Multiset.card ((partitionEquivConjClasses n).symm C).parts) *
        symmetricCharacterTableℂ n i C := by
  rw [symmetricCharacterTableℂ_apply, symmetricCharacterTableℂ_apply,
    conjugateIrreducibleIndex_apply, Equiv.symm_apply_apply, symmetricCharacterTable_conjugate]
  norm_cast

end TauCeti

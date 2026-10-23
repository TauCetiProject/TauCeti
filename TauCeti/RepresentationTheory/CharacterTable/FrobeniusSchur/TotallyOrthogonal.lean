/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.InvolutionCount

/-!
# Totally orthogonal groups and the involution count

Let `G` be a finite group and `k` an algebraically closed field of characteristic zero. The
involution-counting formula
(`TauCeti.card_squareRoot_one_eq_sum_frobeniusSchurIndicatorRow_mul_characterDegree`) reads

`#{g ∈ G : g² = 1} = ∑_χ ν₂(χ) χ(1)`,

and in characteristic zero every Frobenius-Schur indicator `ν₂(χ)` is `1`, `0` or `-1`. Since the
degrees `χ(1)` are positive, the right side is at most `∑_χ χ(1)`, with equality exactly when every
indicator is `1`. So the number of solutions of `g² = 1` is bounded by the sum of the character
degrees, and the bound is attained precisely by the **totally orthogonal** groups, those all of
whose irreducible representations are orthogonal (`ν₂ = 1`, equivalently realizable by an
invariant symmetric form).

This turns total orthogonality into a finite check: count the solutions of `g² = 1` and add up
the degrees of the character table. The symmetric groups are the classical examples.

## Main statements

* `TauCeti.card_squareRoot_one_le_sum_characterDegree`: `#{g : g² = 1} ≤ ∑_χ χ(1)`.
* `TauCeti.card_squareRoot_one_eq_sum_characterDegree_iff`: equality holds exactly when every row
  of the character table has Frobenius-Schur indicator `1`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Corollary 4.6.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2, Proposition 39.
-/

public section

namespace TauCeti

section Fintype

variable (k : Type) (G : Type*) [Field k] [CharZero k] [Group G] [Fintype G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

/-- The involution count in integers: with the row indicators written as integers
`n i ∈ {1, 0, -1}`, `#{g : g² = 1} = ∑ᵢ n i · χᵢ(1)`. -/
private theorem exists_intCast_frobeniusSchurIndicatorRow :
    ∃ n : Fin (Nat.card (ConjClasses G)) → ℤ,
      (∀ i, n i ≤ 1) ∧ (∀ i, (n i = 1 ↔ frobeniusSchurIndicatorRow k i = 1)) ∧
        (Nat.card {g : G // g * g = 1} : ℤ) = ∑ i, n i * characterDegree k (G := G) i := by
  have hval (i : Fin (Nat.card (ConjClasses G))) :
      ∃ m : ℤ, m ≤ 1 ∧ frobeniusSchurIndicatorRow k i = m := by
    rcases frobeniusSchurIndicatorRow_eq_one_or_eq_zero_or_eq_neg_one k i with h | h | h
    · exact ⟨1, le_rfl, by simp [h]⟩
    · exact ⟨0, zero_le_one, by simp [h]⟩
    · exact ⟨-1, by norm_num, by simp [h]⟩
  choose n hle hn using hval
  refine ⟨n, hle, fun i ↦ ?_, ?_⟩
  · rw [hn i]
    exact Int.cast_eq_one.symm
  · apply Int.cast_injective (α := k)
    rw [Int.cast_natCast,
      card_squareRoot_one_eq_sum_frobeniusSchurIndicatorRow_mul_characterDegree k G]
    push_cast
    simp only [hn]

/-- **A group is totally orthogonal exactly when it has as many solutions of `g² = 1` as the sum of
its character degrees.** Over an algebraically closed field of characteristic zero, the bound
`TauCeti.card_squareRoot_one_le_sum_characterDegree` is attained exactly when every row of the
character table has Frobenius-Schur indicator `1`. -/
theorem card_squareRoot_one_eq_sum_characterDegree_iff :
    Nat.card {g : G // g * g = 1} = ∑ i, characterDegree k (G := G) i ↔
      ∀ i, frobeniusSchurIndicatorRow k (G := G) i = 1 := by
  obtain ⟨n, hle, hn, hcount⟩ := exists_intCast_frobeniusSchurIndicatorRow k G
  have hpos (i : Fin (Nat.card (ConjClasses G))) : (0 : ℤ) < characterDegree k i := by
    exact_mod_cast characterDegree_pos k i
  -- The defect `∑ᵢ (1 - n i) χᵢ(1)` is a sum of nonnegative terms, each vanishing exactly when
  -- `n i = 1`, since the degrees are positive.
  have hdefect : (∑ i, (characterDegree k (G := G) i : ℤ)) - Nat.card {g : G // g * g = 1} =
      ∑ i, (1 - n i) * characterDegree k (G := G) i := by
    rw [hcount, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hnonneg (i : Fin (Nat.card (ConjClasses G))) :
      0 ≤ (1 - n i) * (characterDegree k i : ℤ) :=
    mul_nonneg (sub_nonneg.mpr (hle i)) (hpos i).le
  calc Nat.card {g : G // g * g = 1} = ∑ i, characterDegree k (G := G) i
      ↔ (∑ i, (characterDegree k (G := G) i : ℤ)) - Nat.card {g : G // g * g = 1} = 0 := by
        rw [sub_eq_zero]
        exact_mod_cast eq_comm
    _ ↔ ∀ i, (1 - n i) * (characterDegree k (G := G) i : ℤ) = 0 := by
        rw [hdefect, Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hnonneg i]
        simp
    _ ↔ ∀ i, frobeniusSchurIndicatorRow k (G := G) i = 1 := by
        refine forall_congr' fun i ↦ ?_
        rw [mul_eq_zero, or_iff_left (hpos i).ne', sub_eq_zero, eq_comm, hn i]

end Fintype

variable (k : Type) (G : Type*) [Field k] [CharZero k] [Group G] [Finite G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

/-- **The solutions of `g² = 1` are at most as many as the sum of the character degrees**, over an
algebraically closed field of characteristic zero: in the involution count
`#{g : g² = 1} = ∑_χ ν₂(χ) χ(1)` every indicator is at most `1`. -/
theorem card_squareRoot_one_le_sum_characterDegree :
    Nat.card {g : G // g * g = 1} ≤ ∑ i, characterDegree k (G := G) i := by
  have := Fintype.ofFinite G
  obtain ⟨n, hle, -, hcount⟩ := exists_intCast_frobeniusSchurIndicatorRow k G
  have h : (Nat.card {g : G // g * g = 1} : ℤ) ≤ ∑ i, (characterDegree k (G := G) i : ℤ) := by
    rw [hcount]
    exact Finset.sum_le_sum fun i _ ↦ mul_le_of_le_one_left (Nat.cast_nonneg _) (hle i)
  exact_mod_cast h

end TauCeti

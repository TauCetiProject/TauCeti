/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ExactChecker

/-!
# Executable degree recovery from exact central characters

The positive degree belonging to a central-character row is determined by its weighted
Hermitian norm. Clearing the class-size denominators makes this calculation executable in
the coefficient semiring itself, including the integers and exact cyclotomic integers.

`clearedClassRowNorm` multiplies the usual norm by the product of all class sizes.
`recoverCharacterDegree?` tests positive divisors of the group order against the resulting
degree-square equation. It returns `none` if no degree passes. Over a coefficient semiring
admitting a homomorphism to a characteristic-zero domain, at most one degree passes.
For every certified exact character table, recovery returns its degree on each row.

This allows the Dixon--Schneider conversion from central to ordinary characters to recover
degrees independently, instead of enumerating vectors of possible degrees.

## References

* J. D. Dixon, *High speed computation of group characters*, Numer. Math. **10** (1967),
  446–450.
* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 3, for recovery of character
  degrees from central characters and row orthogonality.
-/

public section

namespace TauCeti.ClassData

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable (d : ClassData G) {R : Type*} [CommSemiring R]

/-- The weighted Hermitian norm of a numbered row, with all class-size denominators cleared
by their product. The coefficient of coordinate `k` is the product of the other class sizes. -/
def clearedClassRowNorm (conj : R → R) (row : Fin d.numClasses → R) : R :=
  ∑ k, (∏ j ∈ Finset.univ.erase k, (d.classFinset j).card : ℕ) * row k * conj (row k)

/-- The defining sum for the denominator-cleared class-row norm. -/
theorem clearedClassRowNorm_def (conj : R → R) (row : Fin d.numClasses → R) :
    d.clearedClassRowNorm conj row =
      ∑ k, (∏ j ∈ Finset.univ.erase k, (d.classFinset j).card : ℕ) * row k * conj (row k) :=
  (rfl)

/-- Recover a positive character degree from an exact central-character row. Each positive
divisor of the group order is tested against the denominator-cleared degree-square equation.
An arbitrary row may have no such degree. -/
def recoverCharacterDegree? [DecidableEq R] (conj : R → R)
    (row : Fin d.numClasses → R) : Option ℕ :=
  let norm := d.clearedClassRowNorm conj row
  let target : R := (Fintype.card G : R) * (∏ j, (d.classFinset j).card : ℕ)
  (List.range (Fintype.card G + 1)).find? fun n =>
    decide (0 < n ∧ n ∣ Fintype.card G ∧ (n : R) ^ 2 * norm = target)

/-- A recovered degree is positive, divides the group order, and satisfies the
denominator-cleared degree-square equation. No uniqueness assumption is needed. -/
theorem recoverCharacterDegree?_sound [DecidableEq R] (conj : R → R)
    (row : Fin d.numClasses → R) {n : ℕ}
    (h : d.recoverCharacterDegree? conj row = some n) :
    0 < n ∧ n ∣ Fintype.card G ∧
      (n : R) ^ 2 * d.clearedClassRowNorm conj row =
        (Fintype.card G : R) * (∏ j, (d.classFinset j).card : ℕ) := by
  rw [recoverCharacterDegree?] at h
  simpa only [decide_eq_true_eq] using List.find?_some h

private theorem classSizeProduct_pos : 0 < ∏ j, (d.classFinset j).card :=
  Finset.prod_pos fun j _ => Finset.card_pos.mpr ⟨d.rep j, d.rep_mem_classFinset j⟩

/-- Division-free conversion and diagonal row orthogonality imply the denominator-cleared
degree-square identity over a commutative semiring. No full table certificate is needed. -/
theorem degree_sq_mul_clearedClassRowNorm_eq_card_mul_classSizeProduct
    {conj : R →+* R} {row values : Fin d.numClasses → R} {degree : ℕ}
    (hconvert : ∀ k, (degree : R) * row k = (d.classFinset k).card * values k)
    (horthogonal : ∑ k, (d.classFinset k).card * values k * conj (values k) =
      (Fintype.card G : R)) :
    (degree : R) ^ 2 * d.clearedClassRowNorm conj row =
      (Fintype.card G : R) * (∏ j, (d.classFinset j).card : ℕ) := by
  have hterm (k : Fin d.numClasses) :
      (degree : R) ^ 2 *
          ((∏ j ∈ Finset.univ.erase k, (d.classFinset j).card : ℕ) *
            row k * conj (row k)) =
        (∏ j, (d.classFinset j).card : ℕ) *
          ((d.classFinset k).card * values k * conj (values k)) := by
    have hconj := congrArg conj (hconvert k)
    simp only [map_mul, map_natCast] at hconj
    have hprod :
        ((d.classFinset k).card : R) *
            (∏ j ∈ Finset.univ.erase k, (d.classFinset j).card : ℕ) =
          (∏ j, (d.classFinset j).card : ℕ) := by
      simpa only [Nat.cast_mul] using congrArg (Nat.cast : ℕ → R)
        (Finset.mul_prod_erase Finset.univ
          (fun j => (d.classFinset j).card) (Finset.mem_univ k))
    calc
      _ = (∏ j ∈ Finset.univ.erase k, (d.classFinset j).card : ℕ) *
          ((degree : R) * row k) * ((degree : R) * conj (row k)) := by ring
      _ = (∏ j ∈ Finset.univ.erase k, (d.classFinset j).card : ℕ) *
          ((d.classFinset k).card * values k) *
          ((d.classFinset k).card * conj (values k)) := by
        rw [hconvert, hconj]
      _ = _ := by rw [← hprod]; ring
  rw [clearedClassRowNorm_def, Finset.mul_sum,
    Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum, horthogonal]
  simp [mul_comm]

/-- The denominator-cleared degree-square identity for a certified exact character table.
It involves only ring operations, so no division or passage to complex numbers is needed. -/
theorem IsExactCharacterTableSpec.degree_sq_mul_clearedClassRowNorm_eq_card_mul_classSizeProduct
    {R : Type*} [CommRing R] {d : ClassData G} {conj : R →+* R}
    {omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) R}
    {degree : Fin d.numClasses → ℕ}
    (h : d.IsExactCharacterTableSpec conj omega table degree) (i : Fin d.numClasses) :
    (degree i : R) ^ 2 * d.clearedClassRowNorm conj (omega i) =
      (Fintype.card G : R) * (∏ j, (d.classFinset j).card : ℕ) := by
  exact d.degree_sq_mul_clearedClassRowNorm_eq_card_mul_classSizeProduct
    (h.degree_mul_central i) (by simpa using h.row_orthogonal i i)

private theorem degree_eq_of_norm_eq {K : Type*} [CommSemiring K] [IsDomain K] [CharZero K]
    (f : R →+* K) {norm : R} {m n : ℕ}
    (hm : (m : R) ^ 2 * norm =
      (Fintype.card G : R) * (∏ j, (d.classFinset j).card : ℕ))
    (hn : (n : R) ^ 2 * norm =
      (Fintype.card G : R) * (∏ j, (d.classFinset j).card : ℕ)) : m = n := by
  have hm' := congrArg f hm
  have hn' := congrArg f hn
  simp only [map_mul, map_pow, map_natCast] at hm' hn'
  have hnorm : f norm ≠ 0 := by
    intro hz
    have hright : (Fintype.card G : K) * (∏ j, (d.classFinset j).card : ℕ) ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_pos.ne')
        (Nat.cast_ne_zero.mpr d.classSizeProduct_pos.ne')
    exact hright (by simpa [hz] using hm'.symm)
  have hsq : m ^ 2 = n ^ 2 := by
    exact_mod_cast mul_right_cancel₀ hnorm (hm'.trans hn'.symm)
  exact Nat.pow_left_injective (by decide : 2 ≠ 0) hsq

/-- Recovery succeeds with `n` exactly when `n` is a positive divisor of the group order
satisfying the degree-square equation. A homomorphism to a characteristic-zero domain ensures
that no competing natural degree can satisfy it. -/
theorem recoverCharacterDegree?_eq_some_iff [DecidableEq R]
    {K : Type*} [CommSemiring K] [IsDomain K] [CharZero K] (f : R →+* K)
    (conj : R → R) (row : Fin d.numClasses → R) (n : ℕ) :
    d.recoverCharacterDegree? conj row = some n ↔
      0 < n ∧ n ∣ Fintype.card G ∧
        (n : R) ^ 2 * d.clearedClassRowNorm conj row =
          (Fintype.card G : R) * (∏ j, (d.classFinset j).card : ℕ) := by
  constructor
  · exact d.recoverCharacterDegree?_sound conj row
  · intro hn
    have hmem : n ∈ List.range (Fintype.card G + 1) := by
      simpa using Nat.lt_succ_of_le (Nat.le_of_dvd Fintype.card_pos hn.2.1)
    have hex : (d.recoverCharacterDegree? conj row).isSome := by
      apply List.find?_isSome.mpr
      exact ⟨n, hmem, by simpa using hn⟩
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hex
    have hmnorm := (d.recoverCharacterDegree?_sound conj row hm).2.2
    have hmn := d.degree_eq_of_norm_eq f hmnorm hn.2.2
    simpa [hmn] using hm

/-- Recovering the degree of any row of a certified exact character table returns the
certificate's degree. This applies to integer and exact cyclotomic tables. -/
theorem IsExactCharacterTableSpec.recoverCharacterDegree?_eq_some
    {R : Type*} [CommRing R] [DecidableEq R]
    {K : Type*} [CommSemiring K] [IsDomain K] [CharZero K]
    {d : ClassData G} {conj : R →+* R}
    {omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) R}
    {degree : Fin d.numClasses → ℕ}
    (h : d.IsExactCharacterTableSpec conj omega table degree) (f : R →+* K)
    (i : Fin d.numClasses) :
    d.recoverCharacterDegree? conj (omega i) = some (degree i) := by
  exact (d.recoverCharacterDegree?_eq_some_iff f conj (omega i) (degree i)).mpr
    ⟨h.degree_pos i, h.degree_dvd i,
      h.degree_sq_mul_clearedClassRowNorm_eq_card_mul_classSizeProduct i⟩

end TauCeti.ClassData

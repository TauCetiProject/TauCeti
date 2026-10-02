/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Elementary.WeightEnumerator

/-!
# MacWilliams checks for the repetition and single-parity-check codes

The repetition and single-parity-check codes are Euclidean duals, and both enumerators are known
in closed form: the positive-length repetition enumerator is `X^n + (q - 1) Y^n`, and the
parity-check enumerator satisfies `q W(X,Y) = (X + (q - 1) Y)^n + (q - 1) (X - Y)^n`. Substituting
the MacWilliams variables `(X + (q - 1) Y, X - Y)` into either enumerator therefore gives the
cardinality of that code times the enumerator of the other one, which is the MacWilliams identity
for each code of the pair, checked from the explicit formulas without the general character-sum
argument.

For the repetition code the substitution turns `X^n + (q - 1) Y^n` directly into the right-hand
side of the parity-check formula, so this check holds over every finite ring. The parity-check
side applies the substitution twice, using that it squares to multiplication of both variables by
the alphabet size, and is stated over a finite field. Both checks include the empty coordinate
type, where the repetition code is zero and the parity-check code is the whole word space.

The general theorem is `Submodule.natCard_mul_weightEnumerator_euclideanDual`.

Reference: W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, §7.2.
-/

public section

namespace TauCeti

open MvPolynomial

/-- The MacWilliams substitution of the repetition enumerator is its cardinality times the
single-parity-check enumerator.

This is a pre-simp lemma (`simp↓`): its left-hand side contains the repetition enumerator, which
the `simp` lemma `weightEnumerator_repetitionCode` rewrites first whenever `ι` is nonempty, so a
plain `simp` attribute would not fire at positive length. -/
@[simp↓]
theorem aeval_weightEnumerator_repetitionCode (R ι : Type*) [Ring R] [Finite R] [DecidableEq R]
    [Fintype ι] :
    aeval ![X 0 + (Nat.card R - 1 : MvPolynomial (Fin 2) ℤ) * X 1, X 0 - X 1]
        (repetitionCode R ι : Set (ι → R)).weightEnumerator =
      (Nat.card (repetitionCode R ι) : MvPolynomial (Fin 2) ℤ) *
        (singleParityCheckCode R ι : Set (ι → R)).weightEnumerator := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    simp [repetitionCode_eq_bot_of_isEmpty, singleParityCheckCode_eq_top_of_isEmpty,
      weightEnumerator_univ, Fintype.card_eq_zero]
  | inr hι =>
    rw [weightEnumerator_repetitionCode, natCard_repetitionCode,
      natCard_mul_weightEnumerator_singleParityCheckCode]
    simp

variable (F ι : Type*) [Field F] [Finite F] [DecidableEq F] [Fintype ι]

/-- The MacWilliams substitution of the single-parity-check enumerator is its cardinality
times the repetition enumerator.

This is a pre-simp lemma (`simp↓`): when `Mathlib.Algebra.MvPolynomial.Monad` is imported,
`MvPolynomial.aeval_eq_bind₁` rewrites the substitution before a plain simp rule can fire. -/
@[simp↓]
theorem aeval_weightEnumerator_singleParityCheckCode :
    aeval ![X 0 + (Nat.card F - 1 : MvPolynomial (Fin 2) ℤ) * X 1, X 0 - X 1]
        (singleParityCheckCode F ι : Set (ι → F)).weightEnumerator =
      (Nat.card (singleParityCheckCode F ι) : MvPolynomial (Fin 2) ℤ) *
        (repetitionCode F ι : Set (ι → F)).weightEnumerator := by
  classical
  by_cases hι : Nonempty ι
  · let _ : Nonempty ι := hι
    let q : MvPolynomial (Fin 2) ℤ := Nat.card F
    let A : MvPolynomial (Fin 2) ℤ := X 0 + (q - 1) * X 1
    let B : MvPolynomial (Fin 2) ℤ := X 0 - X 1
    let T : MvPolynomial (Fin 2) ℤ →+* MvPolynomial (Fin 2) ℤ :=
      (aeval ![A, B]).toRingHom
    have hA : T A = q * X 0 := by
      simp [T, A, B, q]
      ring
    have hB : T B = q * X 1 := by
      simp [T, A, B, q]
      ring
    have hformula := natCard_mul_weightEnumerator_singleParityCheckCode F ι
    have htransform : q * T (singleParityCheckCode F ι : Set (ι → F)).weightEnumerator =
        (T A) ^ Fintype.card ι + (q - 1) * (T B) ^ Fintype.card ι := by
      calc
        _ = T (q * (singleParityCheckCode F ι : Set (ι → F)).weightEnumerator) := by
          simp [T, q]
        _ = T (A ^ Fintype.card ι + (q - 1) * B ^ Fintype.card ι) := by
          exact congrArg T (by simpa [A, B, q] using hformula)
        _ = _ := by simp [T, q]
    -- The two transformed linear forms are `qX` and `qY`.
    have htrans : q * T (singleParityCheckCode F ι : Set (ι → F)).weightEnumerator =
        q ^ Fintype.card ι *
          (repetitionCode F ι : Set (ι → F)).weightEnumerator := by
      rw [hA, hB] at htransform
      rw [weightEnumerator_repetitionCode F ι]
      simpa [q, mul_pow, mul_add, mul_assoc, mul_left_comm, mul_comm] using htransform
    have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
    have hpow : q ^ Fintype.card ι = q * q ^ (Fintype.card ι - 1) := by
      calc
        _ = q ^ ((Fintype.card ι - 1) + 1) := by rw [Nat.sub_add_cancel hn]
        _ = _ := by rw [pow_add, pow_one]; ring
    have heq : T (singleParityCheckCode F ι : Set (ι → F)).weightEnumerator =
        q ^ (Fintype.card ι - 1) *
          (repetitionCode F ι : Set (ι → F)).weightEnumerator := by
      have hq : q ≠ 0 := by
        dsimp [q]
        exact_mod_cast (Nat.card_pos (α := F)).ne'
      apply mul_left_cancel₀ hq
      calc
        _ = q ^ Fintype.card ι *
            (repetitionCode F ι : Set (ι → F)).weightEnumerator := htrans
        _ = _ := by rw [hpow]; ring
    simpa [T, A, B, q, natCard_singleParityCheckCode] using heq
  · let _ : IsEmpty ι := not_nonempty_iff.mp hι
    simp [singleParityCheckCode_eq_top_of_isEmpty, repetitionCode_eq_bot_of_isEmpty,
      weightEnumerator_univ, Fintype.card_eq_zero]

end TauCeti

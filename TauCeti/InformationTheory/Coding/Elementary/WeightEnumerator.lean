/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Elementary.Basic
public import TauCeti.InformationTheory.Coding.MacWilliams

/-!
# Weight enumerators of repetition and single-parity-check codes

The repetition code consists of constant words, and the single-parity-check code consists of
words whose coordinate sum is zero. They are Euclidean duals. Their homogeneous weight
enumerators give explicit examples of the MacWilliams transform, alongside the zero code and
the whole word space.

For a nonempty coordinate type of cardinality `n` over a finite field with `q` elements, the
repetition enumerator is `X^n + (q - 1) Y^n`, and the parity-check enumerator satisfies
`q W(X,Y) = (X + (q - 1) Y)^n + (q - 1) (X - Y)^n` over the integers. The nonempty hypothesis
matters: at length zero the repetition code has one word, rather than `q` words.

## References

W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
Press (2003), §§1.2–1.4 and §7.2.
-/

public section

namespace TauCeti

open Finset MvPolynomial

variable (R ι : Type*)

section Enumerators

variable [Fintype ι] [Semiring R] [DecidableEq R]

/-- The positive-length repetition code has enumerator `X^n + (q - 1) Y^n`. -/
@[simp]
theorem weightEnumerator_repetitionCode [Finite R] [Nonempty ι] :
    (repetitionCode R ι : Set (ι → R)).weightEnumerator =
      X 0 ^ Fintype.card ι + (Nat.card R - 1 : MvPolynomial (Fin 2) ℤ) *
        X 1 ^ Fintype.card ι := by
  classical
  let _ : Fintype R := .ofFinite R
  rw [Set.weightEnumerator_eq_sum (Set.toFinite _)]
  have hset : (Set.toFinite (repetitionCode R ι : Set (ι → R))).toFinset =
      univ.image (Function.const ι) := by
    ext x
    simp
  rw [hset, sum_image (fun _ _ _ _ h ↦ Function.const_injective h)]
  simp_rw [hammingNorm_const]
  have hs (a : R) :
      (X 0 : MvPolynomial (Fin 2) ℤ) ^ (Fintype.card ι - if a = 0 then 0 else Fintype.card ι) *
        X 1 ^ (if a = 0 then 0 else Fintype.card ι) =
      X 1 ^ Fintype.card ι + if a = 0 then X 0 ^ Fintype.card ι - X 1 ^ Fintype.card ι
        else 0 := by
    split_ifs <;> simp
  simp_rw [hs]
  simp [sum_add_distrib, Nat.card_eq_fintype_card]
  ring

/-- The integral weight-enumerator formula for a positive-length single-parity-check code. -/
theorem natCard_mul_weightEnumerator_singleParityCheckCode {F : Type*} [Field F] [Finite F]
    [DecidableEq F] [Nonempty ι] :
    (Nat.card F : MvPolynomial (Fin 2) ℤ) *
        (singleParityCheckCode F ι : Set (ι → F)).weightEnumerator =
      (X 0 + (Nat.card F - 1 : MvPolynomial (Fin 2) ℤ) * X 1) ^ Fintype.card ι +
        (Nat.card F - 1 : MvPolynomial (Fin 2) ℤ) * (X 0 - X 1) ^ Fintype.card ι := by
  have h := Submodule.natCard_mul_weightEnumerator_euclideanDual (repetitionCode F ι)
  rw [natCard_repetitionCode, euclideanDual_repetitionCode, weightEnumerator_repetitionCode] at h
  simpa only [map_add, map_mul, map_pow, map_sub, map_natCast, map_one, aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one] using h

end Enumerators

end TauCeti

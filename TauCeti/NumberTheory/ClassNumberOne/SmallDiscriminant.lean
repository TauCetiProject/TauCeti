/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.ClassNumber
import TauCeti.NumberTheory.Multiquadratic.Quadratic.Discriminant

/-!
# Imaginary quadratic fields of class number one with small discriminant

The class number of a quadratic field of discriminant `-n` is the number of primitive reduced
forms of discriminant `-n` (`classNumber_eq_card_primitiveReducedForms_of_discr_eq`), a finite set
the kernel enumerates. This file certifies the two finite computations of the class number one
problem.

* The nine discriminants `-3, -4, -7, -8, -11, -19, -43, -67, -163` have class number one: each
  has the principal form as its only primitive reduced form.
* Among the discriminants `-51 < D < 0`, the class number one fields are exactly those of
  discriminant `-3, -4, -7, -8, -11, -19, -43`. Every other fundamental discriminant in this range
  has a second primitive reduced form. The imprimitive discriminants `-12, -16, -27` and `-28`,
  which also have a single primitive reduced form, are not field discriminants.

In Heegner's argument as completed by Stark, and in Shin's version with Siegel functions, the
product estimates for Siegel functions exclude class number one for `D ≤ -31` when `2` is not
inert, and for `D ≤ -51` when `2` is inert and `3` ramifies. The second statement handles the
discriminants these estimates leave.

## Main results

* `TauCeti.NumberField.classNumber_eq_one_of_discr_mem`: a quadratic field whose discriminant is
  one of the nine discriminants above has class number one.
* `TauCeti.NumberField.classNumber_eq_one_iff_of_neg_fifty_one_lt_discr`: a quadratic field with
  `-51 < discr K < 0` has class number one iff its discriminant is `-3, -4, -7, -8, -11, -19` or
  `-43`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §2, Theorem 2.8 and §7, Theorem 7.7.
* H. M. Stark, *A complete determination of the complex quadratic fields of class number one*,
  Michigan Math. J. 14 (1967), 1–27.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §5.
-/

public section

open Finset Module
open TauCeti.BinaryQuadraticForm (classNumber_eq_card_primitiveReducedForms_of_discr_eq)

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **The nine imaginary quadratic fields of class number one.** A quadratic field whose
discriminant is `-3, -4, -7, -8, -11, -19, -43, -67` or `-163` has class number one: the
principal form is its only primitive reduced form. -/
theorem classNumber_eq_one_of_discr_mem (hK : finrank ℚ K = 2)
    (hD : NumberField.discr K ∈ ({-3, -4, -7, -8, -11, -19, -43, -67, -163} : Finset ℤ)) :
    NumberField.classNumber K = 1 := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, NumberField.discr K = -n :=
    ⟨(NumberField.discr K).natAbs, by simp only [mem_insert, mem_singleton] at hD; omega⟩
  rw [classNumber_eq_card_primitiveReducedForms_of_discr_eq hK hn]
  rw [hn] at hD
  -- The kernel counts the primitive reduced forms of each of the nine discriminants.
  have key : ∀ n ∈ ({3, 4, 7, 8, 11, 19, 43, 67, 163} : Finset ℕ),
      #(primitiveReducedForms n) = 1 := by
    decide +kernel
  exact key n (by simp only [mem_insert, mem_singleton] at hD ⊢; omega)

/-- **Class number one for discriminants above `-51`.** A quadratic field with
`-51 < discr K < 0` has class number one exactly when its discriminant is one of
`-3, -4, -7, -8, -11, -19, -43`. -/
theorem classNumber_eq_one_iff_of_neg_fifty_one_lt_discr (hK : finrank ℚ K = 2)
    (h0 : NumberField.discr K < 0) (h51 : -51 < NumberField.discr K) :
    NumberField.classNumber K = 1 ↔
      NumberField.discr K ∈ ({-3, -4, -7, -8, -11, -19, -43} : Finset ℤ) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, NumberField.discr K = -n := ⟨(NumberField.discr K).natAbs, by omega⟩
  have hfund := hn ▸ Multiquadratic.isFundamentalDiscr_discr hK
  rw [classNumber_eq_card_primitiveReducedForms_of_discr_eq hK hn, hn]
  rw [Int.isFundamentalDiscr_iff_squarefree, ← Int.squarefree_natAbs,
    ← Int.squarefree_natAbs] at hfund
  -- The kernel runs through every `n < 51`, deciding fundamentality by squarefreeness and
  -- counting the primitive reduced forms of discriminant `-n`.
  have key : ∀ n : ℕ, n < 51 →
      (((-n : ℤ) % 4 = 1 ∧ Squarefree (-n : ℤ).natAbs) ∨
        ((-n : ℤ) % 4 = 0 ∧ Squarefree ((-n : ℤ) / 4).natAbs ∧
          ((-n : ℤ) / 4 % 4 = 2 ∨ (-n : ℤ) / 4 % 4 = 3))) →
      (#(primitiveReducedForms n) = 1 ↔
        (-n : ℤ) ∈ ({-3, -4, -7, -8, -11, -19, -43} : Finset ℤ)) := by
    decide +kernel
  exact key n (by omega) hfund

end TauCeti.NumberField

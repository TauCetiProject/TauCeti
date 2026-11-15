/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassNumberOne.HeegnerNumbers
import TauCeti.NumberTheory.FundamentalDiscriminant
import TauCeti.NumberTheory.Multiquadratic.Quadratic.Discriminant

/-!
# Imaginary quadratic fields of class number one with small discriminant

The class number of a quadratic field of discriminant `-n` is the number of primitive reduced
forms of discriminant `-n`
(`TauCeti.BinaryQuadraticForm.classNumber_eq_card_primitiveReducedForms_of_discr_eq`), a finite
set the kernel enumerates. This file certifies the finite computation that ends the class number
one problem: among the discriminants `-51 < D < 0`, the class number one fields are exactly those
of discriminant `-n` for `n ∈ heegnerDiscriminants`, that is `-3, -4, -7, -8, -11, -19, -43`.
Every other fundamental discriminant in this range has a second primitive reduced form. The
imprimitive discriminants `-12, -16, -27` and `-28`, which also have a single primitive reduced
form, are not field discriminants. That all nine Heegner discriminants have class number one is
`TauCeti.NumberField.classNumber_eq_one_of_mem_heegnerDiscriminants`.

In Heegner's argument as completed by Stark, and in Shin's version with Siegel functions, the
product estimates for Siegel functions exclude class number one for `D ≤ -31` when `2` is not
inert, and for `D ≤ -51` when `2` is inert and `3` ramifies. The result here handles the
discriminants these estimates leave.

## Main results

* `TauCeti.NumberField.classNumber_eq_one_iff_of_neg_fifty_one_lt_discr`: a quadratic field of
  discriminant `-n > -51` has class number one iff `n ∈ heegnerDiscriminants`.

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

/-- **Class number one for discriminants above `-51`.** A quadratic field of discriminant `-n`
with `-51 < -n` has class number one exactly when `n ∈ heegnerDiscriminants`, that is when its
discriminant is one of `-3, -4, -7, -8, -11, -19, -43`. -/
theorem classNumber_eq_one_iff_of_neg_fifty_one_lt_discr (hK : finrank ℚ K = 2) {n : ℕ}
    (hn : NumberField.discr K = -n) (h51 : -51 < NumberField.discr K) :
    NumberField.classNumber K = 1 ↔ n ∈ heegnerDiscriminants := by
  rw [classNumber_eq_card_primitiveReducedForms_of_discr_eq hK hn]
  -- The kernel runs through every `n < 51`, deciding fundamentality and counting the primitive
  -- reduced forms of discriminant `-n`.
  have key : ∀ n : ℕ, n < 51 → Int.IsFundamentalDiscr (-n) →
      (#(primitiveReducedForms n) = 1 ↔ n ∈ heegnerDiscriminants) := by
    simp only [mem_heegnerDiscriminants]
    decide +kernel
  exact key n (by omega) (hn ▸ Multiquadratic.isFundamentalDiscr_discr hK)

end TauCeti.NumberField

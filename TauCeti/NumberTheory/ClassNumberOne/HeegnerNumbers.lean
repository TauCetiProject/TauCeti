/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.QuadraticAlgebra
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.NumberTheory.FundamentalDiscriminant
public import Mathlib.NumberTheory.NumberField.ClassNumber
import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.ClassNumber
import TauCeti.NumberTheory.NumberField.Quadratic.ClassNumber

/-!
# The nine imaginary quadratic fields of class number one

The **Heegner numbers** are the positive squarefree integers `d` for which the imaginary quadratic
field `ℚ(√(-d))` has class number one: `1, 2, 3, 7, 11, 19, 43, 67, 163`. The corresponding field
discriminants are `-4, -8, -3, -7, -11, -19, -43, -67, -163`: the discriminant of `ℚ(√(-d))` is
`-d` when `-d ≡ 1 (mod 4)` and `-4d` otherwise.

This file certifies that each of these nine fields has class number one, the easy half of the class
number one theorem; the hard half is that no other imaginary quadratic field has class number one.
For each of the nine fundamental discriminants `-n`, the class number of `ℚ(√(-n))` is the number of
primitive reduced binary quadratic forms of discriminant `-n`
(`TauCeti.BinaryQuadraticForm.classNumber_eq_card_primitiveReducedForms`), and the kernel checks
that the principal form is the only one. Since `ℚ(√(-n))` is `ℚ(√(-d))` for the Heegner numbers
`d ≡ 3 (mod 4)`, this covers seven of the nine radicands; for `d = 1, 2` the model `ℚ(√(-d))` is
handled by Minkowski's bound
(`QuadraticAlgebra.classNumber_eq_one_of_mod_four_ne_one_of_natAbs_le_two`).

## Main definitions and results

* `TauCeti.heegnerNumbers`: the nine Heegner numbers `1, 2, 3, 7, 11, 19, 43, 67, 163`.
* `TauCeti.squarefree_of_mem_heegnerNumbers`: every Heegner number is squarefree, so `-d` is the
  negative squarefree radicand of `ℚ(√(-d))`.
* `TauCeti.isFundamentalDiscr_neg_of_mem`: `-3, -4, -7, -8, -11, -19, -43, -67, -163` are
  fundamental discriminants.
* `TauCeti.classNumber_neg_eq_one_of_mem`: the fields `ℚ(√(-n))` of these nine discriminants `-n`
  have class number one.
* `TauCeti.classNumber_eq_one_of_mem_heegnerNumbers`: for every Heegner number `d`, the field
  `ℚ(√(-d))` has class number one.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §2 (reduced forms and class numbers) and Theorem 7.30
  (the list of imaginary quadratic fields of class number one).
-/

public section

open Finset

namespace TauCeti

/-- The **Heegner numbers** `1, 2, 3, 7, 11, 19, 43, 67, 163`: the positive squarefree integers
`d` for which `ℚ(√(-d))` has class number one. That each of them has this property is
`TauCeti.classNumber_eq_one_of_mem_heegnerNumbers`. -/
def heegnerNumbers : Finset ℕ := {1, 2, 3, 7, 11, 19, 43, 67, 163}

/-- Membership in `heegnerNumbers`, spelled out. -/
@[simp] theorem mem_heegnerNumbers {d : ℕ} :
    d ∈ heegnerNumbers ↔
      d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 7 ∨ d = 11 ∨ d = 19 ∨ d = 43 ∨ d = 67 ∨ d = 163 := by
  simp [heegnerNumbers]

/-- Every Heegner number is squarefree. -/
theorem squarefree_of_mem_heegnerNumbers {d : ℕ} (hd : d ∈ heegnerNumbers) : Squarefree d := by
  revert d
  decide +kernel

/-- `-3, -4, -7, -8, -11, -19, -43, -67, -163` are fundamental discriminants. -/
theorem isFundamentalDiscr_neg_of_mem {n : ℕ}
    (hn : n ∈ ({3, 4, 7, 8, 11, 19, 43, 67, 163} : Finset ℕ)) :
    Int.IsFundamentalDiscr (-n) := by
  rw [Int.isFundamentalDiscr_iff_squarefree, ← Int.squarefree_natAbs, ← Int.squarefree_natAbs]
  revert n
  decide +kernel

/-- **Class number one for the nine discriminants.** For `-n` one of the fundamental discriminants
`-3, -4, -7, -8, -11, -19, -43, -67, -163`, the imaginary quadratic field `ℚ(√(-n))` has class
number one. -/
theorem classNumber_neg_eq_one_of_mem {n : ℕ} [NeZero n]
    (hn : n ∈ ({3, 4, 7, 8, 11, 19, 43, 67, 163} : Finset ℕ)) :
    NumberField.classNumber (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) = 1 := by
  rw [BinaryQuadraticForm.classNumber_eq_card_primitiveReducedForms n
    (isFundamentalDiscr_neg_of_mem hn)]
  simp only [mem_insert, mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- **Class number one for the Heegner numbers.** For each Heegner number
`d ∈ {1, 2, 3, 7, 11, 19, 43, 67, 163}`, the imaginary quadratic field `ℚ(√(-d))` has class
number one. -/
theorem classNumber_eq_one_of_mem_heegnerNumbers {d : ℕ} [NeZero d] (hd : d ∈ heegnerNumbers) :
    NumberField.classNumber (QuadraticAlgebra ℚ ((-d : ℤ) : ℚ) 0) = 1 := by
  by_cases h : d = 1 ∨ d = 2
  · refine QuadraticAlgebra.classNumber_eq_one_of_mod_four_ne_one_of_natAbs_le_two
      (Int.squarefree_natAbs.mp (by simpa using squarefree_of_mem_heegnerNumbers hd))
      ?_ ?_ <;> rcases h with rfl | rfl <;> decide
  · refine classNumber_neg_eq_one_of_mem ?_
    simp only [mem_heegnerNumbers] at hd
    simp only [mem_insert, mem_singleton]
    omega

end TauCeti

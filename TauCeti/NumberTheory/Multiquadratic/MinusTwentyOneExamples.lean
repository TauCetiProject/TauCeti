/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.MinusTwentyOneData

/-!
# Shared data for the `-21` prime-discriminant radicand field examples

The worked examples in the multiquadratic roadmap identify the genus field for `ℚ(√-21)` as
`ℚ(√-1, √-3, √-7)`, attached to the prime discriminants `-4`, `-3`, and `-7`. This file records
the shared root and prime-discriminant package consumed by the degree and Galois-cardinality
examples, without making either final example re-export the other.

The prime-discriminant convention follows the standard genus-theory convention in Cox's
*Primes of the Form x² + ny²* and Lemmermeyer's *Reciprocity Laws*.

## Main result

* `TauCeti.Multiquadratic.MinusTwentyOne.primeDiscriminantPackage`: the packaged roots and
  prime-discriminant hypotheses for the `-21` examples.
-/

public section

namespace TauCeti.Multiquadratic

namespace MinusTwentyOne

private theorem primeDiscriminants_isPrimeDiscriminant :
    ∀ i : Fin 3, IsPrimeDiscriminant (negFourNegThreeNegSevenPrimeDiscriminants i) := by
  intro i
  fin_cases i
  · simp [negFourNegThreeNegSevenPrimeDiscriminants]
  · have h3 : IsPrimeDiscriminant (oddPrimeDiscriminant 3) :=
      isPrimeDiscriminant_oddPrimeDiscriminant (p := 3) (by decide) (by decide)
    simpa [negFourNegThreeNegSevenPrimeDiscriminants,
      oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 3 % 4 = 3)] using h3
  · have h7 : IsPrimeDiscriminant (oddPrimeDiscriminant 7) :=
      isPrimeDiscriminant_oddPrimeDiscriminant (p := 7) (by decide) (by decide)
    simpa [negFourNegThreeNegSevenPrimeDiscriminants,
      oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 7 % 4 = 3)] using h7

private theorem primeDiscriminants_injective :
    Function.Injective negFourNegThreeNegSevenPrimeDiscriminants := by
  decide

private theorem primeDiscriminants_not_all_even :
    ¬ ((∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = -4) ∧
      (∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = 8) ∧
        (∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = -8)) := by
  decide

private noncomputable abbrev primeDiscriminantRoot : Fin 3 → ℂ :=
  ![Complex.I, sqrtNegThree, sqrtNegSeven]

private theorem primeDiscriminantRoot_sq (i : Fin 3) :
    primeDiscriminantRoot i ^ 2 =
      algebraMap ℚ ℂ
        (((primeDiscriminantRadicand
          (negFourNegThreeNegSevenPrimeDiscriminants i) : ℤ) : ℚ)) := by
  fin_cases i
  · simp [primeDiscriminantRoot, negFourNegThreeNegSevenPrimeDiscriminants, Complex.I_sq]
  · have hrad : primeDiscriminantRadicand (-3) = -3 := by
      have h := primeDiscriminantRadicand_oddPrimeDiscriminant (p := 3) (by decide)
      simpa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 3 % 4 = 3)] using h
    simp [primeDiscriminantRoot, negFourNegThreeNegSevenPrimeDiscriminants, hrad]
  · have hrad : primeDiscriminantRadicand (-7) = -7 := by
      have h := primeDiscriminantRadicand_oddPrimeDiscriminant (p := 7) (by decide)
      simpa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 7 % 4 = 3)] using h
    simp [primeDiscriminantRoot, negFourNegThreeNegSevenPrimeDiscriminants, hrad]

private theorem range_primeDiscriminantRoot :
    Set.range primeDiscriminantRoot = {Complex.I, sqrtNegThree, sqrtNegSeven} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    rcases hx with ⟨i, rfl⟩
    fin_cases i <;> simp [primeDiscriminantRoot]
  · intro hx
    rcases hx with hx | hx | hx
    · exact ⟨0, by simp [primeDiscriminantRoot, hx]⟩
    · exact ⟨1, by simp [primeDiscriminantRoot, hx]⟩
    · exact ⟨2, by simp [primeDiscriminantRoot, hx]⟩

/-- Packaged roots and hypotheses for the `-21` prime-discriminant examples. -/
structure PrimeDiscriminantPackage where
  /-- The three chosen square roots attached to the prime discriminants `-4`, `-3`, and `-7`. -/
  root : Fin 3 → ℂ
  /-- Each chosen root squares to the radicand associated to its prime discriminant. -/
  root_sq : ∀ i, root i ^ 2 =
    algebraMap ℚ ℂ
      (((primeDiscriminantRadicand (negFourNegThreeNegSevenPrimeDiscriminants i) : ℤ) : ℚ))
  /-- The entries `-4`, `-3`, and `-7` are prime discriminants. -/
  isPrimeDiscriminant : ∀ i, IsPrimeDiscriminant (negFourNegThreeNegSevenPrimeDiscriminants i)
  /-- The three prime discriminants in the package are pairwise distinct. -/
  injective : Function.Injective negFourNegThreeNegSevenPrimeDiscriminants
  /-- The package does not contain all three even prime discriminants. -/
  not_all_even : ¬ ((∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = -4) ∧
    (∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = 8) ∧
      (∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = -8))
  /-- The chosen roots are exactly `√-1`, `√-3`, and `√-7`. -/
  range_root : Set.range root = {Complex.I, sqrtNegThree, sqrtNegSeven}

/-- The reusable root package for the `ℚ(√-1, √-3, √-7)` worked examples. -/
noncomputable def primeDiscriminantPackage : PrimeDiscriminantPackage where
  root := primeDiscriminantRoot
  root_sq := primeDiscriminantRoot_sq
  isPrimeDiscriminant := primeDiscriminants_isPrimeDiscriminant
  injective := primeDiscriminants_injective
  not_all_even := primeDiscriminants_not_all_even
  range_root := range_primeDiscriminantRoot

end MinusTwentyOne

end TauCeti.Multiquadratic

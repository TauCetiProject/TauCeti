/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.LegendrePrimeDiscriminantExamples
public import TauCeti.NumberTheory.Multiquadratic.MinusTwentyOneGalois

/-!
# Degrees of the first prime-discriminant generator fields

The multiquadratic roadmap's genus-field worked examples use the prime-discriminant generator
lists `[-4, 5]` for `ℚ(√-5)` and `[-4, -3, -7]` for `ℚ(√-21)`. The corresponding radicands are
`[-1, 5]` and `[-1, -3, -7]`, so the proposed genus fields are `ℚ(i, √5)` and
`ℚ(i, √-3, √-7)`.

This file records the immediate Layer-0 degree consequences for those two composita. The actual
class-field-theoretic statements identifying them as genus fields are later roadmap work; here we
only package the already-proved prime-discriminant independence theorem in the two concrete forms
that the worked examples will consume.

The prime-discriminant convention follows Cox's *Primes of the Form x² + ny²* and Lemmermeyer's
*Reciprocity Laws*, as in the prime-discriminant API reused below.

## Main results

* `TauCeti.Multiquadratic.finrank_adjoin_I_sqrt_five`: `[ℚ(i, √5) : ℚ] = 4`.
* `TauCeti.Multiquadratic.finrank_adjoin_I_sqrt_neg_three_sqrt_neg_seven`:
  `[ℚ(i, √-3, √-7) : ℚ] = 8`.
-/

public section

open IntermediateField

namespace TauCeti.Multiquadratic

private theorem root_neg_four_five_sq (i : Fin 2) :
    (fun i : Fin 2 => ![Complex.I, ((Real.sqrt 5 : ℝ) : ℂ)] i) i ^ 2 =
      algebraMap ℚ ℂ
        (((primeDiscriminantRadicand (negFourFivePrimeDiscriminants i) : ℤ) : ℚ)) := by
  fin_cases i
  · simp [negFourFivePrimeDiscriminants, Complex.I_sq]
  · have h : (((Real.sqrt 5 : ℝ) : ℂ) ^ 2) = (5 : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
      norm_num
    simpa [negFourFivePrimeDiscriminants, primeDiscriminantRadicand] using h

private theorem isPrimeDiscriminant_negFourFivePrimeDiscriminants :
    ∀ i : Fin 2, IsPrimeDiscriminant (negFourFivePrimeDiscriminants i) := by
  intro i
  fin_cases i
  · simp [negFourFivePrimeDiscriminants]
  · have h5 : IsPrimeDiscriminant (5 : ℤ) := by
      simpa [oddPrimeDiscriminant_of_mod_four_eq_one (by norm_num : 5 % 4 = 1)]
        using isPrimeDiscriminant_oddPrimeDiscriminant (p := 5) (by decide) (by decide)
    simpa [negFourFivePrimeDiscriminants] using h5

private theorem injective_negFourFivePrimeDiscriminants :
    Function.Injective negFourFivePrimeDiscriminants := by
  decide

private theorem not_all_even_negFourFivePrimeDiscriminants :
    ¬ ((∃ i : Fin 2, negFourFivePrimeDiscriminants i = -4) ∧
      (∃ i : Fin 2, negFourFivePrimeDiscriminants i = 8) ∧
        (∃ i : Fin 2, negFourFivePrimeDiscriminants i = -8)) := by
  decide

private theorem range_roots_neg_four_five :
    (Set.range fun i : Fin 2 => ![Complex.I, ((Real.sqrt 5 : ℝ) : ℂ)] i)
      = {Complex.I, ((Real.sqrt 5 : ℝ) : ℂ)} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    rcases hx with hx | hx
    · exact ⟨0, by simp [hx]⟩
    · exact ⟨1, by simp [hx]⟩

/-- **Worked example: `[ℚ(i, √5) : ℚ] = 4`.** This is the full-degree Layer-0 input for the
prime-discriminant generator field attached to the `ℚ(√-5)` genus-field example. -/
theorem finrank_adjoin_I_sqrt_five :
    Module.finrank ℚ
      (adjoin ℚ ({Complex.I, ((Real.sqrt 5 : ℝ) : ℂ)} : Set ℂ) : IntermediateField ℚ ℂ) = 4 := by
  have h := finrank_adjoin_roots_primeDiscriminantRadicands negFourFivePrimeDiscriminants
    isPrimeDiscriminant_negFourFivePrimeDiscriminants injective_negFourFivePrimeDiscriminants
    not_all_even_negFourFivePrimeDiscriminants
    (fun i : Fin 2 => ![Complex.I, ((Real.sqrt 5 : ℝ) : ℂ)] i) root_neg_four_five_sq
  rw [range_roots_neg_four_five] at h
  exact h.trans (by norm_num [Nat.card_fin])

private theorem root_neg_four_neg_three_neg_seven_sq (i : Fin 3) :
    (fun i : Fin 3 => ![Complex.I, sqrtNegThree, sqrtNegSeven] i) i ^ 2 =
      algebraMap ℚ ℂ
        (((primeDiscriminantRadicand (negFourNegThreeNegSevenPrimeDiscriminants i) : ℤ) : ℚ)) := by
  fin_cases i
  · simp [negFourNegThreeNegSevenPrimeDiscriminants, Complex.I_sq]
  · have hrad : primeDiscriminantRadicand (-3) = -3 := by
      have h := primeDiscriminantRadicand_oddPrimeDiscriminant (p := 3) (by decide)
      simpa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 3 % 4 = 3)] using h
    simp [negFourNegThreeNegSevenPrimeDiscriminants, hrad]
  · have hrad : primeDiscriminantRadicand (-7) = -7 := by
      have h := primeDiscriminantRadicand_oddPrimeDiscriminant (p := 7) (by decide)
      simpa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 7 % 4 = 3)] using h
    simp [negFourNegThreeNegSevenPrimeDiscriminants, hrad]

private theorem isPrimeDiscriminant_negFourNegThreeNegSevenPrimeDiscriminants :
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

private theorem injective_negFourNegThreeNegSevenPrimeDiscriminants :
    Function.Injective negFourNegThreeNegSevenPrimeDiscriminants := by
  decide

private theorem not_all_even_negFourNegThreeNegSevenPrimeDiscriminants :
    ¬ ((∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = -4) ∧
      (∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = 8) ∧
        (∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = -8)) := by
  decide

private theorem range_roots_neg_four_neg_three_neg_seven :
    (Set.range fun i : Fin 3 => ![Complex.I, sqrtNegThree, sqrtNegSeven] i)
      = {Complex.I, sqrtNegThree, sqrtNegSeven} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    rcases hx with hx | hx | hx
    · exact ⟨0, by simp [hx]⟩
    · exact ⟨1, by simp [hx]⟩
    · exact ⟨2, by simp [hx]⟩

/-- **Worked example: `[ℚ(i, √-3, √-7) : ℚ] = 8`.** This is the full-degree Layer-0 input for
the prime-discriminant generator field attached to the `ℚ(√-21)` genus-field example. -/
theorem finrank_adjoin_I_sqrt_neg_three_sqrt_neg_seven :
    Module.finrank ℚ
      (adjoin ℚ ({Complex.I, sqrtNegThree, sqrtNegSeven} : Set ℂ) : IntermediateField ℚ ℂ) =
        8 := by
  have h := finrank_adjoin_roots_primeDiscriminantRadicands
    negFourNegThreeNegSevenPrimeDiscriminants
    isPrimeDiscriminant_negFourNegThreeNegSevenPrimeDiscriminants
    injective_negFourNegThreeNegSevenPrimeDiscriminants
    not_all_even_negFourNegThreeNegSevenPrimeDiscriminants
    (fun i : Fin 3 => ![Complex.I, sqrtNegThree, sqrtNegSeven] i)
    root_neg_four_neg_three_neg_seven_sq
  rw [range_roots_neg_four_neg_three_neg_seven] at h
  exact h.trans (by norm_num [Nat.card_fin])

end TauCeti.Multiquadratic

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Degree
import TauCeti.NumberTheory.Multiquadratic.CMField.Basic
import TauCeti.FieldTheory.Kummer.Extension

/-!
# The prime-discriminant compositum of `ℚ(√3)`

The factorization `12 = (-4) · (-3)` identifies the candidate narrow genus field with
`ℚ(i, √3)`. This concrete presentation is used to identify the narrow Hilbert class field;
unlike the ordinary genus field, it allows ramification at the real places.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §6.A.
* F. Lemmermeyer, *Reciprocity Laws: From Euler to Eisenstein*, §2.2.
-/

public noncomputable section

open IntermediateField

namespace TauCeti.Multiquadratic

/-- The prime-discriminant factorization of the discriminant of `ℚ(√3)` is `12 = (-4)·(-3)`. -/
@[simp] theorem genusPrimeDiscriminants_three (hd : Squarefree (3 : ℤ)) :
    genusPrimeDiscriminants hd = {-4, -3} := by
  apply genusPrimeDiscriminants_eq hd
  · intro P hP
    fin_cases hP
    · exact isPrimeDiscriminant_neg_four
    · simpa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 3 % 4 = 3)]
        using isPrimeDiscriminant_oddPrimeDiscriminant (p := 3) (by decide) (by decide)
  · norm_num [fundamentalDiscriminant_of_mod_four_ne_one (by decide : (3 : ℤ) % 4 ≠ 1)]

/-- The prime-discriminant compositum of `ℚ(√3)` is `ℚ(i, √3)`. -/
theorem candidateGenusField_three_eq (hd : Squarefree (3 : ℤ)) :
    candidateGenusField hd = adjoin ℚ ({Complex.I, (Real.sqrt 3 : ℂ)} : Set ℂ) := by
  have hdeg : Module.finrank ℚ
      (adjoin ℚ ({Complex.I, (Real.sqrt 3 : ℂ)} : Set ℂ)) = 4 := by
    simpa using finrank_adjoin_I_sqrt_prime 3 Nat.prime_three
  have := Module.finite_of_finrank_pos (hdeg ▸ (by norm_num : 0 < 4))
  apply IntermediateField.eq_of_le_of_finrank_eq
  · rw [candidateGenusField_le_iff]
    intro P
    have hP : P.val ∈ ({-4, -3} : Finset ℤ) := by
      simpa only [genusPrimeDiscriminants_three hd] using P.property
    have hI : Complex.I ∈ adjoin ℚ ({Complex.I, (Real.sqrt 3 : ℂ)} : Set ℂ) :=
      subset_adjoin ℚ _ (by simp)
    have hsqrt : (Real.sqrt 3 : ℂ) ∈
        adjoin ℚ ({Complex.I, (Real.sqrt 3 : ℂ)} : Set ℂ) :=
      subset_adjoin ℚ _ (by simp)
    rcases (Finset.mem_insert.trans (or_congr_right Finset.mem_singleton)).mp hP with hP | hP
    · have hroot : genusFieldRoot hd P ^ 2 = algebraMap ℚ ℂ (-1) := by simp [hP]
      have hsq : Complex.I ^ 2 = algebraMap ℚ ℂ (-1) := by simp
      have heq := (adjoin_rootSet_X_pow_two_sub_C hroot).symm.trans
        (adjoin_rootSet_X_pow_two_sub_C hsq)
      exact (adjoin_simple_le_iff.mpr hI)
        (heq ▸ mem_adjoin_simple_self ℚ (genusFieldRoot hd P))
    · have hroot : genusFieldRoot hd P ^ 2 = algebraMap ℚ ℂ (-3) := by
        simp [hP, primeDiscriminantRadicand]
      have hsq : (Complex.I * (Real.sqrt 3 : ℂ)) ^ 2 = algebraMap ℚ ℂ (-3) := by
        simp [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt]
      have heq := (adjoin_rootSet_X_pow_two_sub_C hroot).symm.trans
        (adjoin_rootSet_X_pow_two_sub_C hsq)
      exact (adjoin_simple_le_iff.mpr (mul_mem hI hsqrt))
        (heq ▸ mem_adjoin_simple_self ℚ (genusFieldRoot hd P))
  · rw [finrank_candidateGenusField, genusPrimeDiscriminants_three,
      hdeg]
    norm_num

end TauCeti.Multiquadratic

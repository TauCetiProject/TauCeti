/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.GenusField
public import TauCeti.NumberTheory.Multiquadratic.CMField.Basic
import TauCeti.FieldTheory.KummerExtension

/-!
# The genus field of `ℚ(√-5)`

The prime-discriminant factorization `-20 = (-4) · 5` identifies the canonical genus field
with the explicit complex compositum `ℚ(i, √5)`. Consequently this compositum is abelian over
`ℚ`, everywhere unramified over its quadratic subfield `ℚ(√-5)`, and maximal with these
properties. The chosen square root of `-5` is existential: the field identification is
independent of the signs of the roots used in the canonical construction.

Together with the class-number, relative-degree, and `2`-rank calculations in the neighbouring
modules, this gives the explicit genus-field example for discriminant `-20`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, Section 6.A.
* F. Lemmermeyer, *Reciprocity Laws: From Euler to Eisenstein*, Section 2.2.
-/

public section

open IntermediateField

namespace TauCeti.Multiquadratic

/-- The prime discriminants of `ℚ(√-5)` are `-4` and `5`. -/
@[simp] theorem genusPrimeDiscriminants_neg_five (hd : Squarefree (-5 : ℤ)) :
    genusPrimeDiscriminants hd = {-4, 5} := by
  apply genusPrimeDiscriminants_eq hd
  · intro P hP
    fin_cases hP
    · exact isPrimeDiscriminant_neg_four
    · simpa [oddPrimeDiscriminant_of_mod_four_eq_one (by norm_num : 5 % 4 = 1)]
        using isPrimeDiscriminant_oddPrimeDiscriminant (p := 5) (by decide) (by decide)
  · norm_num [fundamentalDiscriminant_of_mod_four_ne_one (by decide : (-5 : ℤ) % 4 ≠ 1)]

/-- The explicit compositum `ℚ(i, √5)` is a number field. -/
noncomputable instance numberField_adjoin_I_sqrt_five :
    NumberField (adjoin ℚ ({Complex.I, (Real.sqrt 5 : ℂ)} : Set ℂ)) := by
  have hfin : 0 < Module.finrank ℚ
      (adjoin ℚ ({Complex.I, (Real.sqrt 5 : ℂ)} : Set ℂ)) := by
    rw [finrank_adjoin_I_sqrt_five]
    norm_num
  have := Module.finite_of_finrank_pos hfin
  exact NumberField.of_module_finite ℚ _

/-- The canonical genus field of `ℚ(√-5)` is the explicit compositum `ℚ(i, √5)`. -/
theorem candidateGenusField_neg_five_eq (hd : Squarefree (-5 : ℤ)) :
    candidateGenusField hd = adjoin ℚ ({Complex.I, (Real.sqrt 5 : ℂ)} : Set ℂ) := by
  apply IntermediateField.eq_of_le_of_finrank_eq
  · rw [candidateGenusField_le_iff]
    intro P
    have hP : P.val ∈ ({-4, 5} : Finset ℤ) := by
      simpa only [genusPrimeDiscriminants_neg_five hd] using P.property
    -- Each chosen root generates the splitting field of the same quadratic as the explicit root.
    rcases (Finset.mem_insert.trans (or_congr_right Finset.mem_singleton)).mp hP with hP | hP
    · have hroot : genusFieldRoot hd P ^ 2 = algebraMap ℚ ℂ (-1) := by
        simp [hP]
      have hI : Complex.I ^ 2 = algebraMap ℚ ℂ (-1) := by simp
      have heq := (adjoin_rootSet_X_pow_two_sub_C hroot).symm.trans
        (adjoin_rootSet_X_pow_two_sub_C hI)
      exact (adjoin_simple_le_iff.mpr (subset_adjoin ℚ _ (by simp)))
        (heq ▸ mem_adjoin_simple_self ℚ (genusFieldRoot hd P))
    · have hroot : genusFieldRoot hd P ^ 2 = algebraMap ℚ ℂ (5 : ℚ) := by
        simp [hP, primeDiscriminantRadicand]
      have hsqrt : (Real.sqrt 5 : ℂ) ^ 2 = algebraMap ℚ ℂ (5 : ℚ) := by
        norm_cast
        norm_num
      have heq := (adjoin_rootSet_X_pow_two_sub_C hroot).symm.trans
        (adjoin_rootSet_X_pow_two_sub_C hsqrt)
      exact (adjoin_simple_le_iff.mpr (subset_adjoin ℚ _ (by simp)))
        (heq ▸ mem_adjoin_simple_self ℚ (genusFieldRoot hd P))
  · rw [finrank_candidateGenusField, genusPrimeDiscriminants_neg_five,
      finrank_adjoin_I_sqrt_five]
    norm_num

/-- **The genus field of `ℚ(√-5)` is `ℚ(i, √5)`.** The explicit compositum satisfies the
all-places unramifiedness and maximality characterization, for a square root of `-5` in it. -/
theorem exists_isGenusField_adjoin_I_sqrt_five :
    ∃ y : adjoin ℚ ({Complex.I, (Real.sqrt 5 : ℂ)} : Set ℂ),
      IsGenusField (-5) (adjoin ℚ ({Complex.I, (Real.sqrt 5 : ℂ)} : Set ℂ)) y := by
  have hd : Squarefree (-5 : ℤ) := (Int.prime_iff_natAbs_prime.mpr (by decide)).squarefree
  -- Quantify over the number-field instance so transport changes the carrier and its instance
  -- together; rewriting the carrier alone leaves a dependent instance on the old field.
  let motive (F : IntermediateField ℚ ℂ) :=
    ∀ [NumberField F], ∃ y : F, IsGenusField (-5) F y
  have h : motive (candidateGenusField hd) := fun [_] =>
    ⟨candidateGenusFieldBaseRoot hd, isGenusField_candidateGenusField hd (by norm_num)⟩
  have h' : motive (adjoin ℚ ({Complex.I, (Real.sqrt 5 : ℂ)} : Set ℂ)) :=
    (congrArg motive (candidateGenusField_neg_five_eq hd)).mp h
  exact h'

end TauCeti.Multiquadratic

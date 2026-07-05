/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.MinusTwentyOneData
public import TauCeti.NumberTheory.Multiquadratic.Degree

/-!
# The degree of the `-21` prime-discriminant radicand field

This file exposes the degree worked example for `ℚ(√-1, √-3, √-7)`.

## Main result

* `TauCeti.Multiquadratic.finrank_adjoin_I_sqrt_neg_three_sqrt_neg_seven`: the
  worked-example degree `[ℚ(i, √-3, √-7) : ℚ] = 8`.
-/

namespace TauCeti.Multiquadratic

public section

/-- **Worked example: `[ℚ(i, √-3, √-7) : ℚ] = 8`.** This is the degree of the
multiquadratic field `ℚ(√-1, √-3, √-7)` attached to the prime discriminants `-4`, `-3`,
and `-7` in the genus-field example for `ℚ(√-21)`. -/
theorem finrank_adjoin_I_sqrt_neg_three_sqrt_neg_seven :
    Module.finrank ℚ
      (IntermediateField.adjoin ℚ ({Complex.I, sqrtNegThree, sqrtNegSeven} : Set ℂ) :
        IntermediateField ℚ ℂ)
      = 8 := by
  have h := finrank_adjoin_range
    (d := fun i =>
      (((primeDiscriminantRadicand
        (negFourNegThreeNegSevenPrimeDiscriminants i) : ℤ) : ℚ)))
    (root := negFourNegThreeNegSevenPrimeDiscriminantRoots)
    negFourNegThreeNegSevenPrimeDiscriminantRoots_sq
    not_isSquare_prod_negFourNegThreeNegSevenPrimeDiscriminantRadicands
  rw [show ({Complex.I, sqrtNegThree, sqrtNegSeven} : Set ℂ) =
    Set.range negFourNegThreeNegSevenPrimeDiscriminantRoots by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
      constructor
      · intro hx
        rcases hx with hx | hx | hx
        · exact ⟨0, by simp [negFourNegThreeNegSevenPrimeDiscriminantRoots, hx]⟩
        · exact ⟨1, by simp [negFourNegThreeNegSevenPrimeDiscriminantRoots, hx]⟩
        · exact ⟨2, by simp [negFourNegThreeNegSevenPrimeDiscriminantRoots, hx]⟩
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp [negFourNegThreeNegSevenPrimeDiscriminantRoots]]
  simpa [Nat.card_fin] using h

end

end TauCeti.Multiquadratic

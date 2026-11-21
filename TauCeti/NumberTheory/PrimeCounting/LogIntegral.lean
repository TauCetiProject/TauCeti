/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Unoffset
import TauCeti.Analysis.SpecialFunctions.LogIntegral.Bounds

/-!
# Conditional enclosures of `li 2` for explicit prime counting

This file bridges the unconditional enclosures of `Real.li 2 - Real.eulerMascheroniConstant` in
`TauCeti.Analysis.SpecialFunctions.LogIntegral.Bounds` to the decimal enclosure
`|γ - 0.5772156649| < 10⁻⁹` used in explicit prime-counting bounds.

## Main declarations

* `TauCeti.le_li_two_of_abs_eulerMascheroniConstant_sub_lt`: `1.0451 ≤ Real.li 2` assuming
  `|γ - 0.5772156649| < 10⁻⁹`.
* `TauCeti.li_two_le_of_abs_eulerMascheroniConstant_sub_lt`: `Real.li 2 ≤ 1.0452` assuming
  `|γ - 0.5772156649| < 10⁻⁹`.

## References

* O. Ramaré and R. Rumely, *Primes in arithmetic progressions*, *Math. Comp.* 65 (1996)
  (for the decimal enclosure `|γ - 0.5772156649| < 10⁻⁹`).
* F. W. J. Olver et al., *NIST Digital Library of Mathematical Functions*, §6.2.
-/

public section

namespace TauCeti

/-- Conditional lower bound `1.0451 ≤ Real.li 2` under `|γ - 0.5772156649| < 10⁻⁹`. -/
theorem le_li_two_of_abs_eulerMascheroniConstant_sub_lt
    (hγ : |Real.eulerMascheroniConstant - 0.5772156649| < 10 ^ (-(9 : ℤ))) :
    (1.0451 : ℝ) ≤ Real.li 2 := by
  rw [abs_lt] at hγ
  norm_num at hγ
  linarith [hγ.1, Real.le_li_two_sub_eulerMascheroniConstant]

/-- Conditional upper bound `Real.li 2 ≤ 1.0452` under `|γ - 0.5772156649| < 10⁻⁹`. -/
theorem li_two_le_of_abs_eulerMascheroniConstant_sub_lt
    (hγ : |Real.eulerMascheroniConstant - 0.5772156649| < 10 ^ (-(9 : ℤ))) :
    Real.li 2 ≤ 1.0452 := by
  rw [abs_lt] at hγ
  norm_num at hγ
  linarith [hγ.2, Real.li_two_sub_eulerMascheroniConstant_le]

end TauCeti

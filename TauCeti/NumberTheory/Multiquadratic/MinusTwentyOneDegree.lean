/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.MinusTwentyOneData
public import TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminantIndependence
public import TauCeti.NumberTheory.Multiquadratic.MinusTwentyOneExamples

/-!
# The degree of the `-21` prime-discriminant radicand field

This file exposes the degree worked example for `ℚ(√-1, √-3, √-7)`. Its proof uses the shared
prime-discriminant proof package in
`TauCeti.NumberTheory.Multiquadratic.MinusTwentyOneExamples`.

## Main result

* `TauCeti.Multiquadratic.finrank_adjoin_I_sqrt_neg_three_sqrt_neg_seven`: the
  worked-example degree `[ℚ(i, √-3, √-7) : ℚ] = 8`.
-/

public section

open IntermediateField

namespace TauCeti.Multiquadratic

/-- **Worked example: `[ℚ(i, √-3, √-7) : ℚ] = 8`.** This is the degree of the
multiquadratic field `ℚ(√-1, √-3, √-7)` attached to the prime discriminants `-4`, `-3`,
and `-7` in the genus-field example for `ℚ(√-21)`. -/
theorem finrank_adjoin_I_sqrt_neg_three_sqrt_neg_seven :
    Module.finrank ℚ
      (adjoin ℚ ({Complex.I, sqrtNegThree, sqrtNegSeven} : Set ℂ) :
        IntermediateField ℚ ℂ)
      = 8 :=
  MinusTwentyOne.adjoin_I_sqrt_neg_three_sqrt_neg_seven_degree_and_card.1

end TauCeti.Multiquadratic

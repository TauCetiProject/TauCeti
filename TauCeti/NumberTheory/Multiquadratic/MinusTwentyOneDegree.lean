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

This file exposes the degree worked example for `ℚ(√-1, √-3, √-7)` by publicly importing the
shared implementation module.

## Main result

* `TauCeti.Multiquadratic.finrank_adjoin_I_sqrt_neg_three_sqrt_neg_seven`: the
  worked-example degree `[ℚ(i, √-3, √-7) : ℚ] = 8`.
-/

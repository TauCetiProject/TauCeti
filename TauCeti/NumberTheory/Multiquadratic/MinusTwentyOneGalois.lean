/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.MinusTwentyOneData
public import TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminantGaloisGroup
public import TauCeti.NumberTheory.Multiquadratic.MinusTwentyOneExamples

/-!
# The Galois group of the `-21` prime-discriminant radicand field

This file exposes the Galois-cardinality worked example for `ℚ(√-1, √-3, √-7)` by publicly
importing the shared implementation module.

## Main result

* `TauCeti.Multiquadratic.card_aut_adjoin_I_sqrt_neg_three_sqrt_neg_seven`: the
  worked-example cardinality `|Gal(ℚ(i, √-3, √-7)/ℚ)| = 8`.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Basic.Complex.Basic

/-!
# Conjugating integer powers of purely imaginary numbers

A purely imaginary complex number `c` satisfies `conj c = -c`, so conjugating an integer power
`c ^ p` multiplies it by the sign `(-1) ^ p`.

## Main results

* `Complex.conj_zpow_of_conj_eq_neg`: conjugating an integer power `c ^ p` of a purely imaginary
  number multiplies it by the sign `(-1) ^ p`.
-/

public section

namespace Complex

/-- Conjugation of a power of a purely imaginary number is the power multiplied by the sign
`(-1) ^ p`. -/
theorem conj_zpow_of_conj_eq_neg {c : ℂ} (hc : starRingEnd ℂ c = -c) (p : ℤ) :
    starRingEnd ℂ (c ^ p) = (p.negOnePow : ℂ) * c ^ p := by
  rw [map_zpow₀, hc]
  rcases Int.even_or_odd p with hp | hp
  · simp [hp.neg_zpow, Int.negOnePow_even p hp]
  · simp [hp.neg_zpow, Int.negOnePow_odd p hp]

end Complex

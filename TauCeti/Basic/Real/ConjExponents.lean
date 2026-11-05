/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.ConjExponents

/-!
# Natural-number Hölder exponents

A natural number `n` that has a Hölder conjugate exponent satisfies `2 ≤ n`, since Hölder
conjugate exponents are greater than one (`Real.HolderConjugate.two_le_of_natCast`,
`NNReal.HolderConjugate.two_le_of_natCast`). This is how the dimension bound `2 ≤ n` is read off
the Sobolev exponent `n / (n - 1)` of the Gagliardo–Nirenberg–Sobolev inequality.
-/

public section

open scoped NNReal

/-- A natural number with a real Hölder conjugate exponent is at least two. -/
theorem Real.HolderConjugate.two_le_of_natCast {n : ℕ} {q : ℝ}
    (h : (n : ℝ).HolderConjugate q) : 2 ≤ n := by
  exact_mod_cast h.lt

/-- A natural number with a nonnegative real Hölder conjugate exponent is at least two. -/
theorem NNReal.HolderConjugate.two_le_of_natCast {n : ℕ} {q : ℝ≥0}
    (h : (n : ℝ≥0).HolderConjugate q) : 2 ≤ n := by
  exact_mod_cast h.lt

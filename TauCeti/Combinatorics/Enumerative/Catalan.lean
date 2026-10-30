/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# The first-order recurrence of the Catalan numbers

Mathlib defines `catalan` by the convolution recurrence and proves
`(n + 1) * catalan n = Nat.centralBinom n`. Combined with the ratio recurrence of the central
binomial coefficients, this gives the first-order recurrence
`(n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n`. This is the form in which Catalan
numbers arise as solutions of linear moment recurrences, such as the even moments of the
semicircle law.
-/

public section

/-- The first-order recurrence `(n + 2) Cₙ₊₁ = 2 (2n + 1) Cₙ` of the Catalan numbers. -/
theorem add_two_mul_catalan_succ (n : ℕ) :
    (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  apply Nat.eq_of_mul_eq_mul_left n.succ_pos
  calc
    (n + 1) * ((n + 2) * catalan (n + 1)) = (n + 1) * (n + 1).centralBinom := by
      rw [← succ_mul_catalan_eq_centralBinom]
    _ = 2 * (2 * n + 1) * n.centralBinom := Nat.succ_mul_centralBinom_succ n
    _ = (n + 1) * (2 * (2 * n + 1) * catalan n) := by
      rw [← succ_mul_catalan_eq_centralBinom]
      ring

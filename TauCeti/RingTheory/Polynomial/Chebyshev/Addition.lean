/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev

import Mathlib.Tactic.LinearCombination

/-!
# The addition formula for the rescaled Chebyshev polynomials of the second kind

Mathlib's rescaled Chebyshev polynomials of the second kind `Polynomial.Chebyshev.S R n`
satisfy `S₀ = 1`, `S₁ = X` and `Sₙ₊₂ = X Sₙ₊₁ - Sₙ`. This file proves, over any commutative
ring and for all integer indices, the addition formula

`S (m + n) = S m * S n - S (m - 1) * S (n - 1)`,

and deduces the divisibility `S (d - 1) ∣ S (n - 1)` whenever `d ∣ n`.

Evaluated at `δ = q + q⁻¹`, the polynomial `S (n - 1)` is the quantum integer `[n]`, so these
are the identities `[m + n] = [m] [n + 1] - [m - 1] [n]` and `[d] ∣ [n]` for `d ∣ n`, proved once
as identities between polynomials with integer coefficients.

## Main results

* `Polynomial.Chebyshev.S_add`: the addition formula.
* `Polynomial.Chebyshev.S_sub_one_dvd_S_sub_one`: `S (d - 1) ∣ S (n - 1)` when `d ∣ n`.
-/

public section

namespace Polynomial.Chebyshev

variable (R : Type*) [CommRing R]

/-- The **addition formula** for the rescaled Chebyshev polynomials of the second kind:
`S (m + n) = S m * S n - S (m - 1) * S (n - 1)` for all integers `m` and `n`. -/
theorem S_add (m n : ℤ) : S R (m + n) = S R m * S R n - S R (m - 1) * S R (n - 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one =>
    rw [S_one, sub_self, S_zero, S_add_one]
    ring
  | add_two n ih₁ ih₀ =>
    linear_combination (norm := ring_nf) S_add_two R (m + n) + X * ih₁ - ih₀ -
      S R m * S_add_two R n + S R (m - 1) * S_add_one R n
  | neg_add_one n ih₀ ih₁ =>
    linear_combination (norm := ring_nf) S_sub_one R (m + -n) + X * ih₀ - ih₁ -
      S R m * S_sub_one R (-n) + S R (m - 1) * S_sub_one R (-n - 1)

/-- **Divisibility of the rescaled Chebyshev polynomials**: if `d ∣ n` then
`S (d - 1) ∣ S (n - 1)`. At `δ = q + q⁻¹` this says that the quantum integer `[d]` divides
`[n]`. -/
theorem S_sub_one_dvd_S_sub_one {d n : ℤ} (h : d ∣ n) : S R (d - 1) ∣ S R (n - 1) := by
  obtain ⟨k, rfl⟩ := h
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [show d * (k + 1) - 1 = (d * k - 1) + d by ring, S_add]
    exact dvd_sub (dvd_mul_of_dvd_left ih _) (dvd_mul_left _ _)
  | pred k ih =>
    rw [show d * (-(k : ℤ) - 1) - 1 = (d * -k - 1) + -d by ring, S_add,
      show -d - 1 = -(d - 1) - 2 by ring, S_neg_sub_two]
    exact dvd_sub (dvd_mul_of_dvd_left ih _) (dvd_mul_of_dvd_right (dvd_neg.2 dvd_rfl) _)

end Polynomial.Chebyshev

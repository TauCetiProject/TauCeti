/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree

import Mathlib.Algebra.Polynomial.Monic

/-!
# Monic divisors of powers of `X`

Over a semiring without zero divisors, every monic divisor of `X ^ n` is itself a power of `X`:
comparing `natDegree` and `natTrailingDegree` across a factorization `X ^ n = g * q` forces
`g.natTrailingDegree = g.natDegree`, so `g = X ^ g.natDegree` by
`Polynomial.Monic.eq_X_pow_iff_natTrailingDegree_eq_natDegree`.

## Main results

* `Polynomial.Monic.eq_X_pow_of_dvd_X_pow`: a monic divisor `g` of `X ^ n` equals
  `X ^ g.natDegree`.
* `Polynomial.Monic.dvd_X_pow_iff`: a monic polynomial `g` divides `X ^ n` if and only if
  `g = X ^ g.natDegree` and `g.natDegree ≤ n`.
-/

public section

namespace Polynomial.Monic

variable {R : Type*} [Semiring R] [NoZeroDivisors R] {g : R[X]} {n : ℕ}

/-- Over a semiring without zero divisors, every monic divisor of `X ^ n` is `X ^ g.natDegree`. -/
theorem eq_X_pow_of_dvd_X_pow (hg : g.Monic) (hdvd : g ∣ X ^ n) : g = X ^ g.natDegree := by
  nontriviality R
  obtain ⟨q, hq⟩ := hdvd
  have hq0 : q ≠ 0 := right_ne_zero_of_mul (hq ▸ (monic_X_pow n).ne_zero)
  have hdeg : n = g.natDegree + q.natDegree := by
    rw [← natDegree_X_pow (R := R) n, hq, hg.natDegree_mul' hq0]
  have htrail : n = g.natTrailingDegree + q.natTrailingDegree := by
    rw [← natTrailingDegree_X_pow (R := R) n, hq, natTrailingDegree_mul hg.ne_zero hq0]
  have := g.natTrailingDegree_le_natDegree
  have := q.natTrailingDegree_le_natDegree
  exact hg.eq_X_pow_iff_natTrailingDegree_eq_natDegree.2 (by omega)

/-- Over a semiring without zero divisors, a monic polynomial `g` divides `X ^ n` if and only if
`g = X ^ g.natDegree` and `g.natDegree ≤ n`. -/
theorem dvd_X_pow_iff (hg : g.Monic) :
    g ∣ X ^ n ↔ g = X ^ g.natDegree ∧ g.natDegree ≤ n := by
  refine ⟨fun hdvd ↦ ?_, fun ⟨hgX, hle⟩ ↦ hgX ▸ pow_dvd_pow X hle⟩
  have hgX := hg.eq_X_pow_of_dvd_X_pow hdvd
  refine ⟨hgX, ?_⟩
  nontriviality R
  obtain ⟨q, hq⟩ := hdvd
  have hq0 : q ≠ 0 := right_ne_zero_of_mul (hq ▸ (monic_X_pow n).ne_zero)
  have htrail : n = g.natTrailingDegree + q.natTrailingDegree := by
    rw [← natTrailingDegree_X_pow (R := R) n, hq, natTrailingDegree_mul hg.ne_zero hq0]
  have := hg.eq_X_pow_iff_natTrailingDegree_eq_natDegree.1 hgX
  omega

end Polynomial.Monic

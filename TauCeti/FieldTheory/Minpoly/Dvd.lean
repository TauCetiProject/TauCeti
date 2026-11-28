/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.Field

/-!
# Factors of the minimal polynomial are not invertible

Let `x` be an element of a `k`-algebra `A`, integral over a field `k`. If a polynomial `P` of
positive degree divides the minimal polynomial of `x`, then `P(x)` is not invertible in `A`:
writing `minpoly k x = P * Q`, invertibility of `P(x)` would force `Q(x) = 0` with
`deg Q < deg (minpoly k x)`. Applied to an endomorphism `g` of a finite-dimensional vector space and
an irreducible factor `P` of its minimal polynomial, this says that `P(g)` has a nonzero kernel.

## Main results

* `minpoly.not_isUnit_aeval_of_dvd`: a factor `P` of positive degree of the minimal polynomial of
  `x` is not invertible at `x`.
-/

public section

open Polynomial

namespace minpoly

/-- If a polynomial `P` of positive degree divides the minimal polynomial of `x`, then `P(x)` is
not invertible. -/
theorem not_isUnit_aeval_of_dvd {k A : Type*} [Field k] [Ring A] [Algebra k A] {x : A}
    (hx : IsIntegral k x) {P : k[X]} (hP : 0 < P.natDegree) (h : P ∣ minpoly k x) :
    ¬IsUnit (Polynomial.aeval x P) := by
  intro hu
  obtain ⟨Q, hQ⟩ := h
  -- Then `Q(x) = 0`, although `Q` has smaller degree than the minimal polynomial.
  have hQ_zero : Polynomial.aeval x Q = 0 := by
    have h_min := minpoly.aeval k x
    rwa [hQ, map_mul, hu.mul_right_eq_zero] at h_min
  have hQ_ne : Q ≠ 0 := by
    rintro rfl
    exact minpoly.ne_zero hx (by simpa using hQ)
  have h_deg := natDegree_le_of_dvd (minpoly.dvd k x hQ_zero) hQ_ne
  rw [hQ, natDegree_mul (ne_zero_of_natDegree_gt hP) hQ_ne] at h_deg
  omega

end minpoly

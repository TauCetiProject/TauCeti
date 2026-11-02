/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Expand

/-!
# Even polynomials are polynomials in `X²`

A polynomial fixed by the substitution `X ↦ -X`, over a coefficient ring without `2`-torsion, is a
polynomial in `X²`. This is the invariant theory of the group of order two acting on a line.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] [IsAddTorsionFree R]

/-- **An even polynomial is a polynomial in `X²`.** -/
theorem exists_eq_comp_X_sq_of_comp_neg_X_eq {p : R[X]} (hp : p.comp (-X) = p) :
    ∃ r : R[X], p = r.comp (X ^ 2) := by
  refine ⟨contract 2 p, ?_⟩
  rw [← expand_eq_comp_X_pow]
  ext n
  rw [coeff_expand two_pos]
  split_ifs with hn
  · rw [coeff_contract two_ne_zero, Nat.div_mul_cancel hn]
  · have hc := congrArg (coeff · n) hp
    have hneg : (-X : R[X]) = C (-1) * X := by simp
    simp only [hneg, comp_C_mul_X_coeff] at hc
    rw [(Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])).neg_one_pow, mul_neg_one] at hc
    exact neg_eq_self.mp hc

end Polynomial

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees

import Mathlib.Tactic.Ring

/-!
# Clearing denominators in the values of multivariate polynomials

Mathlib's `MvPolynomial.eval_mem` says that a polynomial with coefficients in a subsemiring takes
values in it at points with coordinates in it. If instead only the multiples `c xᵢ` of the
coordinates by a common denominator `c` lie in the subsemiring, then a polynomial of total degree
at most `T` has its value at `x` there after multiplication by `c ^ T`. This is the form in which
the denominators of algebraic numbers enter Liouville-type estimates: for a polynomial with
algebraic-integer coefficients evaluated at algebraic numbers with denominator `c`, the value has
denominator dividing `c ^ T`.

## Main results

* `MvPolynomial.pow_mul_eval_mem`: `c ^ T p(x)` lies in a subsemiring containing `c`, the
  coefficients of `p` and the `c xᵢ`, when `p` has total degree at most `T`.
-/

public section

namespace MvPolynomial

variable {σ S subS : Type*} [CommSemiring S] [SetLike subS S] [SubsemiringClass subS S]

/-- **Clearing denominators in a polynomial value.** If the coefficients of `p` lie in a
subsemiring `s`, `p` has total degree at most `T`, and `c ∈ s` is a common denominator of the
coordinates of `x`, that is `c xᵢ ∈ s` for all `i`, then `c ^ T p(x) ∈ s`. -/
theorem pow_mul_eval_mem {s : subS} {p : MvPolynomial σ S} (hp : ∀ m, p.coeff m ∈ s) {T : ℕ}
    (hT : p.totalDegree ≤ T) {c : S} (hc : c ∈ s) {x : σ → S} (hx : ∀ i, c * x i ∈ s) :
    c ^ T * eval x p ∈ s := by
  rw [eval_eq, Finset.mul_sum]
  refine sum_mem fun m hm ↦ ?_
  have hm' : ∑ i ∈ m.support, m i ≤ T := (le_totalDegree hm).trans hT
  -- Split `c ^ T` as `c ^ (T - |m|) c ^ |m|` and distribute `c ^ |m|` over the monomial.
  have h : c ^ T * (p.coeff m * ∏ i ∈ m.support, x i ^ m i) =
      c ^ (T - ∑ i ∈ m.support, m i) * p.coeff m * ∏ i ∈ m.support, (c * x i) ^ m i := by
    conv_lhs => rw [← Nat.sub_add_cancel hm', pow_add, ← Finset.prod_pow_eq_pow_sum]
    rw [Finset.prod_congr rfl fun i _ ↦ mul_pow c (x i) (m i), Finset.prod_mul_distrib]
    ring
  rw [h]
  exact mul_mem (mul_mem (pow_mem hc _) (hp m)) (prod_mem fun i _ ↦ pow_mem (hx i) _)

end MvPolynomial

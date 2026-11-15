/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees

import Mathlib.Tactic.Ring

/-!
# Denominators and congruences in the values of multivariate polynomials

Mathlib's `MvPolynomial.eval_mem` says that a polynomial with coefficients in a subsemiring takes
values in it at points with coordinates in it. If instead only the multiples `c xᵢ` of the
coordinates by a common denominator `c` lie in the subsemiring, then a polynomial of total degree
at most `T` has its value at `x` there after multiplication by `c ^ T`. This is the form in which
the denominators of algebraic numbers enter Liouville-type estimates: for a polynomial with
algebraic-integer coefficients evaluated at algebraic numbers with denominator `c`, the value has
denominator dividing `c ^ T`.

Over a commutative ring, evaluation also respects congruences: if `d ∣ xᵢ - tᵢ` for every `i`, then
`d ∣ p(x) - p(t)`.

## Main results

* `MvPolynomial.pow_mul_eval_mem`: `c ^ T p(x)` lies in a subsemiring containing `c`, the
  coefficients of `p` and the `c xᵢ`, when `p` has total degree at most `T`.
* `MvPolynomial.dvd_eval_sub_eval`: values at points congruent modulo `d` are congruent modulo `d`.
* `MvPolynomial.eval₂_eq_zero_iff_of_subsingleton_addUnits`: in a zero-sum-free semiring without
  zero divisors, `p.eval₂ f x = 0 ↔ p = 0` when the active coefficients and variables map to
  nonzero elements.
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

/-- The values of a polynomial at points that agree modulo `d` agree modulo `d`. -/
theorem dvd_eval_sub_eval {R : Type*} [CommRing R] (p : MvPolynomial σ R) {d : R} {x t : σ → R}
    (h : ∀ i, d ∣ x i - t i) : d ∣ eval x p - eval t p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simpa [add_sub_add_comm] using dvd_add hp hq
  | mul_X p i hp =>
    convert dvd_add (dvd_mul_of_dvd_left hp (x i)) (dvd_mul_of_dvd_right (h i) (eval t p))
      using 1
    simp only [map_mul, eval_X]
    ring

/-- Evaluating a multivariate polynomial in a zero-sum-free commutative semiring without zero
divisors yields zero if and only if the polynomial is zero, provided every support coefficient and
every variable in the support of a monomial evaluate to nonzero elements. -/
theorem eval₂_eq_zero_iff_of_subsingleton_addUnits {R : Type*} [CommSemiring R]
    [NoZeroDivisors S] [Subsingleton (AddUnits S)] (p : MvPolynomial σ R) {f : R →+* S}
    (hf : ∀ m ∈ p.support, f (p.coeff m) ≠ 0) {x : σ → S}
    (hx : ∀ m ∈ p.support, ∀ i ∈ m.support, x i ≠ 0) :
    p.eval₂ f x = 0 ↔ p = 0 := by
  refine ⟨fun h => ?_, fun hp => by simp [hp]⟩
  rw [eval₂_eq, Finset.sum_eq_zero_iff] at h
  by_contra hp
  obtain ⟨m, hm⟩ := support_nonempty.mpr hp
  have hterm : f (p.coeff m) * ∏ i ∈ m.support, x i ^ m i = 0 := h m hm
  rcases subsingleton_or_nontrivial S with hS | hS
  · exact hf m hm (Subsingleton.elim _ _)
  · exact mul_ne_zero (hf m hm)
      (Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hx m hm i hi)) hterm

end MvPolynomial

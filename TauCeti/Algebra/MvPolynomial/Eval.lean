/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.RingTheory.Ideal.Defs

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

Over a commutative ring, evaluation also respects congruences modulo an element or an ideal: if
`xᵢ - tᵢ` lies in an ideal `I` for every variable `Xᵢ` occurring in `p`, then `p(x) - p(t) ∈ I`;
in particular, coordinatewise divisibility by `d` implies `d ∣ p(x) - p(t)`.

## Main results

* `MvPolynomial.pow_mul_eval_mem`: `c ^ T p(x)` lies in a subsemiring containing `c`, the
  coefficients of `p` and the `c xᵢ`, when `p` has total degree at most `T`.
* `MvPolynomial.dvd_eval_sub_eval`: values at points congruent modulo `d` are congruent modulo `d`.
* `MvPolynomial.eval_sub_eval_mem_of_vars`, `MvPolynomial.eval_sub_eval_mem`: values at points
  whose coordinates on the variables of `p` (or everywhere) are congruent modulo an ideal `I` are
  congruent modulo `I`.
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

/-- The values of a polynomial at points that agree modulo an ideal `I` agree modulo `I`. -/
theorem eval_sub_eval_mem {R : Type*} [CommRing R] (p : MvPolynomial σ R) {I : Ideal R}
    {x t : σ → R} (h : ∀ i, x i - t i ∈ I) : eval x p - eval t p ∈ I := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simpa only [map_add, add_sub_add_comm] using I.add_mem hp hq
  | mul_X p i hp =>
    have hlin : eval x (p * X i) - eval t (p * X i) =
        (eval x p - eval t p) * x i + eval t p * (x i - t i) := by
      simp only [map_mul, eval_X]
      ring
    rw [hlin]
    exact I.add_mem (I.mul_mem_right _ hp) (I.mul_mem_left _ (h i))

/-- The values of a polynomial at points whose coordinates on `p.vars` agree modulo an ideal `I`
agree modulo `I`. -/
theorem eval_sub_eval_mem_of_vars {R : Type*} [CommRing R] (p : MvPolynomial σ R) {I : Ideal R}
    {x t : σ → R} (h : ∀ i ∈ p.vars, x i - t i ∈ I) : eval x p - eval t p ∈ I := by
  obtain ⟨q, hq⟩ := exists_rename_coe_vars_eq p
  rw [← hq, eval_rename, eval_rename]
  exact eval_sub_eval_mem q fun i ↦ h i i.2

end MvPolynomial

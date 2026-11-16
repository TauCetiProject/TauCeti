/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Order.Ring.Defs

import Mathlib.Algebra.Order.Ring.Basic
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

Over a strict linearly ordered field, evaluating a polynomial on quotients `fⱼ(x) / gⱼ(x)` clears
denominators into a single quotient whose denominator is strictly positive wherever no `gⱼ(x)`
vanishes (`MvPolynomial.exists_eval_div_mul_eq_eval`).

## Main results

* `MvPolynomial.pow_mul_eval_mem`: `c ^ T p(x)` lies in a subsemiring containing `c`, the
  coefficients of `p` and the `c xᵢ`, when `p` has total degree at most `T`.
* `MvPolynomial.dvd_eval_sub_eval`: values at points congruent modulo `d` are congruent modulo `d`.
* `MvPolynomial.exists_eval_div_mul_eq_eval`: clearing denominators of a polynomial evaluated on
  quotients `f j / g j` with a strictly positive polynomial denominator over a set where no `g j`
  vanishes.
-/

public section

namespace MvPolynomial

section Subsemiring

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

end Subsemiring

/-- The values of a polynomial at points that agree modulo `d` agree modulo `d`. -/
theorem dvd_eval_sub_eval {σ R : Type*} [CommRing R] (p : MvPolynomial σ R) {d : R}
    {x t : σ → R} (h : ∀ i, d ∣ x i - t i) : d ∣ eval x p - eval t p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simpa [add_sub_add_comm] using dvd_add hp hq
  | mul_X p i hp =>
    convert dvd_add (dvd_mul_of_dvd_left hp (x i)) (dvd_mul_of_dvd_right (h i) (eval t p))
      using 1
    simp only [map_mul, eval_X]
    ring

/-- Clearing denominators of a polynomial evaluated on quotients `f j / g j` with strictly positive
even-power denominators over a set where no `g j` vanishes. -/
theorem exists_eval_div_mul_eq_eval {σ τ K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {u : Set (σ → K)} (f g : τ → MvPolynomial σ K)
    (hg : ∀ x ∈ u, ∀ j, eval x (g j) ≠ 0) (p : MvPolynomial τ K) :
    ∃ num denom : MvPolynomial σ K, (∀ x ∈ u, 0 < eval x denom) ∧
      ∀ x ∈ u, eval (fun j ↦ eval x (f j) / eval x (g j)) p * eval x denom = eval x num := by
  refine MvPolynomial.induction_on
    (motive := fun p ↦ ∃ num denom : MvPolynomial σ K, (∀ x ∈ u, 0 < eval x denom) ∧
      ∀ x ∈ u, eval (fun j ↦ eval x (f j) / eval x (g j)) p * eval x denom = eval x num) p
    (fun a ↦ ⟨C a, 1, fun _ _ ↦ by simp, fun _ _ ↦ by simp⟩)
    (fun p q ⟨np, dp, hdp, hp⟩ ⟨nq, dq, hdq, hq⟩ ↦
      ⟨np * dq + nq * dp, dp * dq, fun x hx ↦ ?_, fun x hx ↦ ?_⟩)
    (fun p j ⟨np, dp, hdp, hp⟩ ↦
      ⟨np * f j * g j, dp * g j ^ 2, fun x hx ↦ ?_, fun x hx ↦ ?_⟩)
  · simpa only [map_mul] using mul_pos (hdp x hx) (hdq x hx)
  · simp only [map_add, map_mul]
    have hp' := hp x hx
    have hq' := hq x hx
    grind
  · simpa only [map_mul, map_pow] using mul_pos (hdp x hx) (sq_pos_of_ne_zero (hg x hx j))
  · have hgj : eval x (f j) / eval x (g j) * eval x (g j) = eval x (f j) :=
      div_mul_cancel₀ _ (hg x hx j)
    have hp' := hp x hx
    simp only [map_mul, eval_X, sq]
    grind

end MvPolynomial

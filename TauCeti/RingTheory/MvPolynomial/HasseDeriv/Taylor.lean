/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import TauCeti.Algebra.MvPolynomial.HasseDeriv.Basic
public import TauCeti.RingTheory.MvPolynomial.OrderAt

/-!
# Hasse derivatives as Taylor coefficients

The Taylor coefficients of a multivariate polynomial are its Hasse derivatives: for the Taylor
shift `MvPolynomial.taylor a`, `[Y^d] P(a + Y) = (∂^d P)(a)`, so that
`P(a + y) = ∑_d (∂^d P)(a) y^d`. Comparing Taylor coefficients of a product gives the Leibniz
rule for Hasse derivatives.

## Main results

* `MvPolynomial.coeff_taylor_X_map_C`, `MvPolynomial.coeff_taylor`: the Taylor coefficients of
  `P` at the generic point and at a point `a` are the Hasse derivatives `∂^d P` and their values
  `(∂^d P)(a)`.
* `MvPolynomial.eval_add_eq_finsum_hasseDeriv`: the finite Taylor expansion
  `P(a + y) = ∑_d (∂^d P)(a) y^d`.
* `MvPolynomial.hasseDeriv_mul`: the Leibniz rule `∂^d (P Q) = ∑_{a + b = d} ∂^a P · ∂^b Q`.

## References

* L. Pottmeyer, *Diophantine Approximation*, lecture notes (2022), §2.6, Lemma 2.6.1.
* Mathlib's univariate `Polynomial.taylor_coeff` (`Mathlib/Algebra/Polynomial/Taylor.lean`), the
  one-variable form of `MvPolynomial.coeff_taylor`.
-/

public section

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R]

/-- The Taylor coefficients of `P` at the generic point are its Hasse derivatives:
`P(X + Y) = ∑_d (∂^d P)(X) Y^d`. -/
theorem coeff_taylor_X_map_C (d : σ →₀ ℕ) (P : MvPolynomial σ R) :
    (taylor (X : σ → MvPolynomial σ R) (map C P)).coeff d = hasseDeriv d P := by
  classical
  induction P using MvPolynomial.induction_on generalizing d with
  | C a =>
    rw [map_C, taylor_C, coeff_C]
    by_cases hd : d = 0
    · subst hd; simp
    · rw [ite_eq_right (Ne.symm hd), hasseDeriv_C hd]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [hasseDeriv_mul_X, mul_comm (hasseDeriv d p)]
    simp [mul_add, mul_comm _ (C _), coeff_C_mul, coeff_mul_X', hp]

/-- The Taylor coefficients of `P` at the point `a` are the values of its Hasse derivatives:
`[Y^d] P(a + Y) = (∂^d P)(a)`. -/
@[simp]
theorem coeff_taylor (a : σ → R) (d : σ →₀ ℕ) (P : MvPolynomial σ R) :
    (taylor a P).coeff d = eval a (hasseDeriv d P) := by
  rw [← eval_coeff_taylor_map_C, coeff_taylor_X_map_C]

/-- The Leibniz rule for Hasse derivatives: `∂^d (P Q) = ∑_{a + b = d} ∂^a P · ∂^b Q`. -/
theorem hasseDeriv_mul [DecidableEq σ] (d : σ →₀ ℕ) (P Q : MvPolynomial σ R) :
    hasseDeriv d (P * Q) =
      ∑ x ∈ Finset.antidiagonal d, hasseDeriv x.1 P * hasseDeriv x.2 Q := by
  simp only [← coeff_taylor_X_map_C, map_mul, coeff_mul]

/-- The finite Taylor expansion with Hasse derivatives: `P(a + y) = ∑_d (∂^d P)(a) y^d`. -/
theorem eval_add_eq_finsum_hasseDeriv (P : MvPolynomial σ R) (a y : σ → R) :
    eval (a + y) P = ∑ᶠ d : σ →₀ ℕ, eval a (hasseDeriv d P) * d.prod fun j k ↦ y j ^ k := by
  rw [add_comm, ← eval_taylor, eval_eq,
    finsum_eq_sum_of_support_subset (s := (taylor a P).support) _ fun d hd ↦ ?_]
  · simp [coeff_taylor, Finsupp.prod]
  · rw [Function.mem_support] at hd
    rw [Finset.mem_coe, mem_support_iff, coeff_taylor]
    exact left_ne_zero_of_mul hd

end MvPolynomial

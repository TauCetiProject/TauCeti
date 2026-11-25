/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The difference of two variables is prime

The polynomials divisible by `X i - X j` in `MvPolynomial σ R` are exactly those that vanish on
the diagonal `X i = X j`, that is, those killed by renaming the variable `i` to `j`
(`MvPolynomial.X_sub_X_dvd_iff`). Over a domain that renaming lands in a domain, so for `i ≠ j`
the difference `X i - X j` is prime (`MvPolynomial.prime_X_sub_X`). These differences are the
prime factors of the Vandermonde product, and so of the discriminant of the generic polynomial
written in its roots.

## Main results

* `MvPolynomial.X_sub_X_dvd_iff`: `X i - X j ∣ p` iff `rename (Function.update id i j) p = 0`.
* `MvPolynomial.prime_X_sub_X`: over a domain, `X i - X j` is prime for `i ≠ j`.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommRing R] [DecidableEq σ]

/-- The polynomial `p` is divisible by `X i - X j` exactly when substituting `X j` for `X i` in
`p` gives zero. -/
theorem X_sub_X_dvd_iff {i j : σ} {p : MvPolynomial σ R} :
    X i - X j ∣ p ↔ rename (Function.update id i j) p = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    simp [Function.update_apply]
  · intro h
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
    -- Modulo `X i - X j`, renaming `i` to `j` changes nothing.
    have hcomp : (Ideal.Quotient.mkₐ R (Ideal.span {X i - X j})).comp
        (rename (Function.update id i j)) = Ideal.Quotient.mkₐ R (Ideal.span {X i - X j}) := by
      ext k
      rcases eq_or_ne k i with rfl | hk
      · simp only [AlgHom.comp_apply, rename_X, Function.update_self, Ideal.Quotient.mkₐ_eq_mk]
        rw [Ideal.Quotient.eq, ← neg_sub (X k)]
        exact neg_mem (Ideal.mem_span_singleton_self _)
      · simp [Function.update_of_ne hk]
    simpa [h] using (congr($hcomp p)).symm

omit [DecidableEq σ] in
/-- Over a domain, the difference `X i - X j` of two distinct variables is prime. -/
theorem prime_X_sub_X [IsDomain R] {i j : σ} (h : i ≠ j) :
    Prime (X i - X j : MvPolynomial σ R) := by
  classical
  exact ⟨sub_ne_zero.2 ((X_injective (σ := σ) (R := R)).ne h), fun hu ↦ by
    simpa [Function.update_apply] using hu.map (rename (R := R) (Function.update id i j)),
    fun a b hab ↦ by
    simpa only [X_sub_X_dvd_iff, map_mul, mul_eq_zero] using hab⟩

end MvPolynomial

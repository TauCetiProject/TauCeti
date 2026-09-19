/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Scaling the variables of a homogeneous polynomial

Evaluating a homogeneous polynomial of degree `n` after multiplying every variable by `a`
multiplies its value by `a ^ n`. This permits normalizing linear substitutions without
expanding the polynomial.
-/

public section

namespace TauCeti

open MvPolynomial

/-- Scaling all variables by `a` scales the value of a degree-`n` homogeneous polynomial
by `a ^ n`, after any change of coefficient ring. -/
theorem eval₂_fun_mul_of_isHomogeneous {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n)
    (f : R →+* S) (g : σ → S) (a : S) :
    eval₂ f (fun i ↦ a * g i) p = a ^ n * eval₂ f g p := by
  classical
  simp only [eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : ∑ i ∈ d.support, d i = n := by
    simpa [Finsupp.weight_apply, Finsupp.sum] using hp (mem_support_iff.mp hd)
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

end TauCeti

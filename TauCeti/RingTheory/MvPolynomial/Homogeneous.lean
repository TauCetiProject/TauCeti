/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Evaluating homogeneous polynomials at scaled arguments

A polynomial `φ` which is homogeneous of degree `n` satisfies `φ(c x) = c ^ n φ(x)`. This file
records that scaling identity for evaluation in any commutative algebra, so that substitutions
into homogeneous polynomials (such as normalized transforms of weight enumerators) can pull a
common scalar factor out of their arguments.
-/

public section

namespace MvPolynomial.IsHomogeneous

variable {σ R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  {φ : MvPolynomial σ R} {n : ℕ}

/-- Scaling every argument of a homogeneous polynomial of degree `n` by `c` multiplies its value
by `c ^ n`. -/
theorem aeval_smul (hφ : φ.IsHomogeneous n) (c : S) (x : σ → S) :
    MvPolynomial.aeval (c • x) φ = c ^ n * MvPolynomial.aeval x φ := by
  simp only [aeval_def, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  simp_rw [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← hφ.degree_eq_sum_deg_support hd]
  ring

end MvPolynomial.IsHomogeneous

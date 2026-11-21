/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs

/-!
# Polynomial evaluation into a subsemiring

The value `p.eval₂ f x` is a finite sum of products `f (p.coeff i) * x ^ i`, so it lies in every
subsemiring, or subring, containing `x` and the images of the coefficients in the support of `p`.
This is the one-variable analogue of `MvPolynomial.eval₂_mem`.
-/

public section

namespace Polynomial

variable {R S σ : Type*} [Semiring R] [Semiring S] [SetLike σ S] [SubsemiringClass σ S]

/-- A polynomial evaluates into every subsemiring containing the evaluation point and the images
of the coefficients in its support. -/
theorem eval₂_mem {f : R →+* S} {p : R[X]} {s : σ} (hs : ∀ i ∈ p.support, f (p.coeff i) ∈ s)
    {x : S} (hx : x ∈ s) : p.eval₂ f x ∈ s := by
  rw [eval₂_eq_sum, Polynomial.sum_def]
  exact sum_mem fun i hi ↦ mul_mem (hs i hi) (pow_mem hx i)

end Polynomial

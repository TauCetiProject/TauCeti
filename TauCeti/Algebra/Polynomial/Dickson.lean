/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Dickson

/-!
# Evaluating Dickson polynomials of the first kind

Dickson polynomials express the power sums of two elements with prescribed product.
The result works after any coefficient homomorphism, allowing the parameter and
polynomial coefficients to live in a smaller ring. The parameter `-1` is used to
descend Laurent polynomials fixed by `T ↦ -T⁻¹` to ordinary polynomials.

This generalizes Mathlib's `Polynomial.dickson_one_one_eval_add_inv`, which treats
the parameter one, using the same Dickson recurrence.
-/

public section

open scoped Polynomial

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Dickson polynomials of the first kind express the power sums of two elements
whose product is the parameter, after any coefficient homomorphism. -/
theorem dickson_one_eval₂_add (f : R →+* S) (a : R) (x y : S) (h : x * y = f a)
    (n : ℕ) :
    (dickson 1 a n).eval₂ f (x + y) = x ^ n + y ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp; ring
  | one => simp
  | more n h₀ h₁ =>
    rw [dickson_add_two, eval₂_sub, eval₂_mul, eval₂_mul, eval₂_X, eval₂_C, h₀, h₁, ← h]
    ring

end Polynomial

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Evaluating polynomials without cancellation

Let `S` be a commutative semiring in which a sum vanishes only when every summand does, spelled
`Subsingleton (AddUnits S)`. Evaluating a polynomial at non-zero-divisors of `S` then involves no
cancellation: the value vanishes only for the zero polynomial, provided the coefficient map
reflects zero. For natural-coefficient polynomials evaluated at units of a zero-sum-free
semifield, every nonzero polynomial thus takes a unit value, which is what lets evaluation
extend to fractions of such polynomials.
-/

public section

open scoped nonZeroDivisors

namespace MvPolynomial

variable {σ R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Evaluation at non-zero-divisors of a zero-sum-free semiring, along a coefficient map that
reflects zero, vanishes only on the zero polynomial. -/
theorem eval₂_eq_zero_iff [Subsingleton (AddUnits S)] {f : R →+* S}
    (hf : ∀ a, f a = 0 → a = 0) {y : σ → S} (hy : ∀ i, y i ∈ S⁰) {p : MvPolynomial σ R} :
    eval₂ f y p = 0 ↔ p = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  induction p using MvPolynomial.induction_on with
  | C a => simp [hf a (by simpa using h)]
  | add p q hp hq =>
    rw [eval₂_add, add_eq_zero] at h
    simp [hp h.1, hq h.2]
  | mul_X p i hp =>
    rw [eval₂_mul, eval₂_X] at h
    simp [hp (mul_right_mem_nonZeroDivisors_eq_zero_iff (hy i) |>.mp h)]

end MvPolynomial

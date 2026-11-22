/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DualNumber

/-!
# Ring-theoretic properties of the dual numbers

Over a field `k`, the maximal ideal `𝔪 = (ε)` of the dual numbers `k[ε]` squares to zero
(`DualNumber.maximalIdeal_sq_eq_bot`).
-/

public section

namespace DualNumber

/-- Over a field `k`, the square of the maximal ideal of the dual numbers `k[ε]` is zero. -/
@[simp]
theorem maximalIdeal_sq_eq_bot {k : Type*} [Field k] :
    IsLocalRing.maximalIdeal (DualNumber k) ^ 2 = ⊥ := by
  rw [maximalIdeal_eq_span_singleton_eps, Ideal.span_singleton_pow, sq, eps_mul_eps,
    Ideal.span_singleton_zero]

end DualNumber

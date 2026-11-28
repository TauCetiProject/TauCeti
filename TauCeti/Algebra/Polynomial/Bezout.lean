/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Ring

/-!
# Evaluating a Bézout relation

Let `x` be an element of an `R`-algebra `S` killed by a polynomial `q`. If `p` is coprime to `q`,
a Bézout relation `a * q + b * p = 1` evaluated at `x` shows that `p(x)` is invertible, with
inverse `b(x)`.

If `x` is killed by a product `A * B` and `u * A + v * B = 1`, then `(v * B)(x)` is an idempotent:
for an endomorphism `x`, it is the projection onto the kernel of `A(x)` along the kernel of `B(x)`.

## Main results

* `Polynomial.isUnit_aeval_of_isCoprime`: if `q(x) = 0` and `q` is coprime to `p`, then `p(x)` is
  a unit.
* `Polynomial.isIdempotentElem_aeval_mul_of_add_eq_one`: if `(A * B)(x) = 0` and
  `u * A + v * B = 1`, then `(v * B)(x)` is idempotent.
-/

public section

namespace Polynomial

variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] {x : S}

/-- If `q(x) = 0` and `q` is coprime to `p`, then `p(x)` is a unit. -/
theorem isUnit_aeval_of_isCoprime {p q : R[X]} (hq : aeval x q = 0) (h : IsCoprime q p) :
    IsUnit (aeval x p) := by
  obtain ⟨a, b, hab⟩ := h
  have h1 : aeval x b * aeval x p = 1 := by simpa [hq] using congrArg (aeval x) hab
  have h2 : aeval x p * aeval x b = 1 := by rw [← map_mul, mul_comm, map_mul, h1]
  exact isUnit_iff_exists.2 ⟨_, h2, h1⟩

/-- If `(A * B)(x) = 0` and `u * A + v * B = 1`, then `(v * B)(x)` is idempotent. -/
theorem isIdempotentElem_aeval_mul_of_add_eq_one {A B u v : R[X]} (huv : u * A + v * B = 1)
    (hx : aeval x (A * B) = 0) : IsIdempotentElem (aeval x (v * B)) := by
  have h : v * B * (v * B) + u * v * (A * B) = v * B := by
    calc v * B * (v * B) + u * v * (A * B) = v * B * (u * A + v * B) := by ring
      _ = v * B := by rw [huv, mul_one]
  simpa [IsIdempotentElem, hx] using congrArg (aeval x) h

end Polynomial

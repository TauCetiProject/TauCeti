/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.LinearRecurrence
import Mathlib.Tactic.Ring

/-!
# Characteristic polynomial of an order-two linear recurrence

Explicit formula for `LinearRecurrence.charPoly` on an order-two recurrence `⟨2, ![a, b]⟩` over a
commutative ring.

## Main results

* `LinearRecurrence.charPoly_mk_two`:
  `(⟨2, ![a, b]⟩ : LinearRecurrence R).charPoly = X ^ 2 - C b * X - C a`.
-/

public section

open Polynomial

namespace LinearRecurrence

/-- The characteristic polynomial of the order-two linear recurrence `⟨2, ![a, b]⟩`
(`u (n + 2) = a * u n + b * u (n + 1)`) is `X ^ 2 - C b * X - C a`. -/
@[simp]
theorem charPoly_mk_two {R : Type*} [CommRing R] (a b : R) :
    (⟨2, ![a, b]⟩ : LinearRecurrence R).charPoly = X ^ 2 - C b * X - C a := by
  simp only [charPoly, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Fin.val_zero, Fin.val_one, ← C_mul_X_pow_eq_monomial, pow_zero,
    pow_one, map_one, one_mul, mul_one]
  ring

end LinearRecurrence

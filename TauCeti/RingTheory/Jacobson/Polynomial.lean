/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.LinearCombination

/-!
# Values of polynomials on the Jacobson radical

A polynomial `P` over a commutative ring satisfies `P(x) ≡ P(0)` modulo `x`. If `x` lies in the
Jacobson radical and the constant term `P(0)` is a unit, then `P(x)` is a unit.

## Main results

* `Polynomial.isUnit_eval_of_isUnit_coeff_zero_of_mem_jacobson`: a polynomial with unit constant
  term takes unit values on the Jacobson radical.
-/

public section

namespace Polynomial

/-- A polynomial whose constant term is a unit takes unit values on the Jacobson radical. -/
theorem isUnit_eval_of_isUnit_coeff_zero_of_mem_jacobson {R : Type*} [CommRing R] {P : R[X]}
    (hP : IsUnit (P.coeff 0)) {x : R} (hx : x ∈ Ring.jacobson R) : IsUnit (P.eval x) := by
  obtain ⟨r, hr⟩ := sub_dvd_eval_sub x 0 P
  rw [← coeff_zero_eq_eval_zero, sub_zero, sub_eq_iff_eq_add] at hr
  obtain ⟨u, hu⟩ := hP
  -- `P(x) = x r + u = (x (r u⁻¹) + 1) u`, and `x (r u⁻¹) + 1` is a unit.
  have h : P.eval x = (x * (r * ↑u⁻¹) + 1) * u := by
    linear_combination hr - hu - x * r * u.inv_mul
  exact h ▸ (Ring.mem_jacobson_iff.mp hx _).mul u.isUnit

end Polynomial

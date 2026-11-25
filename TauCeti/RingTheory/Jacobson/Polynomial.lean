/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.Algebra.Polynomial.FieldDivision
import TauCeti.Algebra.Polynomial.Derivative
import TauCeti.RingTheory.Jacobson.Basic

/-!
# Values of polynomials on the Jacobson radical

A polynomial `P` over a commutative ring satisfies `P(x) ≡ P(0)` modulo `x`. If `x` lies in the
Jacobson radical and the constant term `P(0)` is a unit, then `P(x)` is a unit.

Applying this to the translated linear cofactor `(f /ₘ (X - C a)).comp (X + C a)` at `b - a` shows
that when `b - a` lies in the Jacobson radical and `f'(a)` is a unit, the difference `f(b) - f(a)`
is a unit multiple of `b - a`, and therefore lies in an ideal `K` exactly when `b - a` does.

## Main results

* `Polynomial.isUnit_eval_of_isUnit_coeff_zero_of_mem_jacobson`: a polynomial with unit constant
  term takes unit values on the Jacobson radical.
* `Polynomial.eval_sub_eval_mem_iff_sub_mem`: if `b - a` lies in the Jacobson radical and `f'(a)`
  is a unit, then `f(b) - f(a) ∈ K ↔ b - a ∈ K` for every ideal `K`.
-/

public section

namespace Polynomial

/-- A polynomial whose constant term is a unit takes unit values on the Jacobson radical. -/
theorem isUnit_eval_of_isUnit_coeff_zero_of_mem_jacobson {R : Type*} [CommRing R] {P : R[X]}
    (hP : IsUnit (P.coeff 0)) {x : R} (hx : x ∈ Ring.jacobson R) : IsUnit (P.eval x) := by
  obtain ⟨r, hr⟩ := sub_dvd_eval_sub x 0 P
  rw [← coeff_zero_eq_eval_zero, sub_zero, sub_eq_iff_eq_add, add_comm] at hr
  rw [hr, TauCeti.Ring.isUnit_add_iff_of_mem_jacobson (Ideal.mul_mem_right _ _ hx)]
  exact hP

/-- If `b - a` lies in the Jacobson radical of `R` and `f'(a)` is a unit, then `f(b) - f(a)` lies
in an ideal `K` exactly when `b - a` does: by monic division,
`f(b) - f(a) = (b - a) * (f /ₘ (X - C a)).eval b`, and the cofactor evaluates to the unit `f'(a)`
at `a`, so its value at `b` is also a unit. -/
theorem eval_sub_eval_mem_iff_sub_mem {R : Type*} [CommRing R] (f : R[X]) {K : Ideal R}
    {a b : R} (hba : b - a ∈ Ring.jacobson R) (hu : IsUnit (f.derivative.eval a)) :
    f.eval b - f.eval a ∈ K ↔ b - a ∈ K := by
  set q := f /ₘ (X - C a)
  have hfac : f.eval b - f.eval a = (b - a) * q.eval b := by
    simpa [q, modByMonic_X_sub_C_eq_C_eval] using
      congrArg (eval b) (X_sub_C_mul_divByMonic_eq_sub_modByMonic f a).symm
  have hq : IsUnit (q.eval b) := by
    have h0 : IsUnit ((q.comp (X + C a)).coeff 0) := by
      simpa [q, coeff_zero_eq_eval_zero, eval_comp] using hu
    simpa [eval_comp] using isUnit_eval_of_isUnit_coeff_zero_of_mem_jacobson h0 hba
  rw [hfac, K.mul_unit_mem_iff_mem hq]

end Polynomial

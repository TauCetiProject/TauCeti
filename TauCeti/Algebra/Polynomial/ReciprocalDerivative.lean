/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# Derivatives at reciprocal roots

Reflection reverses coefficients at a given degree bound. At a unit root of a polynomial,
the derivative of the reflected polynomial at the reciprocal root is a unit multiple of the
original derivative. This tracks the value, not just the multiplicity, at reciprocal roots.
-/

public section

namespace Polynomial

/-- At a unit root `u` of `p`, reflection at a degree bound `k + 1` changes its derivative at the
reciprocal root by the factor `-u / u^k`, expressed without division. -/
theorem eval_derivative_reflect_mul_pow {R : Type*} [CommRing R] (p : R[X])
    {k : ℕ} (hk : p.natDegree ≤ k + 1) (u : Rˣ) (hu : p.IsRoot (u : R)) :
    (p.reflect (k + 1)).derivative.eval (↑u⁻¹ : R) * (u : R) ^ k =
      -(u : R) * p.derivative.eval (u : R) := by
  by_cases hp : p = 0
  · simp [hp]
  have := Nontrivial.of_polynomial_ne hp
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hu
  have hqne : q ≠ 0 := right_ne_zero_of_mul (hq ▸ hp)
  have hdeg : p.natDegree = 1 + q.natDegree := by
    rw [hq, (monic_X_sub_C (u : R)).natDegree_mul' hqne, natDegree_X_sub_C]
  have hqk : q.natDegree ≤ k := by omega
  have hreflect : p.reflect (k + 1) = (1 - C (u : R) * X) * q.reflect k := by
    rw [hq, Nat.add_comm k 1, reflect_mul _ _ (by simp) hqk]
    simp [reflect_sub, reflect_C]
  let : Invertible (u : R) := u.isUnit.invertible
  have heval : (q.reflect k).eval (↑u⁻¹ : R) * (u : R) ^ k = q.eval (u : R) := by
    simpa only [invOf_units, eval₂_id] using
      eval₂_reflect_mul_pow (RingHom.id R) (u : R) k q hqk
  rw [hreflect, hq]
  simp [derivative_mul, mul_assoc, heval]

end Polynomial

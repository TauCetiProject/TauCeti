/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Algebra.Polynomial.Derivative

/-!
# Eulerian polynomials

The Eulerian polynomials `Aᵣ = TauCeti.eulerianPolynomial r` use the convention
`A₀ = A₁ = 1` and `A₂ = 1 + X`. They satisfy the differential recurrence
`Aᵣ₊₁ = (1 + rX) Aᵣ + X (1 - X) Aᵣ′` and the normalization `Aᵣ(1) = r!`.
They are the reduced polynomial factors in the rational expression
`Li₋ᵣ(z) = z Aᵣ(z) / (1 - z)^(r+1)` for nonpositive polylogarithms.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762,
  Astérisque 216 (1993), §1.1, (2)–(3), p. 50, for the Euler differential recursion
  from which the polynomial recurrence follows.
-/

public section

open Polynomial

namespace TauCeti

/-- The Eulerian polynomial `Aᵣ = eulerianPolynomial r`, with `A₀ = 1`.
It is the reduced factor after factoring out `z` in
`Li₋ᵣ(z) = z Aᵣ(z) / (1 - z)^(r+1)`. -/
noncomputable def eulerianPolynomial : ℕ → ℤ[X]
  | 0 => 1
  | r + 1 => (1 + C (r : ℤ) * X) * eulerianPolynomial r +
      X * (1 - X) * (eulerianPolynomial r).derivative

/-- The zeroth Eulerian polynomial is 1. -/
@[simp] theorem eulerianPolynomial_zero : eulerianPolynomial 0 = 1 := (rfl)

/-- The Eulerian polynomial recurrence induced by Euler differentiation. -/
theorem eulerianPolynomial_succ (r : ℕ) :
    eulerianPolynomial (r + 1) = (1 + C (r : ℤ) * X) * eulerianPolynomial r +
      X * (1 - X) * (eulerianPolynomial r).derivative := (rfl)

/-- The first Eulerian polynomial is also 1. -/
@[simp] theorem eulerianPolynomial_one : eulerianPolynomial 1 = 1 := by
  simp [eulerianPolynomial_succ]

/-- The second Eulerian polynomial is `1 + X`. -/
@[simp] theorem eulerianPolynomial_two : eulerianPolynomial 2 = 1 + X := by
  simp [eulerianPolynomial_succ]

/-- Evaluating `eulerianPolynomial r` at `1` gives `r!`. -/
@[simp] theorem eulerianPolynomial_eval_one (r : ℕ) :
    (eulerianPolynomial r).eval 1 = (r.factorial : ℤ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    simp [eulerianPolynomial_succ, ih, Nat.factorial_succ, add_comm]

/-- No Eulerian polynomial vanishes at 1. -/
theorem eulerianPolynomial_eval_one_ne_zero (r : ℕ) :
    (eulerianPolynomial r).eval 1 ≠ 0 := by
  rw [eulerianPolynomial_eval_one]
  exact_mod_cast Nat.factorial_ne_zero r

end TauCeti

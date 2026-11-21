/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Algebra.Polynomial.Derivative

/-!
# Eulerian polynomials

The shifted Eulerian polynomials `P_m(X; c) = TauCeti.shiftedEulerianPolynomial c m` over any
commutative ring `R` satisfy `P_0(X; c) = 1`,
`P_{m+1}(X; c) = (c (1 - X) + (m + 1) X) P_m + X (1 - X) P_m'`, `P_m(0; c) = c^m`,
`P_m(1; c) = m!`, and give the rational numerators of nonpositive-integer Lerch transcendents
`Φ(z, -m, c) = P_m(z; c) / (1 - z)^(m+1)`.

The Eulerian polynomials `Aᵣ = TauCeti.eulerianPolynomial r` are the specialization
`shiftedEulerianPolynomial (1 : ℤ) r`, with `A₀ = A₁ = 1`, `A₂ = 1 + X`, differential recurrence
`Aᵣ₊₁ = (1 + rX) Aᵣ + X (1 - X) Aᵣ′`, and normalization `Aᵣ(1) = r!`. They are the reduced
polynomial factors in the rational expression `Li₋ᵣ(z) = z Aᵣ(z) / (1 - z)^(r+1)` for nonpositive
polylogarithms.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762,
  Astérisque 216 (1993), §1.1, (2)–(3), p. 50, for the Euler differential recursion
  from which the polynomial recurrence follows.
* J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function III. Polylogarithms and special values*,
  arXiv:1506.06161, §5, Theorem 5.1, for the shifted Eulerian polynomials `P_m(X; c)`.
-/

public section

open Polynomial

namespace TauCeti

/-- Shifted Eulerian numerator polynomial `P_m(X; c)` over a commutative ring `R`, induced by the
shifted Euler operator `X ∂_X + c` on `(1 - X)⁻¹`. At `c = 1` this specializes to
`TauCeti.eulerianPolynomial m`. -/
noncomputable def shiftedEulerianPolynomial {R : Type*} [CommRing R] (c : R) : ℕ → R[X]
  | 0 => 1
  | m + 1 => (C c * (1 - X) + C (m + 1 : R) * X) * shiftedEulerianPolynomial c m +
      X * (1 - X) * (shiftedEulerianPolynomial c m).derivative

/-- Base case `shiftedEulerianPolynomial c 0 = 1`. -/
@[simp]
theorem shiftedEulerianPolynomial_zero {R : Type*} [CommRing R] (c : R) :
    shiftedEulerianPolynomial c 0 = 1 := by rfl

/-- Differential recurrence for `shiftedEulerianPolynomial c (m + 1)` induced by `X ∂_X + c`. -/
theorem shiftedEulerianPolynomial_succ {R : Type*} [CommRing R] (c : R) (m : ℕ) :
    shiftedEulerianPolynomial c (m + 1) =
      (C c * (1 - X) + C (m + 1 : R) * X) * shiftedEulerianPolynomial c m +
        X * (1 - X) * (shiftedEulerianPolynomial c m).derivative := by rfl

/-- First shifted Eulerian polynomial `shiftedEulerianPolynomial c 1 = c (1 - X) + X`. -/
@[simp]
theorem shiftedEulerianPolynomial_one {R : Type*} [CommRing R] (c : R) :
    shiftedEulerianPolynomial c 1 = C c * (1 - X) + X := by
  simp [shiftedEulerianPolynomial_succ]

/-- Evaluating `shiftedEulerianPolynomial c m` at `0` gives `c ^ m`. -/
@[simp]
theorem shiftedEulerianPolynomial_eval_zero {R : Type*} [CommRing R] (c : R) (m : ℕ) :
    (shiftedEulerianPolynomial c m).eval 0 = c ^ m := by
  induction m with
  | zero => simp
  | succ m ih => simp [shiftedEulerianPolynomial_succ, ih, pow_succ']

/-- Evaluating `shiftedEulerianPolynomial c m` at `1` gives `m!` independently of the shift `c`.
-/
@[simp]
theorem shiftedEulerianPolynomial_eval_one {R : Type*} [CommRing R] (c : R) (m : ℕ) :
    (shiftedEulerianPolynomial c m).eval 1 = (m.factorial : R) := by
  induction m with
  | zero => simp
  | succ m ih => simp [shiftedEulerianPolynomial_succ, ih, Nat.factorial_succ]

/-- Ring-homomorphism naturality of `shiftedEulerianPolynomial`: mapping coefficients along
`f : R →+* S` sends `shiftedEulerianPolynomial c m` to `shiftedEulerianPolynomial (f c) m`. -/
@[simp]
theorem map_shiftedEulerianPolynomial {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (c : R) (m : ℕ) :
    (shiftedEulerianPolynomial c m).map f = shiftedEulerianPolynomial (f c) m := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp [shiftedEulerianPolynomial_succ, ← Polynomial.derivative_map, ih]

/-- The Eulerian polynomial `Aᵣ = eulerianPolynomial r`, defined as the `c = 1` specialization
`shiftedEulerianPolynomial (1 : ℤ) r` with `A₀ = 1`. It is the reduced factor after factoring out
`z` in `Li₋ᵣ(z) = z Aᵣ(z) / (1 - z)^(r+1)`. -/
noncomputable def eulerianPolynomial (r : ℕ) : ℤ[X] :=
  shiftedEulerianPolynomial (1 : ℤ) r

/-- The zeroth Eulerian polynomial is 1. -/
@[simp] theorem eulerianPolynomial_zero : eulerianPolynomial 0 = 1 :=
  shiftedEulerianPolynomial_zero 1

/-- The Eulerian polynomial recurrence induced by Euler differentiation. -/
theorem eulerianPolynomial_succ (r : ℕ) :
    eulerianPolynomial (r + 1) = (1 + C (r : ℤ) * X) * eulerianPolynomial r +
      X * (1 - X) * (eulerianPolynomial r).derivative := by
  rw [eulerianPolynomial, shiftedEulerianPolynomial_succ]
  simp only [eulerianPolynomial, map_one, one_mul, map_add, map_natCast]
  ring

/-- The first Eulerian polynomial is also 1. -/
@[simp] theorem eulerianPolynomial_one : eulerianPolynomial 1 = 1 := by
  simp [eulerianPolynomial]

/-- The second Eulerian polynomial is `1 + X`. -/
@[simp] theorem eulerianPolynomial_two : eulerianPolynomial 2 = 1 + X := by
  simp [eulerianPolynomial_succ]

/-- Evaluating `eulerianPolynomial r` at `0` gives `1`. -/
@[simp] theorem eulerianPolynomial_eval_zero (r : ℕ) :
    (eulerianPolynomial r).eval 0 = 1 := by
  simp [eulerianPolynomial]

/-- Evaluating `eulerianPolynomial r` at `1` gives `r!`. -/
@[simp] theorem eulerianPolynomial_eval_one (r : ℕ) :
    (eulerianPolynomial r).eval 1 = (r.factorial : ℤ) :=
  shiftedEulerianPolynomial_eval_one (1 : ℤ) r

/-- No Eulerian polynomial vanishes at 1. -/
theorem eulerianPolynomial_eval_one_ne_zero (r : ℕ) :
    (eulerianPolynomial r).eval 1 ≠ 0 := by
  rw [eulerianPolynomial_eval_one]
  exact_mod_cast Nat.factorial_ne_zero r

/-- At shift `c = 1` in any commutative ring `R`, `shiftedEulerianPolynomial (1 : R) m` is the
image of `TauCeti.eulerianPolynomial m` under `Int.castRingHom R`. -/
theorem shiftedEulerianPolynomial_one_left {R : Type*} [CommRing R] (m : ℕ) :
    shiftedEulerianPolynomial (1 : R) m = (eulerianPolynomial m).map (Int.castRingHom R) := by
  rw [eulerianPolynomial, map_shiftedEulerianPolynomial, map_one]

end TauCeti

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

The shifted Eulerian polynomials `P_m(X; c) = TauCeti.lerchNegNatPoly c m` over any commutative
ring `R` satisfy `P_0(X; c) = 1`, `P_{m+1}(X; c) = (c (1 - X) + (m + 1) X) P_m + X (1 - X) P_m'`,
`P_m(0; c) = c^m`, `P_m(1; c) = m!`, and specialize at `c = 1` to `(eulerianPolynomial m).map
(Int.castRingHom R)`. They give the rational numerators of nonpositive-integer Lerch transcendents
`Φ(z, -m, c) = P_m(z; c) / (1 - z)^(m+1)`.

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

/-- Evaluating `eulerianPolynomial r` at `0` gives `1`. -/
@[simp] theorem eulerianPolynomial_eval_zero (r : ℕ) :
    (eulerianPolynomial r).eval 0 = 1 := by
  induction r with
  | zero => simp
  | succ r ih => simp [eulerianPolynomial_succ, ih]

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

/-- Shifted Eulerian numerator polynomial `P_m(X; c)` over a commutative ring `R`, induced by the
shifted Euler operator `X ∂_X + c` on `(1 - X)⁻¹`. At `c = 1` this recovers
`TauCeti.eulerianPolynomial m`. -/
noncomputable def lerchNegNatPoly {R : Type*} [CommRing R] (c : R) : ℕ → R[X]
  | 0 => 1
  | m + 1 => (C c * (1 - X) + C (m + 1 : R) * X) * lerchNegNatPoly c m +
      X * (1 - X) * (lerchNegNatPoly c m).derivative

/-- Base case `lerchNegNatPoly c 0 = 1`. -/
@[simp]
theorem lerchNegNatPoly_zero {R : Type*} [CommRing R] (c : R) :
    lerchNegNatPoly c 0 = 1 := by rfl

/-- Differential recurrence for `lerchNegNatPoly c (m + 1)` induced by `X ∂_X + c`. -/
theorem lerchNegNatPoly_succ {R : Type*} [CommRing R] (c : R) (m : ℕ) :
    lerchNegNatPoly c (m + 1) =
      (C c * (1 - X) + C (m + 1 : R) * X) * lerchNegNatPoly c m +
        X * (1 - X) * (lerchNegNatPoly c m).derivative := by rfl

/-- First shifted Eulerian polynomial `lerchNegNatPoly c 1 = c (1 - X) + X`. -/
@[simp]
theorem lerchNegNatPoly_one {R : Type*} [CommRing R] (c : R) :
    lerchNegNatPoly c 1 = C c * (1 - X) + X := by
  simp [lerchNegNatPoly_succ]

/-- Evaluating `lerchNegNatPoly c m` at `0` gives `c ^ m`. -/
@[simp]
theorem lerchNegNatPoly_eval_zero {R : Type*} [CommRing R] (c : R) (m : ℕ) :
    (lerchNegNatPoly c m).eval 0 = c ^ m := by
  induction m with
  | zero => simp
  | succ m ih => simp [lerchNegNatPoly_succ, ih, pow_succ']

/-- Evaluating `lerchNegNatPoly c m` at `1` gives `m!` independently of the shift `c`. -/
@[simp]
theorem lerchNegNatPoly_eval_one {R : Type*} [CommRing R] (c : R) (m : ℕ) :
    (lerchNegNatPoly c m).eval 1 = (m.factorial : R) := by
  induction m with
  | zero => simp
  | succ m ih => simp [lerchNegNatPoly_succ, ih, Nat.factorial_succ]

/-- Ring-homomorphism naturality of `lerchNegNatPoly`: mapping coefficients along `f : R →+* S`
sends `lerchNegNatPoly c m` to `lerchNegNatPoly (f c) m`. -/
@[simp]
theorem map_lerchNegNatPoly {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (c : R) (m : ℕ) :
    (lerchNegNatPoly c m).map f = lerchNegNatPoly (f c) m := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp [lerchNegNatPoly_succ, ← Polynomial.derivative_map, ih]

/-- At shift `c = 1 : ℤ`, `lerchNegNatPoly` coincides with `TauCeti.eulerianPolynomial`. -/
@[simp]
theorem lerchNegNatPoly_one_left_eq_eulerianPolynomial (m : ℕ) :
    lerchNegNatPoly (1 : ℤ) m = eulerianPolynomial m := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [lerchNegNatPoly_succ, eulerianPolynomial_succ, ih, map_add, map_one]
    ring

/-- At shift `c = 1` in any commutative ring `R`, `lerchNegNatPoly (1 : R) m` is the image of
`TauCeti.eulerianPolynomial m` under `Int.castRingHom R`. -/
theorem lerchNegNatPoly_one_left {R : Type*} [CommRing R] (m : ℕ) :
    lerchNegNatPoly (1 : R) m = (eulerianPolynomial m).map (Int.castRingHom R) := by
  rw [← lerchNegNatPoly_one_left_eq_eulerianPolynomial, map_lerchNegNatPoly, map_one]

end TauCeti

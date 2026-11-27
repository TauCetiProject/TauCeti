/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import TauCeti.Algebra.Polynomial.Derivative
import TauCeti.RingTheory.Polynomial.Cyclotomic.Reflect

/-!
# Cyclotomic derivatives at reciprocal roots

Palindromicity determines how the derivative of a cyclotomic polynomial changes when the
primitive root at which it is evaluated is inverted.
-/

public section

open Polynomial

namespace IsPrimitiveRoot

/-- For an order `n > 2`, the derivative of `Φₙ` at the inverse primitive root is minus the
original derivative times the inverse of `ζ ^ (φ(n) - 2)`. -/
theorem eval_derivative_cyclotomic_inv_mul_pow {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} {ζ : Rˣ} (hζ : IsPrimitiveRoot (ζ : R) n) (hn : 2 < n) :
    (cyclotomic n R).derivative.eval (↑ζ⁻¹ : R) * (ζ : R) ^ (n.totient - 2) =
      -(cyclotomic n R).derivative.eval (ζ : R) := by
  have hn0 : 0 < n := by omega
  have hφ : 2 ≤ n.totient := by
    obtain ⟨m, hm⟩ := Nat.totient_even hn
    have := Nat.totient_pos.mpr hn0
    omega
  have hdeg : (n.totient - 2) + 1 + 1 = n.totient := by omega
  have h := eval_derivative_reflect_mul_pow (cyclotomic n R) (k := n.totient - 2 + 1)
    (by simp [natDegree_cyclotomic, hdeg]) ζ (hζ.isRoot_cyclotomic hn0)
  rw [hdeg, reflect_cyclotomic (by omega)] at h
  apply ζ.isUnit.mul_left_cancel
  simpa only [pow_succ, neg_mul, mul_neg, mul_assoc, mul_comm, mul_left_comm] using h

end IsPrimitiveRoot

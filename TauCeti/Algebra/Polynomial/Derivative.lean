/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Polynomial derivatives

This file records auxiliary results relating Mathlib's polynomial derivative APIs, computing
iterated derivatives after a linear change of variables, and controlling degrees of derivatives
under coefficient maps.

The derivation `Polynomial.derivative'` has `Polynomial.derivative` as its underlying function,
and every scalar multiple of it is locally nilpotent.

A coefficient map can lower the degree of a polynomial, and in positive characteristic it can
lower the degree of a derivative even when it preserves the degree of the polynomial itself.
Over an additively torsion-free target the second phenomenon cannot occur: preserving the degree
of `p` preserves the degree of `p.derivative`.

A self-reciprocal polynomial `p` of even degree bound `2 g`, one with `X ^ (2 g) p (1 / X) = p (X)`,
satisfies `p' (1) = g p (1)`: the coefficients in degrees `i` and `2 g - i` agree and their
weights `i - g` and `g - i` cancel. The characteristic polynomial of a symplectic matrix is the
basic example.
-/

public section

namespace TauCeti

open Polynomial

variable {R S : Type*}

/-- The derivation `derivative'` has the ordinary polynomial derivative as its underlying
function. -/
theorem _root_.Polynomial.coe_derivative' [CommSemiring R] :
    ⇑(derivative' : Derivation R R[X] R[X]) = derivative :=
  _root_.funext derivative'_apply

/-- The scaled derivative `r • d / dX` is locally nilpotent: some iterate of it kills each
polynomial. -/
theorem _root_.Polynomial.exists_iterate_smul_derivative'_apply_eq_zero [CommSemiring R] (r : R)
    (p : R[X]) : ∃ n, (r • derivative' : Derivation R R[X] R[X])^[n] p = 0 := by
  refine ⟨p.natDegree + 1, ?_⟩
  rw [← Derivation.coeFn_coe, ← Module.End.coe_pow, Derivation.coe_smul_linearMap, smul_pow,
    LinearMap.smul_apply, Module.End.pow_apply, Derivation.coeFn_coe, coe_derivative',
    iterate_derivative_eq_zero (Nat.lt_succ_self _), smul_zero]

/-- The `k`-th derivative of `p (a X)` is `a ^ k p⁽ᵏ⁾ (a X)`. -/
theorem _root_.Polynomial.iterate_derivative_comp_C_mul_X [CommSemiring R] (p : R[X]) (a : R)
    (k : ℕ) :
    derivative^[k] (p.comp (C a * X)) = C (a ^ k) * (derivative^[k] p).comp (C a * X) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, derivative_C_mul, derivative_comp, derivative_C_mul_X,
      Function.iterate_succ_apply', pow_succ, C_mul]
    ring

/-- **Reciprocal-polynomial identity.** A polynomial `p` of degree at most `2 g` which is its own
reflection at `2 g`, that is `X ^ (2 g) p (1 / X) = p (X)`, satisfies `p' (1) = g p (1)`. -/
theorem _root_.Polynomial.derivative_eval_one_of_reflect_eq [CommRing R] {p : R[X]} {g : ℕ}
    (hp : p.natDegree ≤ 2 * g) (h : p.reflect (2 * g) = p) :
    p.derivative.eval 1 = g * p.eval 1 := by
  have hlt : p.natDegree < 2 * g + 1 := Nat.lt_succ_of_le hp
  rw [derivative_eval, sum_over_range' _ (fun _ ↦ by simp) _ hlt, eval_eq_sum_range' hlt,
    Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  -- The terms in degrees `i` and `2 g - i` cancel, and the term in degree `g` vanishes.
  refine Finset.sum_involution (fun i _ ↦ 2 * g - i) (fun i hi ↦ ?_) (fun i hi hne ↦ ?_)
    (fun i hi ↦ ?_) (fun i hi ↦ ?_) <;>
    have hi : i ≤ 2 * g := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  · have hc : p.coeff (2 * g - i) = p.coeff i := by
      conv_rhs => rw [← h]
      rw [coeff_reflect, revAt_le hi]
    rw [hc, Nat.cast_sub hi]
    push_cast
    ring
  · intro heq
    obtain rfl : i = g := by omega
    simp [mul_comm] at hne
  · simp only [Finset.mem_range]
    omega
  · omega

variable [Semiring R] [Semiring S] [HasUniqueDiv S]

/-- A coefficient map into an additively torsion-free semiring which preserves the degree of a
polynomial also preserves the degree of its derivative. -/
theorem _root_.Polynomial.natDegree_map_derivative_eq_of_natDegree_map_eq {f : R →+* S}
    {p : R[X]} (h : (p.map f).natDegree = p.natDegree) :
    (p.derivative.map f).natDegree = p.derivative.natDegree := by
  refine Nat.le_antisymm natDegree_map_le ?_
  rw [← derivative_map, natDegree_derivative (p.map f), h]
  exact natDegree_derivative_le p

end TauCeti

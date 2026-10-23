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

For a polynomial `p` with coefficients in an `R`-algebra `S`, possibly noncommutative, evaluating
`p′` at the central element `algebraMap R S t` expands as a sum of the coefficients of `p`
weighted by scalars depending on `t`.

A coefficient map can lower the degree of a polynomial, and in positive characteristic it can
lower the degree of a derivative even when it preserves the degree of the polynomial itself.
Over an additively torsion-free target the second phenomenon cannot occur: preserving the degree
of `p` preserves the degree of `p.derivative`.

A self-reciprocal polynomial `p` of even degree bound `2 g`, one with `X ^ (2 g) p (1 / X) = p (X)`,
satisfies `p' (1) = g p (1)`: the coefficients in degrees `i` and `2 g - i` agree and their
weights `i - g` and `g - i` cancel. The characteristic polynomial of a symplectic matrix is the
basic example.

For `δ ≠ 0` over a semiring without zero divisors, the operator `q ↦ q' + δ q` and all of its
iterates preserve the degree of a polynomial and have trivial kernel.
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

section AlgebraMap

variable [CommSemiring R] [Semiring S] [Algebra R S]

/-- Evaluating the derivative of a polynomial at the image of a scalar `t`, with the same range of
coefficients as `Polynomial.eval_algebraMap_eq_sum_range`. -/
theorem _root_.Polynomial.derivative_eval_algebraMap_eq_sum_range (p : S[X]) (t : R) :
    p.derivative.eval (algebraMap R S t) =
      ∑ i ∈ Finset.range (p.natDegree + 1), ((i : R) * t ^ (i - 1)) • p.coeff i := by
  rw [derivative_eval, sum_over_range _ fun n ↦ by simp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Algebra.smul_def, Algebra.commutes]
  simp [mul_assoc]

end AlgebraMap

variable [Semiring R] [Semiring S] [HasUniqueDiv S]

/-- A coefficient map into an additively torsion-free semiring which preserves the degree of a
polynomial also preserves the degree of its derivative. -/
theorem _root_.Polynomial.natDegree_map_derivative_eq_of_natDegree_map_eq {f : R →+* S}
    {p : R[X]} (h : (p.map f).natDegree = p.natDegree) :
    (p.derivative.map f).natDegree = p.derivative.natDegree := by
  refine Nat.le_antisymm natDegree_map_le ?_
  rw [← derivative_map, natDegree_derivative (p.map f), h]
  exact natDegree_derivative_le p

section ShiftedDerivative

variable [NoZeroDivisors R] {δ : R} {q : R[X]}

/-- For `δ ≠ 0`, the coefficient of `X ^ deg q` in `q' + δ q` is `δ` times the leading coefficient
of `q`, so this polynomial is nonzero when `q` is. -/
private theorem coeff_natDegree_derivative_add_C_mul_ne_zero (hδ : δ ≠ 0) (hq : q ≠ 0) :
    (derivative q + C δ * q).coeff q.natDegree ≠ 0 := by
  rw [coeff_add, coeff_derivative, coeff_natDegree_succ_eq_zero, zero_mul, zero_add, coeff_C_mul]
  exact mul_ne_zero hδ (leadingCoeff_ne_zero.2 hq)

/-- For `δ ≠ 0`, the operator `q ↦ q' + δ q` (the derivative of `x ↦ q(x) e^(δ x)`, divided by
`e^(δ x)`) preserves the degree of a polynomial. -/
theorem _root_.Polynomial.natDegree_derivative_add_C_mul (hδ : δ ≠ 0) :
    (derivative q + C δ * q).natDegree = q.natDegree := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_
    (coeff_natDegree_derivative_add_C_mul_ne_zero hδ hq)
  exact natDegree_add_le_of_degree_le (natDegree_derivative_le q |>.trans (Nat.sub_le _ _))
    (natDegree_C_mul_le δ q)

/-- For `δ ≠ 0`, the operator `q ↦ q' + δ q` has trivial kernel. -/
@[simp]
theorem _root_.Polynomial.derivative_add_C_mul_eq_zero_iff (hδ : δ ≠ 0) :
    derivative q + C δ * q = 0 ↔ q = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  by_contra hq
  exact coeff_natDegree_derivative_add_C_mul_ne_zero hδ hq (by rw [h, coeff_zero])

/-- For `δ ≠ 0`, every iterate of the operator `q ↦ q' + δ q` preserves the degree of a
polynomial. -/
theorem _root_.Polynomial.natDegree_iterate_derivative_add_C_mul (hδ : δ ≠ 0) (n : ℕ) :
    ((fun r ↦ derivative r + C δ * r)^[n] q).natDegree = q.natDegree := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', natDegree_derivative_add_C_mul hδ, ih]

/-- For `δ ≠ 0`, every iterate of the operator `q ↦ q' + δ q` has trivial kernel. -/
theorem _root_.Polynomial.iterate_derivative_add_C_mul_eq_zero_iff (hδ : δ ≠ 0) (n : ℕ) :
    (fun r ↦ derivative r + C δ * r)^[n] q = 0 ↔ q = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', derivative_add_C_mul_eq_zero_iff hδ, ih]

end ShiftedDerivative

end TauCeti

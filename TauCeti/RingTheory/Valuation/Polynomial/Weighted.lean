/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import TauCeti.RingTheory.Valuation.Sum
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# Weighted coefficient bounds for polynomial valuations

Fix `x`, a scale `A` and a ratio `S`. Say that a polynomial `P` has *weight `a`* if
`v (P.coeff k * x ^ k) * S ^ a ≤ A ^ a * S ^ k` for every `k`. This file records the generic
weighted coefficient convolution bound `Valuation.map_coeff_mul_mul_pow_le_of_le` (shared with
`TauCeti.RingTheory.Polynomial.Gauss.Valuation.Basic`) together with the weight-stability bounds
for products, powers, evaluation, and composition of polynomials.

## Main results

* `Valuation.map_coeff_mul_mul_pow_le_of_le`: generic weighted convolution bound for products of
  polynomials under a valuation `v : Valuation R Γ₀`.
* `Valuation.map_coeff_mul_mul_pow_le`, `Valuation.map_coeff_pow_mul_pow_le`,
  `Valuation.map_eval_mul_le`, `Valuation.map_coeff_comp_mul_pow_le`: weighted bounds on the
  terms of products, powers, evaluation, and composites of polynomials at a point.
-/

public section

namespace Valuation

open Polynomial

section Monoid

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]

/-- Weighted convolution bound for the coefficients of a product of polynomials: if
`v (p.coeff i) * r ^ i * s₁ ≤ A₁ * S ^ i` and `v (q.coeff j) * r ^ j * s₂ ≤ A₂ * S ^ j`, then
`v ((p * q).coeff k) * r ^ k * (s₁ * s₂) ≤ (A₁ * A₂) * S ^ k`. -/
theorem map_coeff_mul_mul_pow_le_of_le (v : Valuation R Γ₀) {p q : R[X]} {r s₁ s₂ A₁ A₂ S : Γ₀}
    (hp : ∀ i, v (p.coeff i) * r ^ i * s₁ ≤ A₁ * S ^ i)
    (hq : ∀ j, v (q.coeff j) * r ^ j * s₂ ≤ A₂ * S ^ j) (k : ℕ) :
    v ((p * q).coeff k) * r ^ k * (s₁ * s₂) ≤ (A₁ * A₂) * S ^ k := by
  rw [coeff_mul, mul_assoc]
  refine v.map_sum_mul_le fun ij hij ↦ ?_
  rw [Finset.mem_antidiagonal] at hij
  calc v (p.coeff ij.1 * q.coeff ij.2) * (r ^ k * (s₁ * s₂))
      = v (p.coeff ij.1) * r ^ ij.1 * s₁ * (v (q.coeff ij.2) * r ^ ij.2 * s₂) := by
        simp only [← hij, pow_add, map_mul]
        ac_rfl
    _ ≤ A₁ * S ^ ij.1 * (A₂ * S ^ ij.2) := mul_le_mul' (hp _) (hq _)
    _ = (A₁ * A₂) * S ^ k := by
        rw [← hij, pow_add]
        ac_rfl

variable {v : Valuation R Γ₀} {x : R} {A S : Γ₀}

/-- Weights add under multiplication of polynomials. -/
theorem map_coeff_mul_mul_pow_le {P Q : R[X]} {a b : ℕ}
    (hP : ∀ k, v (P.coeff k * x ^ k) * S ^ a ≤ A ^ a * S ^ k)
    (hQ : ∀ k, v (Q.coeff k * x ^ k) * S ^ b ≤ A ^ b * S ^ k) (k : ℕ) :
    v ((P * Q).coeff k * x ^ k) * S ^ (a + b) ≤ A ^ (a + b) * S ^ k := by
  simpa only [map_mul, map_pow, pow_add] using
    v.map_coeff_mul_mul_pow_le_of_le (r := v x) (s₁ := S ^ a) (s₂ := S ^ b)
      (A₁ := A ^ a) (A₂ := A ^ b) (S := S)
      (fun i ↦ by simpa only [map_mul, map_pow] using hP i)
      (fun j ↦ by simpa only [map_mul, map_pow] using hQ j) k

/-- The `n`-th power of a polynomial of weight `1` has weight `n`. -/
theorem map_coeff_pow_mul_pow_le {Q : R[X]} (hQ : ∀ k, v (Q.coeff k * x ^ k) * S ≤ A * S ^ k)
    (n k : ℕ) : v ((Q ^ n).coeff k * x ^ k) * S ^ n ≤ A ^ n * S ^ k := by
  induction n generalizing k with
  | zero =>
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    · simp [coeff_one, hk]
  | succ n ih =>
    rw [pow_succ]
    exact map_coeff_mul_mul_pow_le ih (by simpa using hQ) k

/-- A polynomial of weight `1` whose coefficients vanish below degree `M` has
`v (G.eval x) * S ≤ A * S ^ M`, provided `S ≤ 1`. -/
theorem map_eval_mul_le {G : R[X]} {M : ℕ} (hS : S ≤ 1) (hG₀ : ∀ k < M, G.coeff k = 0)
    (hG : ∀ k, v (G.coeff k * x ^ k) * S ≤ A * S ^ k) : v (G.eval x) * S ≤ A * S ^ M := by
  rw [eval_eq_sum, Polynomial.sum_def]
  refine v.map_sum_mul_le fun k _ ↦ ?_
  rcases lt_or_ge k M with hk | hk
  · simp [hG₀ k hk]
  · exact (hG k).trans (mul_le_mul_right (pow_le_pow_right_of_le_one' hS hk) A)

/-- Composition with a polynomial `F` whose coefficients satisfy
`v (F.coeff n) * A ^ n * S ≤ A * S ^ n` preserves weight `1`. -/
theorem map_coeff_comp_mul_pow_le {F Q : R[X]}
    (hF : ∀ n, v (F.coeff n) * A ^ n * S ≤ A * S ^ n)
    (hQ : ∀ k, v (Q.coeff k * x ^ k) * S ≤ A * S ^ k) (k : ℕ) :
    v ((F.comp Q).coeff k * x ^ k) * S ≤ A * S ^ k := by
  rw [comp_eq_sum_left, Polynomial.sum_def, finsetSum_coeff, Finset.sum_mul]
  refine v.map_sum_mul_le fun n _ ↦ ?_
  have hQn := map_coeff_pow_mul_pow_le hQ n k
  rw [coeff_C_mul, mul_assoc, map_mul, mul_assoc]
  rcases eq_or_ne (A ^ n * S ^ n) 0 with h0 | h0
  · -- A vanishing scale forces the `n`-th power term, or the weight `S`, to vanish.
    rcases eq_or_ne S 0 with rfl | hS
    · simp
    have hA : A ^ n = 0 := (mul_eq_zero.mp h0).resolve_right (pow_ne_zero n hS)
    have hv : v ((Q ^ n).coeff k * x ^ k) * S ^ n = 0 :=
      le_antisymm (hQn.trans_eq (by rw [hA, zero_mul])) zero_le
    simp [(mul_eq_zero.mp hv).resolve_right (pow_ne_zero n hS)]
  refine le_of_mul_le_mul_right ?_ (pos_iff_ne_zero.mpr h0)
  calc v (F.coeff n) * (v ((Q ^ n).coeff k * x ^ k) * S) * (A ^ n * S ^ n)
      = v (F.coeff n) * A ^ n * S * (v ((Q ^ n).coeff k * x ^ k) * S ^ n) := by
        simp only [mul_comm, mul_left_comm, mul_assoc]
    _ ≤ A * S ^ n * (A ^ n * S ^ k) := mul_le_mul' (hF n) hQn
    _ = A * S ^ k * (A ^ n * S ^ n) := by ac_rfl

end Monoid

end Valuation

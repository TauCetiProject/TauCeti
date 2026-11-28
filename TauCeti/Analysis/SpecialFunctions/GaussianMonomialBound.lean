/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exponential and Gaussian monomial bounds

Elementary inequalities bounding Gaussian exponentials, quadratic exponents, and square roots of
monomials under a sum constraint:

* Completing the square in exponential form gives
  `exp (-(π / a * t ^ 2)) ≤ exp (a * D ^ 2) * exp t ^ (-D)` for `a > 0`
  (`TauCeti.exp_neg_pi_div_mul_sq_le`).
* For natural numbers `δ ≤ 2 * M`, `√d * (δ + 1) ^ 2 + 3 * δ ≤ 2 * (2 * d + 6) * (M + 1) ^ 2`
  (`TauCeti.sqrt_mul_sq_add_le_of_le`).
* If nonnegative weights `ρ τ i` sum to at most `exp u * (2 * L + 2) * R` with `L > 0`, then
  `√(∏ τ, ∏ i ∈ I, ρ τ i ^ l (τ, i))` is bounded by `exp (w / 2 + L * R)` where
  `w = ∑ τ, ∑ i ∈ I, (l (τ, i) / L + log (l (τ, i))! + l (τ, i) * u)`
  (`TauCeti.sqrt_prod_pow_le_exp`).

## Main results

* `TauCeti.exp_neg_pi_div_mul_sq_le`
* `TauCeti.sqrt_mul_sq_add_le_of_le`
* `TauCeti.sqrt_prod_pow_le_exp`

## Provenance

Adapted from `grh-lean` (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file
`src/New/UpperBound/Kernels/JetConjugatesAndBounds.lean`, declarations
`New.exp_neg_pi_div_mul_sq_le`, `New.sqrt_mul_sq_add_le_of_le`, and `New.sqrt_prod_pow_le_exp`.
-/

public section

open Real Finset

namespace TauCeti

/-- Completing the square in exponential form: `exp (-(π / a * t ^ 2)) ≤ exp (a * D ^ 2) *
(exp t) ^ (-D)` for `a > 0`. -/
theorem exp_neg_pi_div_mul_sq_le {a : ℝ} (ha : 0 < a) (t D : ℝ) :
    exp (-(π / a * t ^ 2)) ≤ exp (a * D ^ 2) * exp t ^ (-D) := by
  rw [← exp_mul, ← exp_add, exp_le_exp, ← sub_nonneg]
  have h_pi : 0 ≤ π - 1 / 4 := by linarith [two_le_pi]
  calc (0 : ℝ) ≤ ((π - 1 / 4) * t ^ 2 + (t / 2 - a * D) ^ 2) / a := by positivity
    _ = a * D ^ 2 + t * -D - -(π / a * t ^ 2) := by field_simp; ring

/-- Elementary exponent comparison: if `δ ≤ 2 * M`, then
`√d * (δ + 1) ^ 2 + 3 * δ ≤ 2 * (2 * d + 6) * (M + 1) ^ 2`. -/
theorem sqrt_mul_sq_add_le_of_le {d M δ : ℕ} (hδ : δ ≤ 2 * M) :
    √d * (δ + 1) ^ 2 + 3 * (δ : ℝ) ≤ 2 * ((2 * d + 6) * (M + 1) ^ 2) := by
  have h_sqrt : √d ≤ (d : ℝ) :=
    sqrt_le_iff.mpr ⟨Nat.cast_nonneg d, by exact_mod_cast Nat.le_self_pow two_ne_zero d⟩
  have hδ' : (δ : ℝ) ≤ 2 * M := by exact_mod_cast hδ
  have h1 : √d * ((δ : ℝ) + 1) ^ 2 ≤ d * (2 * M + 1) ^ 2 := by
    gcongr
  nlinarith [sq_nonneg (M : ℝ), Nat.cast_nonneg (α := ℝ) d, Nat.cast_nonneg (α := ℝ) M]

/-- If nonnegative weights `ρ τ i` satisfy `∑ τ, ∑ i ∈ I, ρ τ i ≤ exp u * (2 * L + 2) * R` with
`0 < L`, then the square root of the monomial `∏ τ, ∏ i ∈ I, ρ τ i ^ l (τ, i)` is at most
`exp ((∑ τ, ∑ i ∈ I, (l (τ, i) / L + log (l (τ, i))! + l (τ, i) * u)) / 2 + L * R)`. -/
theorem sqrt_prod_pow_le_exp {Φ ι : Type*} [Fintype Φ] (I : Finset ι) (ρ : Φ → ι → ℝ)
    (hρ : ∀ τ, ∀ i ∈ I, 0 ≤ ρ τ i) (l : Φ × ι → ℕ) {L u R : ℝ} (hL : 0 < L)
    (h_sum : ∑ τ : Φ, ∑ i ∈ I, ρ τ i ≤ exp u * (2 * L + 2) * R) :
    √(∏ τ : Φ, ∏ i ∈ I, ρ τ i ^ l (τ, i)) ≤
      exp ((∑ τ : Φ, ∑ i ∈ I,
        ((l (τ, i) : ℝ) / L + log (l (τ, i)).factorial + l (τ, i) * u)) / 2 + L * R) := by
  set S : ℝ := ∑ τ : Φ, ∑ i ∈ I, ρ τ i with hS
  set v : ℝ := u + L⁻¹
  have hS_nonneg : 0 ≤ S := Finset.sum_nonneg fun τ _ ↦ Finset.sum_nonneg fun i hi ↦ hρ τ i hi
  have h_tail : S / exp v ≤ 2 * (L * R) := by
    have h1 : exp u * (L⁻¹ + 1) ≤ exp v := by
      rw [exp_add]; exact mul_le_mul_of_nonneg_left (add_one_le_exp L⁻¹) (exp_pos u).le
    calc S / exp v ≤ exp u * (2 * L + 2) * R / (exp u * (L⁻¹ + 1)) :=
          div_le_div₀ (hS_nonneg.trans h_sum) h_sum (by positivity) h1
      _ = 2 * (L * R) := by have hexp : exp u ≠ 0 := (exp_pos u).ne'; field_simp; ring
  have h_factor (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
      x ^ m ≤ exp (log m.factorial + m * v + x / exp v) := by
    have h_tay := Real.pow_div_factorial_le_exp (x / exp v) (by positivity) m
    have h_fac_pos : (0 : ℝ) < m.factorial := by positivity
    rw [div_le_iff₀ h_fac_pos, div_pow, div_le_iff₀ (pow_pos (exp_pos v) m)] at h_tay
    calc x ^ m ≤ exp (x / exp v) * (m.factorial : ℝ) * exp v ^ m := h_tay
      _ = exp (log m.factorial + m * v + x / exp v) := by
          rw [exp_add (log m.factorial + m * v), exp_add (log m.factorial),
            exp_log h_fac_pos, ← exp_natCast_mul]; ring
  set w : ℝ := ∑ τ : Φ, ∑ i ∈ I,
    ((l (τ, i) : ℝ) / L + log (l (τ, i)).factorial + l (τ, i) * u) with hw
  have h_prod : ∏ τ : Φ, ∏ i ∈ I, ρ τ i ^ l (τ, i) ≤ exp (w + S / exp v) :=
    calc ∏ τ : Φ, ∏ i ∈ I, ρ τ i ^ l (τ, i)
        ≤ ∏ τ : Φ, ∏ i ∈ I, exp (log (l (τ, i)).factorial + l (τ, i) * v + ρ τ i / exp v) := by
          gcongr with τ _ i hi
          · exact fun τ _ ↦ Finset.prod_nonneg fun j hj ↦ pow_nonneg (hρ τ j hj) _
          · exact fun j hj ↦ pow_nonneg (hρ τ j hj) _
          · exact h_factor _ (hρ τ i hi) _
      _ = exp (w + S / exp v) := by
          simp only [hw, hS, v, ← exp_sum, Finset.sum_div, ← Finset.sum_add_distrib]
          congr 1; refine Finset.sum_congr rfl fun τ _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_; ring
  calc √(∏ τ : Φ, ∏ i ∈ I, ρ τ i ^ l (τ, i))
      ≤ √(exp (w + S / exp v)) := Real.sqrt_le_sqrt h_prod
    _ = exp ((w + S / exp v) / 2) := by rw [← exp_half]
    _ ≤ exp (w / 2 + L * R) := by rw [exp_le_exp, add_div]; linarith

end TauCeti

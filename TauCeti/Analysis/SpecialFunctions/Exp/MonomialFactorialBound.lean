/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exponential–factorial bounds for monomials under an `ℓ¹` sum constraint

For any nonnegative real `r`, natural number `n`, and real `v`, the Taylor term bound
`(r / exp v) ^ n / n! ≤ exp (r / exp v)` yields
`r ^ n ≤ exp (log n! + n * v + r / exp v)`. Multiplying over a finite index set `s` bounds any
monomial `∏ i ∈ s, ρ i ^ l i` in terms of `∑ i ∈ s, ρ i`. Choosing `v = u + L⁻¹` for `L > 0` and
using `exp L⁻¹ ≥ L⁻¹ + 1` gives the square-root bound
`√(∏ i ∈ s, ρ i ^ l i) ≤ exp ((∑ i ∈ s, (l i / L + log (l i)! + l i * u)) / 2 + L * R)`
whenever `∑ i ∈ s, ρ i ≤ exp u * (2 * L + 2) * R`.

## Main results

* `TauCeti.pow_le_exp_log_factorial_add`: `r ^ n ≤ exp (log n! + n * v + r / exp v)` for `0 ≤ r`.
* `TauCeti.prod_pow_le_exp_sum_log_factorial`: product form over any `Finset ι` of nonnegative
  reals `ρ i`.
* `TauCeti.sqrt_prod_pow_le_exp`: square-root exponential bound under
  `∑ i ∈ s, ρ i ≤ exp u * (2 * L + 2) * R` with `0 < L`.

## Provenance

Adapted from `grh-lean` (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/New/UpperBound/Kernels/JetConjugatesAndBounds.lean`, declaration `New.sqrt_prod_pow_le_exp`.
Here the monomial bound is stated over an arbitrary `Finset ι` and real-valued `ρ : ι → ℝ` with
nonnegativity hypotheses rather than a product `Φ × I` and `NNReal`.
-/

public section

open Finset Real

namespace TauCeti

/-- **Single-variable exponential–factorial bound.** For `0 ≤ r`, `n : ℕ`, and `v : ℝ`,
`r ^ n ≤ exp (log n! + n * v + r / exp v)`. -/
theorem pow_le_exp_log_factorial_add {r : ℝ} (hr : 0 ≤ r) (n : ℕ) (v : ℝ) :
    r ^ n ≤ exp (log (n.factorial : ℝ) + n * v + r / exp v) := by
  have hfact_pos : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hterm : (r / exp v) ^ n / n.factorial ≤ exp (r / exp v) :=
    Real.pow_div_factorial_le_exp (r / exp v) (div_nonneg hr (exp_pos v).le) n
  have hmul : (r / exp v) ^ n ≤ n.factorial * exp (r / exp v) :=
    (div_le_iff₀ hfact_pos).mp hterm |>.trans_eq (mul_comm _ _)
  have h_rhs : exp (log (n.factorial : ℝ) + n * v + r / exp v) =
      n.factorial * exp (r / exp v) * exp v ^ n := by
    rw [exp_add, exp_add, exp_log hfact_pos, exp_natCast_mul]
    ring
  rw [h_rhs]
  calc r ^ n = (r / exp v) ^ n * exp v ^ n := by
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero n (exp_ne_zero v))]
    _ ≤ n.factorial * exp (r / exp v) * exp v ^ n :=
        mul_le_mul_of_nonneg_right hmul (pow_nonneg (exp_pos v).le n)

/-- **Multivariable exponential–factorial bound.** For nonnegative `ρ : ι → ℝ` on a finite set `s`,
`∏ i ∈ s, ρ i ^ l i ≤ exp (∑ i ∈ s, (log (l i)! + l i * v) + (∑ i ∈ s, ρ i) / exp v)`. -/
theorem prod_pow_le_exp_sum_log_factorial {ι : Type*} (s : Finset ι) (ρ : ι → ℝ)
    (hρ : ∀ i ∈ s, 0 ≤ ρ i) (l : ι → ℕ) (v : ℝ) :
    ∏ i ∈ s, ρ i ^ l i ≤
      exp (∑ i ∈ s, (log ((l i).factorial : ℝ) + l i * v) + (∑ i ∈ s, ρ i) / exp v) := by
  calc ∏ i ∈ s, ρ i ^ l i
      ≤ ∏ i ∈ s, exp (log ((l i).factorial : ℝ) + l i * v + ρ i / exp v) := by
        gcongr with i hi
        · exact fun i hi ↦ pow_nonneg (hρ i hi) _
        · exact pow_le_exp_log_factorial_add (hρ i hi) (l i) v
    _ = exp (∑ i ∈ s, (log ((l i).factorial : ℝ) + l i * v + ρ i / exp v)) := (exp_sum _ _).symm
    _ = exp (∑ i ∈ s, (log ((l i).factorial : ℝ) + l i * v) + (∑ i ∈ s, ρ i) / exp v) := by
        rw [Finset.sum_add_distrib, Finset.sum_div]

/-- **Square-root monomial bound under an `ℓ¹` sum constraint.** If `0 < L`, `ρ i ≥ 0` on `s`, and
`∑ i ∈ s, ρ i ≤ exp u * (2 * L + 2) * R`, then
`√(∏ i ∈ s, ρ i ^ l i) ≤ exp ((∑ i ∈ s, (l i / L + log (l i)! + l i * u)) / 2 + L * R)`. -/
theorem sqrt_prod_pow_le_exp {ι : Type*} (s : Finset ι) (ρ : ι → ℝ) (hρ : ∀ i ∈ s, 0 ≤ ρ i)
    (l : ι → ℕ) {L u R : ℝ} (hL : 0 < L)
    (h_sum : ∑ i ∈ s, ρ i ≤ exp u * (2 * L + 2) * R) :
    √(∏ i ∈ s, ρ i ^ l i) ≤
      exp ((∑ i ∈ s, ((l i : ℝ) / L + log ((l i).factorial : ℝ) + l i * u)) / 2 + L * R) := by
  have h_denom : 0 < exp u * (L⁻¹ + 1) := mul_pos (exp_pos u) (by positivity)
  have h_tail : (∑ i ∈ s, ρ i) / exp (u + L⁻¹) ≤ 2 * (L * R) := by
    calc (∑ i ∈ s, ρ i) / exp (u + L⁻¹)
        ≤ exp u * (2 * L + 2) * R / (exp u * (L⁻¹ + 1)) := by
          rw [exp_add]
          exact div_le_div₀ (by linarith [Finset.sum_nonneg hρ]) h_sum h_denom
            (mul_le_mul_of_nonneg_left (add_one_le_exp L⁻¹) (exp_pos u).le)
      _ = 2 * (L * R) := by field_simp; ring
  have h_prod := prod_pow_le_exp_sum_log_factorial s ρ hρ l (u + L⁻¹)
  have h_exp_eq :
      ∑ i ∈ s, (log ((l i).factorial : ℝ) + l i * (u + L⁻¹)) =
        ∑ i ∈ s, ((l i : ℝ) / L + log ((l i).factorial : ℝ) + l i * u) :=
    Finset.sum_congr rfl fun i _ ↦ by ring
  rw [h_exp_eq] at h_prod
  calc √(∏ i ∈ s, ρ i ^ l i)
      ≤ √(exp (∑ i ∈ s, ((l i : ℝ) / L + log ((l i).factorial : ℝ) + l i * u) +
          2 * (L * R))) := by
        refine Real.sqrt_le_sqrt (h_prod.trans (exp_le_exp.mpr ?_))
        linarith
    _ = exp ((∑ i ∈ s, ((l i : ℝ) / L + log ((l i).factorial : ℝ) + l i * u)) / 2 + L * R) := by
        rw [← exp_half, add_div, mul_div_cancel_left₀ _ two_ne_zero]

end TauCeti

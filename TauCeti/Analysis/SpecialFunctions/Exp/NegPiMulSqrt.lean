/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Certified bounds for `e^{-π √m}`

The nome `|q| = e^{-2π Im τ}` at a CM point with `Im τ = √m / 2` is `e^{-π √m}`. This file turns
rational bounds on `√m` into rational bounds on `e^{-π √m}`, using the certified decimal
enclosures of `π` and `e` and a partial sum of the exponential series. The hypotheses are exact
rational inequalities, so `norm_num` discharges them for concrete `m`.

## Main results

* `TauCeti.exp_neg_pi_mul_sqrt_le`: an upper bound for `e^{-π √m}` from a lower bound `s ≤ √m`.
* `TauCeti.le_exp_neg_pi_mul_sqrt`: a lower bound for `e^{-π √m}` from an upper bound `√m ≤ s`.
-/

public section

open scoped Real

namespace TauCeti

/-- `e^{-x} ≤ (e₋ᵏ ∑_{i < 6} cⁱ / i!)⁻¹` for `k + c ≤ x` and `c ≥ 0`, with `e₋ = 2.7182818283`. -/
private theorem exp_neg_le_of_le {x c : ℝ} (k : ℕ) (hc : 0 ≤ c) (hx : k + c ≤ x) :
    Real.exp (-x) ≤ (2.7182818283 ^ k * ∑ i ∈ Finset.range 6, c ^ i / i.factorial)⁻¹ := by
  have hS : 0 < ∑ i ∈ Finset.range 6, c ^ i / i.factorial := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    positivity
  calc Real.exp (-x) ≤ Real.exp (-(k + c)) := Real.exp_le_exp.2 (by linarith)
    _ = (Real.exp 1 ^ k * Real.exp c)⁻¹ := by
      rw [Real.exp_neg, Real.exp_add, ← Real.exp_natCast_mul, mul_one]
    _ ≤ _ := inv_anti₀ (by positivity) (mul_le_mul (pow_le_pow_left₀ (by norm_num)
      Real.exp_one_gt_d9.le k) (Real.sum_le_exp_of_nonneg hc 6) hS.le (by positivity))

/-- `(∑_{i < 6} dⁱ / i!) / e₊ᵏ ≤ e^{-x}` for `x ≤ k - d` and `d ≥ 0`, with `e₊ = 2.7182818286`. -/
private theorem le_exp_neg_of_le {x d : ℝ} (k : ℕ) (hd : 0 ≤ d) (hx : x ≤ k - d) :
    (∑ i ∈ Finset.range 6, d ^ i / i.factorial) / 2.7182818286 ^ k ≤ Real.exp (-x) := by
  calc (∑ i ∈ Finset.range 6, d ^ i / i.factorial) / 2.7182818286 ^ k
      ≤ Real.exp d / Real.exp 1 ^ k := by
        gcongr
        · exact Real.sum_le_exp_of_nonneg hd 6
        · exact Real.exp_one_lt_d9.le
    _ = Real.exp (-(k - d)) := by
      rw [← Real.exp_natCast_mul, mul_one, ← Real.exp_sub]
      ring_nf
    _ ≤ Real.exp (-x) := Real.exp_le_exp.2 (by linarith)

/-- An upper bound for `e^{-π √m}` from a lower bound `s ≤ √m`: if `k + c ≤ 3.141592 s`, then
`e^{-π √m} ≤ (e₋ᵏ ∑_{i < 6} cⁱ / i!)⁻¹` with `e₋ = 2.7182818283`. -/
theorem exp_neg_pi_mul_sqrt_le {m s c α : ℝ} (k : ℕ) (hs₀ : 0 ≤ s) (hs : s ^ 2 ≤ m)
    (hc : 0 ≤ c) (hk : k + c ≤ 3.141592 * s)
    (hα : (2.7182818283 ^ k * ∑ i ∈ Finset.range 6, c ^ i / i.factorial)⁻¹ ≤ α) :
    Real.exp (-(π * √m)) ≤ α := by
  have h₁ : s ≤ √m := by simpa [Real.sqrt_sq hs₀] using Real.sqrt_le_sqrt hs
  have h₂ : 3.141592 * s ≤ π * √m := mul_le_mul Real.pi_gt_d6.le h₁ hs₀ Real.pi_pos.le
  exact (exp_neg_le_of_le k hc (hk.trans h₂)).trans hα

/-- A lower bound for `e^{-π √m}` from an upper bound `√m ≤ s`: if `3.141593 s ≤ k - d`, then
`(∑_{i < 6} dⁱ / i!) / e₊ᵏ ≤ e^{-π √m}` with `e₊ = 2.7182818286`. -/
theorem le_exp_neg_pi_mul_sqrt {m s d β : ℝ} (k : ℕ) (hs₀ : 0 ≤ s) (hs : m ≤ s ^ 2)
    (hd : 0 ≤ d) (hk : 3.141593 * s ≤ k - d)
    (hβ : β ≤ (∑ i ∈ Finset.range 6, d ^ i / i.factorial) / 2.7182818286 ^ k) :
    β ≤ Real.exp (-(π * √m)) := by
  have h₁ : √m ≤ s := by simpa [Real.sqrt_sq hs₀] using Real.sqrt_le_sqrt hs
  have h₂ : π * √m ≤ 3.141593 * s :=
    mul_le_mul Real.pi_lt_d6.le h₁ (Real.sqrt_nonneg _) (by norm_num)
  exact hβ.trans (le_exp_neg_of_le k hd (h₂.trans hk))

end TauCeti

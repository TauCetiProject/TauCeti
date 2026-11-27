/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TauCeti.NumberTheory.Transcendental.Waldschmidt.Interpolation.Data
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The Liouville reduction of a short rational coefficient relation

In the rank argument of Waldschmidt's proof of his lower bound for linear forms in logarithms
(W00 §9.2.3, §9.3.2), the normalized linear form is

`Λ = β₀ + β₁ λ₁ + ⋯ + β_{m-1} λ_{m-1} - λₘ`,

with coefficient vector `c = (β₁, …, β_{m-1}, -1)`. One excluded case of the zero estimate is
`β₀ = 0` together with a nonzero integral vector `s` (a sum of differences of grid indices) on
the line `ℂ c`. Such an `s` is a short rational coefficient relation: `sₘ ≠ 0` and
`β_k = -s_k / sₘ`, so that

`sₘ Λ = -(s₁ λ₁ + ⋯ + sₘ λₘ)`, i.e. `exp(-sₘ Λ) = α₁ ^ s₁ ⋯ αₘ ^ sₘ`,

where `αⱼ = exp λⱼ`. A lower bound `δ ≤ |α^s - 1|`, which Liouville's inequality
`NumberField.exp_neg_le_norm_prod_zpow_sub_one_of_le` supplies when the `αⱼ` are algebraic and
`α^s ≠ 1`, then bounds `|Λ|` from below; when `α^s = 1`, the number `sₘ Λ` is a nonzero multiple
of `2πi` as soon as `Λ ≠ 0`. Either way `|Λ|` cannot be as small as the measure assumes, which
rules the case out.

Throughout, `m = n + 1`, with the indexing conventions of
`TauCeti.NumberTheory.Transcendental.Waldschmidt.Interpolation.Data`.

## Main results

* `TauCeti.eq_neg_div_of_intCast_mem_span_snoc`: a nonzero integral vector on the line through
  the coefficient vector has nonzero last coordinate `sₘ`, and `β_k = -s_k / sₘ`.
* `TauCeti.intCast_mul_waldschmidtLinearForm_eq_neg_sum`,
  `TauCeti.exp_neg_intCast_mul_waldschmidtLinearForm`: for such a relation with `β₀ = 0`,
  `sₘ Λ = -(s₁ λ₁ + ⋯ + sₘ λₘ)` and `exp(-sₘ Λ) = α^s`.
* `TauCeti.min_one_div_two_le_norm_intCast_mul_waldschmidtLinearForm`: a lower bound
  `δ ≤ |α^s - 1|` gives `min 1 (δ / 2) ≤ |sₘ Λ|`.
* `TauCeti.two_mul_pi_le_norm_intCast_mul_waldschmidtLinearForm`: if `α^s = 1` and `Λ ≠ 0`, then
  `2π ≤ |sₘ Λ|`.
* `TauCeti.min_one_div_two_le_norm_intCast_mul_waldschmidtLinearForm_of_ne_zero`: both cases
  together, under `Λ ≠ 0`.
* `TauCeti.min_one_div_two_le_norm_intCast_mul_waldschmidtLinearForm_of_mem_span`: the same bound
  `min 1 (δ / 2) ≤ |sₘ| |Λ|`, starting from a nonzero integral vector on the line `ℂ c`.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000),
  §9.2.3 and §9.3.2, Step 2.
-/

public section

open Complex Finset

namespace TauCeti

variable {n : ℕ}

/-- A nonzero integral vector `s` on the line through the coefficient vector
`c = (β₁, …, β_{m-1}, -1)` is a short rational coefficient relation: its last coordinate `sₘ` is
nonzero and `β_k = -s_k / sₘ` for `1 ≤ k < m`. -/
theorem eq_neg_div_of_intCast_mem_span_snoc {K : Type*} [Field K] [CharZero K]
    (b : Fin (n + 1) → K) {s : Fin (n + 1) → ℤ} (hs : s ≠ 0)
    (hmem : (fun i ↦ (s i : K)) ∈ K ∙ Fin.snoc (fun k : Fin n ↦ b k.succ) (-1)) :
    s (Fin.last n) ≠ 0 ∧ ∀ k : Fin n, b k.succ = -(s k.castSucc : K) / s (Fin.last n) := by
  rw [← comap_waldschmidtPointMap_span_single, Submodule.mem_comap] at hmem
  have hv := eq_neg_smul_snoc_of_waldschmidtPointMap_mem b hmem
  have hlast : s (Fin.last n) ≠ 0 := by
    refine fun h ↦ hs (funext fun i ↦ ?_)
    simpa [h] using congrFun hv i
  refine ⟨hlast, fun k ↦ ?_⟩
  have := congrFun hv k.castSucc
  simp only [Pi.smul_apply, Fin.snoc_castSucc, smul_eq_mul] at this
  rw [eq_div_iff (Int.cast_ne_zero.2 hlast), this]
  ring

/-- A short rational coefficient relation turns the linear form into an integral one: if `β₀ = 0`
and `β_k = -s_k / sₘ` for `1 ≤ k < m` (as `TauCeti.eq_neg_div_of_intCast_mem_span_snoc`
provides), then `sₘ Λ = -(s₁ λ₁ + ⋯ + sₘ λₘ)`. -/
theorem intCast_mul_waldschmidtLinearForm_eq_neg_sum (l b : Fin (n + 1) → ℂ)
    {s : Fin (n + 1) → ℤ} (hlast : s (Fin.last n) ≠ 0) (hb₀ : b 0 = 0)
    (hb : ∀ k : Fin n, b k.succ = -(s k.castSucc : ℂ) / s (Fin.last n)) :
    (s (Fin.last n) : ℂ) * waldschmidtLinearForm l b = -∑ j, (s j : ℂ) * l j := by
  have hs : (s (Fin.last n) : ℂ) ≠ 0 := Int.cast_ne_zero.2 hlast
  simp only [waldschmidtLinearForm_def, hb₀, hb, Fin.sum_univ_castSucc, mul_sub, mul_sum,
    zero_add]
  have hsum : ∑ k : Fin n, (s (Fin.last n) : ℂ) * (-(s k.castSucc : ℂ) / s (Fin.last n) *
      l k.castSucc) = -∑ k : Fin n, (s k.castSucc : ℂ) * l k.castSucc := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun k _ ↦ by field_simp
  rw [hsum]
  ring

/-- The exponential form of `TauCeti.intCast_mul_waldschmidtLinearForm_eq_neg_sum`: for a short
rational coefficient relation with `β₀ = 0`, `exp(-sₘ Λ) = α₁ ^ s₁ ⋯ αₘ ^ sₘ` with
`αⱼ = exp λⱼ`. So `Λ ≠ 0` as soon as `α^s ≠ 1`. -/
theorem exp_neg_intCast_mul_waldschmidtLinearForm (l b : Fin (n + 1) → ℂ)
    {s : Fin (n + 1) → ℤ} (hlast : s (Fin.last n) ≠ 0) (hb₀ : b 0 = 0)
    (hb : ∀ k : Fin n, b k.succ = -(s k.castSucc : ℂ) / s (Fin.last n)) :
    cexp (-((s (Fin.last n) : ℂ) * waldschmidtLinearForm l b)) = ∏ j, cexp (l j) ^ s j := by
  rw [intCast_mul_waldschmidtLinearForm_eq_neg_sum l b hlast hb₀ hb, neg_neg, Complex.exp_sum]
  exact prod_congr rfl fun j _ ↦ Complex.exp_intCast_mul (s j) (l j)

/-- A lower bound `δ ≤ |α^s - 1|` (for instance Liouville's inequality,
`NumberField.exp_neg_le_norm_prod_zpow_sub_one_of_le`) bounds the linear form of a short rational
coefficient relation with `β₀ = 0` from below: `min 1 (δ / 2) ≤ |sₘ Λ|`. This is because
`exp(-sₘ Λ) = α^s` (`TauCeti.exp_neg_intCast_mul_waldschmidtLinearForm`) and
`|exp z - 1| ≤ 2 |z|` for `|z| ≤ 1`. -/
theorem min_one_div_two_le_norm_intCast_mul_waldschmidtLinearForm (l b : Fin (n + 1) → ℂ)
    {s : Fin (n + 1) → ℤ} (hlast : s (Fin.last n) ≠ 0) (hb₀ : b 0 = 0)
    (hb : ∀ k : Fin n, b k.succ = -(s k.castSucc : ℂ) / s (Fin.last n)) {δ : ℝ}
    (hδ : δ ≤ ‖∏ j, cexp (l j) ^ s j - 1‖) :
    min 1 (δ / 2) ≤ ‖(s (Fin.last n) : ℂ) * waldschmidtLinearForm l b‖ := by
  rcases le_or_gt ‖(s (Fin.last n) : ℂ) * waldschmidtLinearForm l b‖ 1 with h | h
  · refine min_le_of_right_le (div_le_of_le_mul₀ zero_le_two (norm_nonneg _) ?_)
    rw [← exp_neg_intCast_mul_waldschmidtLinearForm l b hlast hb₀ hb] at hδ
    rw [mul_comm, ← norm_neg ((s (Fin.last n) : ℂ) * _)]
    exact hδ.trans (Complex.norm_exp_sub_one_le ((norm_neg _).trans_le h))
  · exact min_le_of_left_le h.le

/-- The case `α^s = 1` of the Liouville reduction: for a short rational coefficient relation with
`β₀ = 0`, `α₁ ^ s₁ ⋯ αₘ ^ sₘ = 1` and `Λ ≠ 0`, the number `sₘ Λ` is a nonzero multiple of `2πi`
(`TauCeti.exp_neg_intCast_mul_waldschmidtLinearForm`), so `2π ≤ |sₘ Λ|`. -/
theorem two_mul_pi_le_norm_intCast_mul_waldschmidtLinearForm (l b : Fin (n + 1) → ℂ)
    {s : Fin (n + 1) → ℤ} (hlast : s (Fin.last n) ≠ 0) (hb₀ : b 0 = 0)
    (hb : ∀ k : Fin n, b k.succ = -(s k.castSucc : ℂ) / s (Fin.last n))
    (hΛ : waldschmidtLinearForm l b ≠ 0) (hα : ∏ j, cexp (l j) ^ s j = 1) :
    2 * Real.pi ≤ ‖(s (Fin.last n) : ℂ) * waldschmidtLinearForm l b‖ := by
  rw [← exp_neg_intCast_mul_waldschmidtLinearForm l b hlast hb₀ hb, Complex.exp_eq_one_iff]
    at hα
  obtain ⟨k, hk⟩ := hα
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (Int.cast_ne_zero.2 hlast) hΛ (by simpa using hk)
  rw [← norm_neg, hk, norm_mul, Complex.norm_intCast, norm_mul, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Complex.norm_I, Real.norm_of_nonneg Real.pi_pos.le, mul_one]
  exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast Int.one_le_abs hk0)

/-- The Liouville reduction of a short rational coefficient relation with `β₀ = 0`, both cases
together: if `Λ ≠ 0` and `δ ≤ |α^s - 1|` whenever `α^s ≠ 1` (for instance by Liouville's
inequality, `NumberField.exp_neg_le_norm_prod_zpow_sub_one_of_le`), then
`min 1 (δ / 2) ≤ |sₘ Λ|`. -/
theorem min_one_div_two_le_norm_intCast_mul_waldschmidtLinearForm_of_ne_zero
    (l b : Fin (n + 1) → ℂ) {s : Fin (n + 1) → ℤ} (hlast : s (Fin.last n) ≠ 0) (hb₀ : b 0 = 0)
    (hb : ∀ k : Fin n, b k.succ = -(s k.castSucc : ℂ) / s (Fin.last n))
    (hΛ : waldschmidtLinearForm l b ≠ 0) {δ : ℝ}
    (hδ : ∏ j, cexp (l j) ^ s j ≠ 1 → δ ≤ ‖∏ j, cexp (l j) ^ s j - 1‖) :
    min 1 (δ / 2) ≤ ‖(s (Fin.last n) : ℂ) * waldschmidtLinearForm l b‖ := by
  by_cases hα : ∏ j, cexp (l j) ^ s j = 1
  · refine min_le_of_left_le (le_trans ?_
      (two_mul_pi_le_norm_intCast_mul_waldschmidtLinearForm l b hlast hb₀ hb hΛ hα))
    linarith [Real.two_le_pi]
  · exact min_one_div_two_le_norm_intCast_mul_waldschmidtLinearForm l b hlast hb₀ hb (hδ hα)

/-- The Liouville reduction in the form the excluded case `β₀ = 0`, `(S - S)[2] ∩ ℂ c ≠ {0}`
presents it: a nonzero integral vector `s` on the line through `c = (β₁, …, β_{m-1}, -1)` has
`sₘ ≠ 0`, and if `Λ ≠ 0` and `δ ≤ |α^s - 1|` whenever `α^s ≠ 1`, then
`min 1 (δ / 2) ≤ |sₘ| |Λ|`. -/
theorem min_one_div_two_le_norm_intCast_mul_waldschmidtLinearForm_of_mem_span
    (l b : Fin (n + 1) → ℂ) {s : Fin (n + 1) → ℤ} (hs : s ≠ 0)
    (hmem : (fun i ↦ (s i : ℂ)) ∈ ℂ ∙ Fin.snoc (fun k : Fin n ↦ b k.succ) (-1)) (hb₀ : b 0 = 0)
    (hΛ : waldschmidtLinearForm l b ≠ 0) {δ : ℝ}
    (hδ : ∏ j, cexp (l j) ^ s j ≠ 1 → δ ≤ ‖∏ j, cexp (l j) ^ s j - 1‖) :
    s (Fin.last n) ≠ 0 ∧
      min 1 (δ / 2) ≤ |(s (Fin.last n) : ℝ)| * ‖waldschmidtLinearForm l b‖ := by
  obtain ⟨hlast, hb⟩ := eq_neg_div_of_intCast_mem_span_snoc b hs hmem
  refine ⟨hlast, ?_⟩
  have h := min_one_div_two_le_norm_intCast_mul_waldschmidtLinearForm_of_ne_zero l b hlast hb₀
    hb hΛ hδ
  rwa [norm_mul, Complex.norm_intCast] at h

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Totient
public import TauCeti.NumberTheory.Mertens.Basic
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.Data.Nat.Totient
import TauCeti.NumberTheory.PrimeFactors.Bounds

/-!
# The minimal order of the totient

Euler's product formula gives `n / φ(n) = ∏_{p ∣ n} (1 - p⁻¹)⁻¹`. This file bounds the product by
splitting the prime divisors of `n` at a real `y > 1`. The primes `p ≤ y` contribute at most the
full Euler product `∏_{p ≤ y} (1 - p⁻¹)⁻¹`, which Mertens's third theorem evaluates as
`e^γ log y + O(1)`. There are at most `log n / log y` prime divisors `p > y`, and each has
`(1 - p⁻¹)⁻¹ ≤ exp (2 / y)`, so they contribute at most `exp (2 log n / (y log y))`. The choice
`y = log n` gives

`n / φ(n) ≤ (e^γ log log n + C) exp (2 / log log n)`

with an absolute constant `C`. Hence `n / φ(n) ≤ C' log log n` for all `n ≥ 3`, and
`n / φ(n) ≤ (e^γ + ε) log log n` for all large `n`, which is the upper half of Landau's theorem
`limsup n / (φ(n) log log n) = e^γ`.

## Main results

* `Nat.card_primeFactors_filter_gt_mul_log_le`: `n` has at most `log n / log y` prime divisors
  `p > y`.
* `Nat.prod_primeFactors_filter_le_one_sub_inv_inv_le`,
  `Nat.prod_primeFactors_filter_gt_one_sub_inv_inv_le`: the bounds for the prime divisors
  `p ≤ y` and `p > y` of `n`.
* `Nat.div_totient_le_prod_primesLE_mul_exp`: `n / φ(n) ≤ ∏_{p ≤ y} (1 - p⁻¹)⁻¹ *
  exp (2 log n / (y log y))` for `y > 1`.
* `TauCeti.exists_div_totient_le_add_mul_exp`: `n / φ(n) ≤ (e^γ log log n + C) *
  exp (2 / log log n)` with an absolute constant `C`.
* `TauCeti.exists_div_totient_le_mul_log_log`, `TauCeti.exists_one_div_totient_le_mul_log_log_div`:
  `n / φ(n) ≤ C log log n` and `1 / φ(n) ≤ C log log n / n` for `n ≥ 3`.
* `TauCeti.eventually_div_totient_le_mul_log_log`: `n / φ(n) ≤ (e^γ + ε) log log n` for all large
  `n`.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*,
  Theorem 2.9.
* A. N. Skorobogatov and E. Sofos, *Schinzel Hypothesis on average and rational points*,
  Invent. Math. 231 (2023), equation (3.7).
-/

public section

open Filter Finset
open scoped Nat Topology

namespace Nat

variable {y : ℝ}

/-- A natural number `n` has at most `log n / log y` prime divisors `p > y`, for every real
`y ≥ 0`: the product of these primes is at most `n`. -/
theorem card_primeFactors_filter_gt_mul_log_le (n : ℕ) (hy : 0 ≤ y) :
    (#(n.primeFactors.filter fun p : ℕ ↦ y < p) : ℝ) * Real.log y ≤ Real.log n := by
  rcases hy.eq_or_lt with rfl | hy
  · simpa using Real.log_natCast_nonneg n
  calc (#(n.primeFactors.filter fun p : ℕ ↦ y < p) : ℝ) * Real.log y
      = ∑ _p ∈ n.primeFactors.filter (fun p : ℕ ↦ y < p), Real.log y := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ ↦ y < p), Real.log p :=
        sum_le_sum fun p hp ↦ Real.log_le_log hy (mem_filter.1 hp).2.le
    _ ≤ ∑ p ∈ n.primeFactors, Real.log p :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ ↦ Real.log_natCast_nonneg p
    _ ≤ Real.log n := sum_primeFactors_log_le n

/-- The Euler factors of the prime divisors `p ≤ y` of `n` are bounded by the full Euler product
over the primes `p ≤ y`. -/
theorem prod_primeFactors_filter_le_one_sub_inv_inv_le (n : ℕ) (y : ℝ) :
    ∏ p ∈ n.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ y), (1 - (p : ℝ)⁻¹)⁻¹ ≤
      ∏ p ∈ primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hpos : ∀ p : ℕ, p.Prime → 0 < 1 - (p : ℝ)⁻¹ := fun p hp ↦
    sub_pos.2 (inv_lt_one_of_one_lt₀ (mod_cast hp.one_lt))
  refine prod_le_prod_of_subset_of_one_le₀ (fun p hp ↦ ?_) (fun p hp ↦ ?_) fun p hp _ ↦ ?_
  · obtain ⟨hp, hpy⟩ := mem_filter.1 hp
    exact mem_primesLE.2 ⟨le_floor hpy, prime_of_mem_primeFactors hp⟩
  · exact (inv_pos.2 (hpos p (prime_of_mem_primeFactors (mem_filter.1 hp).1))).le
  · exact (one_le_inv₀ (hpos p (prime_of_mem_primesLE hp))).2 (sub_le_self 1 (by positivity))

/-- The Euler factors of the prime divisors `p > y` of `n` multiply to at most
`exp (2 log n / (y log y))`, for every real `y > 1`. -/
theorem prod_primeFactors_filter_gt_one_sub_inv_inv_le (n : ℕ) (hy : 1 < y) :
    ∏ p ∈ n.primeFactors.filter (fun p : ℕ ↦ y < p), (1 - (p : ℝ)⁻¹)⁻¹ ≤
      Real.exp (2 * Real.log n / (y * Real.log y)) := by
  have hy0 : 0 < y := zero_lt_one.trans hy
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hfactor : ∀ p ∈ n.primeFactors.filter (fun p : ℕ ↦ y < p),
      (1 - (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (2 / y) := by
    intro p hp
    obtain ⟨hp, hyp⟩ := mem_filter.1 hp
    have hp2 : (2 : ℝ) ≤ p := mod_cast (prime_of_mem_primeFactors hp).two_le
    have hinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [one_div]
      exact inv_anti₀ two_pos hp2
    have hlog := Real.abs_log_le_two_mul_one_sub (x := 1 - (p : ℝ)⁻¹) (by linarith)
      (sub_le_self 1 (inv_nonneg.2 (zero_le_two.trans hp2)))
    rw [sub_sub_cancel] at hlog
    have hpy : (p : ℝ)⁻¹ ≤ y⁻¹ := inv_anti₀ hy0 hyp.le
    rw [← Real.exp_log (inv_pos.2 (by linarith : 0 < 1 - (p : ℝ)⁻¹)), Real.log_inv]
    refine Real.exp_le_exp.2 ?_
    rw [div_eq_mul_inv]
    linarith [neg_le_abs (Real.log (1 - (p : ℝ)⁻¹))]
  have hcard : (#(n.primeFactors.filter fun p : ℕ ↦ y < p) : ℝ) * (2 / y) ≤
      2 * Real.log n / (y * Real.log y) := by
    rw [le_div_iff₀ (mul_pos hy0 hlogy)]
    calc (#(n.primeFactors.filter fun p : ℕ ↦ y < p) : ℝ) * (2 / y) * (y * Real.log y)
        = 2 * ((#(n.primeFactors.filter fun p : ℕ ↦ y < p) : ℝ) * Real.log y) := by field_simp
      _ ≤ 2 * Real.log n := by gcongr; exact card_primeFactors_filter_gt_mul_log_le n hy0.le
  calc ∏ p ∈ n.primeFactors.filter (fun p : ℕ ↦ y < p), (1 - (p : ℝ)⁻¹)⁻¹
      ≤ ∏ p ∈ n.primeFactors.filter (fun p : ℕ ↦ y < p), Real.exp (2 / y) :=
        prod_le_prod₀ (fun p _ ↦ inv_nonneg.2 (sub_nonneg.2 (cast_inv_le_one p))) hfactor
    _ = Real.exp ((#(n.primeFactors.filter fun p : ℕ ↦ y < p) : ℝ) * (2 / y)) := by
        rw [prod_const, ← Real.exp_natCast_mul]
    _ ≤ Real.exp (2 * Real.log n / (y * Real.log y)) := Real.exp_le_exp.2 hcard

/-- **The totient and the Euler product at a cutoff.** For every `n` and every real `y > 1`,
`n / φ(n) ≤ ∏_{p ≤ y} (1 - p⁻¹)⁻¹ * exp (2 log n / (y log y))`. For `n = 0` the left side is
`0`. -/
theorem div_totient_le_prod_primesLE_mul_exp (n : ℕ) (hy : 1 < y) :
    (n : ℝ) / φ n ≤ (∏ p ∈ primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹)⁻¹) *
      Real.exp (2 * Real.log n / (y * Real.log y)) := by
  have hnonneg : ∀ s : Finset ℕ, 0 ≤ ∏ p ∈ s, (1 - (p : ℝ)⁻¹)⁻¹ := fun s ↦
    prod_nonneg fun p _ ↦ inv_nonneg.2 (sub_nonneg.2 (cast_inv_le_one p))
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using hnonneg _
  rw [← TauCeti.Nat.prod_inv_one_sub_inv_eq_div_totient hn,
    ← prod_filter_mul_prod_filter_not n.primeFactors (fun p : ℕ ↦ (p : ℝ) ≤ y)]
  simp only [not_le]
  exact mul_le_mul (prod_primeFactors_filter_le_one_sub_inv_inv_le n y)
    (prod_primeFactors_filter_gt_one_sub_inv_inv_le n hy) (hnonneg _) (hnonneg _)

end Nat

namespace TauCeti

/-- **The minimal order of the totient, with the sharp constant.** There is an absolute constant
`C` with `n / φ(n) ≤ (e^γ log log n + C) exp (2 / log log n)` for every `n`. The estimate has
content for `log n ≥ 2`, where it comes from Mertens's third theorem; the finitely many smaller
`n` are absorbed in `C`. -/
theorem exists_div_totient_le_add_mul_exp :
    ∃ C : ℝ, ∀ n : ℕ,
      (n : ℝ) / φ n ≤
        (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) + C) *
          Real.exp (2 / Real.log (Real.log n)) := by
  obtain ⟨C₁, hC₁⟩ := exists_abs_prod_primesLE_one_sub_inv_inv_sub_exp_mul_log_le
  obtain ⟨M, hM⟩ := ((range ⌈Real.exp 2⌉₊).image fun n : ℕ ↦
    (n : ℝ) / φ n * Real.exp (-(2 / Real.log (Real.log n))) -
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n)).exists_le
  refine ⟨max C₁ M, fun n ↦ ?_⟩
  rcases lt_or_ge (Real.log n) 2 with hn | hn
  · have hmem : n ∈ range ⌈Real.exp 2⌉₊ := by
      rcases eq_or_ne n 0 with rfl | hn0
      · simpa using Real.exp_pos 2
      · exact mem_range.2 (Nat.lt_ceil.2 ((Real.log_lt_iff_lt_exp (by positivity)).1 hn))
    have h := hM _ (mem_image_of_mem _ hmem)
    calc (n : ℝ) / φ n
        = (n : ℝ) / φ n * Real.exp (-(2 / Real.log (Real.log n))) *
            Real.exp (2 / Real.log (Real.log n)) := by
          rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      _ ≤ _ := by gcongr; linarith [le_max_right C₁ M]
  · have hlog : 0 < Real.log n := zero_lt_two.trans_le hn
    have h := Nat.div_totient_le_prod_primesLE_mul_exp n (one_lt_two.trans_le hn)
    rw [mul_comm 2, mul_div_mul_left _ _ hlog.ne'] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    linarith [(abs_le.1 (hC₁ _ hn)).2, le_max_left C₁ M]

/-- **The minimal order of the totient.** There is an absolute constant `C > 0` with
`n / φ(n) ≤ C log log n` for every `n ≥ 3`. -/
theorem exists_div_totient_le_mul_log_log :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n → (n : ℝ) / φ n ≤ C * Real.log (Real.log n) := by
  obtain ⟨C₁, hC₁⟩ := exists_div_totient_le_add_mul_exp
  have hlog3 : 1 < Real.log 3 := (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
  have hll3 : 0 < Real.log (Real.log 3) := Real.log_pos hlog3
  have hA : 0 < (Real.exp Real.eulerMascheroniConstant + |C₁|) * Real.exp 2 := by positivity
  have hB : 0 < Real.exp (Real.exp 1) / Real.log (Real.log 3) := div_pos (Real.exp_pos _) hll3
  refine ⟨(Real.exp Real.eulerMascheroniConstant + |C₁|) * Real.exp 2 +
    Real.exp (Real.exp 1) / Real.log (Real.log 3), add_pos hA hB, fun n hn ↦ ?_⟩
  have hn3 : (3 : ℝ) ≤ n := mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogn : 0 < Real.log n :=
    zero_lt_one.trans (hlog3.trans_le (Real.log_le_log (by norm_num) hn3))
  have hL3 : Real.log (Real.log 3) ≤ Real.log (Real.log n) :=
    Real.log_le_log (zero_lt_one.trans hlog3) (Real.log_le_log (by norm_num) hn3)
  have hL0 : 0 < Real.log (Real.log n) := hll3.trans_le hL3
  rw [add_mul]
  rcases le_or_gt 1 (Real.log (Real.log n)) with hL | hL
  · calc (n : ℝ) / φ n
        ≤ (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) + C₁) *
            Real.exp (2 / Real.log (Real.log n)) := hC₁ n
      _ ≤ (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) +
            |C₁| * Real.log (Real.log n)) * Real.exp 2 := by
          gcongr
          · exact (le_abs_self C₁).trans (le_mul_of_one_le_right (abs_nonneg C₁) hL)
          · exact div_le_self zero_le_two hL
      _ = (Real.exp Real.eulerMascheroniConstant + |C₁|) * Real.exp 2 *
            Real.log (Real.log n) := by ring
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hB.le hL0.le)
  · have hn_lt : (n : ℝ) < Real.exp (Real.exp 1) :=
      (Real.log_lt_iff_lt_exp hn0).1 ((Real.log_lt_iff_lt_exp hlogn).1 hL)
    have hφ : (1 : ℝ) ≤ φ n := mod_cast Nat.totient_pos.2 (by omega)
    calc (n : ℝ) / φ n ≤ n := div_le_self hn0.le hφ
      _ ≤ Real.exp (Real.exp 1) / Real.log (Real.log 3) * Real.log (Real.log 3) := by
          rw [div_mul_cancel₀ _ hll3.ne']
          exact hn_lt.le
      _ ≤ Real.exp (Real.exp 1) / Real.log (Real.log 3) * Real.log (Real.log n) := by gcongr
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hA.le hL0.le)

/-- **The size of `1 / φ(n)`.** There is an absolute constant `C > 0` with
`1 / φ(n) ≤ C log log n / n` for every `n ≥ 3`. -/
theorem exists_one_div_totient_le_mul_log_log_div :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n → 1 / (φ n : ℝ) ≤ C * Real.log (Real.log n) / n := by
  obtain ⟨C, hC, h⟩ := exists_div_totient_le_mul_log_log
  refine ⟨C, hC, fun n hn ↦ ?_⟩
  have hn0 : (0 : ℝ) < n := mod_cast (by omega : 0 < n)
  rw [le_div_iff₀ hn0, one_div_mul_eq_div]
  exact h n hn

/-- **The upper half of Landau's theorem on the totient.** For every `ε > 0`,
`n / φ(n) ≤ (e^γ + ε) log log n` for all sufficiently large `n`. -/
theorem eventually_div_totient_le_mul_log_log {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / φ n ≤ (Real.exp Real.eulerMascheroniConstant + ε) * Real.log (Real.log n) := by
  obtain ⟨C, hC⟩ := exists_div_totient_le_add_mul_exp
  have hlim : Tendsto (fun L : ℝ ↦ (Real.exp Real.eulerMascheroniConstant + C / L) *
      Real.exp (2 / L)) atTop (𝓝 ((Real.exp Real.eulerMascheroniConstant + 0) * Real.exp 0)) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)).mul
      ((Real.continuous_exp.tendsto 0).comp (tendsto_const_nhds.div_atTop tendsto_id))
  rw [add_zero, Real.exp_zero, mul_one] at hlim
  have hL : Tendsto (fun n : ℕ ↦ Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hL.eventually (hlim.eventually_lt_const (lt_add_of_pos_right _ hε)),
    hL.eventually_gt_atTop 0] with n hn hL0
  calc (n : ℝ) / φ n
      ≤ (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) + C) *
          Real.exp (2 / Real.log (Real.log n)) := hC n
    _ = (Real.exp Real.eulerMascheroniConstant + C / Real.log (Real.log n)) *
          Real.exp (2 / Real.log (Real.log n)) * Real.log (Real.log n) := by
        field_simp
    _ ≤ (Real.exp Real.eulerMascheroniConstant + ε) * Real.log (Real.log n) := by gcongr

end TauCeti

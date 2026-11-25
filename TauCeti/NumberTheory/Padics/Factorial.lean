/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Factorial.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Factorials in p-adic fields

The integers `n!` converge to zero at every finite place, although none is zero. This provides
one sequence of rational parameters that simultaneously contracts every local unipotent
one-parameter subgroup. Divisibility by each fixed prime power suffices for the convergence.

## Main results

* `TauCeti.tendsto_padic_natCast_factorial`: the factorials tend to zero in `ℚ_[p]`.
* `TauCeti.padicValNat_factorial_eq_add_sum`: Legendre's formula truncated at level `h`,
  `v_p(n!) = v_p(⌊n / pʰ⌋!) + ∑_{k = 1}^{h} ⌊n / pᵏ⌋`.
* `TauCeti.sub_one_mul_padicValNat_factorial_pow`: Legendre's formula for `(pᵏ)!`,
  `(p - 1) v_p((pᵏ)!) = pᵏ - 1`, and its real form `TauCeti.cast_multiplicity_factorial_pow`.
* `TauCeti.multiplicity_factorial_lt_div`, `TauCeti.multiplicity_factorial_le_div`: Legendre's
  bound `v_p(n!) < n / (p - 1)` for `n ≠ 0`, and its non-strict form for every `n`.
* `TauCeti.norm_factorial_eq_norm_factorial_div_mul_pow`,
  `TauCeti.factorial_dvd_factorial_div_mul_pow`: its consequence that `n!` has the norm of, and
  divides, `⌊n / pʰ⌋! p ^ (∑_{k = 1}^{h} ⌊n / pᵏ⌋)` in `ℤ_[p]`.
* `Padic.norm_factorial_mul`: `‖(p k)!‖ = p ^ (-k) ‖k!‖` in `ℚ_[p]`, by Legendre's formula.
* `Padic.rpow_neg_div_le_norm_factorial`: `p ^ (-n / (p - 1)) ≤ ‖n!‖` in `ℚ_[p]`.
-/

public section

namespace TauCeti

open Filter Topology

/-- The factorials, viewed in a fixed p-adic field, tend to zero. -/
theorem tendsto_padic_natCast_factorial (p : ℕ) [hp : Fact p.Prime] :
    Tendsto (fun n : ℕ ↦ (n.factorial : ℚ_[p])) atTop (𝓝 0) := by
  have hpow : Tendsto (fun k : ℕ ↦ (p : ℝ)⁻¹ ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := (hpow.eventually (gt_mem_nhds hε)).exists
  refine ⟨p ^ k, fun n hn ↦ ?_⟩
  have hd : (p : ℤ) ^ k ∣ (n.factorial : ℤ) := by
    exact_mod_cast Nat.dvd_factorial (pow_pos hp.out.pos _) hn
  have hnorm := (Padic.norm_int_le_pow_iff_dvd (p := p) (n.factorial : ℤ) k).mpr hd
  simp only [Int.cast_natCast, _root_.zpow_neg, zpow_natCast, ← inv_pow] at hnorm
  simpa only [dist_zero_right] using hnorm.trans_lt hk

/-- **Legendre's formula, truncated at level `h`.** The `p`-adic valuation of `n!` exceeds that of
`⌊n / pʰ⌋!` by `∑_{k = 1}^{h} ⌊n / pᵏ⌋`. -/
theorem padicValNat_factorial_eq_add_sum (p : ℕ) [Fact p.Prime] (n h : ℕ) :
    padicValNat p n.factorial =
      padicValNat p (n / p ^ h).factorial + ∑ k ∈ Finset.range h, n / p ^ (k + 1) := by
  simp only [Nat.padicValNat_def]
  induction h with
  | zero => simp
  | succ h ih =>
    rw [ih, Finset.sum_range_succ, ← _root_.multiplicity_mul_div_factorial (n / p ^ h),
      _root_.multiplicity_factorial_mul, Nat.div_div_eq_div_mul, ← pow_succ]
    ring

/-- **Legendre's formula for `(pᵏ)!`.** Since `pᵏ` has base-`p` digit sum one,
`(p - 1) v_p((pᵏ)!) = pᵏ - 1`. -/
theorem sub_one_mul_padicValNat_factorial_pow (p : ℕ) [hp : Fact p.Prime] (k : ℕ) :
    (p - 1) * padicValNat p (p ^ k).factorial = p ^ k - 1 := by
  rw [Nat.padicValNat_def, Nat.Prime.sub_one_mul_multiplicity_factorial hp.out, ← mul_one (p ^ k),
    Nat.digits_base_pow_mul hp.out.one_lt one_pos, Nat.digits_of_lt p 1 one_ne_zero hp.out.one_lt]
  simp

/-- **Legendre's formula for `(pᵏ)!`, in `ℝ`.** `v_p((pᵏ)!) = (pᵏ - 1) / (p - 1)`. -/
theorem cast_multiplicity_factorial_pow (p : ℕ) [hp : Fact p.Prime] (k : ℕ) :
    (multiplicity p (p ^ k).factorial : ℝ) = ((p : ℝ) ^ k - 1) / ((p : ℝ) - 1) := by
  have h : (((p - 1) * multiplicity p (p ^ k).factorial : ℕ) : ℝ) = ((p ^ k - 1 : ℕ) : ℝ) := by
    rw [← Nat.padicValNat_def, sub_one_mul_padicValNat_factorial_pow p k]
  push_cast [Nat.cast_sub hp.out.one_le, Nat.cast_sub (Nat.one_le_pow k p hp.out.pos)] at h
  rw [eq_div_iff (sub_pos.mpr (by exact_mod_cast hp.out.one_lt : (1 : ℝ) < p)).ne']
  linarith

/-- **Legendre's bound.** `v_p(n!) < n / (p - 1)` for `n ≠ 0`, since the base-`p` digit sum of
`n` is positive. -/
theorem multiplicity_factorial_lt_div (p : ℕ) [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    (multiplicity p n.factorial : ℝ) < n / ((p : ℝ) - 1) := by
  have h : (((p - 1) * multiplicity p n.factorial : ℕ) : ℝ) < n := by
    exact_mod_cast sub_one_mul_multiplicity_factorial_lt_of_ne_zero p hn
  push_cast [Nat.cast_sub hp.out.one_le] at h
  rw [lt_div_iff₀ (sub_pos.mpr (by exact_mod_cast hp.out.one_lt : (1 : ℝ) < p))]
  linarith

/-- **Legendre's bound**, non-strict form: `v_p(n!) ≤ n / (p - 1)` for every `n`. -/
theorem multiplicity_factorial_le_div (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (multiplicity p n.factorial : ℝ) ≤ n / ((p : ℝ) - 1) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · exact (multiplicity_factorial_lt_div p hn).le

open Nat in
/-- In `ℤ_p`, `n!` has the norm of `⌊n / pʰ⌋! p ^ (∑_{k = 1}^{h} ⌊n / pᵏ⌋)`: by Legendre's formula
both have valuation `v_p(n!)`. -/
theorem norm_factorial_eq_norm_factorial_div_mul_pow {p : ℕ} [hp : Fact p.Prime] (h n : ℕ) :
    ‖(n ! : ℤ_[p])‖ =
      ‖((n / p ^ h)! : ℤ_[p])‖ * ‖(p : ℤ_[p])‖ ^ ∑ k ∈ Finset.range h, n / p ^ (k + 1) := by
  have hv := padicValNat_factorial_eq_add_sum p n h
  generalize ∑ k ∈ Finset.range h, n / p ^ (k + 1) = s at hv ⊢
  simp [PadicInt.norm_def, Padic.norm_natCast_eq_zpow, factorial_ne_zero, hv, zpow_add₀,
    hp.out.ne_zero, mul_comm]

open Nat in
/-- In `ℤ_p`, `n!` divides `⌊n / pʰ⌋! p ^ (∑_{k = 1}^{h} ⌊n / pᵏ⌋)`: by Legendre's formula both
have valuation `v_p(n!)`. -/
theorem factorial_dvd_factorial_div_mul_pow {p : ℕ} [hp : Fact p.Prime] (h n : ℕ) :
    (n ! : ℤ_[p]) ∣
      ((n / p ^ h)! : ℤ_[p]) * (p : ℤ_[p]) ^ ∑ k ∈ Finset.range h, n / p ^ (k + 1) :=
  PadicInt.dvd_of_norm_le <| by
    rw [norm_mul, norm_pow]
    exact (norm_factorial_eq_norm_factorial_div_mul_pow h n).ge

end TauCeti

namespace Padic

open Nat

variable {p : ℕ} [Fact p.Prime]

/-- The norm of `n!` in `ℚ_[p]` is bounded below by `p ^ (-n / (p - 1))`, by Legendre's
formula. This gives the factorial denominator bound for the p-adic exponential. -/
theorem rpow_neg_div_le_norm_factorial (n : ℕ) :
    (p : ℝ) ^ (-((n : ℝ) / ((p : ℝ) - 1))) ≤ ‖(n ! : ℚ_[p])‖ := by
  rw [norm_natCast_eq_zpow (factorial_ne_zero _), ← Real.rpow_intCast]
  simp only [Int.cast_neg, Int.cast_natCast, Nat.padicValNat_def]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Fact.out : p.Prime).one_le)
    (neg_le_neg (TauCeti.multiplicity_factorial_le_div p n))

/-- The factorial of `p k` has `p`-adic norm `p ^ (-k) ‖k!‖`: by Legendre's formula, passing from
`k!` to `(p k)!` raises the valuation by `k`. -/
theorem norm_factorial_mul (k : ℕ) :
    ‖((p * k)! : ℚ_[p])‖ = (p : ℝ) ^ (-(k : ℤ)) * ‖(k ! : ℚ_[p])‖ := by
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [norm_natCast_eq_zpow (factorial_ne_zero _), norm_natCast_eq_zpow (factorial_ne_zero _),
    Nat.padicValNat_def, _root_.multiplicity_factorial_mul, ← zpow_add₀ hp]
  simp only [Nat.padicValNat_def]
  congr 1
  push_cast
  ring

/-- The factorial weights at a fixed division scale are submultiplicative under addition.
This controls Cauchy products of factorial-weighted moment sequences. -/
theorem norm_factorial_div_add_le (d i j : ℕ) :
    ‖(((i + j) / d)! : ℚ_[p])‖ ≤ ‖((i / d)! : ℚ_[p])‖ * ‖((j / d)! : ℚ_[p])‖ := by
  obtain ⟨k, hk⟩ := (Nat.factorial_mul_factorial_dvd_factorial_add (i / d) (j / d)).trans
    (Nat.factorial_dvd_factorial Nat.div_add_div_le_add_div)
  have hcast : (((i + j) / d)! : ℚ_[p]) = (i / d)! * (j / d)! * (k : ℚ_[p]) := by
    exact_mod_cast hk
  rw [hcast, norm_mul, norm_mul]
  exact mul_le_of_le_one_right (by positivity)
    (by simpa using norm_int_le_one (p := p) (k : ℤ))

end Padic

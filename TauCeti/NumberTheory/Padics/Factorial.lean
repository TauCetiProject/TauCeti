/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Factorial.Basic
import TauCeti.NumberTheory.Padics.AmiceRadius
import TauCeti.NumberTheory.Padics.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Factorials in p-adic fields

The integers `n!` converge to zero at every finite place, although none is zero. This provides
one sequence of rational parameters that simultaneously contracts every local unipotent
one-parameter subgroup. Divisibility by each fixed prime power suffices for the convergence.

Legendre's formula also bounds the `p`-adic norm of `n!` below by `p ^ (-n / (p - 1))` (and by
`p ^ (-(n - 1) / (p - 1))` for `n ≠ 0` in `TauCeti.amiceRadius_zero_pow_sub_one_le_norm_factorial`),
with equality along `n = p ^ k`. Transferring these estimates along `algebraMap ℚ_[p] K` yields
factorial and inverse-factorial norm bounds in any normed algebra or normed division algebra over
`ℚ_[p]`, including weighted estimates at the critical radius `p ^ (-1 / (p - 1))`.

## Main results

* `TauCeti.tendsto_padic_natCast_factorial`: the factorials tend to zero in `ℚ_[p]`.
* `TauCeti.padicValNat_factorial_eq_add_sum`: Legendre's formula truncated at level `h`,
  `v_p(n!) = v_p(⌊n / pʰ⌋!) + ∑_{k = 1}^{h} ⌊n / pᵏ⌋`.
* `TauCeti.sub_one_mul_padicValNat_factorial_pow`: Legendre's formula for `(pᵏ)!`,
  `(p - 1) v_p((pᵏ)!) = pᵏ - 1`.
* `TauCeti.norm_factorial_eq_norm_factorial_div_mul_pow`,
  `TauCeti.factorial_dvd_factorial_div_mul_pow`: its consequence that `n!` has the norm of, and
  divides, `⌊n / pʰ⌋! p ^ (∑_{k = 1}^{h} ⌊n / pᵏ⌋)` in `ℤ_[p]`.
* `Padic.norm_factorial_mul`: `‖(p k)!‖ = p ^ (-k) ‖k!‖` in `ℚ_[p]`, by Legendre's formula.
* `Padic.rpow_neg_div_le_norm_factorial`: `p ^ (-n / (p - 1)) ≤ ‖n!‖` in `ℚ_[p]`.
* `TauCeti.rpow_neg_div_le_norm_factorial`: Legendre's lower bound for `‖(n! : K)‖` in any
  seminormed `ℚ_[p]`-algebra with `‖1‖ = 1`.
* `TauCeti.norm_inv_factorial_le`, `TauCeti.norm_inv_factorial_le_rpow_sub_one_div`,
  `TauCeti.norm_inv_factorial_pow_prime`, `TauCeti.norm_inv_factorial_pow_prime_mul_rpow`,
  `TauCeti.le_norm_inv_factorial_pow_prime_mul_pow`,
  `TauCeti.norm_inv_factorial_mul_pow_le`, `TauCeti.norm_pow_mul_inv_factorial_le_sq`:
  inverse-factorial and critical-radius estimates in any normed division algebra over `ℚ_[p]`.
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
  have hp := (Fact.out : p.Prime)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [norm_natCast_eq_zpow (factorial_ne_zero _), ← Real.rpow_intCast]
  simp only [Int.cast_neg, Int.cast_natCast]
  refine Real.rpow_le_rpow_of_exponent_le hp1.le (neg_le_neg ?_)
  rw [le_div_iff₀ (sub_pos.mpr hp1)]
  have hleg : (p - 1) * padicValNat p n.factorial ≤ n := by
    rw [Nat.padicValNat_def, Nat.Prime.sub_one_mul_multiplicity_factorial hp]
    exact Nat.sub_le _ _
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  simpa only [Nat.cast_mul, hcast, mul_comm] using (Nat.cast_le (α := ℝ)).mpr hleg

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

namespace TauCeti

open scoped Nat

section NormedAlgebra

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [SeminormedRing K] [NormOneClass K]
  [NormedAlgebra ℚ_[p] K]

/-- Legendre's lower bound `p ^ (-n / (p - 1)) ≤ ‖n!‖` in any seminormed `ℚ_[p]`-algebra with
`‖(1 : K)‖ = 1`. -/
theorem rpow_neg_div_le_norm_factorial (n : ℕ) :
    (p : ℝ) ^ (-((n : ℝ) / ((p : ℝ) - 1))) ≤ ‖(n ! : K)‖ := by
  rw [TauCeti.norm_natCast_eq_norm_padic (p := p)]
  exact Padic.rpow_neg_div_le_norm_factorial n

end NormedAlgebra

section NormedDivisionRing

variable {p : ℕ} [hp : Fact p.Prime] {D : Type*} [NormedDivisionRing D] [NormedAlgebra ℚ_[p] D]

/-- Upper bound `‖(n!)⁻¹‖ ≤ p ^ (n / (p - 1))` in a normed division algebra over `ℚ_[p]`. -/
theorem norm_inv_factorial_le (n : ℕ) :
    ‖(n ! : D)⁻¹‖ ≤ (p : ℝ) ^ ((n : ℝ) / ((p : ℝ) - 1)) := by
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-((n : ℝ) / ((p : ℝ) - 1))) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.out.pos) _
  rw [norm_inv]
  refine (inv_anti₀ hpos (rpow_neg_div_le_norm_factorial (p := p) n)).trans_eq ?_
  rw [Real.rpow_neg (Nat.cast_nonneg p), inv_inv]

/-- Sharpened upper bound `‖(n!)⁻¹‖ ≤ p ^ ((n - 1) / (p - 1))` for `n ≠ 0` in a normed division
algebra over `ℚ_[p]`. -/
theorem norm_inv_factorial_le_rpow_sub_one_div {n : ℕ} (hn : n ≠ 0) :
    ‖(n ! : D)⁻¹‖ ≤ (p : ℝ) ^ (((n : ℝ) - 1) / ((p : ℝ) - 1)) := by
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-(((n : ℝ) - 1) / ((p : ℝ) - 1))) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.out.pos) _
  have hfac := amiceRadius_zero_pow_sub_one_le_norm_factorial (p := p) (L := D) hn
  rw [amiceRadius_pow, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn), Nat.cast_one, pow_zero,
    mul_one] at hfac
  rw [norm_inv]
  refine (inv_anti₀ hpos hfac).trans_eq ?_
  rw [Real.rpow_neg (Nat.cast_nonneg p), inv_inv]

/-- Exact norm of `((p ^ k)!)⁻¹` in any normed division algebra over `ℚ_[p]`: since `p ^ k` has
base-`p` digit sum `1`, `‖((p ^ k)!)⁻¹‖ = p ^ ((p ^ k - 1) / (p - 1))`. -/
theorem norm_inv_factorial_pow_prime (k : ℕ) :
    ‖(((p ^ k)! : ℕ) : D)⁻¹‖ = (p : ℝ) ^ ((((p ^ k : ℕ) : ℝ) - 1) / ((p : ℝ) - 1)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpow1 : 1 ≤ p ^ k := Nat.one_le_pow k p hp.out.pos
  have hdiv : (padicValNat p (p ^ k)! : ℝ) = (((p ^ k : ℕ) : ℝ) - 1) / ((p : ℝ) - 1) := by
    rw [eq_div_iff (sub_pos.mpr hp1).ne']
    have hcast : (((p - 1) * padicValNat p (p ^ k)! : ℕ) : ℝ) = ((p ^ k - 1 : ℕ) : ℝ) := by
      exact_mod_cast TauCeti.sub_one_mul_padicValNat_factorial_pow p k
    simpa [Nat.cast_sub hp.out.one_le, Nat.cast_sub hpow1, mul_comm] using hcast
  rw [norm_inv, TauCeti.norm_natCast_eq_norm_padic (p := p),
    Padic.norm_natCast_eq_zpow (Nat.factorial_ne_zero _)]
  simp [← Real.rpow_natCast, hdiv]

/-- At the critical radius `p ^ (-1 / (p - 1))`, the weighted inverse factorials along `n = p ^ k`
equal `p ^ (-1 / (p - 1))`. -/
theorem norm_inv_factorial_pow_prime_mul_rpow (k : ℕ) :
    ‖(((p ^ k)! : ℕ) : D)⁻¹‖ * ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ^ (p ^ k) =
      (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.out.pos
  have hsplit : (((p ^ k : ℕ) : ℝ) - 1) / ((p : ℝ) - 1) +
      -((p : ℝ) - 1)⁻¹ * ((p ^ k : ℕ) : ℝ) = -((p : ℝ) - 1)⁻¹ := by ring
  rw [norm_inv_factorial_pow_prime, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le,
    ← Real.rpow_add hp0, hsplit]

/-- Whenever `p ^ (-1 / (p - 1)) ≤ r`, the `r`-weighted inverse factorials along `n = p ^ k` stay
bounded below by `p ^ (-1 / (p - 1))`. -/
theorem le_norm_inv_factorial_pow_prime_mul_pow {r : ℝ}
    (hr : (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) ≤ r) (k : ℕ) :
    (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) ≤ ‖(((p ^ k)! : ℕ) : D)⁻¹‖ * r ^ (p ^ k) :=
  (norm_inv_factorial_pow_prime_mul_rpow (p := p) (D := D) k).symm.trans_le <|
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg p) _) hr _) (norm_nonneg _)

/-- On the closed critical radius `0 ≤ r ≤ p ^ (-1 / (p - 1))`, the weighted inverse factorials
satisfy `‖(n!)⁻¹‖ * r ^ n ≤ 1` for every `n`. -/
theorem norm_inv_factorial_mul_pow_le {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (n : ℕ) :
    ‖(n ! : D)⁻¹‖ * r ^ n ≤ 1 := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.out.pos
  calc
    ‖(n ! : D)⁻¹‖ * r ^ n
        ≤ (p : ℝ) ^ ((n : ℝ) / ((p : ℝ) - 1)) * ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ^ n :=
          mul_le_mul (norm_inv_factorial_le n) (pow_le_pow_left₀ hr0 hr n)
            (pow_nonneg hr0 n) (Real.rpow_nonneg hp0.le _)
    _ = (p : ℝ) ^ ((n : ℝ) / ((p : ℝ) - 1) + -((p : ℝ) - 1)⁻¹ * (n : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_add hp0]
    _ = 1 := by
          have hexp : (n : ℝ) / ((p : ℝ) - 1) + -((p : ℝ) - 1)⁻¹ * (n : ℝ) = 0 := by ring
          rw [hexp, Real.rpow_zero]

/-- For `n ≥ 2` and any `x : D` with `‖x‖ ≤ p ^ (-1 / (p - 1))`,
`‖x ^ n * (n!)⁻¹‖ ≤ ‖x‖ ^ 2 * p ^ (1 / (p - 1))`. -/
theorem norm_pow_mul_inv_factorial_le_sq {x : D}
    (hx : ‖x‖ ≤ (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) {n : ℕ} (hn : 2 ≤ n) :
    ‖x ^ n * (n ! : D)⁻¹‖ ≤ ‖x‖ ^ 2 * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := Nat.exists_eq_add_of_le' hn
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.out.pos
  have hpow_k : ‖x‖ ^ k * (p : ℝ) ^ ((k : ℝ) / ((p : ℝ) - 1)) ≤ 1 := by
    calc
      ‖x‖ ^ k * (p : ℝ) ^ ((k : ℝ) / ((p : ℝ) - 1))
          ≤ ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ^ k * (p : ℝ) ^ ((k : ℝ) / ((p : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg x) hx k)
              (Real.rpow_nonneg hp0.le _)
      _ = (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹ * (k : ℝ) + (k : ℝ) / ((p : ℝ) - 1)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_add hp0]
      _ = 1 := by
            have hexp : -((p : ℝ) - 1)⁻¹ * (k : ℝ) + (k : ℝ) / ((p : ℝ) - 1) = 0 := by ring
            rw [hexp, Real.rpow_zero]
  have hsplit : (((k + 2 : ℕ) : ℝ) - 1) / ((p : ℝ) - 1) =
      (k : ℝ) / ((p : ℝ) - 1) + ((p : ℝ) - 1)⁻¹ := by
    push_cast
    ring
  rw [norm_mul, norm_pow]
  calc
    ‖x‖ ^ (k + 2) * ‖((k + 2)! : D)⁻¹‖
        ≤ ‖x‖ ^ (k + 2) * (p : ℝ) ^ ((((k + 2 : ℕ) : ℝ) - 1) / ((p : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left
            (norm_inv_factorial_le_rpow_sub_one_div (p := p) (Nat.succ_ne_zero _)) (by positivity)
    _ = (‖x‖ ^ k * (p : ℝ) ^ ((k : ℝ) / ((p : ℝ) - 1))) *
          (‖x‖ ^ 2 * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹)) := by
          rw [pow_add, hsplit, Real.rpow_add hp0]
          ring
    _ ≤ 1 * (‖x‖ ^ 2 * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹)) :=
          mul_le_mul_of_nonneg_right hpow_k (by positivity)
    _ = ‖x‖ ^ 2 * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹) := one_mul _

end NormedDivisionRing

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Logarithmic growth bounds and complex order

An eventual bound `log (1 + ‖f s‖) ≤ C (1 + ‖s‖) ^ A` gives `OrderLE f A` for arbitrary
real `A` and `C`, without analyticity or continuity assumptions.

A bound by `exp (C (1+‖s‖) log (2+‖s‖))` gives `OrderLE f 1`.
This is the growth comparison used after estimating split Mellin integrals.

The bound is stable under the operations used to assemble completed L-functions: it transfers
from `F t` to `F s` when `‖t‖ ≤ 1 + ‖s‖` after multiplying the constant by `21`, and a finite
linear combination of functions with such bounds has one with the largest constant, times the
total mass of the coefficients. A power `n ^ (c s)` of a positive integer satisfies it with
constant `2 |c| log n`.

## Main results

* `TauCeti.orderLE_of_eventually_log_one_add_norm_le_mul_rpow`: a logarithmic power bound
  at infinity gives the corresponding order.
* `TauCeti.orderLE_one_of_norm_le_exp_mul_log`: the logarithmic-exponential norm bound gives
  order at most one.
* `TauCeti.norm_le_exp_mul_log_of_norm_le_one_add`: transfer to a comparable argument.
* `TauCeti.norm_comp_mul_add_le_exp_mul_log` and
  `TauCeti.exists_norm_comp_mul_add_le_exp_mul_log`: transfer across any affine substitution
  `s ↦ a * s + b` for functions valued in a type with a norm.
* `TauCeti.norm_sub_le_exp_mul_log`: logarithmic-exponential bound for linear factors `s - w`.
* `TauCeti.norm_natCast_cpow_ofReal_mul_le_exp_mul_log`: the bound for `n ^ (c s)`.
* `TauCeti.norm_sum_mul_le_mul_exp_mul_log`: the bound for a finite linear combination.

## References

The logarithmic-power criterion extracts the growth-to-order step used in
`Complex.Hadamard.summable_norm_inv_rpow_divisorZeroIndex₀_of_growth` in Matteo Cipollina's
[PrimeNumberTheoremAnd summability development](https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/fb80a640fb3f7ddc5b1c0ebd48494ad29cc83eb4/PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/HadamardFactorization/Summability.lean).
-/

public section

open Real Filter Asymptotics Bornology Topology

namespace TauCeti

/-- An eventual logarithmic power bound gives the corresponding complex order. The exponent
and coefficient may be arbitrary real numbers; no regularity assumption on `f` is needed.
This is a sufficient criterion for the fixed exponent. -/
theorem orderLE_of_eventually_log_one_add_norm_le_mul_rpow
    {f : ℂ → ℂ} {A C : ℝ}
    (hf : ∀ᶠ z in cobounded ℂ, log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ A) :
    OrderLE f A := by
  rw [orderLE_def]
  intro B hAB
  have hshift : (fun x : ℝ ↦ (1 + x) ^ A) =Θ[atTop] (fun x ↦ x ^ A) := by
    apply ((isLittleO_const_id_atTop (1 : ℝ)).right_isTheta_add.symm).rpow
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      exact add_nonneg zero_le_one hx
    · exact eventually_ge_atTop (0 : ℝ)
  have ho := (hshift.1.trans_isLittleO (isLittleO_rpow_rpow_atTop hAB)).const_mul_left C
  refine IsBigO.of_bound 1 ?_
  filter_upwards [hf, tendsto_norm_cobounded_atTop.eventually ho.eventuallyLE] with z hz hs
  have hsmall : |C * (1 + ‖z‖) ^ A| ≤ ‖z‖ ^ B := by
    simpa only [Function.comp_apply, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) B)] using hs
  have hlog : log (1 + ‖f z‖) ≤ ‖z‖ ^ B :=
    hz.trans ((le_abs_self _).trans hsmall)
  have hnorm : ‖f z‖ ≤ exp (‖z‖ ^ B) :=
    (le_add_of_nonneg_left zero_le_one).trans (Real.le_exp_of_log_le hlog)
  simpa only [Real.norm_eq_abs, Real.abs_exp, one_mul] using hnorm

/-- A global logarithmic-exponential norm bound implies order at most one. -/
theorem orderLE_one_of_norm_le_exp_mul_log {f : ℂ → ℂ} {C : ℝ}
    (hf : ∀ s, ‖f s‖ ≤ exp (C * (1 + ‖s‖) * log (2 + ‖s‖))) : OrderLE f 1 := by
  rw [orderLE_def]
  intro p hp
  have ho := (Real.isLittleO_add_one_mul_log_add_two_rpow hp).const_mul_left C
  apply IsBigO.of_bound 1
  filter_upwards [tendsto_norm_cobounded_atTop.eventually ho.eventuallyLE] with s hs
  simp only [Real.norm_eq_abs] at hs
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), one_mul]
  apply (hf s).trans
  apply exp_le_exp.mpr
  have hpow : 0 ≤ ‖s‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
  rw [abs_of_nonneg hpow] at hs
  calc
    C * (1 + ‖s‖) * log (2 + ‖s‖) ≤ |C * ((1 + ‖s‖) * log (2 + ‖s‖))| := by
      simpa only [mul_assoc] using le_abs_self (C * ((1 + ‖s‖) * log (2 + ‖s‖)))
    _ ≤ ‖s‖ ^ p := hs

/-- A logarithmic-exponential bound transfers to arguments `t` with `‖t‖ ≤ 1 + ‖s‖`, at the
cost of the factor `21` in the constant. -/
theorem norm_le_exp_mul_log_of_norm_le_one_add {F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ t, ‖F t‖ ≤ exp (C * (1 + ‖t‖) * log (2 + ‖t‖))) {s t : ℂ}
    (ht : ‖t‖ ≤ 1 + ‖s‖) :
    ‖F t‖ ≤ exp (21 * C * (1 + ‖s‖) * log (2 + ‖s‖)) := by
  have hscale := add_one_mul_log_add_two_le (norm_nonneg s) (norm_nonneg t) zero_le_one
    (by linarith)
  norm_num at hscale
  refine (hF t).trans (exp_le_exp.mpr ?_)
  have := mul_le_mul_of_nonneg_left hscale hC
  linarith

/-- Every linear factor `s - w` satisfies an explicit logarithmic-exponential norm bound. -/
theorem norm_sub_le_exp_mul_log (w s : ℂ) :
    ‖s - w‖ ≤ exp ((1 + 2 * ‖w‖) * (1 + ‖s‖) * log (2 + ‖s‖)) := by
  have hW := one_half_le_one_add_mul_log_two_add (norm_nonneg s)
  have h1 : 1 + ‖w‖ ≤ exp (2 * ‖w‖ * ((1 + ‖s‖) * log (2 + ‖s‖))) := by
    refine (by linarith [add_one_le_exp ‖w‖] : 1 + ‖w‖ ≤ exp ‖w‖).trans (exp_le_exp.mpr ?_)
    nlinarith [norm_nonneg w]
  calc
    ‖s - w‖ ≤ ‖s‖ + ‖w‖ := norm_sub_le _ _
    _ ≤ (1 + ‖w‖) * (1 + ‖s‖) := by nlinarith [norm_nonneg s, norm_nonneg w]
    _ ≤ exp (2 * ‖w‖ * ((1 + ‖s‖) * log (2 + ‖s‖))) *
          exp ((1 + ‖s‖) * log (2 + ‖s‖)) :=
        mul_le_mul h1 (one_add_le_exp_one_add_mul_log_two_add (norm_nonneg s))
          (by positivity) (exp_pos _).le
    _ = _ := by rw [← exp_add]; ring_nf

/-- A logarithmic-exponential bound on a function into a type with a norm transfers across any
affine substitution `s ↦ a * s + b`. -/
theorem norm_comp_mul_add_le_exp_mul_log {E : Type*} [Norm E] {F : ℂ → E} {C : ℝ}
    (hC : 0 ≤ C) (hF : ∀ z, ‖F z‖ ≤ exp (C * (1 + ‖z‖) * log (2 + ‖z‖))) (a b s : ℂ) :
    ‖F (a * s + b)‖ ≤
      exp ((‖a‖ + ‖b‖ + 2) * (2 * (‖a‖ + ‖b‖ + 2) + 1) * C * (1 + ‖s‖) * log (2 + ‖s‖)) := by
  have ht : ‖a * s + b‖ ≤ (‖a‖ + ‖b‖) * (1 + ‖s‖) := by
    calc ‖a * s + b‖ ≤ ‖a * s‖ + ‖b‖ := norm_add_le _ _
      _ = ‖a‖ * ‖s‖ + ‖b‖ := by rw [norm_mul]
      _ ≤ (‖a‖ + ‖b‖) * (1 + ‖s‖) := by nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg s]
  have hscale := add_one_mul_log_add_two_le (norm_nonneg s) (norm_nonneg (a * s + b))
    (by positivity : 0 ≤ ‖a‖ + ‖b‖) ht
  refine (hF (a * s + b)).trans (exp_le_exp.mpr ?_)
  have := mul_le_mul_of_nonneg_left hscale hC
  linarith

/-- Existential form of `norm_comp_mul_add_le_exp_mul_log` preserving positivity of the constant. -/
theorem exists_norm_comp_mul_add_le_exp_mul_log {E : Type*} [Norm E] {F : ℂ → E}
    (hF : ∃ C > 0, ∀ z, ‖F z‖ ≤ exp (C * (1 + ‖z‖) * log (2 + ‖z‖))) (a b : ℂ) :
    ∃ C' > 0, ∀ s, ‖F (a * s + b)‖ ≤ exp (C' * (1 + ‖s‖) * log (2 + ‖s‖)) := by
  obtain ⟨C, hC, hb⟩ := hF
  exact ⟨(‖a‖ + ‖b‖ + 2) * (2 * (‖a‖ + ‖b‖ + 2) + 1) * C, by positivity,
    norm_comp_mul_add_le_exp_mul_log hC.le hb a b⟩

/-- For a positive integer `n` and real `c`, the power `n ^ (c s)` is bounded by
`exp (2 |c| log n (1 + ‖s‖) log (2 + ‖s‖))`. -/
theorem norm_natCast_cpow_ofReal_mul_le_exp_mul_log {n : ℕ} (hn : n ≠ 0) (c : ℝ) (s : ℂ) :
    ‖(n : ℂ) ^ ((c : ℂ) * s)‖ ≤ exp (2 * |c| * log n * (1 + ‖s‖) * log (2 + ‖s‖)) := by
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.re_ofReal_mul,
    rpow_def_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
  refine exp_le_exp.mpr ?_
  have hL : 0 ≤ log n := log_natCast_nonneg n
  have hlog := one_half_le_log_two_add (norm_nonneg s)
  have hW : ‖s‖ ≤ 2 * ((1 + ‖s‖) * log (2 + ‖s‖)) := by nlinarith [norm_nonneg s]
  have hre : c * s.re ≤ |c| * ‖s‖ := (le_abs_self _).trans <| by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm s) (abs_nonneg c)
  calc
    log n * (c * s.re) ≤ log n * (|c| * (2 * ((1 + ‖s‖) * log (2 + ‖s‖)))) :=
      mul_le_mul_of_nonneg_left (hre.trans (mul_le_mul_of_nonneg_left hW (abs_nonneg c))) hL
    _ = _ := by ring

/-- A finite linear combination `∑ a i F i s` of values with logarithmic-exponential bounds of
constants at most `K` is bounded by the total mass `∑ ‖a i‖` times the bound with constant
`K`. -/
theorem norm_sum_mul_le_mul_exp_mul_log {ι : Type*} {t : Finset ι} {a : ι → ℂ}
    {F : ι → ℂ → ℂ} {C : ι → ℝ} {K : ℝ} {s : ℂ} (hCK : ∀ i ∈ t, C i ≤ K)
    (hF : ∀ i ∈ t, ‖F i s‖ ≤ exp (C i * (1 + ‖s‖) * log (2 + ‖s‖))) :
    ‖∑ i ∈ t, a i * F i s‖ ≤ (∑ i ∈ t, ‖a i‖) * exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) := by
  rw [Finset.sum_mul]
  refine norm_sum_le_of_le t fun i hi ↦ ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left ((hF i hi).trans
    (exp_mul_one_add_mul_log_two_add_le_of_le (hCK i hi) (norm_nonneg s))) (norm_nonneg _)

end TauCeti

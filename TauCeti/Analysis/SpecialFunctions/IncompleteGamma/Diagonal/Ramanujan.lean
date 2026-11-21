/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Basic

import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Diagonal.Basic
import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Diagonal.Regularized

/-!
# Ramanujan's remainder `θ(n)` and central exponential partial sums

Specializing the diagonal incomplete Gamma expansions of
`TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Diagonal.Basic` and
`TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Diagonal.Regularized` to positive integers
`a = n` via the Erlang formula `TauCeti.regularizedGamma_natCast` identifies
`n^{1 - n} e^n (γ(n, n) - Γ(n) / 2)` directly with Ramanujan's remainder `θ(n)` in
`∑_{k < n} n^k / k! + (n^n / n!) θ(n) = e^n / 2`. This yields Ramanujan's four-term asymptotic
expansion of `θ(n)` and the companion expansions and limits of the central exponential partial sums
`e^{-n} ∑_{k ≤ n} n^k / k!` and `e^{-n} ∑_{k < n} n^k / k!` (DLMF 8.11.14–8.11.17).

## Main definitions

* `TauCeti.ramanujanTheta`: Ramanujan's remainder function `θ(n)` determined for every `n : ℕ` by
  `∑_{k < n} n^k / k! + (n^n / n!) θ(n) = e^n / 2`.

## Main results

* `TauCeti.sum_range_add_ramanujanTheta`, `TauCeti.exp_neg_mul_sum_range_eq_sub_ramanujanTheta`,
  `TauCeti.exp_neg_mul_sum_range_succ_eq_add_sub_ramanujanTheta`,
  `TauCeti.regularizedGamma_diag_natCast_eq_add_ramanujanTheta`, and
  `TauCeti.ramanujanTheta_eq_mul_lowerIncompleteGamma_sub_half_Gamma`: Ramanujan's defining
  equation and incomplete-Gamma identities (DLMF 8.11.14–8.11.15).
* `TauCeti.isBigO_ramanujanTheta_sub` and `TauCeti.tendsto_ramanujanTheta_atTop`: Ramanujan's
  four-term expansion of `θ(n)` to `O(n^{-4})` and limit `θ(n) → 1 / 3` (DLMF 8.11.17).
* `TauCeti.isBigO_exp_neg_mul_sum_range_succ_sub`, `TauCeti.isBigO_exp_neg_mul_sum_range_sub`,
  `TauCeti.tendsto_exp_neg_mul_sum_range_atTop`, and
  `TauCeti.tendsto_exp_neg_mul_sum_range_succ_atTop`: four-term expansions to `O(n^{-9/2})` and
  limits `1 / 2` for the inclusive and strict central exponential partial sums (DLMF 8.11.16).

## References

* *NIST Digital Library of Mathematical Functions*, [§8.11(v)](https://dlmf.nist.gov/8.11.v),
  Eqs. 8.11.14–8.11.17.
* S. Ramanujan, *Question 294*, J. Indian Math. Soc. **3** (1911), 128; *Collected Papers of
  Srinivasa Ramanujan*, Cambridge Univ. Press (1927), 46–48 and 323–324.
* E. T. Copson, *An approximation connected with $e^{-x}$*, Proc. Edinburgh Math. Soc. (2) **3**
  (1933), 201–206.
* J. D. Buckholtz, *Concerning an approximation of Copson*, Proc. Amer. Math. Soc. **14** (1963),
  564–568.
-/

public section

noncomputable section

open Asymptotics Filter
open scoped Nat Topology

namespace TauCeti

/-- Ramanujan's remainder function `θ(n)` for the central partial sum of the exponential series
(Ramanujan 1911; DLMF 8.11.14–8.11.15), uniquely determined for every `n : ℕ` by
`∑ k < n, n ^ k / k! + (n ^ n / n!) * θ(n) = exp n / 2`. -/
def ramanujanTheta (n : ℕ) : ℝ :=
  (n ! : ℝ) / (n : ℝ) ^ n * (Real.exp n / 2 - ∑ k ∈ Finset.range n, (n : ℝ) ^ k / (k ! : ℝ))

/-- Explicit formula unfolding `TauCeti.ramanujanTheta`. -/
theorem ramanujanTheta_def (n : ℕ) :
    ramanujanTheta n = (n ! : ℝ) / (n : ℝ) ^ n *
      (Real.exp n / 2 - ∑ k ∈ Finset.range n, (n : ℝ) ^ k / (k ! : ℝ)) := by rfl

/-- At `n = 0`, `θ(0) = 1 / 2` under the convention `0 ^ 0 = 1`. -/
@[simp]
theorem ramanujanTheta_zero : ramanujanTheta 0 = 1 / 2 := by simp [ramanujanTheta_def]

/-- At `n = 1`, `θ(1) = e / 2 - 1`. -/
@[simp]
theorem ramanujanTheta_one : ramanujanTheta 1 = Real.exp 1 / 2 - 1 := by simp [ramanujanTheta_def]

/-- **DLMF 8.11.14 / Ramanujan's defining equation**: for every `n : ℕ`,
`∑_{k < n} n^k / k! + (n^n / n!) θ(n) = e^n / 2`. -/
theorem sum_range_add_ramanujanTheta (n : ℕ) :
    (∑ k ∈ Finset.range n, (n : ℝ) ^ k / (k ! : ℝ)) +
      (n : ℝ) ^ n / (n ! : ℝ) * ramanujanTheta n = Real.exp n / 2 := by
  rw [ramanujanTheta_def]
  have hf : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hp : (n : ℝ) ^ n ≠ 0 := by cases n <;> positivity
  field_simp [hf, hp]; ring

/-- Normalized form of DLMF 8.11.14 for the strict partial sum `k < n`, valid for every `n : ℕ`. -/
theorem exp_neg_mul_sum_range_eq_sub_ramanujanTheta (n : ℕ) :
    Real.exp (-(n : ℝ)) * (∑ k ∈ Finset.range n, (n : ℝ) ^ k / (k ! : ℝ)) =
      1 / 2 - Real.exp (-(n : ℝ)) * (n : ℝ) ^ n / (n ! : ℝ) * ramanujanTheta n := by
  have h := congr_arg (Real.exp (-(n : ℝ)) * ·) (sum_range_add_ramanujanTheta n)
  have he : Real.exp (-(n : ℝ)) * Real.exp (n : ℝ) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  linear_combination h + 1 / 2 * he

/-- Normalized form of DLMF 8.11.14 for the inclusive partial sum `k ≤ n`, valid for every
`n : ℕ`. -/
theorem exp_neg_mul_sum_range_succ_eq_add_sub_ramanujanTheta (n : ℕ) :
    Real.exp (-(n : ℝ)) * (∑ k ∈ Finset.range (n + 1), (n : ℝ) ^ k / (k ! : ℝ)) =
      1 / 2 + Real.exp (-(n : ℝ)) * (n : ℝ) ^ n / (n ! : ℝ) * (1 - ramanujanTheta n) := by
  rw [Finset.sum_range_succ, mul_add, exp_neg_mul_sum_range_eq_sub_ramanujanTheta]; ring

/-- **DLMF 8.11.15**: for `n ≠ 0`, `P(n, n) = 1 / 2 + e^{-n} (n^n / n!) θ(n)`.
The hypothesis `n ≠ 0` is necessary because `TauCeti.regularizedGamma 0 0 = 0`, whereas the
right-hand side evaluates to `1` at `n = 0`. -/
theorem regularizedGamma_diag_natCast_eq_add_ramanujanTheta {n : ℕ} (hn : n ≠ 0) :
    regularizedGamma n n =
      1 / 2 + Real.exp (-(n : ℝ)) * (n : ℝ) ^ n / (n ! : ℝ) * ramanujanTheta n := by
  rw [regularizedGamma_natCast hn (Nat.cast_nonneg n), exp_neg_mul_sum_range_eq_sub_ramanujanTheta]
  ring

/-- Exact incomplete-Gamma representation of `θ(n)` for `n ≠ 0`:
`θ(n) = n^{1 - n} e^n (γ(n, n) - Γ(n) / 2)`.
The hypothesis `n ≠ 0` is necessary because at `n = 0` the right-hand side is `0`, whereas
`θ(0) = 1 / 2`. -/
theorem ramanujanTheta_eq_mul_lowerIncompleteGamma_sub_half_Gamma {n : ℕ} (hn : n ≠ 0) :
    ramanujanTheta n =
      (n : ℝ) ^ (1 - (n : ℝ)) * Real.exp n * (lowerIncompleteGamma n n - Real.Gamma n / 2) := by
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hP := regularizedGamma_diag_natCast_eq_add_ramanujanTheta hn
  rw [regularizedGamma_eq_div] at hP
  have hG_pos : 0 < Real.Gamma n := Real.Gamma_pos_of_pos hn_pos
  have hfact : (n ! : ℝ) = (n : ℝ) * Real.Gamma n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [Nat.succ_eq_add_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Real.Gamma_nat_eq_factorial]
  have hrpow : (n : ℝ) ^ (1 - (n : ℝ)) * (n : ℝ) ^ n = (n : ℝ) := by
    rw [← Real.rpow_natCast (n : ℝ) n, ← Real.rpow_add hn_pos,
      show 1 - (n : ℝ) + (n : ℝ) = 1 by ring, Real.rpow_one]
  have hexp : Real.exp n * Real.exp (-(n : ℝ)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hsub : lowerIncompleteGamma n n - Real.Gamma n / 2 =
      Real.Gamma n * (Real.exp (-(n : ℝ)) * (n : ℝ) ^ n / (n ! : ℝ) * ramanujanTheta n) := by
    have hG_ne := hG_pos.ne'; field_simp [hG_ne] at hP ⊢; linarith
  symm
  calc (n : ℝ) ^ (1 - (n : ℝ)) * Real.exp n * (lowerIncompleteGamma n n - Real.Gamma n / 2)
      = ((n : ℝ) ^ (1 - (n : ℝ)) * (n : ℝ) ^ n) * (Real.exp n * Real.exp (-(n : ℝ))) *
          (Real.Gamma n / ((n : ℝ) * Real.Gamma n)) * ramanujanTheta n := by
            rw [hsub, hfact]; ring
    _ = ramanujanTheta n := by rw [hrpow, hexp, mul_one]; field_simp [hn_pos.ne', hG_pos.ne']

/-- **DLMF 8.11.17 (Ramanujan's asymptotic expansion)**: four-term asymptotic expansion of
`TauCeti.ramanujanTheta n` as `n → ∞`, with sharp remainder `O(n^{-4})`. -/
theorem isBigO_ramanujanTheta_sub :
    (fun n : ℕ => ramanujanTheta n -
      (1 / 3 + 4 / (135 * (n : ℝ)) - 8 / (2835 * (n : ℝ) ^ 2) - 16 / (8505 * (n : ℝ) ^ 3)))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ (-4 : ℝ) := by
  refine (isBigO_mul_lowerIncompleteGamma_diag_sub_half_Gamma.comp_tendsto
    tendsto_natCast_atTop_atTop).congr' ?_ .rfl
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Function.comp_apply,
    ramanujanTheta_eq_mul_lowerIncompleteGamma_sub_half_Gamma (Nat.one_le_iff_ne_zero.mp hn)]

/-- Ramanujan's limit `θ(n) → 1 / 3` as `n → ∞`. -/
theorem tendsto_ramanujanTheta_atTop :
    Tendsto ramanujanTheta atTop (𝓝 (1 / 3)) := by
  have herr : Tendsto (fun n : ℕ => ramanujanTheta n -
      (1 / 3 + 4 / (135 * (n : ℝ)) - 8 / (2835 * (n : ℝ) ^ 2) - 16 / (8505 * (n : ℝ) ^ 3)))
      atTop (𝓝 0) :=
    isBigO_ramanujanTheta_sub.trans_tendsto
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4)).comp tendsto_natCast_atTop_atTop)
  have hmain : Tendsto (fun n : ℕ =>
      1 / 3 + 4 / (135 * (n : ℝ)) - 8 / (2835 * (n : ℝ) ^ 2) - 16 / (8505 * (n : ℝ) ^ 3))
      atTop (𝓝 (1 / 3)) := by
    have h := ((by fun_prop : Continuous fun t : ℝ =>
        1 / 3 + 4 * t / 135 - 8 * t ^ 2 / 2835 - 16 * t ^ 3 / 8505).tendsto 0).comp
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    have h0 : (1 / 3 : ℝ) + 4 * 0 / 135 - 8 * 0 ^ 2 / 2835 - 16 * 0 ^ 3 / 8505 = 1 / 3 := by ring
    rw [h0] at h
    exact h.congr fun n => by
      simp only [Function.comp_apply, div_eq_mul_inv, mul_inv, inv_pow]; ring
  have hsum := (herr.add hmain).congr fun n => sub_add_cancel _ _
  rwa [zero_add] at hsum

/-- **DLMF 8.11.16**: four-term asymptotic expansion of the central exponential partial sum
`e^{-n} ∑_{k ≤ n} n^k / k!` as `n → ∞`, with remainder `O(n^{-9/2})`. -/
theorem isBigO_exp_neg_mul_sum_range_succ_sub :
    (fun n : ℕ => Real.exp (-(n : ℝ)) * (∑ k ∈ Finset.range (n + 1), (n : ℝ) ^ k / (k ! : ℝ)) -
      (1 / 2 + (Real.sqrt (2 * Real.pi * n))⁻¹ *
        (2 / 3 - 23 / (270 * (n : ℝ)) + 23 / (3024 * (n : ℝ) ^ 2) +
          259 / (77760 * (n : ℝ) ^ 3))))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ (-9 / 2 : ℝ) := by
  refine ((isBigO_regularizedGamma_add_one_diag_sub.comp_tendsto
    tendsto_natCast_atTop_atTop).neg_left).congr' ?_ .rfl
  filter_upwards [eventually_ge_atTop 1] with n _
  have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  simp only [Function.comp_apply, hcast,
    regularizedGamma_natCast (Nat.succ_ne_zero n) (Nat.cast_nonneg n)]; ring

/-- Four-term asymptotic expansion of the strict central exponential partial sum
`e^{-n} ∑_{k < n} n^k / k!` as `n → ∞`, with remainder `O(n^{-9/2})`. -/
theorem isBigO_exp_neg_mul_sum_range_sub :
    (fun n : ℕ => Real.exp (-(n : ℝ)) * (∑ k ∈ Finset.range n, (n : ℝ) ^ k / (k ! : ℝ)) -
      (1 / 2 - (Real.sqrt (2 * Real.pi * n))⁻¹ *
        (1 / 3 + 1 / (540 * (n : ℝ)) - 25 / (6048 * (n : ℝ) ^ 2) -
          101 / (155520 * (n : ℝ) ^ 3))))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ (-9 / 2 : ℝ) := by
  refine ((isBigO_regularizedGamma_diag_sub.comp_tendsto
    tendsto_natCast_atTop_atTop).neg_left).congr' ?_ .rfl
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Function.comp_apply,
    regularizedGamma_natCast (Nat.one_le_iff_ne_zero.mp hn) (Nat.cast_nonneg n)]; ring

/-- Limit `e^{-n} ∑_{k < n} n^k / k! → 1 / 2` as `n → ∞`. -/
theorem tendsto_exp_neg_mul_sum_range_atTop :
    Tendsto (fun n : ℕ => Real.exp (-(n : ℝ)) * ∑ k ∈ Finset.range n, (n : ℝ) ^ k / (k ! : ℝ))
      atTop (𝓝 (1 / 2)) := by
  refine (tendsto_sub_regularizedGamma_diag_atTop.comp tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Function.comp_apply,
    regularizedGamma_natCast (Nat.one_le_iff_ne_zero.mp hn) (Nat.cast_nonneg n)]; ring

/-- Limit `e^{-n} ∑_{k ≤ n} n^k / k! → 1 / 2` as `n → ∞`. -/
theorem tendsto_exp_neg_mul_sum_range_succ_atTop :
    Tendsto
      (fun n : ℕ => Real.exp (-(n : ℝ)) * ∑ k ∈ Finset.range (n + 1), (n : ℝ) ^ k / (k ! : ℝ))
      atTop (𝓝 (1 / 2)) := by
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub
    tendsto_regularizedGamma_add_one_diag_atTop).comp tendsto_natCast_atTop_atTop
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n _
  have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  simp only [Function.comp_apply, hcast,
    regularizedGamma_natCast (Nat.succ_ne_zero n) (Nat.cast_nonneg n)]; ring

end TauCeti

end

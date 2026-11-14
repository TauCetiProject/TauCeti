/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import TauCeti.RingTheory.PowerSeries.Binomial

import TauCeti.RingTheory.PowerSeries.Derivative
import TauCeti.RingTheory.PowerSeries.Trunc

/-!
# Formal reversion series and rational coefficients for Airy zero expansions

In the oscillatory regime on the negative real axis, the modulus-and-phase representation of the
Airy functions `Ai(-x)` and `Bi(-x)` (DLMF §9.8(ii)) expands the squared moduli
`M(x) ^ 2 = Ai(-x) ^ 2 + Bi(-x) ^ 2` and `N(x) ^ 2 = Ai'(-x) ^ 2 + Bi'(-x) ^ 2`, together with the
phases `θ(x)` and `φ(x)`, in inverse powers of `(2 / 3) x ^ (3 / 2)` with rational coefficients
`a_k`, `b_k`, `c_k`, `d_k` (DLMF 9.8.19–9.8.23).

Because the Wronskian identity `W{Ai, Bi} = 1 / π` expresses the phase derivatives as reciprocal
squared moduli (DLMF 9.8.14), the generating series of `c_k` and `d_k` are determined from the
reciprocal generating series of `a_k` and `b_k` by the formal first-order differential equations

* `airyModulusSqSeries * (airyPhaseSeries - 2 • (X * d⁄dX airyPhaseSeries)) = 1`,
* `airyDerivModulusSqSeries * (airyDerivPhaseSeries - 2 • (X * d⁄dX airyDerivPhaseSeries)) = 1`.

Reverting the resulting phase expansions at the zeros of `Ai`, `Bi`, `Ai'`, and `Bi'`
(DLMF §9.9(iv), 9.9.6–9.9.21) produces four formal power series `T`, `U`, `V`, `W ∈ ℚ⟦X⟧` in the
variable `X = t ^ (-2)` with constant term `1`:

* `airyZeroSeriesT` solves `T ^ (3 / 2) * (evalNegHom airyPhaseSeries)(X * T ^ (-3)) = 1`,
* `airyZeroSeriesU` solves `U ^ (3 / 2) * (evalNegHom airyDerivPhaseSeries)(X * U ^ (-3)) = 1`,
* `airyZeroSeriesV = T ^ (1 / 4) * ((evalNegHom airyModulusSqSeries)(X * T ^ (-3))) ^ (-1 / 2)`
  simplifies by the Wronskian differential identity to `(T - 3 • (X * d⁄dX T)) ^ (-1 / 2)`,
* `airyZeroSeriesW =
    U ^ (-1 / 4) * ((evalNegHom airyDerivModulusSqSeries)(X * U ^ (-3))) ^ (-1 / 2)`
  simplifies to `(U * (U - 3 • (X * d⁄dX U))) ^ (-1 / 2)`.

Their rational coefficient sequences `airyZeroCoeffT`, `airyZeroCoeffU`, `airyZeroCoeffV`, and
`airyZeroCoeffW` govern the asymptotic expansions of the real zeros `a_k`, `b_k`, `a'_k`, `b'_k`,
the complex zeros `β_k`, `β'_k` of `Bi` and `Bi'`, and the values/derivatives at those zeros
(DLMF 9.9.6–9.9.17). We verify all printed rational values in DLMF 9.8.20–9.8.23 and 9.9.18–9.9.21.

## Main definitions

* `TauCeti.airyModulusSqCoeff`, `TauCeti.airyDerivModulusSqCoeff`: the rational coefficients `a_k`
  and `b_k` of the squared-modulus expansions of `M ^ 2` and `N ^ 2` (DLMF 9.8.20–9.8.21).
* `TauCeti.airyPhaseCoeff`, `TauCeti.airyDerivPhaseCoeff`: the rational coefficients `c_k` and
  `d_k` of the phase expansions of `θ` and `φ` (DLMF 9.8.22–9.8.23).
* `TauCeti.airyModulusSqSeries`, `TauCeti.airyDerivModulusSqSeries`, `TauCeti.airyPhaseSeries`,
  `TauCeti.airyDerivPhaseSeries`: their formal generating series in `ℚ⟦X⟧`.
* `TauCeti.airyZeroSeriesT`, `TauCeti.airyZeroSeriesU`, `TauCeti.airyZeroSeriesV`,
  `TauCeti.airyZeroSeriesW`: the four formal reversion series in `ℚ⟦X⟧` for Airy zero expansions.
* `TauCeti.airyZeroCoeffT`, `TauCeti.airyZeroCoeffU`, `TauCeti.airyZeroCoeffV`,
  `TauCeti.airyZeroCoeffW`: the rational coefficient sequences `T_n`, `U_n`, `V_n`, `W_n`
  (DLMF 9.9.18–9.9.21).

## Main results

* `TauCeti.airyModulusSqSeries_mul_phase_deriv`,
  `TauCeti.airyDerivModulusSqSeries_mul_phase_deriv`: the formal Wronskian differential equations
  linking the modulus and phase series.
* `TauCeti.airyZeroSeriesT_reversion`, `TauCeti.eq_airyZeroSeriesT_iff`,
  `TauCeti.airyZeroSeriesU_reversion`, `TauCeti.eq_airyZeroSeriesU_iff`: the characteristic
  fractional-power reversion equations and uniqueness of `T` and `U` (and their `ℚ`-algebra maps).
* `TauCeti.airyZeroSeriesV_eq_binomialPow_deriv`, `TauCeti.airyZeroSeriesV_sq_mul`,
  `TauCeti.airyZeroSeriesW_eq_binomialPow_deriv`, `TauCeti.airyZeroSeriesW_sq_mul`: closed
  differential formulas for `V` and `W` in terms of `T` and `U`.
* `TauCeti.airyZeroCoeffT_one` .. `TauCeti.airyZeroCoeffW_five`: exact rational values of
  `T_1..T_5`, `U_1..U_5`, `V_1..V_5`, `W_1..W_5` matching DLMF 9.9.18–9.9.21.

## References

* NIST Digital Library of Mathematical Functions, §§9.8(ii), 9.9(iv),
  <https://dlmf.nist.gov/9.8>, <https://dlmf.nist.gov/9.9>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974, Chapter 11, §8.
-/

public section

open PowerSeries
open scoped Nat

namespace TauCeti

/-! ## Modulus-squared rational coefficients (DLMF 9.8.20–9.8.21) -/

/-- The `k`-th rational coefficient `a_k = (∏_{j < 3k} (2j + 1)) / (k! * 96 ^ k)` of the asymptotic
expansion of `π (-x) ^ (1 / 2) M(x) ^ 2` as `x → -∞` (DLMF 9.8.20). -/
def airyModulusSqCoeff (k : ℕ) : ℚ :=
  (∏ j ∈ Finset.range (3 * k), (2 * (j : ℚ) + 1)) / ((k ! : ℚ) * 96 ^ k)

/-- Explicit product formula for `airyModulusSqCoeff`. -/
theorem airyModulusSqCoeff_def (k : ℕ) :
    airyModulusSqCoeff k =
      (∏ j ∈ Finset.range (3 * k), (2 * (j : ℚ) + 1)) / ((k ! : ℚ) * 96 ^ k) :=
  (rfl)

/-- The leading squared-modulus coefficient is `a_0 = 1`. -/
@[simp]
theorem airyModulusSqCoeff_zero : airyModulusSqCoeff 0 = 1 := by
  simp [airyModulusSqCoeff]

/-- Multiplicative recurrence for `airyModulusSqCoeff`:
`a_{k+1} = (6k + 1)(6k + 3)(6k + 5) / (96 (k + 1)) * a_k`. -/
theorem airyModulusSqCoeff_succ (k : ℕ) :
    airyModulusSqCoeff (k + 1) =
      (6 * (k : ℚ) + 1) * (6 * (k : ℚ) + 3) * (6 * (k : ℚ) + 5) /
        (96 * ((k : ℚ) + 1)) * airyModulusSqCoeff k := by
  rw [airyModulusSqCoeff_def, airyModulusSqCoeff_def,
    show 3 * (k + 1) = 3 * k + 1 + 1 + 1 by omega,
    Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Nat.factorial_succ, pow_succ]
  push_cast
  field_simp
  ring

/-- Every coefficient `airyModulusSqCoeff k` is strictly positive. -/
theorem airyModulusSqCoeff_pos (k : ℕ) : 0 < airyModulusSqCoeff k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [airyModulusSqCoeff_succ]
    refine mul_pos (div_pos ?_ ?_) ih <;> positivity

/-- DLMF 9.8.20: `a_1 = 5 / 32`. -/
theorem airyModulusSqCoeff_one : airyModulusSqCoeff 1 = 5 / 32 := by
  rw [airyModulusSqCoeff_succ, airyModulusSqCoeff_zero]
  norm_num

/-- DLMF 9.8.20: `a_2 = 1155 / 2048`. -/
theorem airyModulusSqCoeff_two : airyModulusSqCoeff 2 = 1155 / 2048 := by
  rw [airyModulusSqCoeff_succ, airyModulusSqCoeff_one]
  norm_num

/-- The `k`-th rational coefficient `b_k = ((1 + 6k) / (1 - 6k)) a_k` of the asymptotic expansion
of `π (-x) ^ (-1 / 2) N(x) ^ 2` as `x → -∞` (DLMF 9.8.21). -/
def airyDerivModulusSqCoeff (k : ℕ) : ℚ :=
  (1 + 6 * (k : ℚ)) / (1 - 6 * (k : ℚ)) * airyModulusSqCoeff k

/-- Explicit formula for `airyDerivModulusSqCoeff` in terms of `airyModulusSqCoeff`. -/
theorem airyDerivModulusSqCoeff_def (k : ℕ) :
    airyDerivModulusSqCoeff k =
      (1 + 6 * (k : ℚ)) / (1 - 6 * (k : ℚ)) * airyModulusSqCoeff k :=
  (rfl)

/-- The leading derivative squared-modulus coefficient is `b_0 = 1`. -/
@[simp]
theorem airyDerivModulusSqCoeff_zero : airyDerivModulusSqCoeff 0 = 1 := by
  simp [airyDerivModulusSqCoeff]

/-- For `k ≥ 1`, the derivative squared-modulus coefficient `b_k` is strictly negative. -/
theorem airyDerivModulusSqCoeff_neg_of_pos {k : ℕ} (hk : 0 < k) :
    airyDerivModulusSqCoeff k < 0 := by
  rw [airyDerivModulusSqCoeff_def]
  have hk' : (1 : ℚ) ≤ k := by exact_mod_cast hk
  exact mul_neg_of_neg_of_pos
    (div_neg_of_pos_of_neg (by linarith) (by linarith)) (airyModulusSqCoeff_pos k)

/-- DLMF 9.8.21: `b_1 = -7 / 32`. -/
theorem airyDerivModulusSqCoeff_one : airyDerivModulusSqCoeff 1 = -7 / 32 := by
  rw [airyDerivModulusSqCoeff_def, airyModulusSqCoeff_one]
  norm_num

/-- DLMF 9.8.21: `b_2 = -1365 / 2048`. -/
theorem airyDerivModulusSqCoeff_two : airyDerivModulusSqCoeff 2 = -1365 / 2048 := by
  rw [airyDerivModulusSqCoeff_def, airyModulusSqCoeff_two]
  norm_num

noncomputable section

/-! ## Modulus and phase generating series and Wronskian differential identities -/

/-- Formal generating series `∑_{k ≥ 0} a_k X ^ k ∈ ℚ⟦X⟧` of `airyModulusSqCoeff`. -/
def airyModulusSqSeries : ℚ⟦X⟧ :=
  PowerSeries.mk airyModulusSqCoeff

/-- Defining equation for `airyModulusSqSeries`. -/
theorem airyModulusSqSeries_def : airyModulusSqSeries = PowerSeries.mk airyModulusSqCoeff :=
  (rfl)

/-- The `k`-th coefficient of `airyModulusSqSeries` is `airyModulusSqCoeff k`. -/
@[simp]
theorem coeff_airyModulusSqSeries (k : ℕ) :
    coeff k airyModulusSqSeries = airyModulusSqCoeff k :=
  coeff_mk k airyModulusSqCoeff

/-- `airyModulusSqSeries` has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_airyModulusSqSeries : constantCoeff airyModulusSqSeries = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_airyModulusSqSeries, airyModulusSqCoeff_zero]

/-- Formal generating series `∑_{k ≥ 0} b_k X ^ k ∈ ℚ⟦X⟧` of `airyDerivModulusSqCoeff`. -/
def airyDerivModulusSqSeries : ℚ⟦X⟧ :=
  PowerSeries.mk airyDerivModulusSqCoeff

/-- Defining equation for `airyDerivModulusSqSeries`. -/
theorem airyDerivModulusSqSeries_def :
    airyDerivModulusSqSeries = PowerSeries.mk airyDerivModulusSqCoeff :=
  (rfl)

/-- The `k`-th coefficient of `airyDerivModulusSqSeries` is `airyDerivModulusSqCoeff k`. -/
@[simp]
theorem coeff_airyDerivModulusSqSeries (k : ℕ) :
    coeff k airyDerivModulusSqSeries = airyDerivModulusSqCoeff k :=
  coeff_mk k airyDerivModulusSqCoeff

/-- `airyDerivModulusSqSeries` has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_airyDerivModulusSqSeries : constantCoeff airyDerivModulusSqSeries = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_airyDerivModulusSqSeries,
    airyDerivModulusSqCoeff_zero]

/-- The `k`-th rational coefficient `c_k` of the phase expansion of `θ(x)` as `x → -∞`
(DLMF 9.8.15, 9.8.22), obtained by dividing the `k`-th coefficient of `airyModulusSqSeries⁻¹` by
`1 - 2k`. -/
def airyPhaseCoeff (k : ℕ) : ℚ :=
  coeff k (invOfUnit airyModulusSqSeries 1) / (1 - 2 * (k : ℚ))

/-- Explicit formula for `airyPhaseCoeff`. -/
theorem airyPhaseCoeff_def (k : ℕ) :
    airyPhaseCoeff k = coeff k (invOfUnit airyModulusSqSeries 1) / (1 - 2 * (k : ℚ)) :=
  (rfl)

/-- The leading phase coefficient is `c_0 = 1`. -/
@[simp]
theorem airyPhaseCoeff_zero : airyPhaseCoeff 0 = 1 := by
  rw [airyPhaseCoeff_def, coeff_zero_eq_constantCoeff_apply, constantCoeff_invOfUnit]
  norm_num

/-- The `k`-th rational coefficient `d_k` of the derivative-phase expansion of `φ(x)` as `x → -∞`
(DLMF 9.8.16, 9.8.23), obtained by dividing the `k`-th coefficient of
`airyDerivModulusSqSeries⁻¹` by `1 - 2k`. -/
def airyDerivPhaseCoeff (k : ℕ) : ℚ :=
  coeff k (invOfUnit airyDerivModulusSqSeries 1) / (1 - 2 * (k : ℚ))

/-- Explicit formula for `airyDerivPhaseCoeff`. -/
theorem airyDerivPhaseCoeff_def (k : ℕ) :
    airyDerivPhaseCoeff k = coeff k (invOfUnit airyDerivModulusSqSeries 1) / (1 - 2 * (k : ℚ)) :=
  (rfl)

/-- The leading derivative-phase coefficient is `d_0 = 1`. -/
@[simp]
theorem airyDerivPhaseCoeff_zero : airyDerivPhaseCoeff 0 = 1 := by
  rw [airyDerivPhaseCoeff_def, coeff_zero_eq_constantCoeff_apply, constantCoeff_invOfUnit]
  norm_num

/-- Formal generating series `∑_{k ≥ 0} c_k X ^ k ∈ ℚ⟦X⟧` of `airyPhaseCoeff`. -/
def airyPhaseSeries : ℚ⟦X⟧ :=
  PowerSeries.mk airyPhaseCoeff

/-- Defining equation for `airyPhaseSeries`. -/
theorem airyPhaseSeries_def : airyPhaseSeries = PowerSeries.mk airyPhaseCoeff :=
  (rfl)

/-- The `k`-th coefficient of `airyPhaseSeries` is `airyPhaseCoeff k`. -/
@[simp]
theorem coeff_airyPhaseSeries (k : ℕ) : coeff k airyPhaseSeries = airyPhaseCoeff k :=
  coeff_mk k airyPhaseCoeff

/-- `airyPhaseSeries` has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_airyPhaseSeries : constantCoeff airyPhaseSeries = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_airyPhaseSeries, airyPhaseCoeff_zero]

/-- Formal generating series `∑_{k ≥ 0} d_k X ^ k ∈ ℚ⟦X⟧` of `airyDerivPhaseCoeff`. -/
def airyDerivPhaseSeries : ℚ⟦X⟧ :=
  PowerSeries.mk airyDerivPhaseCoeff

/-- Defining equation for `airyDerivPhaseSeries`. -/
theorem airyDerivPhaseSeries_def : airyDerivPhaseSeries = PowerSeries.mk airyDerivPhaseCoeff :=
  (rfl)

/-- The `k`-th coefficient of `airyDerivPhaseSeries` is `airyDerivPhaseCoeff k`. -/
@[simp]
theorem coeff_airyDerivPhaseSeries (k : ℕ) :
    coeff k airyDerivPhaseSeries = airyDerivPhaseCoeff k :=
  coeff_mk k airyDerivPhaseCoeff

/-- `airyDerivPhaseSeries` has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_airyDerivPhaseSeries : constantCoeff airyDerivPhaseSeries = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_airyDerivPhaseSeries, airyDerivPhaseCoeff_zero]

/-- Applying `1 - 2 X d⁄dX` to `airyPhaseSeries` recovers the formal inverse of
`airyModulusSqSeries`. -/
theorem airyPhaseSeries_sub_two_X_mul_deriv :
    airyPhaseSeries - (2 : ℚ) • (X * d⁄dX airyPhaseSeries) =
      invOfUnit airyModulusSqSeries 1 := by
  ext k
  have hne : (1 - 2 * (k : ℚ)) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) - 2 * k ≠ 0 by omega)
  have hcd : coeff k (X * d⁄dX airyPhaseSeries) = (k : ℚ) * coeff k airyPhaseSeries := by
    simpa using coeff_X_pow_mul_iterate_derivative airyPhaseSeries 1 k
  rw [map_sub, coeff_smul, hcd, coeff_airyPhaseSeries, airyPhaseCoeff_def,
    smul_eq_mul, show coeff k (invOfUnit airyModulusSqSeries 1) / (1 - 2 * (k : ℚ)) -
      2 * ((k : ℚ) * (coeff k (invOfUnit airyModulusSqSeries 1) / (1 - 2 * (k : ℚ)))) =
      (1 - 2 * (k : ℚ)) * (coeff k (invOfUnit airyModulusSqSeries 1) / (1 - 2 * (k : ℚ))) by ring,
    mul_div_cancel₀ _ hne]

/-- **Formal Wronskian differential equation for `airyPhaseSeries`** (from DLMF 9.8.14–9.8.15):
`airyModulusSqSeries * (airyPhaseSeries - 2 • (X * d⁄dX airyPhaseSeries)) = 1`. -/
theorem airyModulusSqSeries_mul_phase_deriv :
    airyModulusSqSeries * (airyPhaseSeries - (2 : ℚ) • (X * d⁄dX airyPhaseSeries)) = 1 := by
  rw [airyPhaseSeries_sub_two_X_mul_deriv]
  exact mul_invOfUnit airyModulusSqSeries 1 constantCoeff_airyModulusSqSeries

/-- Applying `1 - 2 X d⁄dX` to `airyDerivPhaseSeries` recovers the formal inverse of
`airyDerivModulusSqSeries`. -/
theorem airyDerivPhaseSeries_sub_two_X_mul_deriv :
    airyDerivPhaseSeries - (2 : ℚ) • (X * d⁄dX airyDerivPhaseSeries) =
      invOfUnit airyDerivModulusSqSeries 1 := by
  ext k
  have hne : (1 - 2 * (k : ℚ)) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) - 2 * k ≠ 0 by omega)
  have hcd : coeff k (X * d⁄dX airyDerivPhaseSeries) = (k : ℚ) * coeff k airyDerivPhaseSeries := by
    simpa using coeff_X_pow_mul_iterate_derivative airyDerivPhaseSeries 1 k
  rw [map_sub, coeff_smul, hcd, coeff_airyDerivPhaseSeries,
    airyDerivPhaseCoeff_def, smul_eq_mul,
    show coeff k (invOfUnit airyDerivModulusSqSeries 1) / (1 - 2 * (k : ℚ)) -
      2 * ((k : ℚ) * (coeff k (invOfUnit airyDerivModulusSqSeries 1) / (1 - 2 * (k : ℚ)))) =
      (1 - 2 * (k : ℚ)) *
        (coeff k (invOfUnit airyDerivModulusSqSeries 1) / (1 - 2 * (k : ℚ))) by ring,
    mul_div_cancel₀ _ hne]

/-- **Formal Wronskian differential equation for `airyDerivPhaseSeries`** (from DLMF 9.8.14,
9.8.16):
`airyDerivModulusSqSeries * (airyDerivPhaseSeries - 2 • (X * d⁄dX airyDerivPhaseSeries)) = 1`. -/
theorem airyDerivModulusSqSeries_mul_phase_deriv :
    airyDerivModulusSqSeries *
      (airyDerivPhaseSeries - (2 : ℚ) • (X * d⁄dX airyDerivPhaseSeries)) = 1 := by
  rw [airyDerivPhaseSeries_sub_two_X_mul_deriv]
  exact mul_invOfUnit airyDerivModulusSqSeries 1 constantCoeff_airyDerivModulusSqSeries

/-! ## Formal reversion series `T`, `U`, `V`, `W` for Airy zeros (DLMF 9.9.6–9.9.21) -/

/-- The formal reversion series `T(X) = ∑_{n ≥ 0} T_n X ^ n ∈ ℚ⟦X⟧` in `X = t ^ (-2)` governing
the asymptotic expansion of the zeros `a_k`, `b_k`, and `β_k` of `Ai` and `Bi` (DLMF 9.9.6, 9.9.10,
9.9.14, 9.9.18). It is the unique power series with constant coefficient `1` solving
`T ^ (3 / 2) * (evalNegHom airyPhaseSeries)(X * T ^ (-3)) = 1`. -/
def airyZeroSeriesT : ℚ⟦X⟧ :=
  (evalNegHom airyPhaseSeries).binomialReversion
    (Units.mk0 (3 / 2 : ℚ) (by norm_num)) (Units.mk0 (3 : ℚ) (by norm_num))

/-- Defining equation for `airyZeroSeriesT`. -/
theorem airyZeroSeriesT_def :
    airyZeroSeriesT =
      (evalNegHom airyPhaseSeries).binomialReversion
        (Units.mk0 (3 / 2 : ℚ) (by norm_num)) (Units.mk0 (3 : ℚ) (by norm_num)) :=
  (rfl)

/-- `airyZeroSeriesT` has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_airyZeroSeriesT : constantCoeff airyZeroSeriesT = 1 :=
  constantCoeff_binomialReversion _ _ _

/-- The formal reversion series `U(X) = ∑_{n ≥ 0} U_n X ^ n ∈ ℚ⟦X⟧` in `X = t ^ (-2)` governing
the asymptotic expansion of the derivative zeros `a'_k`, `b'_k`, and `β'_k` of `Ai'` and `Bi'`
(DLMF 9.9.8, 9.9.12, 9.9.16, 9.9.19). It is the unique power series with constant coefficient `1`
solving `U ^ (3 / 2) * (evalNegHom airyDerivPhaseSeries)(X * U ^ (-3)) = 1`. -/
def airyZeroSeriesU : ℚ⟦X⟧ :=
  (evalNegHom airyDerivPhaseSeries).binomialReversion
    (Units.mk0 (3 / 2 : ℚ) (by norm_num)) (Units.mk0 (3 : ℚ) (by norm_num))

/-- Defining equation for `airyZeroSeriesU`. -/
theorem airyZeroSeriesU_def :
    airyZeroSeriesU =
      (evalNegHom airyDerivPhaseSeries).binomialReversion
        (Units.mk0 (3 / 2 : ℚ) (by norm_num)) (Units.mk0 (3 : ℚ) (by norm_num)) :=
  (rfl)

/-- `airyZeroSeriesU` has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_airyZeroSeriesU : constantCoeff airyZeroSeriesU = 1 :=
  constantCoeff_binomialReversion _ _ _

/-- The formal series `V(X) = ∑_{n ≥ 0} V_n X ^ n ∈ ℚ⟦X⟧` in `X = t ^ (-2)` governing the
asymptotic expansion of `Ai'(a_k)`, `Bi'(b_k)`, and `Bi'(β_k)` (DLMF 9.9.7, 9.9.11, 9.9.15,
9.9.20): `T ^ (1 / 4) * ((evalNegHom airyModulusSqSeries)(X * T ^ (-3))) ^ (-1 / 2)`. -/
def airyZeroSeriesV : ℚ⟦X⟧ :=
  airyZeroSeriesT.binomialPow (1 / 4 : ℚ) *
    binomialPow
      ((evalNegHom airyModulusSqSeries).subst (X * airyZeroSeriesT.binomialPow (-3 : ℚ)))
      (-1 / 2 : ℚ)

/-- Defining equation for `airyZeroSeriesV`. -/
theorem airyZeroSeriesV_def :
    airyZeroSeriesV =
      airyZeroSeriesT.binomialPow (1 / 4 : ℚ) *
        binomialPow
          ((evalNegHom airyModulusSqSeries).subst (X * airyZeroSeriesT.binomialPow (-3 : ℚ)))
          (-1 / 2 : ℚ) :=
  (rfl)

/-- `airyZeroSeriesV` has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_airyZeroSeriesV : constantCoeff airyZeroSeriesV = 1 := by
  have hsub0 : constantCoeff
      ((evalNegHom airyModulusSqSeries).subst (X * airyZeroSeriesT.binomialPow (-3 : ℚ)) : ℚ⟦X⟧) =
        1 := by
    rw [constantCoeff_eq, constantCoeff_subst_of_constantCoeff_zero (by simp [← constantCoeff_eq]),
      ← coeff_zero_eq_constantCoeff_apply, evalNegHom, coeff_rescale]
    simp
  rw [airyZeroSeriesV_def, map_mul, constantCoeff_binomialPow constantCoeff_airyZeroSeriesT,
    constantCoeff_binomialPow hsub0, one_mul]

/-- The formal series `W(X) = ∑_{n ≥ 0} W_n X ^ n ∈ ℚ⟦X⟧` in `X = t ^ (-2)` governing the
asymptotic expansion of `Ai(a'_k)`, `Bi(b'_k)`, and `Bi(β'_k)` (DLMF 9.9.9, 9.9.13, 9.9.17,
9.9.21): `U ^ (-1 / 4) * ((evalNegHom airyDerivModulusSqSeries)(X * U ^ (-3))) ^ (-1 / 2)`. -/
def airyZeroSeriesW : ℚ⟦X⟧ :=
  airyZeroSeriesU.binomialPow (-1 / 4 : ℚ) *
    binomialPow
      ((evalNegHom airyDerivModulusSqSeries).subst (X * airyZeroSeriesU.binomialPow (-3 : ℚ)))
      (-1 / 2 : ℚ)

/-- Defining equation for `airyZeroSeriesW`. -/
theorem airyZeroSeriesW_def :
    airyZeroSeriesW =
      airyZeroSeriesU.binomialPow (-1 / 4 : ℚ) *
        binomialPow
          ((evalNegHom airyDerivModulusSqSeries).subst (X * airyZeroSeriesU.binomialPow (-3 : ℚ)))
          (-1 / 2 : ℚ) :=
  (rfl)

/-- `airyZeroSeriesW` has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_airyZeroSeriesW : constantCoeff airyZeroSeriesW = 1 := by
  have hsub0 : constantCoeff ((evalNegHom airyDerivModulusSqSeries).subst
      (X * airyZeroSeriesU.binomialPow (-3 : ℚ)) : ℚ⟦X⟧) = 1 := by
    rw [constantCoeff_eq, constantCoeff_subst_of_constantCoeff_zero (by simp [← constantCoeff_eq]),
      ← coeff_zero_eq_constantCoeff_apply, evalNegHom, coeff_rescale]
    simp
  rw [airyZeroSeriesW_def, map_mul, constantCoeff_binomialPow constantCoeff_airyZeroSeriesU,
    constantCoeff_binomialPow hsub0, one_mul]

/-- The `n`-th rational coefficient `T_n` of `airyZeroSeriesT` (DLMF 9.9.18). -/
def airyZeroCoeffT (n : ℕ) : ℚ :=
  coeff n airyZeroSeriesT

/-- Defining equation for `airyZeroCoeffT`. -/
theorem airyZeroCoeffT_def (n : ℕ) : airyZeroCoeffT n = coeff n airyZeroSeriesT :=
  (rfl)

/-- `T_0 = 1`. -/
@[simp]
theorem airyZeroCoeffT_zero : airyZeroCoeffT 0 = 1 := by
  rw [airyZeroCoeffT_def, coeff_zero_eq_constantCoeff_apply, constantCoeff_airyZeroSeriesT]

/-- The `n`-th rational coefficient `U_n` of `airyZeroSeriesU` (DLMF 9.9.19). -/
def airyZeroCoeffU (n : ℕ) : ℚ :=
  coeff n airyZeroSeriesU

/-- Defining equation for `airyZeroCoeffU`. -/
theorem airyZeroCoeffU_def (n : ℕ) : airyZeroCoeffU n = coeff n airyZeroSeriesU :=
  (rfl)

/-- `U_0 = 1`. -/
@[simp]
theorem airyZeroCoeffU_zero : airyZeroCoeffU 0 = 1 := by
  rw [airyZeroCoeffU_def, coeff_zero_eq_constantCoeff_apply, constantCoeff_airyZeroSeriesU]

/-- The `n`-th rational coefficient `V_n` of `airyZeroSeriesV` (DLMF 9.9.20). -/
def airyZeroCoeffV (n : ℕ) : ℚ :=
  coeff n airyZeroSeriesV

/-- Defining equation for `airyZeroCoeffV`. -/
theorem airyZeroCoeffV_def (n : ℕ) : airyZeroCoeffV n = coeff n airyZeroSeriesV :=
  (rfl)

/-- `V_0 = 1`. -/
@[simp]
theorem airyZeroCoeffV_zero : airyZeroCoeffV 0 = 1 := by
  rw [airyZeroCoeffV_def, coeff_zero_eq_constantCoeff_apply, constantCoeff_airyZeroSeriesV]

/-- The `n`-th rational coefficient `W_n` of `airyZeroSeriesW` (DLMF 9.9.21). -/
def airyZeroCoeffW (n : ℕ) : ℚ :=
  coeff n airyZeroSeriesW

/-- Defining equation for `airyZeroCoeffW`. -/
theorem airyZeroCoeffW_def (n : ℕ) : airyZeroCoeffW n = coeff n airyZeroSeriesW :=
  (rfl)

/-- `W_0 = 1`. -/
@[simp]
theorem airyZeroCoeffW_zero : airyZeroCoeffW 0 = 1 := by
  rw [airyZeroCoeffW_def, coeff_zero_eq_constantCoeff_apply, constantCoeff_airyZeroSeriesW]

/-! ## Reversion equations, uniqueness, and differential formulas for `V` and `W` -/

private theorem constantCoeff_evalNegHom_airyPhaseSeries :
    constantCoeff (evalNegHom airyPhaseSeries) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, evalNegHom, coeff_rescale]
  simp

private theorem constantCoeff_evalNegHom_airyDerivPhaseSeries :
    constantCoeff (evalNegHom airyDerivPhaseSeries) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, evalNegHom, coeff_rescale]
  simp

/-- **Characteristic formal reversion equation for `airyZeroSeriesT`**:
`T ^ (3 / 2) * (evalNegHom airyPhaseSeries)(X * T ^ (-3)) = 1`. -/
theorem airyZeroSeriesT_reversion :
    airyZeroSeriesT.binomialPow (3 / 2 : ℚ) *
      (evalNegHom airyPhaseSeries).subst (X * airyZeroSeriesT.binomialPow (-3 : ℚ)) = 1 := by
  simpa [airyZeroSeriesT_def] using
    binomialPow_binomialReversion_mul_subst constantCoeff_evalNegHom_airyPhaseSeries
      (Units.mk0 (3 / 2 : ℚ) (by norm_num)) (Units.mk0 (3 : ℚ) (by norm_num))

/-- **Uniqueness of `airyZeroSeriesT`**: `airyZeroSeriesT` is the unique formal series `g ∈ ℚ⟦X⟧`
with constant coefficient `1` solving
`g ^ (3 / 2) * (evalNegHom airyPhaseSeries)(X * g ^ (-3)) = 1`. -/
theorem eq_airyZeroSeriesT_iff {g : ℚ⟦X⟧} :
    constantCoeff g = 1 ∧
      g.binomialPow (3 / 2 : ℚ) *
        (evalNegHom airyPhaseSeries).subst (X * g.binomialPow (-3 : ℚ)) = 1 ↔
      g = airyZeroSeriesT := by
  simpa [airyZeroSeriesT_def] using
    eq_binomialReversion_iff (g := g) constantCoeff_evalNegHom_airyPhaseSeries
      (Units.mk0 (3 / 2 : ℚ) (by norm_num)) (Units.mk0 (3 : ℚ) (by norm_num))

/-- Over any commutative `ℚ`-algebra `A`, `airyZeroSeriesT.map (algebraMap ℚ A)` is the unique
formal series `g ∈ A⟦X⟧` with constant coefficient `1` solving the mapped reversion equation. -/
theorem eq_map_airyZeroSeriesT_iff {A : Type*} [CommRing A] [Algebra ℚ A] {g : A⟦X⟧} :
    constantCoeff g = 1 ∧
      g.binomialPow (3 / 2 : ℚ) *
        ((evalNegHom airyPhaseSeries).map (algebraMap ℚ A)).subst
          (X * g.binomialPow (-3 : ℚ)) = 1 ↔
      g = airyZeroSeriesT.map (algebraMap ℚ A) := by
  have hfA : constantCoeff ((evalNegHom airyPhaseSeries).map (algebraMap ℚ A)) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff,
      constantCoeff_evalNegHom_airyPhaseSeries, map_one]
  rw [airyZeroSeriesT_def,
    map_algebraMap_binomialReversion constantCoeff_evalNegHom_airyPhaseSeries]
  simpa using eq_binomialReversion_iff (g := g) hfA
    (Units.mk0 (3 / 2 : ℚ) (by norm_num)) (Units.mk0 (3 : ℚ) (by norm_num))

/-- **Characteristic formal reversion equation for `airyZeroSeriesU`**:
`U ^ (3 / 2) * (evalNegHom airyDerivPhaseSeries)(X * U ^ (-3)) = 1`. -/
theorem airyZeroSeriesU_reversion :
    airyZeroSeriesU.binomialPow (3 / 2 : ℚ) *
      (evalNegHom airyDerivPhaseSeries).subst (X * airyZeroSeriesU.binomialPow (-3 : ℚ)) = 1 := by
  simpa [airyZeroSeriesU_def] using
    binomialPow_binomialReversion_mul_subst constantCoeff_evalNegHom_airyDerivPhaseSeries
      (Units.mk0 (3 / 2 : ℚ) (by norm_num)) (Units.mk0 (3 : ℚ) (by norm_num))

/-- **Uniqueness of `airyZeroSeriesU`**: `airyZeroSeriesU` is the unique formal series `g ∈ ℚ⟦X⟧`
with constant coefficient `1` solving
`g ^ (3 / 2) * (evalNegHom airyDerivPhaseSeries)(X * g ^ (-3)) = 1`. -/
theorem eq_airyZeroSeriesU_iff {g : ℚ⟦X⟧} :
    constantCoeff g = 1 ∧
      g.binomialPow (3 / 2 : ℚ) *
        (evalNegHom airyDerivPhaseSeries).subst (X * g.binomialPow (-3 : ℚ)) = 1 ↔
      g = airyZeroSeriesU := by
  simpa [airyZeroSeriesU_def] using
    eq_binomialReversion_iff (g := g) constantCoeff_evalNegHom_airyDerivPhaseSeries
      (Units.mk0 (3 / 2 : ℚ) (by norm_num)) (Units.mk0 (3 : ℚ) (by norm_num))

/-- Over any commutative `ℚ`-algebra `A`, `airyZeroSeriesU.map (algebraMap ℚ A)` is the unique
formal series `g ∈ A⟦X⟧` with constant coefficient `1` solving the mapped reversion equation. -/
theorem eq_map_airyZeroSeriesU_iff {A : Type*} [CommRing A] [Algebra ℚ A] {g : A⟦X⟧} :
    constantCoeff g = 1 ∧
      g.binomialPow (3 / 2 : ℚ) *
        ((evalNegHom airyDerivPhaseSeries).map (algebraMap ℚ A)).subst
          (X * g.binomialPow (-3 : ℚ)) = 1 ↔
      g = airyZeroSeriesU.map (algebraMap ℚ A) := by
  have hfA : constantCoeff ((evalNegHom airyDerivPhaseSeries).map (algebraMap ℚ A)) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff,
      constantCoeff_evalNegHom_airyDerivPhaseSeries, map_one]
  rw [airyZeroSeriesU_def,
    map_algebraMap_binomialReversion constantCoeff_evalNegHom_airyDerivPhaseSeries]
  simpa using eq_binomialReversion_iff (g := g) hfA
    (Units.mk0 (3 / 2 : ℚ) (by norm_num)) (Units.mk0 (3 : ℚ) (by norm_num))

/-- **Differential formula for `airyZeroSeriesV`**:
`airyZeroSeriesV = (airyZeroSeriesT - 3 • (X * d⁄dX airyZeroSeriesT)) ^ (-1 / 2)`. -/
theorem airyZeroSeriesV_eq_binomialPow_deriv :
    airyZeroSeriesV =
      (airyZeroSeriesT - (3 : ℚ) • (X * d⁄dX airyZeroSeriesT)).binomialPow (-1 / 2 : ℚ) := by
  have hode : evalNegHom airyModulusSqSeries *
      (evalNegHom airyPhaseSeries -
        (2 : ℚ) • (X * d⁄dX (evalNegHom airyPhaseSeries))) = 1 := by
    have hsmul (p : ℚ⟦X⟧) : (2 : ℚ) • p = 2 * p := by rw [Algebra.smul_def, map_ofNat]
    have hneg : evalNegHom (X * d⁄dX airyPhaseSeries) =
        X * d⁄dX (evalNegHom airyPhaseSeries) := by
      simp only [evalNegHom, map_mul, rescale_X, derivative_rescale]
      ring
    have h := congrArg evalNegHom airyModulusSqSeries_mul_phase_deriv
    rwa [hsmul, map_mul, map_sub, map_one, map_mul, map_ofNat, hneg, ← hsmul] at h
  have hsub := subst_X_mul_binomialPow_binomialReversion_of_mul_deriv
    constantCoeff_evalNegHom_airyPhaseSeries
    (Units.mk0 (3 / 2 : ℚ) (by norm_num)) (Units.mk0 (3 : ℚ) (by norm_num))
    (by norm_num; exact hode)
  simp only [Units.val_mk0, ← airyZeroSeriesT_def, show (3 / 2 : ℚ) - 1 = 1 / 2 by norm_num] at hsub
  have hd0 : constantCoeff (airyZeroSeriesT - (3 : ℚ) • (X * d⁄dX airyZeroSeriesT)) = 1 := by
    simp
  rw [airyZeroSeriesV_def, hsub,
    binomialPow_mul (constantCoeff_binomialPow constantCoeff_airyZeroSeriesT _) hd0,
    binomialPow_binomialPow constantCoeff_airyZeroSeriesT, ← mul_assoc,
    ← binomialPow_add constantCoeff_airyZeroSeriesT,
    show (1 / 4 : ℚ) + (1 / 2 : ℚ) * (-1 / 2 : ℚ) = 0 by norm_num, binomialPow_zero, one_mul]

/-- Polynomial differential relation between `airyZeroSeriesV` and `airyZeroSeriesT`:
`V ^ 2 * (T - 3 • (X * d⁄dX T)) = 1`. -/
theorem airyZeroSeriesV_sq_mul :
    airyZeroSeriesV ^ 2 * (airyZeroSeriesT - (3 : ℚ) • (X * d⁄dX airyZeroSeriesT)) = 1 := by
  have hd0 : constantCoeff (airyZeroSeriesT - (3 : ℚ) • (X * d⁄dX airyZeroSeriesT)) = 1 := by
    simp
  have hneg := binomialPow_neg_mul hd0 (1 : ℚ)
  rw [binomialPow_one hd0] at hneg
  rwa [← binomialPow_natCast (R := ℚ) constantCoeff_airyZeroSeriesV 2,
    airyZeroSeriesV_eq_binomialPow_deriv, binomialPow_binomialPow hd0,
    show (-1 / 2 : ℚ) * (2 : ℕ) = -1 by norm_num]

/-- **Differential formula for `airyZeroSeriesW`**:
`airyZeroSeriesW =`
`(airyZeroSeriesU * (airyZeroSeriesU - 3 • (X * d⁄dX airyZeroSeriesU))) ^ (-1 / 2)`. -/
theorem airyZeroSeriesW_eq_binomialPow_deriv :
    airyZeroSeriesW =
      (airyZeroSeriesU *
        (airyZeroSeriesU - (3 : ℚ) • (X * d⁄dX airyZeroSeriesU))).binomialPow (-1 / 2 : ℚ) := by
  have hode : evalNegHom airyDerivModulusSqSeries *
      (evalNegHom airyDerivPhaseSeries -
        (2 : ℚ) • (X * d⁄dX (evalNegHom airyDerivPhaseSeries))) = 1 := by
    have hsmul (p : ℚ⟦X⟧) : (2 : ℚ) • p = 2 * p := by rw [Algebra.smul_def, map_ofNat]
    have hneg : evalNegHom (X * d⁄dX airyDerivPhaseSeries) =
        X * d⁄dX (evalNegHom airyDerivPhaseSeries) := by
      simp only [evalNegHom, map_mul, rescale_X, derivative_rescale]
      ring
    have h := congrArg evalNegHom airyDerivModulusSqSeries_mul_phase_deriv
    rwa [hsmul, map_mul, map_sub, map_one, map_mul, map_ofNat, hneg, ← hsmul] at h
  have hsub := subst_X_mul_binomialPow_binomialReversion_of_mul_deriv
    constantCoeff_evalNegHom_airyDerivPhaseSeries
    (Units.mk0 (3 / 2 : ℚ) (by norm_num)) (Units.mk0 (3 : ℚ) (by norm_num))
    (by norm_num; exact hode)
  simp only [Units.val_mk0, ← airyZeroSeriesU_def, show (3 / 2 : ℚ) - 1 = 1 / 2 by norm_num] at hsub
  have hd0 : constantCoeff (airyZeroSeriesU - (3 : ℚ) • (X * d⁄dX airyZeroSeriesU)) = 1 := by
    simp
  rw [airyZeroSeriesW_def, hsub,
    binomialPow_mul (constantCoeff_binomialPow constantCoeff_airyZeroSeriesU _) hd0,
    binomialPow_binomialPow constantCoeff_airyZeroSeriesU, ← mul_assoc,
    ← binomialPow_add constantCoeff_airyZeroSeriesU,
    show (-1 / 4 : ℚ) + (1 / 2 : ℚ) * (-1 / 2 : ℚ) = -1 / 2 by norm_num,
    ← binomialPow_mul constantCoeff_airyZeroSeriesU hd0]

/-- Polynomial differential relation between `airyZeroSeriesW` and `airyZeroSeriesU`:
`W ^ 2 * (U * (U - 3 • (X * d⁄dX U))) = 1`. -/
theorem airyZeroSeriesW_sq_mul :
    airyZeroSeriesW ^ 2 *
      (airyZeroSeriesU * (airyZeroSeriesU - (3 : ℚ) • (X * d⁄dX airyZeroSeriesU))) = 1 := by
  have hd0 : constantCoeff
      (airyZeroSeriesU * (airyZeroSeriesU - (3 : ℚ) • (X * d⁄dX airyZeroSeriesU))) = 1 := by
    simp
  have hneg := binomialPow_neg_mul hd0 (1 : ℚ)
  rw [binomialPow_one hd0] at hneg
  rwa [← binomialPow_natCast (R := ℚ) constantCoeff_airyZeroSeriesW 2,
    airyZeroSeriesW_eq_binomialPow_deriv, binomialPow_binomialPow hd0,
    show (-1 / 2 : ℚ) * (2 : ℕ) = -1 by norm_num]

/-! ## Exact rational coefficients (DLMF 9.8.22–9.8.23 and 9.9.18–9.9.21) -/

section RationalChecks

private abbrev jet6 (a : Fin 6 → ℚ) : ℚ⟦X⟧ :=
  ∑ i : Fin 6, C (a i) * X ^ (i : ℕ)

private def mulJet6 (a b : Fin 6 → ℚ) : Fin 6 → ℚ :=
  ![a 0 * b 0,
    a 0 * b 1 + a 1 * b 0,
    a 0 * b 2 + a 1 * b 1 + a 2 * b 0,
    a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0,
    a 0 * b 4 + a 1 * b 3 + a 2 * b 2 + a 3 * b 1 + a 4 * b 0,
    a 0 * b 5 + a 1 * b 4 + a 2 * b 3 + a 3 * b 2 + a 4 * b 1 + a 5 * b 0]

private def powJet6 (a : Fin 6 → ℚ) : ℕ → Fin 6 → ℚ
  | 0 => ![1, 0, 0, 0, 0, 0]
  | k + 1 => mulJet6 (powJet6 a k) a

private def substXMulJet6 (r q : Fin 6 → ℚ) : Fin 6 → ℚ :=
  ![r 0 * powJet6 q 0 0,
    r 0 * powJet6 q 0 1 + r 1 * powJet6 q 1 0,
    r 0 * powJet6 q 0 2 + r 1 * powJet6 q 1 1 + r 2 * powJet6 q 2 0,
    r 0 * powJet6 q 0 3 + r 1 * powJet6 q 1 2 + r 2 * powJet6 q 2 1 + r 3 * powJet6 q 3 0,
    r 0 * powJet6 q 0 4 + r 1 * powJet6 q 1 3 + r 2 * powJet6 q 2 2 + r 3 * powJet6 q 3 1 +
      r 4 * powJet6 q 4 0,
    r 0 * powJet6 q 0 5 + r 1 * powJet6 q 1 4 + r 2 * powJet6 q 2 3 + r 3 * powJet6 q 3 2 +
      r 4 * powJet6 q 4 1 + r 5 * powJet6 q 5 0]

private def derivThreeJet6 (a : Fin 6 → ℚ) : Fin 6 → ℚ :=
  ![a 0, -2 * a 1, -5 * a 2, -8 * a 3, -11 * a 4, -14 * a 5]

private theorem jet6_one : jet6 ![1, 0, 0, 0, 0, 0] = 1 := by
  ext n
  rw [coeff_sum_C_mul_X_pow]
  rcases n with _ | _ | _ | _ | _ | _ | n <;> simp

private theorem X_pow_six_dvd_mul_jet6 (a b : Fin 6 → ℚ) :
    (X : ℚ⟦X⟧) ^ 6 ∣ jet6 a * jet6 b - jet6 (mulJet6 a b) := by
  rw [X_pow_dvd_iff]
  intro n hn
  have hsum : (∑ x ∈ Finset.range (n + 1), coeff x (jet6 a) * coeff (n - x) (jet6 b)) =
      ∑ x ∈ Finset.range (n + 1),
        (if hx : x < 6 then a ⟨x, hx⟩ else 0) *
          (if hnx : n - x < 6 then b ⟨n - x, hnx⟩ else 0) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [coeff_sum_C_mul_X_pow, coeff_sum_C_mul_X_pow]
  rw [map_sub, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hsum,
    coeff_sum_C_mul_X_pow, dite_eq_left hn]
  interval_cases n <;> simp [Finset.sum_range_succ, mulJet6]

private theorem X_pow_six_dvd_pow_jet6 (a : Fin 6 → ℚ) (k : ℕ) :
    (X : ℚ⟦X⟧) ^ 6 ∣ jet6 a ^ k - jet6 (powJet6 a k) := by
  induction k with
  | zero =>
    rw [pow_zero, powJet6, jet6_one, sub_self]
    exact dvd_zero _
  | succ k ih =>
    rw [pow_succ (jet6 a) k, powJet6, show jet6 a ^ k * jet6 a - jet6 (mulJet6 (powJet6 a k) a) =
      (jet6 a ^ k - jet6 (powJet6 a k)) * jet6 a +
        (jet6 (powJet6 a k) * jet6 a - jet6 (mulJet6 (powJet6 a k) a)) by ring]
    exact dvd_add (dvd_mul_of_dvd_left ih _) (X_pow_six_dvd_mul_jet6 _ _)

private theorem coeff_eq_of_X_pow_six_dvd {f : ℚ⟦X⟧} {a : Fin 6 → ℚ}
    (h : (X : ℚ⟦X⟧) ^ 6 ∣ f - jet6 a) {n : ℕ} (hn : n < 6) :
    coeff n f = a ⟨n, hn⟩ := by
  have hc := sub_eq_zero.mp (by simpa only [map_sub] using X_pow_dvd_iff.mp h n hn)
  rwa [coeff_sum_C_mul_X_pow, dite_eq_left hn] at hc

private theorem X_pow_six_dvd_subst_X_mul {R Q : ℚ⟦X⟧} {r q : Fin 6 → ℚ}
    (hR : (X : ℚ⟦X⟧) ^ 6 ∣ R - jet6 r) (hQ : (X : ℚ⟦X⟧) ^ 6 ∣ Q - jet6 q) :
    (X : ℚ⟦X⟧) ^ 6 ∣ R.subst (X * Q) - jet6 (substXMulJet6 r q) := by
  have hterm (k n : ℕ) (hk : k ≤ n) (hn : n < 6) :
      coeff k R • coeff n ((X * Q) ^ k) =
        r ⟨k, by omega⟩ * powJet6 q k ⟨n - k, by omega⟩ := by
    have hQk : (X : ℚ⟦X⟧) ^ 6 ∣ Q ^ k - jet6 (powJet6 q k) := by
      rw [show Q ^ k - jet6 (powJet6 q k) =
        (Q ^ k - jet6 q ^ k) + (jet6 q ^ k - jet6 (powJet6 q k)) by ring]
      exact dvd_add (dvd_trans hQ (sub_dvd_pow_sub_pow Q (jet6 q) k))
        (X_pow_six_dvd_pow_jet6 q k)
    have hshift : coeff n (X ^ k * Q ^ k) = coeff (n - k) (Q ^ k) := by
      conv_lhs => rw [show n = (n - k) + k by omega, coeff_X_pow_mul]
    rw [smul_eq_mul, coeff_eq_of_X_pow_six_dvd hR (by omega), mul_pow, hshift,
      coeff_eq_of_X_pow_six_dvd hQk (by omega)]
  rw [X_pow_dvd_iff]
  intro n hn
  have hsum : (∑ k ∈ Finset.range (n + 1), coeff k R • coeff n ((X * Q) ^ k)) =
      ∑ k ∈ Finset.range (n + 1),
        if hk : k ≤ n then r ⟨k, by omega⟩ * powJet6 q k ⟨n - k, by omega⟩ else 0 := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range_succ_iff] at hk
    rw [dite_eq_left hk, hterm k n hk hn]
  rw [map_sub, coeff_subst_eq_sum_range R (by simp), hsum, coeff_sum_C_mul_X_pow, dite_eq_left hn]
  interval_cases n <;> simp [Finset.sum_range_succ, substXMulJet6]

private theorem X_pow_six_dvd_derivThree {f : ℚ⟦X⟧} {a : Fin 6 → ℚ}
    (hf : (X : ℚ⟦X⟧) ^ 6 ∣ f - jet6 a) :
    (X : ℚ⟦X⟧) ^ 6 ∣ (f - (3 : ℚ) • (X * d⁄dX f)) - jet6 (derivThreeJet6 a) := by
  rw [X_pow_dvd_iff]
  intro n hn
  have hcd : coeff n (X * d⁄dX f) = (n : ℚ) * coeff n f := by
    simpa using coeff_X_pow_mul_iterate_derivative f 1 n
  rw [map_sub, map_sub, coeff_smul, smul_eq_mul, hcd,
    coeff_eq_of_X_pow_six_dvd hf hn, coeff_sum_C_mul_X_pow, dite_eq_left hn]
  interval_cases n <;> simp [derivThreeJet6] <;> ring

private def vecA : Fin 6 → ℚ :=
  ![1, 5 / 32, 1155 / 2048, 425425 / 65536, 1301375075 / 8388608, 1698294472875 / 268435456]

private def vecInvA : Fin 6 → ℚ :=
  ![1, -5 / 32, -1105 / 2048, -414125 / 65536, -1282031525 / 8388608, -1683480621875 / 268435456]

private def vecB : Fin 6 → ℚ :=
  ![1, -7 / 32, -1365 / 2048, -475475 / 65536, -1414538125 / 8388608, -1815418229625 / 268435456]

private def vecInvB : Fin 6 → ℚ :=
  ![1, 7 / 32, 1463 / 2048, 495271 / 65536, 1445713003 / 8388608, 1838183317201 / 268435456]

private def vecRc : Fin 6 → ℚ :=
  ![1, -5 / 32, 1105 / 6144, -82825 / 65536, 1282031525 / 58720256, -1683480621875 / 2415919104]

private def vecRd : Fin 6 → ℚ :=
  ![1, 7 / 32, -1463 / 6144, 495271 / 327680, -206530429 / 8388608, 1838183317201 / 2415919104]

private theorem X_pow_six_dvd_airyModulusSqSeries :
    (X : ℚ⟦X⟧) ^ 6 ∣ airyModulusSqSeries - jet6 vecA := by
  have h3 : airyModulusSqCoeff 3 = 425425 / 65536 := by
    rw [airyModulusSqCoeff_succ, airyModulusSqCoeff_two]; norm_num
  have h4 : airyModulusSqCoeff 4 = 1301375075 / 8388608 := by
    rw [airyModulusSqCoeff_succ, h3]; norm_num
  have h5 : airyModulusSqCoeff 5 = 1698294472875 / 268435456 := by
    rw [airyModulusSqCoeff_succ, h4]; norm_num
  rw [X_pow_dvd_iff]
  intro n hn
  rw [map_sub, coeff_airyModulusSqSeries, coeff_sum_C_mul_X_pow, dite_eq_left hn]
  interval_cases n <;> simp [vecA, airyModulusSqCoeff_one, airyModulusSqCoeff_two, h3, h4, h5]

private theorem X_pow_six_dvd_inv_airyModulusSqSeries :
    (X : ℚ⟦X⟧) ^ 6 ∣ invOfUnit airyModulusSqSeries 1 - jet6 vecInvA := by
  have hmul_eq : mulJet6 vecA vecInvA = ![1, 0, 0, 0, 0, 0] := by
    ext i; fin_cases i <;> norm_num [mulJet6, vecA, vecInvA]
  have hprod : (X : ℚ⟦X⟧) ^ 6 ∣ airyModulusSqSeries * jet6 vecInvA - 1 := by
    rw [← jet6_one, ← hmul_eq,
      show airyModulusSqSeries * jet6 vecInvA - jet6 (mulJet6 vecA vecInvA) =
        (airyModulusSqSeries - jet6 vecA) * jet6 vecInvA +
          (jet6 vecA * jet6 vecInvA - jet6 (mulJet6 vecA vecInvA)) by ring]
    exact dvd_add (dvd_mul_of_dvd_left X_pow_six_dvd_airyModulusSqSeries _)
      (X_pow_six_dvd_mul_jet6 _ _)
  have hunit := mul_invOfUnit airyModulusSqSeries 1 constantCoeff_airyModulusSqSeries
  have h := dvd_mul_of_dvd_right hprod (invOfUnit airyModulusSqSeries 1)
  have hrew : invOfUnit airyModulusSqSeries 1 * (airyModulusSqSeries * jet6 vecInvA - 1) =
      jet6 vecInvA - invOfUnit airyModulusSqSeries 1 := by
    calc
      invOfUnit airyModulusSqSeries 1 * (airyModulusSqSeries * jet6 vecInvA - 1) =
          (airyModulusSqSeries * invOfUnit airyModulusSqSeries 1) * jet6 vecInvA -
            invOfUnit airyModulusSqSeries 1 := by ring
      _ = jet6 vecInvA - invOfUnit airyModulusSqSeries 1 := by rw [hunit, one_mul]
  rwa [hrew, ← neg_sub, dvd_neg] at h

/-- DLMF 9.8.22: `c_1 = 5 / 32`. -/
theorem airyPhaseCoeff_one : airyPhaseCoeff 1 = 5 / 32 := by
  rw [airyPhaseCoeff_def, coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_inv_airyModulusSqSeries
    (by decide : 1 < 6)]
  norm_num [vecInvA]

/-- DLMF 9.8.22: `c_2 = 1105 / 6144`. -/
theorem airyPhaseCoeff_two : airyPhaseCoeff 2 = 1105 / 6144 := by
  rw [airyPhaseCoeff_def, coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_inv_airyModulusSqSeries
    (by decide : 2 < 6)]
  norm_num [vecInvA]

/-- DLMF 9.8.22: `c_3 = 82825 / 65536`. -/
theorem airyPhaseCoeff_three : airyPhaseCoeff 3 = 82825 / 65536 := by
  rw [airyPhaseCoeff_def, coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_inv_airyModulusSqSeries
    (by decide : 3 < 6)]
  norm_num [vecInvA]

/-- DLMF 9.8.22: `c_4 = 1282031525 / 58720256`. -/
theorem airyPhaseCoeff_four : airyPhaseCoeff 4 = 1282031525 / 58720256 := by
  rw [airyPhaseCoeff_def, coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_inv_airyModulusSqSeries
    (by decide : 4 < 6)]
  norm_num [vecInvA]

private theorem X_pow_six_dvd_airyDerivModulusSqSeries :
    (X : ℚ⟦X⟧) ^ 6 ∣ airyDerivModulusSqSeries - jet6 vecB := by
  rw [X_pow_dvd_iff]
  intro n hn
  have ha := coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_airyModulusSqSeries hn
  rw [coeff_airyModulusSqSeries] at ha
  rw [map_sub, coeff_airyDerivModulusSqSeries, airyDerivModulusSqCoeff_def, ha,
    coeff_sum_C_mul_X_pow, dite_eq_left hn]
  interval_cases n <;> norm_num [vecA, vecB]

private theorem X_pow_six_dvd_inv_airyDerivModulusSqSeries :
    (X : ℚ⟦X⟧) ^ 6 ∣ invOfUnit airyDerivModulusSqSeries 1 - jet6 vecInvB := by
  have hmul_eq : mulJet6 vecB vecInvB = ![1, 0, 0, 0, 0, 0] := by
    ext i; fin_cases i <;> norm_num [mulJet6, vecB, vecInvB]
  have hprod : (X : ℚ⟦X⟧) ^ 6 ∣ airyDerivModulusSqSeries * jet6 vecInvB - 1 := by
    rw [← jet6_one, ← hmul_eq,
      show airyDerivModulusSqSeries * jet6 vecInvB - jet6 (mulJet6 vecB vecInvB) =
        (airyDerivModulusSqSeries - jet6 vecB) * jet6 vecInvB +
          (jet6 vecB * jet6 vecInvB - jet6 (mulJet6 vecB vecInvB)) by ring]
    exact dvd_add (dvd_mul_of_dvd_left X_pow_six_dvd_airyDerivModulusSqSeries _)
      (X_pow_six_dvd_mul_jet6 _ _)
  have hunit := mul_invOfUnit airyDerivModulusSqSeries 1 constantCoeff_airyDerivModulusSqSeries
  have h := dvd_mul_of_dvd_right hprod (invOfUnit airyDerivModulusSqSeries 1)
  have hrew : invOfUnit airyDerivModulusSqSeries 1 *
      (airyDerivModulusSqSeries * jet6 vecInvB - 1) =
        jet6 vecInvB - invOfUnit airyDerivModulusSqSeries 1 := by
    calc
      invOfUnit airyDerivModulusSqSeries 1 * (airyDerivModulusSqSeries * jet6 vecInvB - 1) =
          (airyDerivModulusSqSeries * invOfUnit airyDerivModulusSqSeries 1) * jet6 vecInvB -
            invOfUnit airyDerivModulusSqSeries 1 := by ring
      _ = jet6 vecInvB - invOfUnit airyDerivModulusSqSeries 1 := by rw [hunit, one_mul]
  rwa [hrew, ← neg_sub, dvd_neg] at h

/-- DLMF 9.8.23: `d_1 = -7 / 32`. -/
theorem airyDerivPhaseCoeff_one : airyDerivPhaseCoeff 1 = -7 / 32 := by
  rw [airyDerivPhaseCoeff_def, coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_inv_airyDerivModulusSqSeries
    (by decide : 1 < 6)]
  norm_num [vecInvB]

/-- DLMF 9.8.23: `d_2 = -1463 / 6144`. -/
theorem airyDerivPhaseCoeff_two : airyDerivPhaseCoeff 2 = -1463 / 6144 := by
  rw [airyDerivPhaseCoeff_def, coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_inv_airyDerivModulusSqSeries
    (by decide : 2 < 6)]
  norm_num [vecInvB]

/-- DLMF 9.8.23: `d_3 = -495271 / 327680`. -/
theorem airyDerivPhaseCoeff_three : airyDerivPhaseCoeff 3 = -495271 / 327680 := by
  rw [airyDerivPhaseCoeff_def, coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_inv_airyDerivModulusSqSeries
    (by decide : 3 < 6)]
  norm_num [vecInvB]

/-- DLMF 9.8.23: `d_4 = -206530429 / 8388608`. -/
theorem airyDerivPhaseCoeff_four : airyDerivPhaseCoeff 4 = -206530429 / 8388608 := by
  rw [airyDerivPhaseCoeff_def, coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_inv_airyDerivModulusSqSeries
    (by decide : 4 < 6)]
  norm_num [vecInvB]

private theorem X_pow_six_dvd_evalNegHom_airyPhaseSeries :
    (X : ℚ⟦X⟧) ^ 6 ∣ evalNegHom airyPhaseSeries - jet6 vecRc := by
  rw [X_pow_dvd_iff]
  intro n hn
  have hinv := coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_inv_airyModulusSqSeries hn
  rw [map_sub, evalNegHom, coeff_rescale, coeff_airyPhaseSeries, airyPhaseCoeff_def, hinv,
    coeff_sum_C_mul_X_pow, dite_eq_left hn]
  interval_cases n <;> norm_num [vecInvA, vecRc]

private theorem X_pow_six_dvd_evalNegHom_airyDerivPhaseSeries :
    (X : ℚ⟦X⟧) ^ 6 ∣ evalNegHom airyDerivPhaseSeries - jet6 vecRd := by
  rw [X_pow_dvd_iff]
  intro n hn
  have hinv := coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_inv_airyDerivModulusSqSeries hn
  rw [map_sub, evalNegHom, coeff_rescale, coeff_airyDerivPhaseSeries, airyDerivPhaseCoeff_def, hinv,
    coeff_sum_C_mul_X_pow, dite_eq_left hn]
  interval_cases n <;> norm_num [vecInvB, vecRd]

private def vecT : Fin 6 → ℚ :=
  ![1, 5 / 48, -5 / 36, 77125 / 82944, -108056875 / 6967296, 162375596875 / 334430208]

private def vecQT : Fin 6 → ℚ :=
  ![1, -5 / 16, 185 / 384, -18275 / 6144, 21952425 / 458752, -32543414375 / 22020096]

private def vecU : Fin 6 → ℚ :=
  ![1, -7 / 48, 35 / 288, -181223 / 207360, 18683371 / 1244160, -91145884361 / 191102976]

private def vecQU : Fin 6 → ℚ :=
  ![1, 7 / 16, -91 / 384, 74963 / 30720, -14255157 / 327680, 22081222163 / 15728640]

private def vecV : Fin 6 → ℚ :=
  ![1, 5 / 48, -1525 / 4608, 2397875 / 663552, -74898940625 / 891813888,
    144198303734375 / 42807066624]

private def vecW : Fin 6 → ℚ :=
  ![1, -7 / 96, 1673 / 6144, -84394709 / 26542080, 780277135421 / 10192158720,
    -204449051051945 / 65229815808]

private theorem constantCoeff_jet6_of_zero_eq_one {v : Fin 6 → ℚ} (hv : v 0 = 1) :
    constantCoeff (jet6 v) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_sum_C_mul_X_pow, dite_eq_left (by decide : 0 < 6)]
  exact hv

private theorem X_pow_six_dvd_binomialReversion_three_halves_three {f : ℚ⟦X⟧} {r v : Fin 6 → ℚ}
    (q : Fin 6 → ℚ) (hf0 : constantCoeff f = 1) (hv0 : v 0 = 1)
    (hf : (X : ℚ⟦X⟧) ^ 6 ∣ f - jet6 r)
    (hq : mulJet6 (powJet6 v 3) q = ![1, 0, 0, 0, 0, 0])
    (hrev : powJet6 (substXMulJet6 r q) 2 = q) :
    (X : ℚ⟦X⟧) ^ 6 ∣ jet6 v -
      f.binomialReversion (Units.mk0 (3 / 2 : ℚ) (by norm_num))
        (Units.mk0 (3 : ℚ) (by norm_num)) := by
  have hv_cc : constantCoeff (jet6 v) = 1 := constantCoeff_jet6_of_zero_eq_one hv0
  have hq_prod : (X : ℚ⟦X⟧) ^ 6 ∣ jet6 v ^ 3 * jet6 q - 1 := by
    rw [← jet6_one, ← hq, show jet6 v ^ 3 * jet6 q - jet6 (mulJet6 (powJet6 v 3) q) =
      (jet6 v ^ 3 - jet6 (powJet6 v 3)) * jet6 q +
        (jet6 (powJet6 v 3) * jet6 q - jet6 (mulJet6 (powJet6 v 3) q)) by ring]
    exact dvd_add (dvd_mul_of_dvd_left (X_pow_six_dvd_pow_jet6 v 3) _)
      (X_pow_six_dvd_mul_jet6 _ _)
  have hv_neg3 : (X : ℚ⟦X⟧) ^ 6 ∣ (jet6 v).binomialPow (-3 : ℚ) - jet6 q := by
    have hmul := dvd_mul_of_dvd_right hq_prod ((jet6 v).binomialPow (-3 : ℚ))
    have hcan : jet6 v ^ 3 * (jet6 v).binomialPow (-3 : ℚ) = 1 := by
      rw [← binomialPow_natCast (R := ℚ) hv_cc 3]
      simpa using binomialPow_mul_neg hv_cc (3 : ℚ)
    have hrew : (jet6 v).binomialPow (-3 : ℚ) * (jet6 v ^ 3 * jet6 q - 1) =
        jet6 q - (jet6 v).binomialPow (-3 : ℚ) := by
      calc
        (jet6 v).binomialPow (-3 : ℚ) * (jet6 v ^ 3 * jet6 q - 1) =
            (jet6 v ^ 3 * (jet6 v).binomialPow (-3 : ℚ)) * jet6 q -
              (jet6 v).binomialPow (-3 : ℚ) := by ring
        _ = jet6 q - (jet6 v).binomialPow (-3 : ℚ) := by rw [hcan, one_mul]
    rwa [hrew, ← neg_sub, dvd_neg] at hmul
  set S : ℚ⟦X⟧ := f.subst (X * (jet6 v).binomialPow (-3 : ℚ))
  have hS0 : constantCoeff S = 1 := by
    rw [constantCoeff_eq, constantCoeff_subst_of_constantCoeff_zero (by simp [← constantCoeff_eq]),
      hf0, map_one]
  have hS2 : (X : ℚ⟦X⟧) ^ 6 ∣ S ^ 2 - jet6 q := by
    rw [← hrev, show S ^ 2 - jet6 (powJet6 (substXMulJet6 r q) 2) =
      (S ^ 2 - jet6 (substXMulJet6 r q) ^ 2) +
        (jet6 (substXMulJet6 r q) ^ 2 - jet6 (powJet6 (substXMulJet6 r q) 2)) by ring]
    exact dvd_add (dvd_trans (X_pow_six_dvd_subst_X_mul hf hv_neg3)
      (sub_dvd_pow_sub_pow S _ 2)) (X_pow_six_dvd_pow_jet6 _ 2)
  have hsq : (X : ℚ⟦X⟧) ^ 6 ∣ ((jet6 v).binomialPow (3 / 2 : ℚ) * S) ^ 2 - 1 := by
    have hv3 : ((jet6 v).binomialPow (3 / 2 : ℚ)) ^ 2 = jet6 v ^ 3 := by
      rw [← binomialPow_natCast (R := ℚ) (constantCoeff_binomialPow hv_cc _) 2,
        binomialPow_binomialPow hv_cc, show (3 / 2 : ℚ) * (2 : ℕ) = (3 : ℕ) by norm_num,
        binomialPow_natCast hv_cc 3]
    rw [mul_pow, hv3, show jet6 v ^ 3 * S ^ 2 - 1 =
      jet6 v ^ 3 * (S ^ 2 - jet6 q) + (jet6 v ^ 3 * jet6 q - 1) by ring]
    exact dvd_add (dvd_mul_of_dvd_right hS2 _) hq_prod
  have hprod_cc : constantCoeff ((jet6 v).binomialPow (3 / 2 : ℚ) * S) = 1 := by
    rw [map_mul, constantCoeff_binomialPow hv_cc, hS0, one_mul]
  rw [← binomialPow_natCast (R := ℚ) hprod_cc 2,
    ← binomialPow_one_left (R := ℚ) ((2 : ℕ) : ℚ)] at hsq
  have hchar := (X_pow_dvd_binomialPow_sub_binomialPow_iff hprod_cc constantCoeff_one
    (Units.mk0 (2 : ℚ) (by norm_num))).mp (by simpa using hsq)
  exact X_pow_dvd_sub_binomialReversion hf0 hv_cc _ _ (by simpa [S] using hchar)

private theorem X_pow_six_dvd_airyZeroSeriesT :
    (X : ℚ⟦X⟧) ^ 6 ∣ airyZeroSeriesT - jet6 vecT := by
  have hT3 : powJet6 vecT 3 =
      ![1, 5 / 16, -295 / 768, 11075 / 4096, -23685175 / 516096, 3411908875 / 2359296] := by
    ext i; fin_cases i <;> norm_num [powJet6, mulJet6, vecT]
  have hsubT : substXMulJet6 vecRc vecQT =
      ![1, -5 / 32, 1405 / 6144, -95125 / 65536, 12510921125 / 528482304,
        -12428503188125 / 16911433728] := by
    ext i; fin_cases i <;> norm_num [substXMulJet6, powJet6, mulJet6, vecRc, vecQT]
  rw [← dvd_neg, neg_sub, airyZeroSeriesT_def]
  refine X_pow_six_dvd_binomialReversion_three_halves_three vecQT
    constantCoeff_evalNegHom_airyPhaseSeries rfl X_pow_six_dvd_evalNegHom_airyPhaseSeries ?_ ?_
  · rw [hT3]; ext i; fin_cases i <;> norm_num [mulJet6, vecQT]
  · rw [hsubT]; ext i; fin_cases i <;> norm_num [powJet6, mulJet6, vecQT]

private theorem X_pow_six_dvd_airyZeroSeriesU :
    (X : ℚ⟦X⟧) ^ 6 ∣ airyZeroSeriesU - jet6 vecU := by
  have hU3 : powJet6 vecU 3 =
      ![1, -7 / 16, 329 / 768, -55937 / 20480, 3381707 / 73728, -17042121649 / 11796480] := by
    ext i; fin_cases i <;> norm_num [powJet6, mulJet6, vecU]
  have hsubU : substXMulJet6 vecRd vecQU =
      ![1, 7 / 32, -875 / 6144, 410011 / 327680, -8318121329 / 377487360,
        1707913743529 / 2415919104] := by
    ext i; fin_cases i <;> norm_num [substXMulJet6, powJet6, mulJet6, vecRd, vecQU]
  rw [← dvd_neg, neg_sub, airyZeroSeriesU_def]
  refine X_pow_six_dvd_binomialReversion_three_halves_three vecQU
    constantCoeff_evalNegHom_airyDerivPhaseSeries rfl
    X_pow_six_dvd_evalNegHom_airyDerivPhaseSeries ?_ ?_
  · rw [hU3]; ext i; fin_cases i <;> norm_num [mulJet6, vecQU]
  · rw [hsubU]; ext i; fin_cases i <;> norm_num [powJet6, mulJet6, vecQU]

private theorem X_pow_six_dvd_of_sq_mul_eq_one {S D : ℚ⟦X⟧} {v d : Fin 6 → ℚ}
    (hS0 : constantCoeff S = 1) (hv0 : v 0 = 1) (hSD : S ^ 2 * D = 1)
    (hD : (X : ℚ⟦X⟧) ^ 6 ∣ D - jet6 d)
    (hmul : mulJet6 (powJet6 v 2) d = ![1, 0, 0, 0, 0, 0]) :
    (X : ℚ⟦X⟧) ^ 6 ∣ S - jet6 v := by
  have hv_cc : constantCoeff (jet6 v) = 1 := constantCoeff_jet6_of_zero_eq_one hv0
  have hprod : (X : ℚ⟦X⟧) ^ 6 ∣ jet6 v ^ 2 * D - 1 := by
    rw [← jet6_one, ← hmul, show jet6 v ^ 2 * D - jet6 (mulJet6 (powJet6 v 2) d) =
      jet6 v ^ 2 * (D - jet6 d) + (jet6 v ^ 2 - jet6 (powJet6 v 2)) * jet6 d +
        (jet6 (powJet6 v 2) * jet6 d - jet6 (mulJet6 (powJet6 v 2) d)) by ring]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_right hD _)
      (dvd_mul_of_dvd_left (X_pow_six_dvd_pow_jet6 v 2) _)) (X_pow_six_dvd_mul_jet6 _ _)
  have hsq : (X : ℚ⟦X⟧) ^ 6 ∣ S ^ 2 - jet6 v ^ 2 := by
    have h := dvd_mul_of_dvd_left hprod (S ^ 2)
    have hrew : (jet6 v ^ 2 * D - 1) * S ^ 2 = jet6 v ^ 2 - S ^ 2 := by
      calc
        (jet6 v ^ 2 * D - 1) * S ^ 2 = jet6 v ^ 2 * (S ^ 2 * D) - S ^ 2 := by ring
        _ = jet6 v ^ 2 - S ^ 2 := by rw [hSD, mul_one]
    rwa [hrew, ← neg_sub, dvd_neg] at h
  rw [← binomialPow_natCast (R := ℚ) hS0 2, ← binomialPow_natCast (R := ℚ) hv_cc 2] at hsq
  exact (X_pow_dvd_binomialPow_sub_binomialPow_iff hS0 hv_cc
    (Units.mk0 (2 : ℚ) (by norm_num))).mp (by simpa using hsq)

private theorem X_pow_six_dvd_airyZeroSeriesV :
    (X : ℚ⟦X⟧) ^ 6 ∣ airyZeroSeriesV - jet6 vecV := by
  refine X_pow_six_dvd_of_sq_mul_eq_one constantCoeff_airyZeroSeriesV rfl airyZeroSeriesV_sq_mul
    (X_pow_six_dvd_derivThree X_pow_six_dvd_airyZeroSeriesT) ?_
  ext i; fin_cases i <;> norm_num [mulJet6, powJet6, derivThreeJet6, vecV, vecT]

private theorem X_pow_six_dvd_airyZeroSeriesW :
    (X : ℚ⟦X⟧) ^ 6 ∣ airyZeroSeriesW - jet6 vecW := by
  have hdU := X_pow_six_dvd_derivThree X_pow_six_dvd_airyZeroSeriesU
  have hUD : (X : ℚ⟦X⟧) ^ 6 ∣
      airyZeroSeriesU * (airyZeroSeriesU - (3 : ℚ) • (X * d⁄dX airyZeroSeriesU)) -
        jet6 (mulJet6 vecU (derivThreeJet6 vecU)) := by
    rw [show airyZeroSeriesU * (airyZeroSeriesU - (3 : ℚ) • (X * d⁄dX airyZeroSeriesU)) -
      jet6 (mulJet6 vecU (derivThreeJet6 vecU)) =
      (airyZeroSeriesU - jet6 vecU) * (airyZeroSeriesU - (3 : ℚ) • (X * d⁄dX airyZeroSeriesU)) +
        jet6 vecU * ((airyZeroSeriesU - (3 : ℚ) • (X * d⁄dX airyZeroSeriesU)) -
          jet6 (derivThreeJet6 vecU)) +
        (jet6 vecU * jet6 (derivThreeJet6 vecU) -
          jet6 (mulJet6 vecU (derivThreeJet6 vecU))) by ring]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_left X_pow_six_dvd_airyZeroSeriesU _)
      (dvd_mul_of_dvd_right hdU _)) (X_pow_six_dvd_mul_jet6 _ _)
  refine X_pow_six_dvd_of_sq_mul_eq_one constantCoeff_airyZeroSeriesW rfl airyZeroSeriesW_sq_mul
    hUD ?_
  ext i; fin_cases i <;> norm_num [mulJet6, powJet6, derivThreeJet6, vecW, vecU]

/-- DLMF 9.9.18: `T_1 = 5 / 48`. -/
theorem airyZeroCoeffT_one : airyZeroCoeffT 1 = 5 / 48 := by
  simpa [airyZeroCoeffT_def, vecT] using
    coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_airyZeroSeriesT (by decide : 1 < 6)

/-- DLMF 9.9.18: `T_2 = -5 / 36`. -/
theorem airyZeroCoeffT_two : airyZeroCoeffT 2 = -5 / 36 := by
  simpa [airyZeroCoeffT_def, vecT] using
    coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_airyZeroSeriesT (by decide : 2 < 6)

/-- DLMF 9.9.18: `T_3 = 77125 / 82944`. -/
theorem airyZeroCoeffT_three : airyZeroCoeffT 3 = 77125 / 82944 := by
  simpa [airyZeroCoeffT_def, vecT] using
    coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_airyZeroSeriesT (by decide : 3 < 6)

/-- DLMF 9.9.18: `T_4 = -108056875 / 6967296`. -/
theorem airyZeroCoeffT_four : airyZeroCoeffT 4 = -108056875 / 6967296 := by
  simpa [airyZeroCoeffT_def, vecT] using
    coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_airyZeroSeriesT (by decide : 4 < 6)

/-- DLMF 9.9.18: `T_5 = 162375596875 / 334430208`. -/
theorem airyZeroCoeffT_five : airyZeroCoeffT 5 = 162375596875 / 334430208 := by
  simpa [airyZeroCoeffT_def, vecT] using
    coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_airyZeroSeriesT (by decide : 5 < 6)

/-- DLMF 9.9.19: `U_1 = -7 / 48`. -/
theorem airyZeroCoeffU_one : airyZeroCoeffU 1 = -7 / 48 := by
  simpa [airyZeroCoeffU_def, vecU] using
    coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_airyZeroSeriesU (by decide : 1 < 6)

/-- DLMF 9.9.19: `U_2 = 35 / 288`. -/
theorem airyZeroCoeffU_two : airyZeroCoeffU 2 = 35 / 288 := by
  simpa [airyZeroCoeffU_def, vecU] using
    coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_airyZeroSeriesU (by decide : 2 < 6)

/-- DLMF 9.9.19: `U_3 = -181223 / 207360`. -/
theorem airyZeroCoeffU_three : airyZeroCoeffU 3 = -181223 / 207360 := by
  simpa [airyZeroCoeffU_def, vecU] using
    coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_airyZeroSeriesU (by decide : 3 < 6)

/-- DLMF 9.9.19: `U_4 = 18683371 / 1244160`. -/
theorem airyZeroCoeffU_four : airyZeroCoeffU 4 = 18683371 / 1244160 := by
  simpa [airyZeroCoeffU_def, vecU] using
    coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_airyZeroSeriesU (by decide : 4 < 6)

/-- DLMF 9.9.19: `U_5 = -91145884361 / 191102976`. -/
theorem airyZeroCoeffU_five : airyZeroCoeffU 5 = -91145884361 / 191102976 := by
  simpa [airyZeroCoeffU_def, vecU] using
    coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_airyZeroSeriesU (by decide : 5 < 6)

/-- DLMF 9.9.20: `V_1 = 5 / 48`. -/
theorem airyZeroCoeffV_one : airyZeroCoeffV 1 = 5 / 48 := by
  simpa [airyZeroCoeffV_def, vecV] using
    coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_airyZeroSeriesV (by decide : 1 < 6)

/-- DLMF 9.9.20: `V_2 = -1525 / 4608`. -/
theorem airyZeroCoeffV_two : airyZeroCoeffV 2 = -1525 / 4608 := by
  simpa [airyZeroCoeffV_def, vecV] using
    coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_airyZeroSeriesV (by decide : 2 < 6)

/-- DLMF 9.9.20: `V_3 = 2397875 / 663552`. -/
theorem airyZeroCoeffV_three : airyZeroCoeffV 3 = 2397875 / 663552 := by
  simpa [airyZeroCoeffV_def, vecV] using
    coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_airyZeroSeriesV (by decide : 3 < 6)

/-- DLMF 9.9.20: `V_4 = -74898940625 / 891813888`. -/
theorem airyZeroCoeffV_four : airyZeroCoeffV 4 = -74898940625 / 891813888 := by
  simpa [airyZeroCoeffV_def, vecV] using
    coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_airyZeroSeriesV (by decide : 4 < 6)

/-- DLMF 9.9.20: `V_5 = 144198303734375 / 42807066624`. -/
theorem airyZeroCoeffV_five : airyZeroCoeffV 5 = 144198303734375 / 42807066624 := by
  simpa [airyZeroCoeffV_def, vecV] using
    coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_airyZeroSeriesV (by decide : 5 < 6)

/-- DLMF 9.9.21: `W_1 = -7 / 96`. -/
theorem airyZeroCoeffW_one : airyZeroCoeffW 1 = -7 / 96 := by
  simpa [airyZeroCoeffW_def, vecW] using
    coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_airyZeroSeriesW (by decide : 1 < 6)

/-- DLMF 9.9.21: `W_2 = 1673 / 6144`. -/
theorem airyZeroCoeffW_two : airyZeroCoeffW 2 = 1673 / 6144 := by
  simpa [airyZeroCoeffW_def, vecW] using
    coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_airyZeroSeriesW (by decide : 2 < 6)

/-- DLMF 9.9.21: `W_3 = -84394709 / 26542080`. -/
theorem airyZeroCoeffW_three : airyZeroCoeffW 3 = -84394709 / 26542080 := by
  simpa [airyZeroCoeffW_def, vecW] using
    coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_airyZeroSeriesW (by decide : 3 < 6)

/-- DLMF 9.9.21: `W_4 = 780277135421 / 10192158720`. -/
theorem airyZeroCoeffW_four : airyZeroCoeffW 4 = 780277135421 / 10192158720 := by
  simpa [airyZeroCoeffW_def, vecW] using
    coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_airyZeroSeriesW (by decide : 4 < 6)

/-- DLMF 9.9.21: `W_5 = -204449051051945 / 65229815808`. -/
theorem airyZeroCoeffW_five : airyZeroCoeffW 5 = -204449051051945 / 65229815808 := by
  simpa [airyZeroCoeffW_def, vecW] using
    coeff_eq_of_X_pow_six_dvd X_pow_six_dvd_airyZeroSeriesW (by decide : 5 < 6)

/-- Linear reversion relation `(3 / 2) T_1 = c_1` and first-order relation `V_1 = T_1 / 4 + a_1 / 2`
relating the leading nontrivial coefficients of `T` and `V` to `c_1` and `a_1`. -/
theorem airyZeroCoeffT_one_and_airyZeroCoeffV_one_rel :
    (3 / 2 : ℚ) * airyZeroCoeffT 1 - airyPhaseCoeff 1 = 0 ∧
      airyZeroCoeffV 1 = airyZeroCoeffT 1 / 4 + airyModulusSqCoeff 1 / 2 := by
  rw [airyZeroCoeffT_one, airyPhaseCoeff_one, airyZeroCoeffV_one, airyModulusSqCoeff_one]
  norm_num

end RationalChecks

end

end TauCeti

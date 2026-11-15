/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Ordinary points of homogeneous second-order linear differential equations

Let `f` and `g` be holomorphic on an open disc `Metric.eball z₀ r` (`0 < r ≤ ∞`) in the complex
plane (or real-analytic with scalar power series on `Metric.eball z₀ r` over `ℝ`). A point `z₀` is
an *ordinary point* of the homogeneous second-order linear differential equation

  `w''(z) + f(z) w'(z) + g(z) w(z) = 0`.

Equating power-series coefficients of `f(z) = ∑ fs_n (z - z₀)^n` and `g(z) = ∑ gs_n (z - z₀)^n`
around `z₀` determines the Taylor coefficients `a_n` of any solution `w(z) = ∑ a_n (z - z₀)^n`
from the initial values `a_0 = w(z₀)` and `a_1 = w'(z₀)` by the recurrence

  `(n + 2)(n + 1) a_{n + 2} = - ∑_{k = 0}^n ((k + 1) fs_{n - k} a_{k + 1} + gs_{n - k} a_k)`.

This file develops the formal coefficient recurrence (`TauCeti.ordinaryPointCoeff`), proves by a
Cauchy majorant estimate on partial sums that over `ℝ` or `ℂ` (`RCLike 𝕜`) the resulting scalar
power series converges on the entire common ball of convergence of `fs` and `gs`
(`TauCeti.le_radius_ofScalars_ordinaryPointCoeff`), constructs the canonical Taylor-series
solution `TauCeti.ordinaryPointSolution` over `RCLike 𝕜`, and over `ℂ` upgrades mere complex
differentiability on `Metric.eball z₀ r` (including `r = ⊤` for entire coefficients) directly to
power-series convergence, uniqueness on preconnected open domains, and Cramer's-rule fundamental
pair expansions.

## Main definitions

* `TauCeti.ordinaryPointCoeff fs gs w₀ w₁`: the formal Taylor coefficient sequence around an
  ordinary point determined by coefficient sequences `fs`, `gs` and initial data `w₀`, `w₁`.
* `TauCeti.ordinaryPointSolution f g z₀ w₀ w₁`: the scalar Taylor-series solution around `z₀`
  associated with `f`, `g : 𝕜 → 𝕜` and initial data `w(z₀) = w₀`, `w'(z₀) = w₁`.

## Main results

* `TauCeti.eq_ordinaryPointCoeff_iff`: universal characterization of `ordinaryPointCoeff` in
  characteristic zero by its two initial values and the cleared-denominator recurrence.
* `TauCeti.le_radius_ofScalars_ordinaryPointCoeff`: over `ℝ` or `ℂ`, the radius of convergence
  of `ordinaryPointCoeff fs gs w₀ w₁` is at least any lower bound on the radii of `fs` and `gs`.
* `TauCeti.forall_mem_eball_deriv_deriv_add_eq_zero_iff`: over `ℝ` or `ℂ`, a scalar power series on
  `Metric.eball z₀ r` solves `w'' + f w' + g w = 0` on the whole ball if and only if its
  coefficients equal `ordinaryPointCoeff fs gs (w z₀) (deriv w z₀)`.
* `TauCeti.hasFPowerSeriesOnBall_ordinaryPointSolution`,
  `TauCeti.deriv_deriv_ordinaryPointSolution`: for `f`, `g : ℂ → ℂ` holomorphic on
  `Metric.eball z₀ r` (`0 < r`), `ordinaryPointSolution f g z₀ w₀ w₁` is represented on the whole
  disc by its Taylor series and solves the initial-value problem there.
* `TauCeti.exists_holomorphic_ordinaryPoint_eball`,
  `TauCeti.exists_holomorphic_ordinaryPoint_ball`,
  `TauCeti.existsUnique_entire_ordinaryPoint`: existence and uniqueness of holomorphic solutions
  on extended discs, finite discs, and all of `ℂ`.
* `TauCeti.eqOn_of_analyticOnNhd_of_deriv_deriv_add_eq_zero`,
  `TauCeti.eqOn_linear_combination_of_analyticOnNhd_of_wronskian_ne_zero`,
  `TauCeti.eqOn_of_differentiableOn_of_deriv_deriv_add_eq_zero`,
  `TauCeti.eqOn_linear_combination_of_wronskian_ne_zero`,
  `TauCeti.eq_linear_combination_of_wronskian_ne_zero`: uniqueness and Cramer's-rule expansion in
  terms of a pair of solutions with nonzero Wronskian at `z₀`, for analytic functions on
  preconnected sets and holomorphic or entire functions over `ℂ`.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press (1974; reprinted A K Peters,
  1997), Chapter 5, §1.
* NIST Digital Library of Mathematical Functions, §2.7(i), equation (2.7.1),
  <https://dlmf.nist.gov/2.7.i>.
-/

public section

open Filter Set Topology
open scoped BigOperators ContDiff ENNReal NNReal Nat

namespace TauCeti

/-! ### Formal Taylor-coefficient recurrence -/

section Coefficients

variable {𝕜 : Type*} [Field 𝕜]

/-- The formal Taylor coefficient sequence around an ordinary point of `w'' + f w' + g w = 0`,
computed from the Taylor coefficient sequences `fs`, `gs` of `f`, `g` and initial data `w₀`, `w₁`.
At step `n + 2`, the recurrence divides by `(n + 2)(n + 1)` in `𝕜`; over a field of
characteristic zero this is equivalent to the cleared-denominator polynomial recurrence
(`TauCeti.eq_ordinaryPointCoeff_iff`). -/
def ordinaryPointCoeff (fs gs : ℕ → 𝕜) (w₀ w₁ : 𝕜) : ℕ → 𝕜
  | 0 => w₀
  | 1 => w₁
  | n + 2 =>
    -(((n + 2 : 𝕜) * (n + 1 : 𝕜))⁻¹ *
      ∑ i : Fin (n + 1),
        ((i.val + 1 : 𝕜) * fs (n - i.val) * ordinaryPointCoeff fs gs w₀ w₁ (i.val + 1) +
          gs (n - i.val) * ordinaryPointCoeff fs gs w₀ w₁ i.val))
termination_by n => n
decreasing_by
  all_goals
    have := i.isLt
    omega

/-- The zeroth Taylor coefficient is the prescribed initial value `w₀`. -/
@[simp]
theorem ordinaryPointCoeff_zero (fs gs : ℕ → 𝕜) (w₀ w₁ : 𝕜) :
    ordinaryPointCoeff fs gs w₀ w₁ 0 = w₀ := by
  rw [ordinaryPointCoeff]

/-- The first Taylor coefficient is the prescribed initial derivative `w₁`. -/
@[simp]
theorem ordinaryPointCoeff_one (fs gs : ℕ → 𝕜) (w₀ w₁ : 𝕜) :
    ordinaryPointCoeff fs gs w₀ w₁ 1 = w₁ := by
  rw [ordinaryPointCoeff]

/-- The defining recurrence for `ordinaryPointCoeff` at index `n + 2`. -/
@[simp]
theorem ordinaryPointCoeff_add_two (fs gs : ℕ → 𝕜) (w₀ w₁ : 𝕜) (n : ℕ) :
    ordinaryPointCoeff fs gs w₀ w₁ (n + 2) =
      -(((n + 2 : 𝕜) * (n + 1 : 𝕜))⁻¹ *
        ∑ k ∈ Finset.range (n + 1),
          ((k + 1 : 𝕜) * fs (n - k) * ordinaryPointCoeff fs gs w₀ w₁ (k + 1) +
            gs (n - k) * ordinaryPointCoeff fs gs w₀ w₁ k)) := by
  rw [ordinaryPointCoeff, ← Fin.sum_univ_eq_sum_range]

/-- In characteristic zero, `ordinaryPointCoeff` satisfies the cleared-denominator recurrence
`(n + 2)(n + 1) a_{n + 2} = - ∑_{k = 0}^n ((k + 1) fs_{n - k} a_{k + 1} + gs_{n - k} a_k)`. -/
theorem mul_ordinaryPointCoeff_add_two [CharZero 𝕜]
    (fs gs : ℕ → 𝕜) (w₀ w₁ : 𝕜) (n : ℕ) :
    (n + 2 : 𝕜) * (n + 1 : 𝕜) * ordinaryPointCoeff fs gs w₀ w₁ (n + 2) =
      -∑ k ∈ Finset.range (n + 1),
        ((k + 1 : 𝕜) * fs (n - k) * ordinaryPointCoeff fs gs w₀ w₁ (k + 1) +
          gs (n - k) * ordinaryPointCoeff fs gs w₀ w₁ k) := by
  have hne : ((n + 2 : 𝕜) * (n + 1 : 𝕜)) ≠ 0 := by
    have h1 : (n + 1 : 𝕜) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have h2 : (n + 2 : 𝕜) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
    exact mul_ne_zero h2 h1
  rw [ordinaryPointCoeff_add_two, mul_neg, mul_inv_cancel_left₀ hne]

/-- Additive homogeneous form of the cleared-denominator recurrence for `ordinaryPointCoeff`. -/
theorem mul_ordinaryPointCoeff_add_two_add_sum_eq_zero [CharZero 𝕜]
    (fs gs : ℕ → 𝕜) (w₀ w₁ : 𝕜) (n : ℕ) :
    (n + 2 : 𝕜) * (n + 1 : 𝕜) * ordinaryPointCoeff fs gs w₀ w₁ (n + 2) +
      ∑ k ∈ Finset.range (n + 1),
        ((k + 1 : 𝕜) * fs (n - k) * ordinaryPointCoeff fs gs w₀ w₁ (k + 1) +
          gs (n - k) * ordinaryPointCoeff fs gs w₀ w₁ k) = 0 := by
  rw [mul_ordinaryPointCoeff_add_two, neg_add_cancel]

/-- **Uniqueness of the formal coefficient sequence.** In characteristic zero, any sequence `a`
with `a 0 = w₀`, `a 1 = w₁`, and satisfying the cleared-denominator recurrence equals
`ordinaryPointCoeff fs gs w₀ w₁`. -/
theorem eq_ordinaryPointCoeff_of_rec [CharZero 𝕜] {fs gs a : ℕ → 𝕜} {w₀ w₁ : 𝕜}
    (ha0 : a 0 = w₀) (ha1 : a 1 = w₁)
    (hrec : ∀ n : ℕ, (n + 2 : 𝕜) * (n + 1 : 𝕜) * a (n + 2) +
      ∑ k ∈ Finset.range (n + 1),
        ((k + 1 : 𝕜) * fs (n - k) * a (k + 1) + gs (n - k) * a k) = 0) :
    a = ordinaryPointCoeff fs gs w₀ w₁ := by
  ext m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    rcases m with _ | _ | n
    · simpa using ha0
    · simpa using ha1
    · have hne : ((n + 2 : 𝕜) * (n + 1 : 𝕜)) ≠ 0 := by
        have h1 : (n + 1 : 𝕜) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        have h2 : (n + 2 : 𝕜) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
        exact mul_ne_zero h2 h1
      have hstep : a (n + 2) = -(((n + 2 : 𝕜) * (n + 1 : 𝕜))⁻¹ *
          ∑ k ∈ Finset.range (n + 1),
            ((k + 1 : 𝕜) * fs (n - k) * a (k + 1) + gs (n - k) * a k)) := by
        rw [← mul_neg, ← eq_neg_of_add_eq_zero_left (hrec n), inv_mul_cancel_left₀ hne]
      rw [hstep, ordinaryPointCoeff_add_two]
      congr 2
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [Finset.mem_range] at hk
      rw [ih (k + 1) (by omega), ih k (by omega)]

/-- Characterization of `ordinaryPointCoeff` in characteristic zero by its initial values and
homogeneous polynomial recurrence. -/
theorem eq_ordinaryPointCoeff_iff [CharZero 𝕜] {fs gs a : ℕ → 𝕜} {w₀ w₁ : 𝕜} :
    a = ordinaryPointCoeff fs gs w₀ w₁ ↔
      a 0 = w₀ ∧ a 1 = w₁ ∧ ∀ n : ℕ, (n + 2 : 𝕜) * (n + 1 : 𝕜) * a (n + 2) +
        ∑ k ∈ Finset.range (n + 1),
          ((k + 1 : 𝕜) * fs (n - k) * a (k + 1) + gs (n - k) * a k) = 0 := by
  constructor
  · rintro rfl
    exact ⟨ordinaryPointCoeff_zero _ _ _ _, ordinaryPointCoeff_one _ _ _ _,
      mul_ordinaryPointCoeff_add_two_add_sum_eq_zero _ _ _ _⟩
  · rintro ⟨ha0, ha1, hrec⟩
    exact eq_ordinaryPointCoeff_of_rec ha0 ha1 hrec

/-- With zero initial data, every Taylor coefficient vanishes. -/
@[simp]
theorem ordinaryPointCoeff_zero_zero (fs gs : ℕ → 𝕜) (n : ℕ) :
    ordinaryPointCoeff fs gs 0 0 n = 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases n with _ | _ | m
    · simp
    · simp
    · rw [ordinaryPointCoeff_add_two]
      suffices ∑ k ∈ Finset.range (m + 1),
          ((k + 1 : 𝕜) * fs (m - k) * ordinaryPointCoeff fs gs 0 0 (k + 1) +
            gs (m - k) * ordinaryPointCoeff fs gs 0 0 k) = 0 by
        simp [this]
      refine Finset.sum_eq_zero fun k hk ↦ ?_
      rw [Finset.mem_range] at hk
      simp [ih (k + 1) (by omega), ih k (by omega)]

/-- Functional form of `ordinaryPointCoeff_zero_zero`. -/
@[simp]
theorem ordinaryPointCoeff_zero_zero_eq (fs gs : ℕ → 𝕜) :
    ordinaryPointCoeff fs gs (0 : 𝕜) 0 = 0 :=
  funext (ordinaryPointCoeff_zero_zero fs gs)

/-- `ordinaryPointCoeff` is additive in the initial data `(w₀, w₁)`. -/
theorem ordinaryPointCoeff_add (fs gs : ℕ → 𝕜) (w₀ w₁ u₀ u₁ : 𝕜) (n : ℕ) :
    ordinaryPointCoeff fs gs (w₀ + u₀) (w₁ + u₁) n =
      ordinaryPointCoeff fs gs w₀ w₁ n + ordinaryPointCoeff fs gs u₀ u₁ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases n with _ | _ | m
    · simp
    · simp
    · rw [ordinaryPointCoeff_add_two, ordinaryPointCoeff_add_two, ordinaryPointCoeff_add_two,
        ← neg_add, ← mul_add, ← Finset.sum_add_distrib]
      congr 2
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [Finset.mem_range] at hk
      rw [ih (k + 1) (by omega), ih k (by omega)]
      ring

/-- `ordinaryPointCoeff` commutes with scalar multiplication of the initial data `(w₀, w₁)`. -/
theorem ordinaryPointCoeff_mul_left (fs gs : ℕ → 𝕜) (c w₀ w₁ : 𝕜) (n : ℕ) :
    ordinaryPointCoeff fs gs (c * w₀) (c * w₁) n =
      c * ordinaryPointCoeff fs gs w₀ w₁ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases n with _ | _ | m
    · simp
    · simp
    · rw [ordinaryPointCoeff_add_two, ordinaryPointCoeff_add_two]
      have hsum : ∑ k ∈ Finset.range (m + 1),
          ((k + 1 : 𝕜) * fs (m - k) * ordinaryPointCoeff fs gs (c * w₀) (c * w₁) (k + 1) +
            gs (m - k) * ordinaryPointCoeff fs gs (c * w₀) (c * w₁) k) =
          c * ∑ k ∈ Finset.range (m + 1),
            ((k + 1 : 𝕜) * fs (m - k) * ordinaryPointCoeff fs gs w₀ w₁ (k + 1) +
              gs (m - k) * ordinaryPointCoeff fs gs w₀ w₁ k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        rw [Finset.mem_range] at hk
        rw [ih (k + 1) (by omega), ih k (by omega)]
        ring
      rw [hsum]
      ring

/-- `ordinaryPointCoeff` commutes with negation of the initial data `(w₀, w₁)`. -/
theorem ordinaryPointCoeff_neg (fs gs : ℕ → 𝕜) (w₀ w₁ : 𝕜) (n : ℕ) :
    ordinaryPointCoeff fs gs (-w₀) (-w₁) n = -ordinaryPointCoeff fs gs w₀ w₁ n := by
  simpa using ordinaryPointCoeff_mul_left fs gs (-1 : 𝕜) w₀ w₁ n

/-- `ordinaryPointCoeff` commutes with subtraction of the initial data `(w₀, w₁)`. -/
theorem ordinaryPointCoeff_sub (fs gs : ℕ → 𝕜) (w₀ w₁ u₀ u₁ : 𝕜) (n : ℕ) :
    ordinaryPointCoeff fs gs (w₀ - u₀) (w₁ - u₁) n =
      ordinaryPointCoeff fs gs w₀ w₁ n - ordinaryPointCoeff fs gs u₀ u₁ n := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ordinaryPointCoeff_add, ordinaryPointCoeff_neg,
    sub_eq_add_neg]

/-- Every formal coefficient sequence decomposes into the two fundamental sequences with initial
data `(1, 0)` and `(0, 1)`. -/
theorem ordinaryPointCoeff_linear_combination (fs gs : ℕ → 𝕜) (w₀ w₁ : 𝕜) (n : ℕ) :
    ordinaryPointCoeff fs gs w₀ w₁ n =
      w₀ * ordinaryPointCoeff fs gs 1 0 n + w₁ * ordinaryPointCoeff fs gs 0 1 n := by
  rw [← ordinaryPointCoeff_mul_left, ← ordinaryPointCoeff_mul_left, ← ordinaryPointCoeff_add]
  simp

/-- The `n`-th coefficient `ordinaryPointCoeff fs gs w₀ w₁ n` depends only on `fs k` and `gs k`
for `k + 2 ≤ n`. -/
theorem ordinaryPointCoeff_congr {fs₁ fs₂ gs₁ gs₂ : ℕ → 𝕜} {w₀ w₁ : 𝕜} {n : ℕ}
    (hfs : ∀ k, k + 2 ≤ n → fs₁ k = fs₂ k)
    (hgs : ∀ k, k + 2 ≤ n → gs₁ k = gs₂ k) :
    ordinaryPointCoeff fs₁ gs₁ w₀ w₁ n = ordinaryPointCoeff fs₂ gs₂ w₀ w₁ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases n with _ | _ | m
    · simp
    · simp
    · rw [ordinaryPointCoeff_add_two, ordinaryPointCoeff_add_two]
      congr 2
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [Finset.mem_range] at hk
      have hk1 : ordinaryPointCoeff fs₁ gs₁ w₀ w₁ (k + 1) =
          ordinaryPointCoeff fs₂ gs₂ w₀ w₁ (k + 1) :=
        ih (k + 1) (by omega) (fun j hj ↦ hfs j (by omega)) (fun j hj ↦ hgs j (by omega))
      have hk0 : ordinaryPointCoeff fs₁ gs₁ w₀ w₁ k =
          ordinaryPointCoeff fs₂ gs₂ w₀ w₁ k :=
        ih k (by omega) (fun j hj ↦ hfs j (by omega)) (fun j hj ↦ hgs j (by omega))
      rw [hk1, hk0, hfs (m - k) (by omega), hgs (m - k) (by omega)]

/-- For `w'' = 0` (`fs = 0`, `gs = 0`), all Taylor coefficients of order at least `2` vanish. -/
theorem ordinaryPointCoeff_zero_coeffs_add_two (w₀ w₁ : 𝕜) (n : ℕ) :
    ordinaryPointCoeff (0 : ℕ → 𝕜) 0 w₀ w₁ (n + 2) = 0 := by
  simp

end Coefficients

/-! ### Cauchy majorant and radius of convergence -/

noncomputable section

section Radius

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Single-step weighted Cauchy estimate for `ordinaryPointCoeff`: if `‖fs m‖ ρ^m ≤ M₁` and
`‖gs m‖ ρ^m ≤ M₂`, then `(n + 2) ‖a_{n + 2}‖ ρ^{n + 2}` is bounded by
`(M₁ ρ + M₂ ρ²) ∑_{j ≤ n + 1} ‖a_j‖ ρ^j`. -/
private theorem mul_norm_ordinaryPointCoeff_add_two_mul_pow_le
    {fs gs : ℕ → 𝕜} {w₀ w₁ : 𝕜} {ρ M₁ M₂ : ℝ} (hρ : 0 ≤ ρ)
    (hfs : ∀ m, ‖fs m‖ * ρ ^ m ≤ M₁) (hgs : ∀ m, ‖gs m‖ * ρ ^ m ≤ M₂) (n : ℕ) :
    (n + 2 : ℝ) * (‖ordinaryPointCoeff fs gs w₀ w₁ (n + 2)‖ * ρ ^ (n + 2)) ≤
      (M₁ * ρ + M₂ * ρ ^ 2) *
        ∑ j ∈ Finset.range (n + 2), ‖ordinaryPointCoeff fs gs w₀ w₁ j‖ * ρ ^ j := by
  let a := ordinaryPointCoeff fs gs w₀ w₁
  let u : ℕ → ℝ := fun j ↦ ‖a j‖ * ρ ^ j
  have hu_nonneg (j : ℕ) : 0 ≤ u j := by positivity
  have : 0 ≤ M₁ := (by positivity : 0 ≤ ‖fs 0‖ * ρ ^ 0).trans (hfs 0)
  have : 0 ≤ M₂ := (by positivity : 0 ≤ ‖gs 0‖ * ρ ^ 0).trans (hgs 0)
  -- Step 1: Bound `‖a (n + 2)‖` from the recurrence via the triangle inequality.
  have hcast1 : ‖(n + 1 : 𝕜)‖ = (n + 1 : ℝ) := by
    rw [← Nat.cast_add_one, RCLike.norm_natCast, Nat.cast_add_one]
  have hcast2 : ‖(n + 2 : 𝕜)‖ = (n + 2 : ℝ) := by
    have heq : (n + 2 : 𝕜) = ((n + 2 : ℕ) : 𝕜) := by push_cast; ring
    rw [heq, RCLike.norm_natCast]
    push_cast; ring
  have hnorm : ‖a (n + 2)‖ ≤ ((n + 2 : ℝ) * (n + 1 : ℝ))⁻¹ *
      ∑ k ∈ Finset.range (n + 1), ((k + 1 : ℝ) * ‖fs (n - k)‖ * ‖a (k + 1)‖ +
        ‖gs (n - k)‖ * ‖a k‖) := by
    dsimp only [a]
    rw [ordinaryPointCoeff_add_two, norm_neg, norm_mul, norm_inv, norm_mul, hcast2, hcast1]
    gcongr
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
    refine (norm_add_le _ _).trans ?_
    have hkcast : ‖(k + 1 : 𝕜)‖ = (k + 1 : ℝ) := by
      rw [← Nat.cast_add_one, RCLike.norm_natCast, Nat.cast_add_one]
    simp only [norm_mul, hkcast, le_rfl]
  -- Step 2: Multiply by `(n + 1)(n + 2) ρ^(n + 2)` and split `ρ^(n + 2)` across each term.
  have hprod : (n + 1 : ℝ) * ((n + 2 : ℝ) * u (n + 2)) ≤
      (n + 1 : ℝ) * ∑ k ∈ Finset.range (n + 1),
        (M₁ * ρ * u (k + 1) + M₂ * ρ ^ 2 * u k) := by
    calc
      (n + 1 : ℝ) * ((n + 2 : ℝ) * u (n + 2))
          = (n + 2 : ℝ) * (n + 1 : ℝ) * ‖a (n + 2)‖ * ρ ^ (n + 2) := by
            dsimp only [u]; ring
      _ ≤ ((n + 2 : ℝ) * (n + 1 : ℝ) * (((n + 2 : ℝ) * (n + 1 : ℝ))⁻¹ *
            ∑ k ∈ Finset.range (n + 1),
              ((k + 1 : ℝ) * ‖fs (n - k)‖ * ‖a (k + 1)‖ +
                ‖gs (n - k)‖ * ‖a k‖))) * ρ ^ (n + 2) := by gcongr
      _ = ∑ k ∈ Finset.range (n + 1),
            (((k + 1 : ℝ) * ‖fs (n - k)‖ * ‖a (k + 1)‖ +
              ‖gs (n - k)‖ * ‖a k‖) * ρ ^ (n + 2)) := by
          have hne : ((n + 2 : ℝ) * (n + 1 : ℝ)) ≠ 0 := by positivity
          rw [mul_inv_cancel_left₀ hne, Finset.sum_mul]
      _ ≤ ∑ k ∈ Finset.range (n + 1),
            ((n + 1 : ℝ) * (M₁ * ρ * u (k + 1) + M₂ * ρ ^ 2 * u k)) := by
          refine Finset.sum_le_sum fun k hk ↦ ?_
          rw [Finset.mem_range] at hk
          have hp1 : ρ ^ (n + 2) = ρ ^ (n - k) * ρ * ρ ^ (k + 1) := by
            calc
              ρ ^ (n + 2) = ρ ^ ((n - k) + 1 + (k + 1)) := by congr 1; omega
              _ = ρ ^ (n - k) * ρ * ρ ^ (k + 1) := by simp [pow_add, pow_one]
          have hp2 : ρ ^ (n + 2) = ρ ^ (n - k) * ρ ^ 2 * ρ ^ k := by
            calc
              ρ ^ (n + 2) = ρ ^ ((n - k) + 2 + k) := by congr 1; omega
              _ = ρ ^ (n - k) * ρ ^ 2 * ρ ^ k := by simp [pow_add]
          have ht1 : (k + 1 : ℝ) * ‖fs (n - k)‖ * ‖a (k + 1)‖ * ρ ^ (n + 2) ≤
              (n + 1 : ℝ) * (M₁ * ρ * u (k + 1)) := by
            rw [hp1]
            calc
              (k + 1 : ℝ) * ‖fs (n - k)‖ * ‖a (k + 1)‖ *
                  (ρ ^ (n - k) * ρ * ρ ^ (k + 1))
                  = (k + 1 : ℝ) * ((‖fs (n - k)‖ * ρ ^ (n - k)) * ρ * u (k + 1)) := by
                    dsimp only [u]; ring
              _ ≤ (n + 1 : ℝ) * (M₁ * ρ * u (k + 1)) := by
                  have hkn : (k + 1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast hk
                  gcongr
                  exact hfs (n - k)
          have ht2 : ‖gs (n - k)‖ * ‖a k‖ * ρ ^ (n + 2) ≤
              (n + 1 : ℝ) * (M₂ * ρ ^ 2 * u k) := by
            rw [hp2]
            calc
              ‖gs (n - k)‖ * ‖a k‖ * (ρ ^ (n - k) * ρ ^ 2 * ρ ^ k)
                  = 1 * ((‖gs (n - k)‖ * ρ ^ (n - k)) * ρ ^ 2 * u k) := by
                    dsimp only [u]; ring
              _ ≤ (n + 1 : ℝ) * (M₂ * ρ ^ 2 * u k) := by
                  have h1n : (1 : ℝ) ≤ (n + 1 : ℝ) := by linarith
                  gcongr
                  exact hgs (n - k)
          linarith
      _ = (n + 1 : ℝ) * ∑ k ∈ Finset.range (n + 1),
            (M₁ * ρ * u (k + 1) + M₂ * ρ ^ 2 * u k) := by
          rw [Finset.mul_sum]
  -- Step 3: Cancel `n + 1 > 0` and enlarge both index ranges to `Finset.range (n + 2)`.
  have hstep := le_of_mul_le_mul_left hprod (by positivity : (0 : ℝ) < n + 1)
  have hsum1 : ∑ k ∈ Finset.range (n + 1), u (k + 1) ≤
      ∑ j ∈ Finset.range (n + 2), u j := by
    rw [Finset.sum_range_succ' u (n + 1)]
    linarith [hu_nonneg 0]
  have hsum0 : ∑ k ∈ Finset.range (n + 1), u k ≤
      ∑ j ∈ Finset.range (n + 2), u j := by
    rw [Finset.sum_range_succ u (n + 1)]
    linarith [hu_nonneg (n + 1)]
  calc
    (n + 2 : ℝ) * u (n + 2)
        ≤ ∑ k ∈ Finset.range (n + 1), (M₁ * ρ * u (k + 1) + M₂ * ρ ^ 2 * u k) := hstep
    _ = M₁ * ρ * (∑ k ∈ Finset.range (n + 1), u (k + 1)) +
          M₂ * ρ ^ 2 * (∑ k ∈ Finset.range (n + 1), u k) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ M₁ * ρ * (∑ j ∈ Finset.range (n + 2), u j) +
          M₂ * ρ ^ 2 * (∑ j ∈ Finset.range (n + 2), u j) := by gcongr
    _ = (M₁ * ρ + M₂ * ρ ^ 2) * ∑ j ∈ Finset.range (n + 2), u j := by ring

/-- If a nonnegative sequence `u` satisfies `(n + 2) u_{n + 2} ≤ K ∑_{j ≤ n + 1} u_j`, then
for every contraction factor `θ ∈ (0, 1)` the rescaled sequence `u_m θ^m` is bounded. -/
private theorem exists_bound_of_step_sum_le {u : ℕ → ℝ} (hu : ∀ j, 0 ≤ u j) {K : ℝ}
    (hstep : ∀ n : ℕ, (n + 2 : ℝ) * u (n + 2) ≤ K * ∑ j ∈ Finset.range (n + 2), u j)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ B : ℝ, ∀ m, u m * θ ^ m ≤ B := by
  let S : ℕ → ℝ := fun m ↦ ∑ j ∈ Finset.range (m + 1), u j
  have hS_nonneg (m : ℕ) : 0 ≤ S m := Finset.sum_nonneg fun j _ ↦ hu j
  have hu_le_S (m : ℕ) : u m ≤ S m :=
    Finset.single_le_sum (fun j _ ↦ hu j) (Finset.mem_range.mpr (Nat.lt_succ_self m))
  -- Choose `N` large enough that `(1 + K / (n + 2)) θ ≤ 1` for all `n ≥ N`.
  have hδ : 0 < θ⁻¹ - 1 := sub_pos.mpr ((one_lt_inv₀ hθ0).mpr hθ1)
  obtain ⟨N, hN⟩ := exists_nat_ge (K / (θ⁻¹ - 1))
  have hmono : ∀ m ≥ N + 1, S m * θ ^ m ≤ S (N + 1) * θ ^ (N + 1) := by
    refine Nat.le_induction le_rfl fun m hm ih ↦ ?_
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hnN : N ≤ n := by omega
    have hSn : S (n + 2) ≤ (1 + K / (n + 2 : ℝ)) * S (n + 1) := by
      have hu_bound : u (n + 2) ≤ K / (n + 2 : ℝ) * S (n + 1) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < n + 2)]
        simpa [S, mul_comm] using hstep n
      calc
        S (n + 2) = S (n + 1) + u (n + 2) := Finset.sum_range_succ u (n + 2)
        _ ≤ S (n + 1) + K / (n + 2 : ℝ) * S (n + 1) := by linarith
        _ = (1 + K / (n + 2 : ℝ)) * S (n + 1) := by ring
    have hratio : (1 + K / (n + 2 : ℝ)) * θ ≤ 1 := by
      have hK_le : K ≤ (θ⁻¹ - 1) * (n + 2 : ℝ) := by
        have h1 : K ≤ (θ⁻¹ - 1) * N := by rwa [div_le_iff₀' hδ] at hN
        have h2 : (N : ℝ) ≤ (n + 2 : ℝ) := by exact_mod_cast (by omega : N ≤ n + 2)
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hδ.le)
      have hdiv : K / (n + 2 : ℝ) ≤ θ⁻¹ - 1 :=
        (div_le_iff₀ (by positivity : (0 : ℝ) < n + 2)).mpr hK_le
      calc
        (1 + K / (n + 2 : ℝ)) * θ ≤ (1 + (θ⁻¹ - 1)) * θ := by gcongr
        _ = 1 := by simp [hθ0.ne']
    calc
      S (n + 2) * θ ^ (n + 2)
          ≤ ((1 + K / (n + 2 : ℝ)) * S (n + 1)) * (θ ^ (n + 1) * θ) := by
            rw [pow_succ]
            gcongr
      _ = ((1 + K / (n + 2 : ℝ)) * θ) * (S (n + 1) * θ ^ (n + 1)) := by ring
      _ ≤ 1 * (S (n + 1) * θ ^ (n + 1)) := by
          gcongr
          exact mul_nonneg (hS_nonneg _) (by positivity)
      _ ≤ S (N + 1) * θ ^ (N + 1) := by linarith
  -- Bound both the finite prefix `m ≤ N + 1` and the tail `m > N + 1` by the prefix sum.
  refine ⟨∑ j ∈ Finset.range (N + 2), S j * θ ^ j, fun m ↦ ?_⟩
  have hum : u m * θ ^ m ≤ S m * θ ^ m := by gcongr; exact hu_le_S m
  refine hum.trans ?_
  by_cases hm : m < N + 2
  · exact Finset.single_le_sum (fun j _ ↦ mul_nonneg (hS_nonneg j) (by positivity))
      (Finset.mem_range.mpr hm)
  · refine (hmono m (by omega)).trans ?_
    exact Finset.single_le_sum (fun j _ ↦ mul_nonneg (hS_nonneg j) (by positivity))
      (Finset.mem_range.mpr (by omega))

/-- **Convergence radius at an ordinary point.** Over `ℝ` or `ℂ`, if the scalar power series
`fs` and `gs` both have radius of convergence at least `r`, then so does
`ordinaryPointCoeff fs gs w₀ w₁` for any initial values `w₀`, `w₁`. -/
theorem le_radius_ofScalars_ordinaryPointCoeff {fs gs : ℕ → 𝕜} {r : ℝ≥0∞}
    (hf : r ≤ (FormalMultilinearSeries.ofScalars 𝕜 fs).radius)
    (hg : r ≤ (FormalMultilinearSeries.ofScalars 𝕜 gs).radius) (w₀ w₁ : 𝕜) :
    r ≤ (FormalMultilinearSeries.ofScalars 𝕜 (ordinaryPointCoeff fs gs w₀ w₁)).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun ρ₀ hρ₀ ↦ ?_
  rcases eq_or_lt_of_le (zero_le : 0 ≤ ρ₀) with rfl | hρ₀_pos
  · simp
  obtain ⟨ρ, hρ₀ρ, hρr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hρ₀
  have hρ₀ρ_real : (ρ₀ : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ₀ρ
  have hρ_pos : (0 : ℝ) < (ρ : ℝ) := lt_trans (by exact_mod_cast hρ₀_pos) hρ₀ρ_real
  obtain ⟨M₁, _, hM₁⟩ :=
    (FormalMultilinearSeries.ofScalars 𝕜 fs).norm_mul_pow_le_of_lt_radius (hρr.trans_le hf)
  obtain ⟨M₂, _, hM₂⟩ :=
    (FormalMultilinearSeries.ofScalars 𝕜 gs).norm_mul_pow_le_of_lt_radius (hρr.trans_le hg)
  have hfs_bound (m : ℕ) : ‖fs m‖ * (ρ : ℝ) ^ m ≤ M₁ := by
    simpa [FormalMultilinearSeries.ofScalars_norm] using hM₁ m
  have hgs_bound (m : ℕ) : ‖gs m‖ * (ρ : ℝ) ^ m ≤ M₂ := by
    simpa [FormalMultilinearSeries.ofScalars_norm] using hM₂ m
  let θ : ℝ := (ρ₀ : ℝ) / (ρ : ℝ)
  have hθ0 : 0 < θ := div_pos (by exact_mod_cast hρ₀_pos) hρ_pos
  have hθ1 : θ < 1 := (div_lt_one hρ_pos).mpr hρ₀ρ_real
  obtain ⟨B, hB⟩ := exists_bound_of_step_sum_le
    (u := fun m ↦ ‖ordinaryPointCoeff fs gs w₀ w₁ m‖ * (ρ : ℝ) ^ m)
    (fun _ ↦ by positivity)
    (mul_norm_ordinaryPointCoeff_add_two_mul_pow_le hρ_pos.le hfs_bound hgs_bound)
    hθ0 hθ1
  refine FormalMultilinearSeries.le_radius_of_bound _ B fun m ↦ ?_
  rw [FormalMultilinearSeries.ofScalars_norm]
  have hθρ : (ρ : ℝ) * θ = (ρ₀ : ℝ) := mul_div_cancel₀ _ hρ_pos.ne'
  calc
    ‖ordinaryPointCoeff fs gs w₀ w₁ m‖ * (ρ₀ : ℝ) ^ m
        = ‖ordinaryPointCoeff fs gs w₀ w₁ m‖ * (ρ : ℝ) ^ m * θ ^ m := by
          rw [← hθρ, mul_pow, mul_assoc]
    _ ≤ B := hB m

/-- If `fs` and `gs` have infinite radius of convergence, then so does
`ordinaryPointCoeff fs gs w₀ w₁`. -/
theorem radius_ofScalars_ordinaryPointCoeff_eq_top {fs gs : ℕ → 𝕜}
    (hf : (FormalMultilinearSeries.ofScalars 𝕜 fs).radius = ⊤)
    (hg : (FormalMultilinearSeries.ofScalars 𝕜 gs).radius = ⊤) (w₀ w₁ : 𝕜) :
    (FormalMultilinearSeries.ofScalars 𝕜 (ordinaryPointCoeff fs gs w₀ w₁)).radius = ⊤ :=
  top_unique <| le_radius_ofScalars_ordinaryPointCoeff (by simp [hf]) (by simp [hg]) w₀ w₁

end Radius

/-! ### Iterated-derivative recurrence and analytic uniqueness -/

section IteratedDeriv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

/-- Normalized `n`-th iterated derivative at `z₀` of `w'' + f w' + g w`: dividing by `n!`
produces the exact algebraic expression equated in the ordinary-point Taylor recurrence. -/
theorem iteratedDeriv_div_factorial_deriv_deriv_add
    {f g w : 𝕜 → 𝕜} {z₀ : 𝕜} (n : ℕ)
    (hf : ContDiffAt 𝕜 n f z₀) (hg : ContDiffAt 𝕜 n g z₀)
    (hw : ContDiffAt 𝕜 ((n + 2 : ℕ) : ℕ∞ω) w z₀) :
    iteratedDeriv n (fun z ↦ deriv (deriv w) z + f z * deriv w z + g z * w z) z₀ /
        (n ! : 𝕜) =
      (n + 2 : 𝕜) * (n + 1 : 𝕜) * (iteratedDeriv (n + 2) w z₀ / ((n + 2)! : 𝕜)) +
        ∑ k ∈ Finset.range (n + 1),
          ((k + 1 : 𝕜) * (iteratedDeriv (n - k) f z₀ / ((n - k)! : 𝕜)) *
              (iteratedDeriv (k + 1) w z₀ / ((k + 1)! : 𝕜)) +
            (iteratedDeriv (n - k) g z₀ / ((n - k)! : 𝕜)) *
              (iteratedDeriv k w z₀ / (k ! : 𝕜))) := by
  -- Step 1: Split `iteratedDeriv n` across the sum and apply Leibniz's rule to `f w'` and `g w`.
  have hw' : ContDiffAt 𝕜 ((n + 1 : ℕ) : ℕ∞ω) (deriv w) z₀ :=
    hw.derivWithin (by exact_mod_cast le_rfl)
  have hw'' : ContDiffAt 𝕜 n (deriv (deriv w)) z₀ :=
    hw'.derivWithin (by exact_mod_cast le_rfl)
  have hw_n : ContDiffAt 𝕜 n w z₀ := hw.of_le (by exact_mod_cast Nat.le_add_right n 2)
  have hw'_n : ContDiffAt 𝕜 n (deriv w) z₀ := hw'.of_le (by exact_mod_cast Nat.le_succ n)
  have h1 : iteratedDeriv n (fun z ↦ deriv (deriv w) z + f z * deriv w z + g z * w z) z₀ =
      iteratedDeriv n (deriv (deriv w)) z₀ +
        iteratedDeriv n (f * deriv w) z₀ + iteratedDeriv n (g * w) z₀ := by
    have ha1 := iteratedDeriv_add (f := deriv (deriv w) + f * deriv w) (g := g * w)
      (hw''.add (hf.mul hw'_n)) (hg.mul hw_n)
    have ha2 := iteratedDeriv_add (f := deriv (deriv w)) (g := f * deriv w)
      hw'' (hf.mul hw'_n)
    exact ha1.trans (congrArg (· + iteratedDeriv n (g * w) z₀) ha2)
  rw [h1, iteratedDeriv_mul hf hw'_n, iteratedDeriv_mul hg hw_n]
  -- Step 2: Reindex the binomial sums via `sum_range_reflect` and clear `n!`.
  have hd2 : iteratedDeriv n (deriv (deriv w)) z₀ = iteratedDeriv (n + 2) w z₀ := by
    rw [← iteratedDeriv_succ', ← iteratedDeriv_succ']
  rw [hd2, ← Finset.sum_range_reflect (fun i ↦ (n.choose i : 𝕜) * iteratedDeriv i f z₀ *
      iteratedDeriv (n - i) (deriv w) z₀),
    ← Finset.sum_range_reflect (fun i ↦ (n.choose i : 𝕜) * iteratedDeriv i g z₀ *
      iteratedDeriv (n - i) w z₀)]
  simp only [Nat.add_sub_cancel]
  have hnfac : (n ! : 𝕜) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [div_eq_iff hnfac, add_assoc, ← Finset.sum_add_distrib, add_mul, Finset.sum_mul]
  congr 1
  · have hfac2 : ((n + 2)! : 𝕜) = (n + 2 : 𝕜) * (n + 1 : 𝕜) * (n ! : 𝕜) := by
      simp only [Nat.factorial_succ]; push_cast; ring
    have hn1 : (n + 1 : 𝕜) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hn2 : (n + 2 : 𝕜) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
    rw [hfac2]
    field_simp [hnfac, hn1, hn2]
  · refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [Finset.mem_range] at hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp hk
    have hsub : n - (n - k) = k := Nat.sub_sub_self hkn
    have hchoose : (n.choose (n - k) : 𝕜) * ((n - k)! : 𝕜) * (k ! : 𝕜) = (n ! : 𝕜) := by
      rw [Nat.choose_symm hkn, mul_right_comm]
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
    have hkfac : (k ! : 𝕜) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hnkfac : ((n - k)! : 𝕜) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - k)
    have hk1 : (k + 1 : 𝕜) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hk1fac : ((k + 1)! : 𝕜) = (k + 1 : 𝕜) * (k ! : 𝕜) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hd1 : iteratedDeriv k (deriv w) z₀ = iteratedDeriv (k + 1) w z₀ := by
      rw [iteratedDeriv_succ']
    rw [hsub, hd1, hk1fac, ← hchoose]
    field_simp [hkfac, hnkfac, hk1]

/-- **Local Taylor-coefficient determination.** Any `C^∞` local solution of
`w'' + f w' + g w = 0` near `z₀` (with `f`, `g` also `C^∞` at `z₀`) has normalized Taylor
coefficients `iteratedDeriv n w z₀ / n!` equal to `ordinaryPointCoeff`. -/
theorem iteratedDeriv_div_factorial_eq_ordinaryPointCoeff
    {f g w : 𝕜 → 𝕜} {z₀ : 𝕜}
    (hf : ContDiffAt 𝕜 ∞ f z₀) (hg : ContDiffAt 𝕜 ∞ g z₀)
    (hw : ContDiffAt 𝕜 ∞ w z₀)
    (hode : ∀ᶠ z in 𝓝 z₀, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) (n : ℕ) :
    iteratedDeriv n w z₀ / (n ! : 𝕜) =
      ordinaryPointCoeff
        (fun k ↦ iteratedDeriv k f z₀ / (k ! : 𝕜))
        (fun k ↦ iteratedDeriv k g z₀ / (k ! : 𝕜))
        (w z₀) (deriv w z₀) n := by
  have hall : (fun k ↦ iteratedDeriv k w z₀ / (k ! : 𝕜)) =
      ordinaryPointCoeff
        (fun k ↦ iteratedDeriv k f z₀ / (k ! : 𝕜))
        (fun k ↦ iteratedDeriv k g z₀ / (k ! : 𝕜))
        (w z₀) (deriv w z₀) := by
    refine eq_ordinaryPointCoeff_of_rec (by simp) (by simp) fun m ↦ ?_
    have hzero : iteratedDeriv m
        (fun z ↦ deriv (deriv w) z + f z * deriv w z + g z * w z) z₀ = 0 := by
      have heq : (fun z ↦ deriv (deriv w) z + f z * deriv w z + g z * w z) =ᶠ[𝓝 z₀]
          (fun _ : 𝕜 ↦ (0 : 𝕜)) := hode
      rw [heq.iteratedDeriv_eq, iteratedDeriv_fun_const_zero]
    have hid := iteratedDeriv_div_factorial_deriv_deriv_add m
      (contDiffAt_infty.mp hf m)
      (contDiffAt_infty.mp hg m)
      (contDiffAt_infty.mp hw (m + 2))
    rwa [hzero, zero_div, eq_comm] at hid
  exact congrFun hall n

/-- **Analytic uniqueness on preconnected domains.** Over any complete nontrivially normed field
of characteristic zero, two analytic functions on a preconnected set `U` containing `z₀` that
solve `w'' + f w' + g w = 0` near `z₀` (with `f`, `g` smooth at `z₀`) and share the same value
and first derivative at `z₀` agree throughout `U`. -/
theorem eqOn_of_analyticOnNhd_of_deriv_deriv_add_eq_zero [CompleteSpace 𝕜]
    {f g w₁ w₂ : 𝕜 → 𝕜} {U : Set 𝕜} {z₀ : 𝕜}
    (hU : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hf : ContDiffAt 𝕜 ∞ f z₀) (hg : ContDiffAt 𝕜 ∞ g z₀)
    (hw₁ : AnalyticOnNhd 𝕜 w₁ U) (hw₂ : AnalyticOnNhd 𝕜 w₂ U)
    (hode₁ : ∀ᶠ z in 𝓝 z₀, deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z = 0)
    (hode₂ : ∀ᶠ z in 𝓝 z₀, deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z = 0)
    (h0 : w₁ z₀ = w₂ z₀) (h1 : deriv w₁ z₀ = deriv w₂ z₀) :
    EqOn w₁ w₂ U := by
  have hp₁ := (hw₁ z₀ hz₀).hasFPowerSeriesAt
  have hp₂ := (hw₂ z₀ hz₀).hasFPowerSeriesAt
  have hseries :
      FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ iteratedDeriv n w₁ z₀ / (n ! : 𝕜)) =
        FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ iteratedDeriv n w₂ z₀ / (n ! : 𝕜)) := by
    congr 1; ext n
    rw [iteratedDeriv_div_factorial_eq_ordinaryPointCoeff hf hg (hw₁ z₀ hz₀).contDiffAt hode₁,
      iteratedDeriv_div_factorial_eq_ordinaryPointCoeff hf hg (hw₂ z₀ hz₀).contDiffAt hode₂,
      h0, h1]
  rw [hseries] at hp₁
  have hev : w₁ =ᶠ[𝓝 z₀] w₂ := by
    have hsub : HasFPowerSeriesAt (w₁ - w₂) (0 : FormalMultilinearSeries 𝕜 𝕜 𝕜) z₀ := by
      simpa using hp₁.sub hp₂
    filter_upwards [hsub.eventually_eq_zero] with z hz
    exact sub_eq_zero.mp hz
  exact hw₁.eqOn_of_preconnected_of_eventuallyEq hw₂ hU hz₀ hev

/-- **Analytic fundamental-pair expansion on preconnected sets.** Over any complete nontrivially
normed field of characteristic zero, let `u`, `v`, and `w` be analytic on a preconnected set `U`
containing `z₀` and solve `w'' + f w' + g w = 0` near `z₀` (with `f`, `g` smooth at `z₀`). If the
Wronskian `u(z₀) v'(z₀) - u'(z₀) v(z₀)` is nonzero, then `w` is expressed throughout `U` by
Cramer's rule in terms of `u` and `v`. -/
theorem eqOn_linear_combination_of_analyticOnNhd_of_wronskian_ne_zero [CompleteSpace 𝕜]
    {f g u v w : 𝕜 → 𝕜} {U : Set 𝕜} {z₀ : 𝕜}
    (hU : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hf : ContDiffAt 𝕜 ∞ f z₀) (hg : ContDiffAt 𝕜 ∞ g z₀)
    (hu : AnalyticOnNhd 𝕜 u U) (hv : AnalyticOnNhd 𝕜 v U) (hw : AnalyticOnNhd 𝕜 w U)
    (hu_ode : ∀ᶠ z in 𝓝 z₀, deriv (deriv u) z + f z * deriv u z + g z * u z = 0)
    (hv_ode : ∀ᶠ z in 𝓝 z₀, deriv (deriv v) z + f z * deriv v z + g z * v z = 0)
    (hw_ode : ∀ᶠ z in 𝓝 z₀, deriv (deriv w) z + f z * deriv w z + g z * w z = 0)
    (hW : u z₀ * deriv v z₀ - deriv u z₀ * v z₀ ≠ 0) :
    EqOn w
      (fun z ↦
        ((w z₀ * deriv v z₀ - deriv w z₀ * v z₀) /
            (u z₀ * deriv v z₀ - deriv u z₀ * v z₀)) * u z +
          ((deriv w z₀ * u z₀ - w z₀ * deriv u z₀) /
            (u z₀ * deriv v z₀ - deriv u z₀ * v z₀)) * v z) U := by
  let W₀ := u z₀ * deriv v z₀ - deriv u z₀ * v z₀
  have hW₀ : W₀ ≠ 0 := hW
  let c₁ := (w z₀ * deriv v z₀ - deriv w z₀ * v z₀) / W₀
  let c₂ := (deriv w z₀ * u z₀ - w z₀ * deriv u z₀) / W₀
  let L : 𝕜 → 𝕜 := fun z ↦ c₁ * u z + c₂ * v z
  have hL_an : AnalyticOnNhd 𝕜 L U :=
    (analyticOnNhd_const.mul hu).add (analyticOnNhd_const.mul hv)
  have hL_deriv_ev : deriv L =ᶠ[𝓝 z₀] fun z ↦ c₁ * deriv u z + c₂ * deriv v z := by
    filter_upwards [(hu z₀ hz₀).eventually_analyticAt, (hv z₀ hz₀).eventually_analyticAt]
      with z huz hvz
    exact (HasDerivAt.add (huz.differentiableAt.hasDerivAt.const_mul c₁)
      (hvz.differentiableAt.hasDerivAt.const_mul c₂)).deriv
  have hL_ode : ∀ᶠ z in 𝓝 z₀, deriv (deriv L) z + f z * deriv L z + g z * L z = 0 := by
    filter_upwards [hL_deriv_ev, hL_deriv_ev.eventually_nhds,
      (hu z₀ hz₀).deriv.eventually_analyticAt, (hv z₀ hz₀).deriv.eventually_analyticAt,
      hu_ode, hv_ode] with z hLz hLz_nhds hu'z hv'z huz_ode hvz_ode
    have hdL' : HasDerivAt (fun ζ ↦ c₁ * deriv u ζ + c₂ * deriv v ζ)
        (c₁ * deriv (deriv u) z + c₂ * deriv (deriv v) z) z :=
      HasDerivAt.add (hu'z.differentiableAt.hasDerivAt.const_mul c₁)
        (hv'z.differentiableAt.hasDerivAt.const_mul c₂)
    rw [Filter.EventuallyEq.deriv_eq hLz_nhds, hdL'.deriv, hLz]
    dsimp only [L]
    linear_combination c₁ * huz_ode + c₂ * hvz_ode
  change EqOn w L U
  refine eqOn_of_analyticOnNhd_of_deriv_deriv_add_eq_zero
    hU hz₀ hf hg hw hL_an hw_ode hL_ode ?_ ?_
  · dsimp only [L, c₁, c₂]
    field_simp [hW₀]
    dsimp only [W₀]
    ring
  · rw [hL_deriv_ev.self_of_nhds]
    dsimp only [c₁, c₂]
    field_simp [hW₀]
    dsimp only [W₀]
    ring

end IteratedDeriv

/-! ### Analytic Taylor-series solutions over `ℝ` and `ℂ` -/

section AnalyticSolution

variable {𝕜 : Type*} [RCLike 𝕜]

/-- If `f : 𝕜 → 𝕜` has scalar power series `fs` around `z₀`, then `fs n` is the normalized
iterated derivative `iteratedDeriv n f z₀ / n!`. -/
private theorem coeff_eq_iteratedDeriv_div_factorial_of_hasFPowerSeriesAt
    {f : 𝕜 → 𝕜} {fs : ℕ → 𝕜} {z₀ : 𝕜}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars 𝕜 fs) z₀) (n : ℕ) :
    fs n = iteratedDeriv n f z₀ / (n ! : 𝕜) := by
  have heq := hf.eq_formalMultilinearSeries hf.analyticAt.hasFPowerSeriesAt
  simpa using congrArg (fun p ↦ p.coeff n) heq

/-- **Characterization of scalar power-series solutions on a ball.** Over `ℝ` or `ℂ`, let `f`,
`g`, and `w` be represented on `Metric.eball z₀ r` by scalar power series `fs`, `gs`, and `a`.
Then `w` solves `w'' + f w' + g w = 0` throughout `Metric.eball z₀ r` if and only if `a` equals
`ordinaryPointCoeff fs gs (w z₀) (deriv w z₀)`. -/
theorem forall_mem_eball_deriv_deriv_add_eq_zero_iff
    {f g w : 𝕜 → 𝕜} {fs gs a : ℕ → 𝕜} {z₀ : 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars 𝕜 fs) z₀ r)
    (hg : HasFPowerSeriesOnBall g (FormalMultilinearSeries.ofScalars 𝕜 gs) z₀ r)
    (hw : HasFPowerSeriesOnBall w (FormalMultilinearSeries.ofScalars 𝕜 a) z₀ r) :
    (∀ z ∈ Metric.eball z₀ r, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) ↔
      a = ordinaryPointCoeff fs gs (w z₀) (deriv w z₀) := by
  have hfs_eq : fs = fun k ↦ iteratedDeriv k f z₀ / (k ! : 𝕜) :=
    funext (coeff_eq_iteratedDeriv_div_factorial_of_hasFPowerSeriesAt hf.hasFPowerSeriesAt)
  have hgs_eq : gs = fun k ↦ iteratedDeriv k g z₀ / (k ! : 𝕜) :=
    funext (coeff_eq_iteratedDeriv_div_factorial_of_hasFPowerSeriesAt hg.hasFPowerSeriesAt)
  have ha_eq : a = fun k ↦ iteratedDeriv k w z₀ / (k ! : 𝕜) :=
    funext (coeff_eq_iteratedDeriv_div_factorial_of_hasFPowerSeriesAt hw.hasFPowerSeriesAt)
  constructor
  · intro hode
    have hev : ∀ᶠ z in 𝓝 z₀, deriv (deriv w) z + f z * deriv w z + g z * w z = 0 := by
      filter_upwards [Metric.eball_mem_nhds z₀ hw.r_pos] with z hz using hode z hz
    rw [hfs_eq, hgs_eq, ha_eq]
    ext n
    exact iteratedDeriv_div_factorial_eq_ordinaryPointCoeff
      hf.analyticAt.contDiffAt hg.analyticAt.contDiffAt hw.analyticAt.contDiffAt hev n
  · intro ha z hz
    let L : 𝕜 → 𝕜 := fun ζ ↦ deriv (deriv w) ζ + f ζ * deriv w ζ + g ζ * w ζ
    have hL_an : AnalyticOnNhd 𝕜 L (Metric.eball z₀ r) :=
      (hw.analyticOnNhd.deriv.deriv.add (hf.analyticOnNhd.mul hw.analyticOnNhd.deriv)).add
        (hg.analyticOnNhd.mul hw.analyticOnNhd)
    have hL_deriv (n : ℕ) : iteratedDeriv n L z₀ / (n ! : 𝕜) = 0 := by
      have hid := iteratedDeriv_div_factorial_deriv_deriv_add n
        hf.analyticAt.contDiffAt hg.analyticAt.contDiffAt hw.analyticAt.contDiffAt
      have hrec := (eq_ordinaryPointCoeff_iff.mp ha).2.2 n
      rw [hfs_eq, hgs_eq, ha_eq] at hrec
      rwa [hrec] at hid
    have hz₀ : z₀ ∈ Metric.eball z₀ r := Metric.mem_eball_self hw.r_pos
    have hL_zero : HasFPowerSeriesAt L (0 : FormalMultilinearSeries 𝕜 𝕜 𝕜) z₀ := by
      have h0 : (fun n ↦ iteratedDeriv n L z₀ / (n ! : 𝕜)) = 0 := funext hL_deriv
      simpa [h0] using (hL_an z₀ hz₀).hasFPowerSeriesAt
    exact hL_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_eball z₀ r).isPreconnected hz₀ hL_zero.eventually_eq_zero hz

/-- The analytic Taylor-series solution around an ordinary point `z₀` of `w'' + f w' + g w = 0`
with initial values `w(z₀) = w₀` and `w'(z₀) = w₁`, defined as the sum of the formal Taylor series
around `z₀` determined by the normalized iterated derivatives of `f` and `g` at `z₀`. -/
def ordinaryPointSolution (f g : 𝕜 → 𝕜) (z₀ w₀ w₁ z : 𝕜) : 𝕜 :=
  FormalMultilinearSeries.ofScalarsSum
    (ordinaryPointCoeff
      (fun n ↦ iteratedDeriv n f z₀ / (n ! : 𝕜))
      (fun n ↦ iteratedDeriv n g z₀ / (n ! : 𝕜)) w₀ w₁)
    (z - z₀)

/-- Defining formula for `ordinaryPointSolution` in terms of `ofScalarsSum` and
`ordinaryPointCoeff`. -/
theorem ordinaryPointSolution_def (f g : 𝕜 → 𝕜) (z₀ w₀ w₁ z : 𝕜) :
    ordinaryPointSolution f g z₀ w₀ w₁ z =
      FormalMultilinearSeries.ofScalarsSum
        (ordinaryPointCoeff
          (fun n ↦ iteratedDeriv n f z₀ / (n ! : 𝕜))
          (fun n ↦ iteratedDeriv n g z₀ / (n ! : 𝕜)) w₀ w₁)
        (z - z₀) := (rfl)

/-- At the expansion center `z₀`, `ordinaryPointSolution` evaluates to `w₀`. -/
@[simp]
theorem ordinaryPointSolution_self (f g : 𝕜 → 𝕜) (z₀ w₀ w₁ : 𝕜) :
    ordinaryPointSolution f g z₀ w₀ w₁ z₀ = w₀ := by
  simp [ordinaryPointSolution]

/-- With zero initial values `w₀ = 0` and `w₁ = 0`, `ordinaryPointSolution` vanishes
identically. -/
@[simp]
theorem ordinaryPointSolution_zero_zero (f g : 𝕜 → 𝕜) (z₀ z : 𝕜) :
    ordinaryPointSolution f g z₀ 0 0 z = 0 := by
  simp [ordinaryPointSolution, FormalMultilinearSeries.ofScalarsSum_eq_tsum]

/-- `ordinaryPointSolution` commutes with scalar multiplication of the initial data `(w₀, w₁)`. -/
theorem ordinaryPointSolution_mul_left (f g : 𝕜 → 𝕜) (c z₀ w₀ w₁ z : 𝕜) :
    ordinaryPointSolution f g z₀ (c * w₀) (c * w₁) z =
      c * ordinaryPointSolution f g z₀ w₀ w₁ z := by
  simp only [ordinaryPointSolution_def, FormalMultilinearSeries.ofScalarsSum_eq_tsum, smul_eq_mul,
    ordinaryPointCoeff_mul_left, mul_assoc, tsum_mul_left]

/-- `ordinaryPointSolution` commutes with negation of the initial data `(w₀, w₁)`. -/
theorem ordinaryPointSolution_neg (f g : 𝕜 → 𝕜) (z₀ w₀ w₁ z : 𝕜) :
    ordinaryPointSolution f g z₀ (-w₀) (-w₁) z =
      -ordinaryPointSolution f g z₀ w₀ w₁ z := by
  simpa using ordinaryPointSolution_mul_left f g (-1 : 𝕜) z₀ w₀ w₁ z

/-- **Power-series representation on an extended ball.** Over `ℝ` or `ℂ`, if `f` and `g` are
represented on `Metric.eball z₀ r` by scalar power series `fs` and `gs`, then
`ordinaryPointSolution f g z₀ w₀ w₁` is represented on the whole ball `Metric.eball z₀ r` by
`ordinaryPointCoeff fs gs w₀ w₁`. -/
theorem hasFPowerSeriesOnBall_ordinaryPointSolution_of_hasFPowerSeriesOnBall
    {f g : 𝕜 → 𝕜} {fs gs : ℕ → 𝕜} {z₀ : 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars 𝕜 fs) z₀ r)
    (hg : HasFPowerSeriesOnBall g (FormalMultilinearSeries.ofScalars 𝕜 gs) z₀ r)
    (w₀ w₁ : 𝕜) :
    HasFPowerSeriesOnBall (ordinaryPointSolution f g z₀ w₀ w₁)
      (FormalMultilinearSeries.ofScalars 𝕜 (ordinaryPointCoeff fs gs w₀ w₁)) z₀ r := by
  have hfs_eq : fs = fun n ↦ iteratedDeriv n f z₀ / (n ! : 𝕜) :=
    funext (coeff_eq_iteratedDeriv_div_factorial_of_hasFPowerSeriesAt hf.hasFPowerSeriesAt)
  have hgs_eq : gs = fun n ↦ iteratedDeriv n g z₀ / (n ! : 𝕜) :=
    funext (coeff_eq_iteratedDeriv_div_factorial_of_hasFPowerSeriesAt hg.hasFPowerSeriesAt)
  subst hfs_eq hgs_eq
  have hrad := le_radius_ofScalars_ordinaryPointCoeff hf.r_le hg.r_le w₀ w₁
  have h0 := (((FormalMultilinearSeries.ofScalars 𝕜
      (ordinaryPointCoeff (fun n ↦ iteratedDeriv n f z₀ / (n ! : 𝕜))
        (fun n ↦ iteratedDeriv n g z₀ / (n ! : 𝕜)) w₀ w₁)).hasFPowerSeriesOnBall
      (hf.r_pos.trans_le hrad)).mono hf.r_pos hrad).comp_sub z₀
  rw [zero_add] at h0
  exact h0

/-- If `f` and `g` are analytic at `z₀`, then `ordinaryPointSolution f g z₀ w₀ w₁` has local
power-series representation `ordinaryPointCoeff` at `z₀`. -/
theorem hasFPowerSeriesAt_ordinaryPointSolution
    {f g : 𝕜 → 𝕜} {z₀ : 𝕜} (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
    (w₀ w₁ : 𝕜) :
    HasFPowerSeriesAt (ordinaryPointSolution f g z₀ w₀ w₁)
      (FormalMultilinearSeries.ofScalars 𝕜
        (ordinaryPointCoeff
          (fun n ↦ iteratedDeriv n f z₀ / (n ! : 𝕜))
          (fun n ↦ iteratedDeriv n g z₀ / (n ! : 𝕜)) w₀ w₁)) z₀ := by
  obtain ⟨r₁, hr₁⟩ := hf.hasFPowerSeriesAt
  obtain ⟨r₂, hr₂⟩ := hg.hasFPowerSeriesAt
  have hr_pos : 0 < min r₁ r₂ := lt_min hr₁.r_pos hr₂.r_pos
  exact (hasFPowerSeriesOnBall_ordinaryPointSolution_of_hasFPowerSeriesOnBall
    (hr₁.mono hr_pos (min_le_left _ _))
    (hr₂.mono hr_pos (min_le_right _ _)) w₀ w₁).hasFPowerSeriesAt

/-- If `f` and `g` are analytic at `z₀`, then `ordinaryPointSolution f g z₀ w₀ w₁` is analytic at
`z₀`. -/
theorem analyticAt_ordinaryPointSolution
    {f g : 𝕜 → 𝕜} {z₀ : 𝕜} (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
    (w₀ w₁ : 𝕜) :
    AnalyticAt 𝕜 (ordinaryPointSolution f g z₀ w₀ w₁) z₀ :=
  (hasFPowerSeriesAt_ordinaryPointSolution hf hg w₀ w₁).analyticAt

/-- If `f` and `g` are analytic at `z₀`, the normalized `n`-th derivative of
`ordinaryPointSolution f g z₀ w₀ w₁` at `z₀` recovers `ordinaryPointCoeff`. -/
theorem iteratedDeriv_ordinaryPointSolution_div_factorial
    {f g : 𝕜 → 𝕜} {z₀ : 𝕜} (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
    (w₀ w₁ : 𝕜) (n : ℕ) :
    iteratedDeriv n (ordinaryPointSolution f g z₀ w₀ w₁) z₀ / (n ! : 𝕜) =
      ordinaryPointCoeff
        (fun k ↦ iteratedDeriv k f z₀ / (k ! : 𝕜))
        (fun k ↦ iteratedDeriv k g z₀ / (k ! : 𝕜)) w₀ w₁ n :=
  (coeff_eq_iteratedDeriv_div_factorial_of_hasFPowerSeriesAt
    (hasFPowerSeriesAt_ordinaryPointSolution hf hg w₀ w₁) n).symm

/-- If `f` and `g` are analytic at `z₀`, then the first derivative of
`ordinaryPointSolution f g z₀ w₀ w₁` at `z₀` is `w₁`. -/
theorem deriv_ordinaryPointSolution_self
    {f g : 𝕜 → 𝕜} {z₀ : 𝕜} (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
    (w₀ w₁ : 𝕜) :
    deriv (ordinaryPointSolution f g z₀ w₀ w₁) z₀ = w₁ := by
  simpa [iteratedDeriv_one] using iteratedDeriv_ordinaryPointSolution_div_factorial hf hg w₀ w₁ 1

/-- Over `ℝ` or `ℂ`, if `f` and `g` are represented on `Metric.eball z₀ r` by scalar power series,
then `ordinaryPointSolution f g z₀ w₀ w₁` solves `w'' + f w' + g w = 0` throughout
`Metric.eball z₀ r`. -/
theorem deriv_deriv_ordinaryPointSolution_of_hasFPowerSeriesOnBall
    {f g : 𝕜 → 𝕜} {fs gs : ℕ → 𝕜} {z₀ : 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars 𝕜 fs) z₀ r)
    (hg : HasFPowerSeriesOnBall g (FormalMultilinearSeries.ofScalars 𝕜 gs) z₀ r)
    (w₀ w₁ : 𝕜) {z : 𝕜} (hz : z ∈ Metric.eball z₀ r) :
    deriv (deriv (ordinaryPointSolution f g z₀ w₀ w₁)) z +
      f z * deriv (ordinaryPointSolution f g z₀ w₀ w₁) z +
      g z * ordinaryPointSolution f g z₀ w₀ w₁ z = 0 := by
  have hw := hasFPowerSeriesOnBall_ordinaryPointSolution_of_hasFPowerSeriesOnBall hf hg w₀ w₁
  refine (forall_mem_eball_deriv_deriv_add_eq_zero_iff hf hg hw).mpr ?_ z hz
  rw [ordinaryPointSolution_self, deriv_ordinaryPointSolution_self hf.analyticAt hg.analyticAt]

/-- Over `ℝ` or `ℂ`, if `f` and `g` are represented on `Metric.eball z₀ r` by scalar power series
`fs` and `gs`, then the Taylor series with coefficients `ordinaryPointCoeff fs gs w₀ w₁` converges
pointwise (`HasSum`) to `ordinaryPointSolution f g z₀ w₀ w₁ z` throughout `Metric.eball z₀ r`. -/
theorem hasSum_ordinaryPointSolution_of_hasFPowerSeriesOnBall
    {f g : 𝕜 → 𝕜} {fs gs : ℕ → 𝕜} {z₀ : 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars 𝕜 fs) z₀ r)
    (hg : HasFPowerSeriesOnBall g (FormalMultilinearSeries.ofScalars 𝕜 gs) z₀ r)
    {z : 𝕜} (hz : z ∈ Metric.eball z₀ r) (w₀ w₁ : 𝕜) :
    HasSum (fun n ↦ ordinaryPointCoeff fs gs w₀ w₁ n * (z - z₀) ^ n)
      (ordinaryPointSolution f g z₀ w₀ w₁ z) := by
  refine ((hasFPowerSeriesOnBall_ordinaryPointSolution_of_hasFPowerSeriesOnBall
    hf hg w₀ w₁).hasSum_sub hz).congr_fun fun n ↦ ?_
  rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-- Over `ℝ` or `ℂ`, on a ball `Metric.eball z₀ r` where `f` and `g` have scalar power-series
expansions, `ordinaryPointSolution` is additive in the initial data `(w₀, w₁)`. -/
theorem ordinaryPointSolution_add_of_hasFPowerSeriesOnBall
    {f g : 𝕜 → 𝕜} {fs gs : ℕ → 𝕜} {z₀ : 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars 𝕜 fs) z₀ r)
    (hg : HasFPowerSeriesOnBall g (FormalMultilinearSeries.ofScalars 𝕜 gs) z₀ r)
    (w₀ w₁ u₀ u₁ : 𝕜) {z : 𝕜} (hz : z ∈ Metric.eball z₀ r) :
    ordinaryPointSolution f g z₀ (w₀ + u₀) (w₁ + u₁) z =
      ordinaryPointSolution f g z₀ w₀ w₁ z + ordinaryPointSolution f g z₀ u₀ u₁ z := by
  have hsum := (hasSum_ordinaryPointSolution_of_hasFPowerSeriesOnBall hf hg hz w₀ w₁).add
    (hasSum_ordinaryPointSolution_of_hasFPowerSeriesOnBall hf hg hz u₀ u₁)
  refine (hasSum_ordinaryPointSolution_of_hasFPowerSeriesOnBall hf hg hz
    (w₀ + u₀) (w₁ + u₁)).unique (hsum.congr_fun fun n ↦ ?_)
  rw [ordinaryPointCoeff_add, add_mul]

/-- Over `ℝ` or `ℂ`, on a ball `Metric.eball z₀ r` where `f` and `g` have scalar power-series
expansions, `ordinaryPointSolution f g z₀ w₀ w₁` decomposes into the canonical fundamental
solutions with initial data `(1, 0)` and `(0, 1)`. -/
theorem ordinaryPointSolution_linear_combination_of_hasFPowerSeriesOnBall
    {f g : 𝕜 → 𝕜} {fs gs : ℕ → 𝕜} {z₀ : 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars 𝕜 fs) z₀ r)
    (hg : HasFPowerSeriesOnBall g (FormalMultilinearSeries.ofScalars 𝕜 gs) z₀ r)
    (w₀ w₁ : 𝕜) {z : 𝕜} (hz : z ∈ Metric.eball z₀ r) :
    ordinaryPointSolution f g z₀ w₀ w₁ z =
      w₀ * ordinaryPointSolution f g z₀ 1 0 z + w₁ * ordinaryPointSolution f g z₀ 0 1 z := by
  rw [← ordinaryPointSolution_mul_left, ← ordinaryPointSolution_mul_left,
    ← ordinaryPointSolution_add_of_hasFPowerSeriesOnBall hf hg _ _ _ _ hz]
  simp

end AnalyticSolution

/-! ### Holomorphic solutions in the complex plane -/

section Complex

/-- **Power-series representation on a disc where `f` and `g` are holomorphic.** If `f` and `g`
are holomorphic on `Metric.eball z₀ r` (`0 < r ≤ ∞`), then
`ordinaryPointSolution f g z₀ w₀ w₁` has `HasFPowerSeriesOnBall` on the whole disc
`Metric.eball z₀ r`. -/
theorem hasFPowerSeriesOnBall_ordinaryPointSolution
    {f g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (Metric.eball z₀ r))
    (hg : DifferentiableOn ℂ g (Metric.eball z₀ r)) (hr : 0 < r) (w₀ w₁ : ℂ) :
    HasFPowerSeriesOnBall (ordinaryPointSolution f g z₀ w₀ w₁)
      (FormalMultilinearSeries.ofScalars ℂ
        (ordinaryPointCoeff
          (fun n ↦ iteratedDeriv n f z₀ / (n ! : ℂ))
          (fun n ↦ iteratedDeriv n g z₀ / (n ! : ℂ)) w₀ w₁)) z₀ r :=
  hasFPowerSeriesOnBall_ordinaryPointSolution_of_hasFPowerSeriesOnBall
    (hf.hasFPowerSeriesOnBall_ofScalars hr) (hg.hasFPowerSeriesOnBall_ofScalars hr) w₀ w₁

/-- On `Metric.eball z₀ r` (`0 < r`), the Taylor series with coefficients `ordinaryPointCoeff`
converges pointwise (`HasSum`) to `ordinaryPointSolution f g z₀ w₀ w₁ z`. -/
theorem hasSum_ordinaryPointSolution
    {f g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (Metric.eball z₀ r))
    (hg : DifferentiableOn ℂ g (Metric.eball z₀ r))
    {z : ℂ} (hz : z ∈ Metric.eball z₀ r) (w₀ w₁ : ℂ) :
    HasSum (fun n ↦
      ordinaryPointCoeff
        (fun k ↦ iteratedDeriv k f z₀ / (k ! : ℂ))
        (fun k ↦ iteratedDeriv k g z₀ / (k ! : ℂ)) w₀ w₁ n * (z - z₀) ^ n)
      (ordinaryPointSolution f g z₀ w₀ w₁ z) := by
  have hr : 0 < r := (zero_le : (0 : ℝ≥0∞) ≤ edist z z₀).trans_lt (Metric.mem_eball.mp hz)
  exact hasSum_ordinaryPointSolution_of_hasFPowerSeriesOnBall
    (hf.hasFPowerSeriesOnBall_ofScalars hr) (hg.hasFPowerSeriesOnBall_ofScalars hr) hz w₀ w₁

/-- On `Metric.eball z₀ r`, `ordinaryPointSolution` is additive in the initial data `(w₀, w₁)`. -/
theorem ordinaryPointSolution_add_on_eball
    {f g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (Metric.eball z₀ r))
    (hg : DifferentiableOn ℂ g (Metric.eball z₀ r))
    (w₀ w₁ u₀ u₁ : ℂ) {z : ℂ} (hz : z ∈ Metric.eball z₀ r) :
    ordinaryPointSolution f g z₀ (w₀ + u₀) (w₁ + u₁) z =
      ordinaryPointSolution f g z₀ w₀ w₁ z + ordinaryPointSolution f g z₀ u₀ u₁ z := by
  have hr : 0 < r := (zero_le : (0 : ℝ≥0∞) ≤ edist z z₀).trans_lt (Metric.mem_eball.mp hz)
  exact ordinaryPointSolution_add_of_hasFPowerSeriesOnBall
    (hf.hasFPowerSeriesOnBall_ofScalars hr) (hg.hasFPowerSeriesOnBall_ofScalars hr) w₀ w₁ u₀ u₁ hz

/-- On `Metric.eball z₀ r`, `ordinaryPointSolution f g z₀ w₀ w₁` decomposes into the canonical
fundamental solutions with initial data `(1, 0)` and `(0, 1)`. -/
theorem ordinaryPointSolution_linear_combination_on_eball
    {f g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (Metric.eball z₀ r))
    (hg : DifferentiableOn ℂ g (Metric.eball z₀ r))
    (w₀ w₁ : ℂ) {z : ℂ} (hz : z ∈ Metric.eball z₀ r) :
    ordinaryPointSolution f g z₀ w₀ w₁ z =
      w₀ * ordinaryPointSolution f g z₀ 1 0 z + w₁ * ordinaryPointSolution f g z₀ 0 1 z := by
  have hr : 0 < r := (zero_le : (0 : ℝ≥0∞) ≤ edist z z₀).trans_lt (Metric.mem_eball.mp hz)
  exact ordinaryPointSolution_linear_combination_of_hasFPowerSeriesOnBall
    (hf.hasFPowerSeriesOnBall_ofScalars hr) (hg.hasFPowerSeriesOnBall_ofScalars hr) w₀ w₁ hz

/-- If `f` and `g` are holomorphic on `Metric.eball z₀ r`, then so is
`ordinaryPointSolution f g z₀ w₀ w₁`. -/
theorem differentiableOn_ordinaryPointSolution
    {f g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (Metric.eball z₀ r))
    (hg : DifferentiableOn ℂ g (Metric.eball z₀ r)) (w₀ w₁ : ℂ) :
    DifferentiableOn ℂ (ordinaryPointSolution f g z₀ w₀ w₁) (Metric.eball z₀ r) := by
  rcases eq_or_lt_of_le (zero_le : 0 ≤ r) with rfl | hr
  · simp [differentiableOn_empty]
  · exact (hasFPowerSeriesOnBall_ordinaryPointSolution hf hg hr w₀ w₁).differentiableOn

/-- If `f` and `g` are holomorphic on `Metric.eball z₀ r`, then `ordinaryPointSolution` is
complex-analytic on `Metric.eball z₀ r`. -/
theorem analyticOnNhd_ordinaryPointSolution
    {f g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (Metric.eball z₀ r))
    (hg : DifferentiableOn ℂ g (Metric.eball z₀ r)) (w₀ w₁ : ℂ) :
    AnalyticOnNhd ℂ (ordinaryPointSolution f g z₀ w₀ w₁) (Metric.eball z₀ r) :=
  (differentiableOn_ordinaryPointSolution hf hg w₀ w₁).analyticOnNhd Metric.isOpen_eball

/-- On `Metric.eball z₀ r`, `ordinaryPointSolution f g z₀ w₀ w₁` satisfies the differential
equation `w'' + f w' + g w = 0`. -/
theorem deriv_deriv_ordinaryPointSolution
    {f g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (Metric.eball z₀ r))
    (hg : DifferentiableOn ℂ g (Metric.eball z₀ r))
    (w₀ w₁ : ℂ) {z : ℂ} (hz : z ∈ Metric.eball z₀ r) :
    deriv (deriv (ordinaryPointSolution f g z₀ w₀ w₁)) z +
      f z * deriv (ordinaryPointSolution f g z₀ w₀ w₁) z +
      g z * ordinaryPointSolution f g z₀ w₀ w₁ z = 0 := by
  have hr : 0 < r := (zero_le : (0 : ℝ≥0∞) ≤ edist z z₀).trans_lt (Metric.mem_eball.mp hz)
  exact deriv_deriv_ordinaryPointSolution_of_hasFPowerSeriesOnBall
    (hf.hasFPowerSeriesOnBall_ofScalars hr) (hg.hasFPowerSeriesOnBall_ofScalars hr) w₀ w₁ hz

/-! ### Uniqueness and fundamental pairs on preconnected open domains -/

/-- **Uniqueness on preconnected open sets.** Let `U ⊆ ℂ` be open and preconnected with `z₀ ∈ U`,
and let `f`, `g` be holomorphic on `U`. Any two holomorphic solutions of `w'' + f w' + g w = 0`
on `U` with the same value and first derivative at `z₀` agree throughout `U`. -/
theorem eqOn_of_differentiableOn_of_deriv_deriv_add_eq_zero
    {f g w₁ w₂ : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hU_open : IsOpen U) (hU_conn : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hw₁ : DifferentiableOn ℂ w₁ U) (hw₂ : DifferentiableOn ℂ w₂ U)
    (hode₁ : ∀ z ∈ U, deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z = 0)
    (hode₂ : ∀ z ∈ U, deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z = 0)
    (h0 : w₁ z₀ = w₂ z₀) (h1 : deriv w₁ z₀ = deriv w₂ z₀) :
    EqOn w₁ w₂ U := by
  have hmem : U ∈ 𝓝 z₀ := hU_open.mem_nhds hz₀
  exact eqOn_of_analyticOnNhd_of_deriv_deriv_add_eq_zero hU_conn hz₀
    (hf.analyticAt hmem).contDiffAt
    (hg.analyticAt hmem).contDiffAt
    (hw₁.analyticOnNhd hU_open) (hw₂.analyticOnNhd hU_open)
    (Filter.eventually_of_mem hmem hode₁) (Filter.eventually_of_mem hmem hode₂) h0 h1

/-- A holomorphic solution of `w'' + f w' + g w = 0` on a preconnected open set `U` whose value
and first derivative both vanish at a point `z₀ ∈ U` vanishes throughout `U`. -/
theorem eqOn_zero_of_differentiableOn_of_deriv_deriv_add_eq_zero
    {f g w : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hU_open : IsOpen U) (hU_conn : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hw : DifferentiableOn ℂ w U)
    (hode : ∀ z ∈ U, deriv (deriv w) z + f z * deriv w z + g z * w z = 0)
    (h0 : w z₀ = 0) (h1 : deriv w z₀ = 0) :
    EqOn w 0 U :=
  eqOn_of_differentiableOn_of_deriv_deriv_add_eq_zero hU_open hU_conn hz₀ hf hg hw
    (differentiableOn_const 0) hode (fun _ _ ↦ by simp) h0 (by simpa using h1)

/-- Any holomorphic solution on `Metric.eball z₀ r` agrees on that disc with
`ordinaryPointSolution f g z₀ (w z₀) (deriv w z₀)`. -/
theorem eqOn_ordinaryPointSolution_eball
    {f g w : ℂ → ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (Metric.eball z₀ r))
    (hg : DifferentiableOn ℂ g (Metric.eball z₀ r))
    (hw : DifferentiableOn ℂ w (Metric.eball z₀ r))
    (hode : ∀ z ∈ Metric.eball z₀ r, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) :
    EqOn w (ordinaryPointSolution f g z₀ (w z₀) (deriv w z₀)) (Metric.eball z₀ r) := by
  rcases eq_or_lt_of_le (zero_le : 0 ≤ r) with rfl | hr
  · simp
  · have hf_ser := hf.hasFPowerSeriesOnBall_ofScalars hr
    exact eqOn_of_differentiableOn_of_deriv_deriv_add_eq_zero
      Metric.isOpen_eball (convex_eball z₀ r).isPreconnected (Metric.mem_eball_self hr) hf hg hw
      (differentiableOn_ordinaryPointSolution hf hg _ _) hode
      (fun z hz ↦ deriv_deriv_ordinaryPointSolution hf hg _ _ hz)
      (ordinaryPointSolution_self _ _ _ _ _).symm
      (deriv_ordinaryPointSolution_self hf_ser.analyticAt
        (hg.hasFPowerSeriesOnBall_ofScalars hr).analyticAt _ _).symm

/-- **Taylor series of an arbitrary holomorphic solution on a disc.** Every holomorphic solution
`w` of `w'' + f w' + g w = 0` on `Metric.eball z₀ r` (`0 < r`) has scalar Taylor series
`ordinaryPointCoeff` converging to `w` on the whole disc `Metric.eball z₀ r`. -/
theorem hasFPowerSeriesOnBall_of_deriv_deriv_add_eq_zero
    {f g w : ℂ → ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (Metric.eball z₀ r))
    (hg : DifferentiableOn ℂ g (Metric.eball z₀ r))
    (hw : DifferentiableOn ℂ w (Metric.eball z₀ r)) (hr : 0 < r)
    (hode : ∀ z ∈ Metric.eball z₀ r, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) :
    HasFPowerSeriesOnBall w
      (FormalMultilinearSeries.ofScalars ℂ
        (ordinaryPointCoeff
          (fun n ↦ iteratedDeriv n f z₀ / (n ! : ℂ))
          (fun n ↦ iteratedDeriv n g z₀ / (n ! : ℂ)) (w z₀) (deriv w z₀))) z₀ r :=
  (hasFPowerSeriesOnBall_ordinaryPointSolution hf hg hr (w z₀) (deriv w z₀)).congr
    (eqOn_ordinaryPointSolution_eball hf hg hw hode).symm

/-- **Existence and uniqueness at an ordinary point on an extended disc `Metric.eball z₀ r`.**
For `0 < r ≤ ∞` and `f`, `g` holomorphic on `Metric.eball z₀ r`, every initial pair `(w₀, w₁)`
admits a holomorphic solution on `Metric.eball z₀ r`, unique up to equality on the disc. -/
theorem exists_holomorphic_ordinaryPoint_eball
    {f g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (Metric.eball z₀ r))
    (hg : DifferentiableOn ℂ g (Metric.eball z₀ r)) (hr : 0 < r) (w₀ w₁ : ℂ) :
    ∃ w : ℂ → ℂ, DifferentiableOn ℂ w (Metric.eball z₀ r) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ ∧
      (∀ z ∈ Metric.eball z₀ r, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) ∧
      ∀ u : ℂ → ℂ, DifferentiableOn ℂ u (Metric.eball z₀ r) →
        u z₀ = w₀ → deriv u z₀ = w₁ →
        (∀ z ∈ Metric.eball z₀ r, deriv (deriv u) z + f z * deriv u z + g z * u z = 0) →
        EqOn u w (Metric.eball z₀ r) := by
  refine ⟨ordinaryPointSolution f g z₀ w₀ w₁,
    differentiableOn_ordinaryPointSolution hf hg w₀ w₁,
    ordinaryPointSolution_self f g z₀ w₀ w₁,
    deriv_ordinaryPointSolution_self
      (hf.hasFPowerSeriesOnBall_ofScalars hr).analyticAt
      (hg.hasFPowerSeriesOnBall_ofScalars hr).analyticAt w₀ w₁,
    fun z hz ↦ deriv_deriv_ordinaryPointSolution hf hg w₀ w₁ hz,
    fun u hu hu0 hu1 hu_ode ↦ ?_⟩
  simpa only [hu0, hu1] using eqOn_ordinaryPointSolution_eball hf hg hu hu_ode

/-- **Existence and uniqueness at an ordinary point on a finite disc `Metric.ball z₀ r`.** -/
theorem exists_holomorphic_ordinaryPoint_ball
    {f g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ r))
    (hg : DifferentiableOn ℂ g (Metric.ball z₀ r)) (hr : 0 < r) (w₀ w₁ : ℂ) :
    ∃ w : ℂ → ℂ, DifferentiableOn ℂ w (Metric.ball z₀ r) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ ∧
      (∀ z ∈ Metric.ball z₀ r, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) ∧
      ∀ u : ℂ → ℂ, DifferentiableOn ℂ u (Metric.ball z₀ r) →
        u z₀ = w₀ → deriv u z₀ = w₁ →
        (∀ z ∈ Metric.ball z₀ r, deriv (deriv u) z + f z * deriv u z + g z * u z = 0) →
        EqOn u w (Metric.ball z₀ r) := by
  simp_rw [← Metric.eball_ofReal] at hf hg ⊢
  exact exists_holomorphic_ordinaryPoint_eball hf hg (ENNReal.ofReal_pos.mpr hr) w₀ w₁

/-- **Fundamental-pair expansion on a preconnected open set.** Let `u` and `v` be holomorphic
solutions of `w'' + f w' + g w = 0` on a preconnected open set `U` whose Wronskian
`W₀ = u(z₀) v'(z₀) - u'(z₀) v(z₀)` is nonzero at `z₀ ∈ U`. Then every holomorphic solution `w`
on `U` is expressed on `U` by Cramer's rule in terms of `u` and `v`. -/
theorem eqOn_linear_combination_of_wronskian_ne_zero
    {f g u v w : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hU_open : IsOpen U) (hU_conn : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hu : DifferentiableOn ℂ u U) (hv : DifferentiableOn ℂ v U) (hw : DifferentiableOn ℂ w U)
    (hu_ode : ∀ z ∈ U, deriv (deriv u) z + f z * deriv u z + g z * u z = 0)
    (hv_ode : ∀ z ∈ U, deriv (deriv v) z + f z * deriv v z + g z * v z = 0)
    (hw_ode : ∀ z ∈ U, deriv (deriv w) z + f z * deriv w z + g z * w z = 0)
    (hW : u z₀ * deriv v z₀ - deriv u z₀ * v z₀ ≠ 0) :
    EqOn w
      (fun z ↦
        ((w z₀ * deriv v z₀ - deriv w z₀ * v z₀) /
            (u z₀ * deriv v z₀ - deriv u z₀ * v z₀)) * u z +
          ((deriv w z₀ * u z₀ - w z₀ * deriv u z₀) /
            (u z₀ * deriv v z₀ - deriv u z₀ * v z₀)) * v z) U := by
  have hmem : U ∈ 𝓝 z₀ := hU_open.mem_nhds hz₀
  exact eqOn_linear_combination_of_analyticOnNhd_of_wronskian_ne_zero hU_conn hz₀
    (hf.analyticAt hmem).contDiffAt (hg.analyticAt hmem).contDiffAt
    (hu.analyticOnNhd hU_open) (hv.analyticOnNhd hU_open) (hw.analyticOnNhd hU_open)
    (Filter.eventually_of_mem hmem hu_ode)
    (Filter.eventually_of_mem hmem hv_ode)
    (Filter.eventually_of_mem hmem hw_ode) hW

/-! ### Entire coefficients and global entire solutions -/

/-- If `f` and `g` are entire, then `ordinaryPointSolution f g z₀ w₀ w₁` is entire. -/
@[fun_prop]
theorem differentiable_ordinaryPointSolution
    {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (z₀ w₀ w₁ : ℂ) :
    Differentiable ℂ (ordinaryPointSolution f g z₀ w₀ w₁) := by
  rw [← differentiableOn_univ, ← Metric.eball_top (x := z₀)]
  exact differentiableOn_ordinaryPointSolution hf.differentiableOn hg.differentiableOn w₀ w₁

/-- For entire `f` and `g`, `ordinaryPointSolution` is additive in the initial data `(w₀, w₁)`. -/
theorem ordinaryPointSolution_add
    {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (z₀ w₀ w₁ u₀ u₁ z : ℂ) :
    ordinaryPointSolution f g z₀ (w₀ + u₀) (w₁ + u₁) z =
      ordinaryPointSolution f g z₀ w₀ w₁ z + ordinaryPointSolution f g z₀ u₀ u₁ z :=
  ordinaryPointSolution_add_on_eball (r := ⊤) hf.differentiableOn hg.differentiableOn
    w₀ w₁ u₀ u₁ (by simp)

/-- For entire `f` and `g`, `ordinaryPointSolution f g z₀ w₀ w₁` decomposes globally into the
canonical fundamental entire solutions with initial data `(1, 0)` and `(0, 1)`. -/
theorem ordinaryPointSolution_linear_combination
    {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (z₀ w₀ w₁ z : ℂ) :
    ordinaryPointSolution f g z₀ w₀ w₁ z =
      w₀ * ordinaryPointSolution f g z₀ 1 0 z + w₁ * ordinaryPointSolution f g z₀ 0 1 z :=
  ordinaryPointSolution_linear_combination_on_eball (r := ⊤) hf.differentiableOn
    hg.differentiableOn w₀ w₁ (by simp)

/-- If `f` and `g` are entire, then `ordinaryPointSolution f g z₀ w₀ w₁` solves
`w'' + f w' + g w = 0` everywhere on `ℂ`. -/
theorem deriv_deriv_ordinaryPointSolution_of_entire
    {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (z₀ w₀ w₁ z : ℂ) :
    deriv (deriv (ordinaryPointSolution f g z₀ w₀ w₁)) z +
      f z * deriv (ordinaryPointSolution f g z₀ w₀ w₁) z +
      g z * ordinaryPointSolution f g z₀ w₀ w₁ z = 0 :=
  deriv_deriv_ordinaryPointSolution (r := ⊤) hf.differentiableOn hg.differentiableOn w₀ w₁
    (by simp)

/-- Every entire solution `w` of `w'' + f w' + g w = 0` (with `f`, `g` entire) equals
`ordinaryPointSolution f g z₀ (w z₀) (deriv w z₀)` globally on `ℂ`. -/
theorem eq_ordinaryPointSolution_of_entire
    {f g w : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hw : Differentiable ℂ w) (z₀ : ℂ)
    (hode : ∀ z, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) :
    w = ordinaryPointSolution f g z₀ (w z₀) (deriv w z₀) := by
  ext z
  exact eqOn_ordinaryPointSolution_eball (r := ⊤) hf.differentiableOn hg.differentiableOn
    hw.differentiableOn (fun ζ _ ↦ hode ζ) (by simp)

/-- **Global existence and uniqueness for entire coefficients.** If `f` and `g` are entire,
then for every point `z₀` and initial values `w₀`, `w₁` there is a unique entire function
`w : ℂ → ℂ` with `w(z₀) = w₀`, `w'(z₀) = w₁`, and `w''(z) + f(z) w'(z) + g(z) w(z) = 0` for
all `z : ℂ`. -/
theorem existsUnique_entire_ordinaryPoint
    {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (z₀ w₀ w₁ : ℂ) :
    ∃! w : ℂ → ℂ, Differentiable ℂ w ∧ w z₀ = w₀ ∧ deriv w z₀ = w₁ ∧
      ∀ z, deriv (deriv w) z + f z * deriv w z + g z * w z = 0 := by
  refine ⟨ordinaryPointSolution f g z₀ w₀ w₁,
    ⟨differentiable_ordinaryPointSolution hf hg z₀ w₀ w₁,
      ordinaryPointSolution_self f g z₀ w₀ w₁,
      deriv_ordinaryPointSolution_self (hf.analyticAt z₀) (hg.analyticAt z₀) w₀ w₁,
      deriv_deriv_ordinaryPointSolution_of_entire hf hg z₀ w₀ w₁⟩, ?_⟩
  rintro u ⟨hu, hu0, hu1, hu_ode⟩
  simpa only [hu0, hu1] using eq_ordinaryPointSolution_of_entire hf hg hu z₀ hu_ode

/-- Two entire solutions of `w'' + f w' + g w = 0` (with `f`, `g` entire) that share the same
value and first derivative at one point `z₀` are equal everywhere on `ℂ`. -/
theorem eq_of_differentiable_of_deriv_deriv_add_eq_zero
    {f g w₁ w₂ : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hw₁ : Differentiable ℂ w₁) (hw₂ : Differentiable ℂ w₂) (z₀ : ℂ)
    (hode₁ : ∀ z, deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z = 0)
    (hode₂ : ∀ z, deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z = 0)
    (h0 : w₁ z₀ = w₂ z₀) (h1 : deriv w₁ z₀ = deriv w₂ z₀) :
    w₁ = w₂ := by
  rw [eq_ordinaryPointSolution_of_entire hf hg hw₁ z₀ hode₁,
    eq_ordinaryPointSolution_of_entire hf hg hw₂ z₀ hode₂, h0, h1]

/-- **Global fundamental-pair expansion for entire equations.** Let `f`, `g`, `u`, `v`, and `w`
be entire, with `u`, `v`, `w` solving `w'' + f w' + g w = 0` on `ℂ` and
`u(z₀) v'(z₀) - u'(z₀) v(z₀) ≠ 0` at some point `z₀`. Then `w` is globally a linear
combination of `u` and `v` with Cramer's-rule coefficients evaluated at `z₀`. -/
theorem eq_linear_combination_of_wronskian_ne_zero
    {f g u v w : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hu : Differentiable ℂ u) (hv : Differentiable ℂ v) (hw : Differentiable ℂ w)
    (hu_ode : ∀ z, deriv (deriv u) z + f z * deriv u z + g z * u z = 0)
    (hv_ode : ∀ z, deriv (deriv v) z + f z * deriv v z + g z * v z = 0)
    (hw_ode : ∀ z, deriv (deriv w) z + f z * deriv w z + g z * w z = 0)
    {z₀ : ℂ} (hW : u z₀ * deriv v z₀ - deriv u z₀ * v z₀ ≠ 0) :
    w = fun z ↦
      ((w z₀ * deriv v z₀ - deriv w z₀ * v z₀) /
          (u z₀ * deriv v z₀ - deriv u z₀ * v z₀)) * u z +
        ((deriv w z₀ * u z₀ - w z₀ * deriv u z₀) /
          (u z₀ * deriv v z₀ - deriv u z₀ * v z₀)) * v z := by
  ext z
  exact eqOn_linear_combination_of_wronskian_ne_zero isOpen_univ isPreconnected_univ
    (mem_univ z₀) hf.differentiableOn hg.differentiableOn hu.differentiableOn
    hv.differentiableOn hw.differentiableOn (fun ζ _ ↦ hu_ode ζ) (fun ζ _ ↦ hv_ode ζ)
    (fun ζ _ ↦ hw_ode ζ) hW (mem_univ z)

/-! ### Concrete checks -/

-- Check 1: `w'' = 0` (`f = 0`, `g = 0`) recovers `z ↦ w₀ + w₁ * (z - z₀)`.
example (z₀ w₀ w₁ : ℂ) :
    ordinaryPointSolution 0 0 z₀ w₀ w₁ = fun z ↦ w₀ + w₁ * (z - z₀) := by
  symm
  let u : ℂ → ℂ := fun z ↦ w₀ + w₁ * (z - z₀)
  have h1 : deriv u = fun _ ↦ w₁ := by
    ext z
    have hd : HasDerivAt u (w₁ * 1) z :=
      (((hasDerivAt_id' z).sub_const z₀).const_mul w₁).const_add w₀
    simpa using hd.deriv
  have heq := eq_ordinaryPointSolution_of_entire (f := 0) (g := 0) (w := u)
    (differentiable_const 0) (differentiable_const 0) (by dsimp [u]; fun_prop) z₀
    (fun z ↦ by simp [h1])
  simpa [u, h1] using heq

-- Check 2: `w'' - w = 0` (`f = 0`, `g = -1`) with `w(0) = 1`, `w'(0) = 1` recovers `Complex.exp`.
example : ordinaryPointSolution 0 (-1) 0 1 1 = Complex.exp := by
  symm
  have heq := eq_ordinaryPointSolution_of_entire (f := 0) (g := -1)
    (differentiable_const 0) (differentiable_const (-1)) Complex.differentiable_exp 0
    (fun z ↦ by simp [Complex.deriv_exp])
  simpa [Complex.deriv_exp] using heq

-- Check 3: Airy's equation `w'' = z w` (`f = 0`, `g = fun z ↦ -z`) has a unique entire solution
-- for every initial pair `(w₀, w₁)` at the origin.
example (w₀ w₁ : ℂ) :
    ∃! w : ℂ → ℂ, Differentiable ℂ w ∧ w 0 = w₀ ∧ deriv w 0 = w₁ ∧
      ∀ z, deriv (deriv w) z = z * w z := by
  have heq : ∀ (w : ℂ → ℂ) (z : ℂ),
      (deriv (deriv w) z = z * w z) ↔
        (deriv (deriv w) z + (0 : ℂ → ℂ) z * deriv w z + (fun ζ ↦ -ζ) z * w z = 0) := by
    intro w z
    simp [add_neg_eq_zero, neg_mul]
  simp_rw [heq]
  exact existsUnique_entire_ordinaryPoint (differentiable_const 0) differentiable_id.neg 0 w₀ w₁

end Complex

end

end TauCeti

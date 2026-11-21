/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.MoreauYosida.Convex
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.ODE.Gronwall
import TauCeti.Algebra.Order.Floor.Semifield
import TauCeti.Analysis.Calculus.GridInterpolation
import TauCeti.Analysis.GradientFlow.MinimizingMovement

/-!
# Two-step error estimate for Moreau–Yosida minimizing movements

Let `φ : X → EReal` be an energy on a pseudometric space and `m : ℝ`. Given two minimizing movement
sequences `U` (step `τ > 0`) and `V` (step `η > 0`) of `φ` with real energies under
`TauCeti.PenalizedConvex m τ φ` and `TauCeti.PenalizedConvex m η φ` (Ambrosio–Gigli–Savaré,
Assumption 4.0.1), this file proves the quantitative two-time-step comparison bound
`TauCeti.dist_ceil_sq_le_of_penalizedConvex` (Ambrosio–Gigli–Savaré, Theorem 4.0.4 / Section 4.1).

Interpolating the matrix `a_{n,k} = d(U n, V k)² / 2` bilinearly across the product grid
`[n τ, (n + 1) τ] × [k η, (k + 1) η]` produces a continuous function `B(t)` whose right derivative
on `[0, ∞)` is a convex combination of difference quotients in `n` and `k`. Summing the four
one-step discrete variational inequalities
(`TauCeti.PenalizedConvex.apply_add_le_of_mem_moreauYosidaResolvent`) cancels the cross-evaluated
energies identically into `α_n(t) (φ(U n) - φ(U (n + 1))) + β_k(t) (φ(V k) - φ(V (k + 1)))`, while
the one-step dissipations `-d(U n, U (n + 1))² / (2τ)` and `-d(V k, V (k + 1))² / (2η)` absorb the
metric shift terms coming from `-m`. Integrating by Grönwall's inequality bounds
`d(U ⌈t / τ⌉₊, V ⌈t / η⌉₊)²` in terms of `d(U 0, V 0)²` and `(τ + η)` times the energy dissipated
up to steps `⌊t / τ⌋₊ + 1` and `⌊t / η⌋₊ + 1`.

## Main results

* `TauCeti.dist_ceil_sq_le_of_penalizedConvex`: quantitative two-step error bound between two
  minimizing movement sequences under penalized convexity.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Theorem 4.0.4 and Section 4.1.
-/

public section

noncomputable section

open Set Topology Real
open scoped NNReal

namespace TauCeti

/-! ### Piecewise quadratic primitive of discrete energy dissipation -/

section EnergyPrim

/-- Piecewise quadratic primitive of `t ↦ stepWeight τ ⌊t / τ⌋₊ t * (e ⌊t / τ⌋₊ - e (⌊t / τ⌋₊ + 1))`
starting at `0`. -/
private def energyPrim (τ : ℝ) (e : ℕ → ℝ) : ℝ → ℝ :=
  piecewiseStep τ fun n t ↦
    (τ / 2) * (e 0 - e (n + 1) + stepWeight τ n t ^ 2 * (e (n + 1) - e n))

private theorem energyPrim_zero {τ : ℝ} (hτ : 0 < τ) (e : ℕ → ℝ) : energyPrim τ e 0 = 0 := by
  simp [energyPrim, hτ.ne']

private theorem energyPrim_le {τ t : ℝ} (hτ : 0 < τ) {e : ℕ → ℝ} (he : Antitone e) :
    energyPrim τ e t ≤ (τ / 2) * (e 0 - e (⌊t / τ⌋₊ + 1)) := by
  simp only [energyPrim, piecewiseStep_def]
  have hle : stepWeight τ ⌊t / τ⌋₊ t ^ 2 * (e (⌊t / τ⌋₊ + 1) - e ⌊t / τ⌋₊) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (sub_nonpos.2 (he (Nat.le_succ _)))
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

private theorem continuousOn_energyPrim {τ : ℝ} (hτ : 0 < τ) (e : ℕ → ℝ) :
    ContinuousOn (energyPrim τ e) (Ici 0) :=
  continuousOn_piecewiseStep hτ (fun _ ↦ by simp [hτ.ne']) fun _ ↦ by fun_prop

private theorem hasDerivWithinAt_energyPrim {τ : ℝ} (hτ : 0 < τ) (e : ℕ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (energyPrim τ e)
      (stepWeight τ ⌊t / τ⌋₊ t * (e ⌊t / τ⌋₊ - e (⌊t / τ⌋₊ + 1))) (Ici t) t := by
  unfold energyPrim
  rw [hasDerivWithinAt_piecewiseStep_iff hτ ht]
  have hd := ((((hasDerivAt_stepWeight τ ⌊t / τ⌋₊ t).pow 2).mul_const
    (e (⌊t / τ⌋₊ + 1) - e ⌊t / τ⌋₊)).const_add (e 0 - e (⌊t / τ⌋₊ + 1))).const_mul (τ / 2)
  exact (hd.congr_deriv (by have := hτ.ne'; field_simp; ring)).hasDerivWithinAt

end EnergyPrim

/-! ### Discrete two-step error estimate -/

section TwoStepBound

/-- Absorbs one metric shift `α m (d(x, y)² / 2 - d(x', y)² / 2)` into the one-step dissipation
`-d(x, x')² / (2τ)` when `|m| τ ≤ 1 / 2` and `α ∈ [0, 1]`. -/
private theorem mul_half_dist_sq_sub_le {X : Type*} [PseudoMetricSpace X] (x x' y : X)
    {m τ α : ℝ} (hτ : 0 < τ) (hmτ : |m| * τ ≤ 1 / 2) (hα : α ∈ Icc (0 : ℝ) 1) :
    α * m * (dist x y ^ 2 / 2 - dist x' y ^ 2 / 2) - dist x x' ^ 2 / (2 * τ) ≤
      2 * m ^ 2 * τ * (α * (dist x y ^ 2 / 2)) := by
  set d := dist x y; set d' := dist x' y; set Δ := dist x x'
  have hd0 : 0 ≤ d := dist_nonneg
  have hd'0 : 0 ≤ d' := dist_nonneg
  have hdiff : |d ^ 2 - d' ^ 2| ≤ 2 * d * Δ + Δ ^ 2 := by
    have h1 : |d - d'| ≤ Δ := abs_dist_sub_le x x' y
    have h2 : d + d' ≤ 2 * d + Δ := by linarith [dist_triangle_left x' y x]
    calc |d ^ 2 - d' ^ 2| = |d - d'| * (d + d') := by
          rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg hd0 hd'0), mul_comm]
      _ ≤ Δ * (2 * d + Δ) := mul_le_mul h1 h2 (add_nonneg hd0 hd'0) dist_nonneg
      _ = 2 * d * Δ + Δ ^ 2 := by ring
  have hm_bd : m * (d ^ 2 / 2 - d' ^ 2 / 2) ≤ |m| * d * Δ + |m| * Δ ^ 2 / 2 := by
    have h : m * (d ^ 2 - d' ^ 2) ≤ |m| * (2 * d * Δ + Δ ^ 2) := (le_abs_self _).trans <| by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hdiff (abs_nonneg m)
    linarith
  refine le_of_mul_le_mul_right ?_ (by positivity : 0 < 4 * τ)
  have hclear : (α * m * (d ^ 2 / 2 - d' ^ 2 / 2) - Δ ^ 2 / (2 * τ)) * (4 * τ) =
      4 * τ * α * (m * (d ^ 2 / 2 - d' ^ 2 / 2)) - 2 * Δ ^ 2 := by field_simp; ring
  have hα0 : 0 ≤ α := hα.1
  have h1 := mul_le_mul_of_nonneg_left hm_bd (by positivity : 0 ≤ 4 * τ * α)
  have hΔ : 2 * τ * α * |m| * Δ ^ 2 ≤ Δ ^ 2 :=
    (mul_le_mul_of_nonneg_right (by nlinarith [hα.1, hα.2, hmτ, abs_nonneg m] :
      2 * τ * α * |m| ≤ 1) (sq_nonneg Δ)).trans_eq (one_mul _)
  have hαm : 4 * τ ^ 2 * α ^ 2 * |m| ^ 2 * d ^ 2 ≤ 4 * τ ^ 2 * α * m ^ 2 * d ^ 2 := by
    rw [sq_abs]
    have := mul_le_mul_of_nonneg_right (by nlinarith [hα.1, hα.2] : α ^ 2 ≤ α)
      (by positivity : 0 ≤ 4 * τ ^ 2 * m ^ 2 * d ^ 2)
    linarith
  rw [hclear]
  nlinarith [sq_nonneg (Δ - 2 * τ * α * |m| * d), h1, hΔ, hαm]

/-- One-step real-valued discrete variational inequality for `d(U (n + 1), v)² / 2 - d(U n, v)² / 2`
along a minimizing movement sequence with real energies. -/
private theorem div_sub_half_dist_sq_le {X : Type*} [PseudoMetricSpace X] {m : ℝ} {τ : ℝ≥0}
    {φ : X → EReal} (h : PenalizedConvex m τ φ) (hτ : 0 < τ) {U : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n)) {eU : ℕ → ℝ}
    (heU : ∀ n, φ (U n) = eU n) {v : X} {ev : ℝ} (hev : φ v = ev) (n : ℕ) :
    (dist (U (n + 1)) v ^ 2 / 2 - dist (U n) v ^ 2 / 2) / τ ≤
      ev - eU (n + 1) - dist (U n) (U (n + 1)) ^ 2 / (2 * τ) -
        m * (dist (U (n + 1)) v ^ 2 / 2) := by
  have hvi := h.apply_add_le_of_mem_moreauYosidaResolvent hτ (hU n) (hev ▸ EReal.coe_ne_top ev)
  rw [heU (n + 1), hev, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at hvi
  have hτr : (0 : ℝ) < τ := hτ
  rw [div_le_iff₀ hτr]
  have := mul_le_mul_of_nonneg_right hvi hτr.le
  field_simp at this ⊢
  linarith

/-- Algebraic four-corner bound combining discrete variational inequalities and metric shift bounds
into the bilinear interpolation derivative estimate. -/
private theorem bilin_deriv_algebraic_le {a₀₀ a₁₀ a₀₁ a₁₁ eU₀ eU₁ eV₀ eV₁ dU dV m τ η α β : ℝ}
    (ha₀₀ : 0 ≤ a₀₀) (ha₁₀ : 0 ≤ a₁₀) (ha₀₁ : 0 ≤ a₀₁) (ha₁₁ : 0 ≤ a₁₁)
    (hτ : 0 ≤ τ) (hη : 0 ≤ η) (hα : α ∈ Icc (0 : ℝ) 1) (hβ : β ∈ Icc (0 : ℝ) 1)
    (hUk : (a₁₀ - a₀₀) / τ ≤ eV₀ - eU₁ - dU - m * a₁₀)
    (hUk1 : (a₁₁ - a₀₁) / τ ≤ eV₁ - eU₁ - dU - m * a₁₁)
    (hVn : (a₀₁ - a₀₀) / η ≤ eU₀ - eV₁ - dV - m * a₀₁)
    (hVn1 : (a₁₁ - a₁₀) / η ≤ eU₁ - eV₁ - dV - m * a₁₁)
    (hs1 : α * m * (a₀₀ - a₁₀) - dU ≤ 2 * m ^ 2 * τ * (α * a₀₀))
    (hs2 : α * m * (a₀₁ - a₁₁) - dU ≤ 2 * m ^ 2 * τ * (α * a₀₁))
    (hs3 : β * m * (a₀₀ - a₀₁) - dV ≤ 2 * m ^ 2 * η * (β * a₀₀))
    (hs4 : β * m * (a₁₀ - a₁₁) - dV ≤ 2 * m ^ 2 * η * (β * a₁₀)) :
    β * (a₁₀ - a₀₀) / τ + (1 - β) * (a₁₁ - a₀₁) / τ +
      α * (a₀₁ - a₀₀) / η + (1 - α) * (a₁₁ - a₁₀) / η ≤
      max 0 (-2 * m + 2 * m ^ 2 * τ + 2 * m ^ 2 * η) *
        (β * (α * a₀₀ + (1 - α) * a₁₀) + (1 - β) * (α * a₀₁ + (1 - α) * a₁₁)) +
        α * (eU₀ - eU₁) + β * (eV₀ - eV₁) := by
  set b := β * (α * a₀₀ + (1 - α) * a₁₀) + (1 - β) * (α * a₀₁ + (1 - α) * a₁₁)
  have hα0 := hα.1; have hα1 := sub_nonneg.2 hα.2
  have hβ0 := hβ.1; have hβ1 := sub_nonneg.2 hβ.2
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hα_le : β * (α * a₀₀) + (1 - β) * (α * a₀₁) ≤ b := by
    have : 0 ≤ β * ((1 - α) * a₁₀) + (1 - β) * ((1 - α) * a₁₁) := by positivity
    dsimp [b]; linarith
  have hbτ := mul_le_mul_of_nonneg_left hα_le (by positivity : 0 ≤ 2 * m ^ 2 * τ)
  have hβ_le : α * (β * a₀₀) + (1 - α) * (β * a₁₀) ≤ b := by
    have : 0 ≤ (1 - β) * (α * a₀₁ + (1 - α) * a₁₁) := by positivity
    dsimp [b]; linarith
  have hbη := mul_le_mul_of_nonneg_left hβ_le (by positivity : 0 ≤ 2 * m ^ 2 * η)
  have hK := mul_le_mul_of_nonneg_right
    (le_max_right 0 (-2 * m + 2 * m ^ 2 * τ + 2 * m ^ 2 * η)) hb0
  have hdecomp : β * (eV₀ - eU₁ - dU - m * a₁₀) + (1 - β) * (eV₁ - eU₁ - dU - m * a₁₁) +
      α * (eU₀ - eV₁ - dV - m * a₀₁) + (1 - α) * (eU₁ - eV₁ - dV - m * a₁₁) =
      -2 * m * b + β * (α * m * (a₀₀ - a₁₀) - dU) + (1 - β) * (α * m * (a₀₁ - a₁₁) - dU) +
        α * (β * m * (a₀₀ - a₀₁) - dV) + (1 - α) * (β * m * (a₁₀ - a₁₁) - dV) +
        α * (eU₀ - eU₁) + β * (eV₀ - eV₁) := by dsimp [b]; ring
  simp only [mul_div_assoc]
  linarith [hdecomp, hbτ, hbη, hK,
    mul_le_mul_of_nonneg_left hUk hβ0, mul_le_mul_of_nonneg_left hUk1 hβ1,
    mul_le_mul_of_nonneg_left hVn hα0, mul_le_mul_of_nonneg_left hVn1 hα1,
    mul_le_mul_of_nonneg_left hs1 hβ0, mul_le_mul_of_nonneg_left hs2 hβ1,
    mul_le_mul_of_nonneg_left hs3 hα0, mul_le_mul_of_nonneg_left hs4 hα1]

/-- Exponential Grönwall rate for the discrete two-step comparison at time steps `τ` and `η`. -/
private def twoStepRate (m : ℝ) (τ η : ℝ≥0) : ℝ :=
  max 0 (-2 * m + 2 * m ^ 2 * τ + 2 * m ^ 2 * η)

/-- Matrix of half-squared distances `d(U n, V k)² / 2` between two discrete trajectories. -/
private def halfDistSq {X : Type*} [PseudoMetricSpace X] (U V : ℕ → X) (n k : ℕ) : ℝ :=
  dist (U n) (V k) ^ 2 / 2

/-- Pointwise differential inequality for the diagonal bilinear interpolant of `d(U n, V k)² / 2`
along two minimizing movement sequences. -/
private theorem bilin_deriv_le_of_penalizedConvex {X : Type*} [PseudoMetricSpace X] {m : ℝ}
    {τ η : ℝ≥0} {φ : X → EReal} (hτc : PenalizedConvex m τ φ) (hηc : PenalizedConvex m η φ)
    (hτ : 0 < τ) (hη : 0 < η) (hmτ : |m| * τ ≤ 1 / 2) (hmη : |m| * η ≤ 1 / 2)
    {U V : ℕ → X} (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ η (V k))
    {eU eV : ℕ → ℝ} (heU : ∀ n, φ (U n) = eU n) (heV : ∀ k, φ (V k) = eV k)
    {t : ℝ} (ht : 0 ≤ t) :
    (stepWeight η ⌊t / η⌋₊ t / τ) •
        (halfDistSq U V (⌊t / τ⌋₊ + 1) ⌊t / η⌋₊ - halfDistSq U V ⌊t / τ⌋₊ ⌊t / η⌋₊) +
      ((1 - stepWeight η ⌊t / η⌋₊ t) / τ) •
        (halfDistSq U V (⌊t / τ⌋₊ + 1) (⌊t / η⌋₊ + 1) -
          halfDistSq U V ⌊t / τ⌋₊ (⌊t / η⌋₊ + 1)) +
      (stepWeight τ ⌊t / τ⌋₊ t / η) •
        (halfDistSq U V ⌊t / τ⌋₊ (⌊t / η⌋₊ + 1) - halfDistSq U V ⌊t / τ⌋₊ ⌊t / η⌋₊) +
      ((1 - stepWeight τ ⌊t / τ⌋₊ t) / η) •
        (halfDistSq U V (⌊t / τ⌋₊ + 1) (⌊t / η⌋₊ + 1) -
          halfDistSq U V (⌊t / τ⌋₊ + 1) ⌊t / η⌋₊) ≤
      twoStepRate m τ η * gridBilinearInterpolant τ η (halfDistSq U V) t t +
        stepWeight τ ⌊t / τ⌋₊ t * (eU ⌊t / τ⌋₊ - eU (⌊t / τ⌋₊ + 1)) +
        stepWeight η ⌊t / η⌋₊ t * (eV ⌊t / η⌋₊ - eV (⌊t / η⌋₊ + 1)) := by
  set n := ⌊t / (τ : ℝ)⌋₊; set k := ⌊t / (η : ℝ)⌋₊
  have hα : stepWeight τ n t ∈ Icc (0 : ℝ) 1 := stepWeight_floor_mem_Icc hτ ht
  have hβ : stepWeight η k t ∈ Icc (0 : ℝ) 1 := stepWeight_floor_mem_Icc hη ht
  have hVn := div_sub_half_dist_sq_le hηc hη hV heV (heU n) k
  have hVn1 := div_sub_half_dist_sq_le hηc hη hV heV (heU (n + 1)) k
  have hs3 := mul_half_dist_sq_sub_le (V k) (V (k + 1)) (U n) hη hmη hβ
  have hs4 := mul_half_dist_sq_sub_le (V k) (V (k + 1)) (U (n + 1)) hη hmη hβ
  simp only [dist_comm (V _) (U _)] at hVn hVn1 hs3 hs4
  rw [gridBilinearInterpolant_apply]
  simp only [smul_eq_mul, div_mul_eq_mul_div]
  dsimp only [twoStepRate, halfDistSq]
  exact bilin_deriv_algebraic_le (by positivity) (by positivity) (by positivity) (by positivity)
    (NNReal.coe_nonneg τ) (NNReal.coe_nonneg η) hα hβ
    (div_sub_half_dist_sq_le hτc hτ hU heU (heV k) n)
    (div_sub_half_dist_sq_le hτc hτ hU heU (heV (k + 1)) n) hVn hVn1
    (mul_half_dist_sq_sub_le (U n) (U (n + 1)) (V k) hτ hmτ hα)
    (mul_half_dist_sq_sub_le (U n) (U (n + 1)) (V (k + 1)) hτ hmτ hα) hs3 hs4

/-- Nonpositive right-hand derivative of the Grönwall auxiliary function
`s ↦ exp (-twoStepRate m τ η * s) * gridBilinearInterpolant τ η (halfDistSq U V) s s - ...`
for `s ≥ 0`. -/
private theorem exists_hasDerivWithinAt_exp_bilinInterp_sub {X : Type*} [PseudoMetricSpace X]
    {m : ℝ} {τ η : ℝ≥0} {φ : X → EReal} (hτc : PenalizedConvex m τ φ)
    (hηc : PenalizedConvex m η φ) (hτ : 0 < τ) (hη : 0 < η) (hmτ : |m| * τ ≤ 1 / 2)
    (hmη : |m| * η ≤ 1 / 2) {U V : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ η (V k))
    {eU eV : ℕ → ℝ} (heU : ∀ n, φ (U n) = eU n) (heV : ∀ k, φ (V k) = eV k)
    (hantiU : Antitone eU) (hantiV : Antitone eV) {s : ℝ} (hs : 0 ≤ s) :
    ∃ d : ℝ, d ≤ 0 ∧ HasDerivWithinAt
      (fun r ↦ exp (-twoStepRate m τ η * r) * gridBilinearInterpolant τ η (halfDistSq U V) r r -
        energyPrim τ eU r - energyPrim η eV r) d (Ici s) s := by
  set K := twoStepRate m τ η
  have hK0 : 0 ≤ K := le_max_left _ _
  have hexp : HasDerivWithinAt (fun r ↦ exp (-K * r)) (-K * exp (-K * s)) (Ici s) s :=
    (((hasDerivAt_id' s).const_mul (-K)).exp).hasDerivWithinAt.congr_deriv (by ring)
  refine ⟨_, ?_, ((hexp.mul (hasDerivWithinAt_gridBilinearInterpolant_diag hτ hη
    (halfDistSq U V) hs)).sub (hasDerivWithinAt_energyPrim hτ eU hs)).sub
    (hasDerivWithinAt_energyPrim hη eV hs)⟩
  have hbd := bilin_deriv_le_of_penalizedConvex hτc hηc hτ hη hmτ hmη hU hV heU heV hs
  set pU := stepWeight τ ⌊s / τ⌋₊ s * (eU ⌊s / τ⌋₊ - eU (⌊s / τ⌋₊ + 1))
  set pV := stepWeight η ⌊s / η⌋₊ s * (eV ⌊s / η⌋₊ - eV (⌊s / η⌋₊ + 1))
  have hpU : 0 ≤ pU :=
    mul_nonneg (stepWeight_floor_mem_Icc hτ hs).1 (sub_nonneg.2 (hantiU (Nat.le_succ _)))
  have hpV : 0 ≤ pV :=
    mul_nonneg (stepWeight_floor_mem_Icc hη hs).1 (sub_nonneg.2 (hantiV (Nat.le_succ _)))
  have hexp1 : exp (-K * s) ≤ 1 := exp_le_one_iff.2 (by nlinarith [hs, hK0])
  have h1 := add_le_add_left (mul_le_mul_of_nonneg_left hbd (exp_pos (-K * s)).le)
    ((-K * exp (-K * s)) * gridBilinearInterpolant τ η (halfDistSq U V) s s)
  have h2 := (mul_le_mul_of_nonneg_right hexp1 (add_nonneg hpU hpV)).trans_eq (one_mul _)
  rw [sub_sub, sub_nonpos, add_comm]
  exact (h1.trans_eq (by dsimp only [K]; ring)).trans h2

/-- Grönwall integration of `bilin_deriv_le_of_penalizedConvex` bounds
`2 * gridBilinearInterpolant τ η (halfDistSq U V) t t`. -/
private theorem two_mul_bilinInterp_le_of_penalizedConvex {X : Type*} [PseudoMetricSpace X]
    {m : ℝ} {τ η : ℝ≥0} {φ : X → EReal} (hτc : PenalizedConvex m τ φ)
    (hηc : PenalizedConvex m η φ) (hτ : 0 < τ) (hη : 0 < η) (hmτ : |m| * τ ≤ 1 / 2)
    (hmη : |m| * η ≤ 1 / 2) {U V : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ η (V k))
    {eU eV : ℕ → ℝ} (heU : ∀ n, φ (U n) = eU n) (heV : ∀ k, φ (V k) = eV k)
    (hantiU : Antitone eU) (hantiV : Antitone eV) {t : ℝ} (ht : 0 ≤ t) :
    2 * gridBilinearInterpolant τ η (halfDistSq U V) t t ≤
      exp (twoStepRate m τ η * t) * dist (U 0) (V 0) ^ 2 +
        exp (twoStepRate m τ η * t) *
          (τ * (eU 0 - eU (⌊t / τ⌋₊ + 1)) + η * (eV 0 - eV (⌊t / η⌋₊ + 1))) := by
  set K := twoStepRate m τ η
  set G : ℝ → ℝ := fun s ↦
    exp (-K * s) * gridBilinearInterpolant τ η (halfDistSq U V) s s -
      energyPrim τ eU s - energyPrim η eV s
  have hBcont : ContinuousOn (fun s ↦ gridBilinearInterpolant τ η (halfDistSq U V) s s) (Icc 0 t) :=
    (continuousOn_gridBilinearInterpolant hτ hη (halfDistSq U V)).comp
      (continuousOn_id.prodMk continuousOn_id) fun _ hs ↦ ⟨hs.1, hs.1⟩
  have hGcont : ContinuousOn G (Icc 0 t) :=
    ((((by fun_prop : ContinuousOn (fun s ↦ exp (-K * s)) (Icc 0 t))).mul hBcont).sub
      ((continuousOn_energyPrim hτ eU).mono Icc_subset_Ici_self)).sub
      ((continuousOn_energyPrim hη eV).mono Icc_subset_Ici_self)
  have hGderiv (s : ℝ) : ∃ d : ℝ, s ∈ Ico 0 t → d ≤ 0 ∧ HasDerivWithinAt G d (Ici s) s := by
    by_cases hs : s ∈ Ico 0 t
    · obtain ⟨d, hd0, hd⟩ := exists_hasDerivWithinAt_exp_bilinInterp_sub hτc hηc hτ hη hmτ hmη
        hU hV heU heV hantiU hantiV hs.1
      exact ⟨d, fun _ ↦ ⟨hd0, hd⟩⟩
    · exact ⟨0, fun h ↦ absurd h hs⟩
  choose d hdG using hGderiv
  have hgr := le_gronwallBound_of_liminf_deriv_right_le (f := G) (f' := d) (δ := G 0) (K := 0)
    (ε := 0) hGcont (fun s hs r hr ↦ ((hdG s hs).2).liminf_right_slope_le hr) le_rfl
    (fun s hs ↦ by linarith [(hdG s hs).1]) t ⟨ht, le_rfl⟩
  simp only [gronwallBound_K0, zero_mul, add_zero] at hgr
  have hG0 : G 0 = dist (U 0) (V 0) ^ 2 / 2 := by
    simp only [G, mul_zero, exp_zero, one_mul,
      gridBilinearInterpolant_apply_zero (NNReal.coe_pos.2 hτ).ne' (NNReal.coe_pos.2 hη).ne',
      energyPrim_zero (τ := τ) hτ, energyPrim_zero (τ := η) hη, sub_zero, halfDistSq]
  have hcan : exp (K * t) * exp (-K * t) = 1 := by rw [← exp_add]; simp [neg_mul]
  have hmul := mul_le_mul_of_nonneg_left (by
      linarith [hgr, hG0, energyPrim_le (τ := τ) (t := t) hτ hantiU,
        energyPrim_le (τ := η) (t := t) hη hantiV] :
      exp (-K * t) * gridBilinearInterpolant τ η (halfDistSq U V) t t ≤
        dist (U 0) (V 0) ^ 2 / 2 +
          ((τ : ℝ) / 2) * (eU 0 - eU (⌊t / τ⌋₊ + 1)) +
          ((η : ℝ) / 2) * (eV 0 - eV (⌊t / η⌋₊ + 1)))
    (by positivity : 0 ≤ 2 * exp (K * t))
  rw [← mul_assoc, mul_assoc 2, hcan, mul_one] at hmul
  have hrhs : 2 * exp (K * t) * (dist (U 0) (V 0) ^ 2 / 2 +
      ((τ : ℝ) / 2) * (eU 0 - eU (⌊t / τ⌋₊ + 1)) + ((η : ℝ) / 2) * (eV 0 - eV (⌊t / η⌋₊ + 1))) =
    exp (K * t) * dist (U 0) (V 0) ^ 2 +
      exp (K * t) * (τ * (eU 0 - eU (⌊t / τ⌋₊ + 1)) + η * (eV 0 - eV (⌊t / η⌋₊ + 1))) := by ring
  linarith [hmul, hrhs]

/-- **Quantitative two-step error bound for minimizing movements.** Under
`TauCeti.PenalizedConvex m τ φ` and `TauCeti.PenalizedConvex m η φ` with `|m| τ ≤ 1 / 2` and
`|m| η ≤ 1 / 2`, the piecewise constant interpolants of two minimizing movement sequences with real
energies satisfy an explicit bound in terms of `d(U 0, V 0)²` and `(τ + η)` times the energy
dissipated up to steps `⌊t / τ⌋₊ + 1` and `⌊t / η⌋₊ + 1`. -/
theorem dist_ceil_sq_le_of_penalizedConvex {X : Type*} [PseudoMetricSpace X]
    {m : ℝ} {τ η : ℝ≥0} {φ : X → EReal} (hτc : PenalizedConvex m τ φ)
    (hηc : PenalizedConvex m η φ) (hτ : 0 < τ) (hη : 0 < η) (hmτ : |m| * τ ≤ 1 / 2)
    (hmη : |m| * η ≤ 1 / 2) {U V : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ η (V k))
    {eU eV : ℕ → ℝ} (heU : ∀ n, φ (U n) = eU n) (heV : ∀ k, φ (V k) = eV k)
    {t : ℝ} (ht : 0 ≤ t) :
    dist (U ⌈t / τ⌉₊) (V ⌈t / η⌉₊) ^ 2 ≤
      2 * exp (max 0 (-2 * m + 2 * m ^ 2 * τ + 2 * m ^ 2 * η) * t) * dist (U 0) (V 0) ^ 2 +
        (2 * exp (max 0 (-2 * m + 2 * m ^ 2 * τ + 2 * m ^ 2 * η) * t) + 8) *
          (τ * (eU 0 - eU (⌊t / τ⌋₊ + 1)) + η * (eV 0 - eV (⌊t / η⌋₊ + 1))) := by
  have hantiU : Antitone eU := fun i j hij ↦ EReal.coe_le_coe_iff.1
    (heU j ▸ heU i ▸ antitone_comp_of_forall_mem_moreauYosidaResolvent hU hij)
  have hantiV : Antitone eV := fun i j hij ↦ EReal.coe_le_coe_iff.1
    (heV j ▸ heV i ▸ antitone_comp_of_forall_mem_moreauYosidaResolvent hV hij)
  have hstep {δ : ℝ≥0} {W : ℕ → X} (hW : ∀ i, W (i + 1) ∈ moreauYosidaResolvent φ δ (W i))
      {e : ℕ → ℝ} (he : ∀ i, φ (W i) = e i) (hanti : Antitone e) (i : ℕ) :
      dist (W i) (W (i + 1)) ^ 2 ≤ 2 * δ * (e 0 - e (i + 1)) := by
    have h1 := toReal_edist_sq_le_mul_sub_of_forall_mem_moreauYosidaResolvent hW
      (Nat.le_add_right i 1) (he i) (he (i + 1))
    simp only [← dist_edist, Nat.add_sub_cancel_left, Nat.cast_one, one_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right (hanti (Nat.zero_le i)) _)
      (by positivity))
  set n := ⌊t / (τ : ℝ)⌋₊; set k := ⌊t / (η : ℝ)⌋₊
  set ΔU := dist (U n) (U (n + 1)); set ΔV := dist (V k) (V (k + 1))
  have hΔU := hstep hU heU hantiU n
  have hΔV := hstep hV heV hantiV k
  have hdU (i : ℕ) (hi : i = n ∨ i = n + 1) : dist (U ⌈t / τ⌉₊) (U i) ≤ ΔU := by
    rcases ceil_eq_floor_or_add_one (t / (τ : ℝ)) with hc | hc <;>
      rcases hi with rfl | rfl <;> simp [hc, n, ΔU, dist_comm]
  have hdV (j : ℕ) (hj : j = k ∨ j = k + 1) : dist (V j) (V ⌈t / η⌉₊) ≤ ΔV := by
    rcases ceil_eq_floor_or_add_one (t / (η : ℝ)) with hc | hc <;>
      rcases hj with rfl | rfl <;> simp [hc, k, ΔV, dist_comm]
  have hcell (i j : ℕ) (hi : i = n ∨ i = n + 1) (hj : j = k ∨ j = k + 1) :
      dist (U ⌈t / τ⌉₊) (V ⌈t / η⌉₊) ^ 2 ≤ 2 * dist (U i) (V j) ^ 2 + 4 * ΔU ^ 2 + 4 * ΔV ^ 2 := by
    have htri : dist (U ⌈t / τ⌉₊) (V ⌈t / η⌉₊) ≤ dist (U i) (V j) + ΔU + ΔV :=
      (dist_triangle4 (U ⌈t / τ⌉₊) (U i) (V j) (V ⌈t / η⌉₊)).trans
        (by linarith [hdU i hi, hdV j hj])
    nlinarith [sq_nonneg (dist (U i) (V j) - ΔU - ΔV), sq_nonneg (ΔU - ΔV),
      pow_le_pow_left₀ dist_nonneg htri 2]
  obtain ⟨hα0, hα1⟩ := stepWeight_floor_mem_Icc (τ := τ) hτ ht
  obtain ⟨hβ0, hβ1⟩ := stepWeight_floor_mem_Icc (τ := η) hη ht
  have hb := two_mul_bilinInterp_le_of_penalizedConvex hτc hηc hτ hη hmτ hmη hU hV heU heV
    hantiU hantiV ht
  rw [gridBilinearInterpolant_apply] at hb
  simp only [smul_eq_mul] at hb
  dsimp only [twoStepRate, halfDistSq] at hb
  nlinarith [hΔU, hΔV, hb,
    mul_le_mul_of_nonneg_left (hcell n k (.inl rfl) (.inl rfl)) (mul_nonneg hβ0 hα0),
    mul_le_mul_of_nonneg_left (hcell (n + 1) k (.inr rfl) (.inl rfl))
      (mul_nonneg hβ0 (sub_nonneg.2 hα1)),
    mul_le_mul_of_nonneg_left (hcell n (k + 1) (.inl rfl) (.inr rfl))
      (mul_nonneg (sub_nonneg.2 hβ1) hα0),
    mul_le_mul_of_nonneg_left (hcell (n + 1) (k + 1) (.inr rfl) (.inr rfl))
      (mul_nonneg (sub_nonneg.2 hβ1) (sub_nonneg.2 hα1))]

end TwoStepBound

end TauCeti

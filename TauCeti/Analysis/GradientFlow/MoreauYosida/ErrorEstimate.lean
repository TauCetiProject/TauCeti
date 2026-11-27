/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.MoreauYosida.Convex
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Algebra.Order.Floor.Semifield
import TauCeti.Analysis.Calculus.GridInterpolation
import TauCeti.Analysis.GradientFlow.MinimizingMovement
import TauCeti.Topology.ContinuousOn.GridInterpolation
import TauCeti.Topology.MetricSpace.Pseudo.Defs

/-!
# Two-step error estimate for Moreau–Yosida minimizing movements

Let `φ : X → EReal` be an energy on a pseudometric space and `m : ℝ`. Given two minimizing movement
sequences `U` (step `τ > 0`) and `V` (step `η > 0`) of `φ` with real energies under
`TauCeti.PenalizedConvex m τ φ` and `TauCeti.PenalizedConvex m η φ` (Ambrosio–Gigli–Savaré,
Assumption 4.0.1), this file proves `TauCeti.dist_ceil_sq_le_of_penalizedConvex`
(Ambrosio–Gigli–Savaré, Theorem 4.0.4 / Section 4.1).

Interpolating `a_{n,k} = d(U n, V k)² / 2` bilinearly on `[n τ, (n + 1) τ] × [k η, (k + 1) η]`
gives a continuous function `B(t)` whose right derivative is a convex combination of difference
quotients. Summing the four discrete variational inequalities cancels the cross energies into
`α_n(t) (φ(U n) - φ(U (n + 1))) + β_k(t) (φ(V k) - φ(V (k + 1)))`, while the dissipations absorb
the `-m` metric shift terms. Right-derivative comparison (`TauCeti.stepWeightDiffPrimitive`) then
bounds `d(U ⌈t / τ⌉₊, V ⌈t / η⌉₊)²` in terms of `d(U 0, V 0)²`, `τ` times the energy dissipated
by `U` up to step `⌊t / τ⌋₊ + 1`, and `η` times the energy dissipated by `V` up to step
`⌊t / η⌋₊ + 1`.

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

/-! ### Discrete two-step error estimate -/

section TwoStepBound

/-- Absorbs one metric shift `α m (d(x, y)² / 2 - d(x', y)² / 2)` into the one-step dissipation
`-d(x, x')² / (2τ)` when `(-m) * τ ≤ 1 / 2` and `α ∈ [0, 1]`. -/
private theorem mul_half_dist_sq_sub_le {X : Type*} [PseudoMetricSpace X] (x x' y : X)
    {m τ α : ℝ} (hτ : 0 < τ) (hmτ : (-m) * τ ≤ 1 / 2) (hα : α ∈ Icc (0 : ℝ) 1) :
    α * m * (dist x y ^ 2 / 2 - dist x' y ^ 2 / 2) - dist x x' ^ 2 / (2 * τ) ≤
      2 * m ^ 2 * τ * (α * (dist x y ^ 2 / 2)) := by
  set d := dist x y; set d' := dist x' y; set Δ := dist x x'; have hα0 := hα.1
  refine le_of_mul_le_mul_right ?_ (by positivity : 0 < 4 * τ)
  have hclear : (α * m * (d ^ 2 / 2 - d' ^ 2 / 2) - Δ ^ 2 / (2 * τ)) * (4 * τ) =
      2 * τ * α * (m * (d ^ 2 - d' ^ 2)) - 2 * Δ ^ 2 := by field_simp; ring
  have hαm := mul_le_mul_of_nonneg_right (by nlinarith [hα.1, hα.2] : α ^ 2 ≤ α)
    (by positivity : 0 ≤ 4 * τ ^ 2 * m ^ 2 * d ^ 2)
  rw [hclear]
  rcases le_or_gt m 0 with hm0 | hm0
  · have hm_bd : m * (d ^ 2 - d' ^ 2) ≤ (-m) * (2 * d * Δ + Δ ^ 2) :=
      calc m * (d ^ 2 - d' ^ 2) = (-m) * (-(d ^ 2 - d' ^ 2)) := by ring
        _ ≤ (-m) * |d ^ 2 - d' ^ 2| := mul_le_mul_of_nonneg_left (neg_le_abs _) (neg_nonneg.2 hm0)
        _ ≤ (-m) * (2 * d * Δ + Δ ^ 2) :=
            mul_le_mul_of_nonneg_left (abs_dist_sq_sub_le x x' y) (neg_nonneg.2 hm0)
    have h1 := mul_le_mul_of_nonneg_left hm_bd (by positivity : 0 ≤ 2 * τ * α)
    have hΔ := (mul_le_mul_of_nonneg_right (by nlinarith [hα.1, hα.2, hmτ] :
      2 * τ * α * (-m) ≤ 1) (sq_nonneg Δ)).trans_eq (one_mul _)
    nlinarith [sq_nonneg (Δ + 2 * τ * α * m * d), h1, hΔ, hαm]
  · have h1 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (dist_sq_sub_le x x' y) hm0.le) (by positivity : 0 ≤ 2 * τ * α)
    nlinarith [sq_nonneg (Δ - 2 * τ * α * m * d), sq_nonneg Δ, h1, hαm]

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
  rw [div_le_iff₀ hτr]; have := mul_le_mul_of_nonneg_right hvi hτr.le
  field_simp at this ⊢; linarith

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
  have hα0 := hα.1; have hα1 := sub_nonneg.2 hα.2; have hβ0 := hβ.1; have hβ1 := sub_nonneg.2 hβ.2
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hα_le : β * (α * a₀₀) + (1 - β) * (α * a₀₁) ≤ b := by
    dsimp [b]; linarith [mul_nonneg hβ0 (mul_nonneg hα1 ha₁₀), mul_nonneg hβ1 (mul_nonneg hα1 ha₁₁)]
  have hβ_le : α * (β * a₀₀) + (1 - α) * (β * a₁₀) ≤ b := by
    dsimp [b]; linarith [mul_nonneg hβ1 (add_nonneg (mul_nonneg hα0 ha₀₁) (mul_nonneg hα1 ha₁₁))]
  have hdecomp : β * (eV₀ - eU₁ - dU - m * a₁₀) + (1 - β) * (eV₁ - eU₁ - dU - m * a₁₁) +
      α * (eU₀ - eV₁ - dV - m * a₀₁) + (1 - α) * (eU₁ - eV₁ - dV - m * a₁₁) =
      -2 * m * b + β * (α * m * (a₀₀ - a₁₀) - dU) + (1 - β) * (α * m * (a₀₁ - a₁₁) - dU) +
        α * (β * m * (a₀₀ - a₀₁) - dV) + (1 - α) * (β * m * (a₁₀ - a₁₁) - dV) +
        α * (eU₀ - eU₁) + β * (eV₀ - eV₁) := by dsimp [b]; ring
  simp only [mul_div_assoc]
  linarith [hdecomp,
    mul_le_mul_of_nonneg_left hα_le (by positivity : 0 ≤ 2 * m ^ 2 * τ),
    mul_le_mul_of_nonneg_left hβ_le (by positivity : 0 ≤ 2 * m ^ 2 * η),
    mul_le_mul_of_nonneg_right (le_max_right 0 (-2 * m + 2 * m ^ 2 * τ + 2 * m ^ 2 * η)) hb0,
    mul_le_mul_of_nonneg_left hUk hβ0, mul_le_mul_of_nonneg_left hUk1 hβ1,
    mul_le_mul_of_nonneg_left hVn hα0, mul_le_mul_of_nonneg_left hVn1 hα1,
    mul_le_mul_of_nonneg_left hs1 hβ0, mul_le_mul_of_nonneg_left hs2 hβ1,
    mul_le_mul_of_nonneg_left hs3 hα0, mul_le_mul_of_nonneg_left hs4 hα1]

/-- Exponential growth rate for the discrete two-step comparison at time steps `τ` and `η`. -/
private def twoStepRate (m : ℝ) (τ η : ℝ≥0) : ℝ :=
  max 0 (-2 * m + 2 * m ^ 2 * τ + 2 * m ^ 2 * η)

/-- Matrix of half-squared distances `d(U n, V k)² / 2` between two discrete trajectories. -/
private def halfDistSq {X : Type*} [PseudoMetricSpace X] (U V : ℕ → X) (n k : ℕ) : ℝ :=
  dist (U n) (V k) ^ 2 / 2

/-- Pointwise differential inequality for the diagonal bilinear interpolant of `d(U n, V k)² / 2`
along two minimizing movement sequences, returning the right-hand derivative witness together with
its bound. -/
private theorem bilin_deriv_le_of_penalizedConvex {X : Type*} [PseudoMetricSpace X] {m : ℝ}
    {τ η : ℝ≥0} {φ : X → EReal} (hτc : PenalizedConvex m τ φ) (hηc : PenalizedConvex m η φ)
    (hτ : 0 < τ) (hη : 0 < η) (hmτ : (-m) * τ ≤ 1 / 2) (hmη : (-m) * η ≤ 1 / 2)
    {U V : ℕ → X} (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ η (V k))
    {eU eV : ℕ → ℝ} (heU : ∀ n, φ (U n) = eU n) (heV : ∀ k, φ (V k) = eV k)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ dB : ℝ, HasDerivWithinAt (fun r ↦ gridBilinearInterpolant τ η (halfDistSq U V) r r)
      dB (Ici t) t ∧
      dB ≤ twoStepRate m τ η * gridBilinearInterpolant τ η (halfDistSq U V) t t +
        stepWeight τ ⌊t / τ⌋₊ t * (eU ⌊t / τ⌋₊ - eU (⌊t / τ⌋₊ + 1)) +
        stepWeight η ⌊t / η⌋₊ t * (eV ⌊t / η⌋₊ - eV (⌊t / η⌋₊ + 1)) := by
  set n := ⌊t / (τ : ℝ)⌋₊; set k := ⌊t / (η : ℝ)⌋₊
  have hα := stepWeight_floor_mem_Icc hτ ht; have hβ := stepWeight_floor_mem_Icc hη ht
  have hVn := div_sub_half_dist_sq_le hηc hη hV heV (heU n) k
  have hVn1 := div_sub_half_dist_sq_le hηc hη hV heV (heU (n + 1)) k
  have hs3 := mul_half_dist_sq_sub_le (V k) (V (k + 1)) (U n) hη hmη hβ
  have hs4 := mul_half_dist_sq_sub_le (V k) (V (k + 1)) (U (n + 1)) hη hmη hβ
  simp only [dist_comm (V _) (U _)] at hVn hVn1 hs3 hs4
  refine ⟨_, hasDerivWithinAt_gridBilinearInterpolant_diag (NNReal.coe_pos.2 hτ)
    (NNReal.coe_pos.2 hη) (halfDistSq U V) ht, ?_⟩
  rw [gridBilinearInterpolant_apply]; simp only [smul_eq_mul, div_mul_eq_mul_div]
  dsimp only [twoStepRate, halfDistSq]
  exact bilin_deriv_algebraic_le (by positivity) (by positivity) (by positivity) (by positivity)
    (NNReal.coe_nonneg τ) (NNReal.coe_nonneg η) hα hβ
    (div_sub_half_dist_sq_le hτc hτ hU heU (heV k) n)
    (div_sub_half_dist_sq_le hτc hτ hU heU (heV (k + 1)) n) hVn hVn1
    (mul_half_dist_sq_sub_le (U n) (U (n + 1)) (V k) hτ hmτ hα)
    (mul_half_dist_sq_sub_le (U n) (U (n + 1)) (V (k + 1)) hτ hmτ hα) hs3 hs4

/-- Nonpositive right-hand derivative of the exponentially weighted auxiliary function
`s ↦ exp (-twoStepRate m τ η * s) * gridBilinearInterpolant τ η (halfDistSq U V) s s - ...`
for `s ≥ 0`. -/
private theorem exists_hasDerivWithinAt_exp_bilinInterp_sub {X : Type*} [PseudoMetricSpace X]
    {m : ℝ} {τ η : ℝ≥0} {φ : X → EReal} (hτc : PenalizedConvex m τ φ)
    (hηc : PenalizedConvex m η φ) (hτ : 0 < τ) (hη : 0 < η) (hmτ : (-m) * τ ≤ 1 / 2)
    (hmη : (-m) * η ≤ 1 / 2) {U V : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ η (V k))
    {eU eV : ℕ → ℝ} (heU : ∀ n, φ (U n) = eU n) (heV : ∀ k, φ (V k) = eV k)
    (hantiU : Antitone eU) (hantiV : Antitone eV) {s : ℝ} (hs : 0 ≤ s) :
    ∃ d : ℝ, d ≤ 0 ∧ HasDerivWithinAt
      (fun r ↦ exp (-twoStepRate m τ η * r) * gridBilinearInterpolant τ η (halfDistSq U V) r r -
        stepWeightDiffPrimitive τ eU r - stepWeightDiffPrimitive η eV r) d (Ici s) s := by
  set K := twoStepRate m τ η; have hK0 : 0 ≤ K := le_max_left _ _
  have hexp : HasDerivWithinAt (fun r ↦ exp (-K * r)) (-K * exp (-K * s)) (Ici s) s :=
    (((hasDerivAt_id' s).const_mul (-K)).exp).hasDerivWithinAt.congr_deriv (by ring)
  obtain ⟨dB, hdB, hbd⟩ := bilin_deriv_le_of_penalizedConvex hτc hηc hτ hη hmτ hmη hU hV heU heV hs
  refine ⟨_, ?_, ((hexp.mul hdB).sub (hasDerivWithinAt_stepWeightDiffPrimitive hτ eU hs)).sub
    (hasDerivWithinAt_stepWeightDiffPrimitive hη eV hs)⟩
  have hpU : 0 ≤ stepWeight τ ⌊s / τ⌋₊ s * (eU ⌊s / τ⌋₊ - eU (⌊s / τ⌋₊ + 1)) :=
    mul_nonneg (stepWeight_floor_mem_Icc hτ hs).1 (sub_nonneg.2 (hantiU (Nat.le_succ _)))
  have hpV : 0 ≤ stepWeight η ⌊s / η⌋₊ s * (eV ⌊s / η⌋₊ - eV (⌊s / η⌋₊ + 1)) :=
    mul_nonneg (stepWeight_floor_mem_Icc hη hs).1 (sub_nonneg.2 (hantiV (Nat.le_succ _)))
  have h1 := add_le_add_left (mul_le_mul_of_nonneg_left hbd (exp_pos (-K * s)).le)
    ((-K * exp (-K * s)) * gridBilinearInterpolant τ η (halfDistSq U V) s s)
  have hKs : -K * s ≤ 0 := by nlinarith [hs, hK0]
  have h2 := (mul_le_mul_of_nonneg_right (exp_le_one_iff.2 hKs)
    (add_nonneg hpU hpV)).trans_eq (one_mul _)
  simp only [smul_eq_mul, sub_sub, sub_nonpos]; rw [add_comm]
  exact (h1.trans_eq (by dsimp only [K]; ring)).trans h2

/-- Integrating `bilin_deriv_le_of_penalizedConvex` via right-derivative comparison bounds
`2 * gridBilinearInterpolant τ η (halfDistSq U V) t t`. -/
private theorem two_mul_bilinInterp_le_of_penalizedConvex {X : Type*} [PseudoMetricSpace X]
    {m : ℝ} {τ η : ℝ≥0} {φ : X → EReal} (hτc : PenalizedConvex m τ φ)
    (hηc : PenalizedConvex m η φ) (hτ : 0 < τ) (hη : 0 < η) (hmτ : (-m) * τ ≤ 1 / 2)
    (hmη : (-m) * η ≤ 1 / 2) {U V : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ η (V k))
    {eU eV : ℕ → ℝ} (heU : ∀ n, φ (U n) = eU n) (heV : ∀ k, φ (V k) = eV k)
    (hantiU : Antitone eU) (hantiV : Antitone eV) {t : ℝ} (ht : 0 ≤ t) :
    2 * gridBilinearInterpolant τ η (halfDistSq U V) t t ≤
      exp (twoStepRate m τ η * t) * dist (U 0) (V 0) ^ 2 +
        exp (twoStepRate m τ η * t) *
          (τ * (eU 0 - eU (⌊t / τ⌋₊ + 1)) + η * (eV 0 - eV (⌊t / η⌋₊ + 1))) := by
  set K := twoStepRate m τ η
  set G : ℝ → ℝ := fun s ↦ exp (-K * s) * gridBilinearInterpolant τ η (halfDistSq U V) s s -
    stepWeightDiffPrimitive τ eU s - stepWeightDiffPrimitive η eV s
  have hBcont : ContinuousOn (fun s ↦ gridBilinearInterpolant τ η (halfDistSq U V) s s) (Icc 0 t) :=
    (continuousOn_gridBilinearInterpolant hτ hη (halfDistSq U V)).comp
      (continuousOn_id.prodMk continuousOn_id) fun _ hs ↦ ⟨hs.1, hs.1⟩
  have hGcont : ContinuousOn G (Icc 0 t) :=
    ((((by fun_prop : ContinuousOn (fun s ↦ exp (-K * s)) (Icc 0 t))).mul hBcont).sub
      ((continuousOn_stepWeightDiffPrimitive hτ eU).mono Icc_subset_Ici_self)).sub
      ((continuousOn_stepWeightDiffPrimitive hη eV).mono Icc_subset_Ici_self)
  have hgr := image_le_of_liminf_slope_right_le_deriv_boundary hGcont (B := fun _ ↦ G 0)
    (B' := fun _ ↦ 0) le_rfl continuousOn_const (fun s _ ↦ hasDerivWithinAt_const s _ (G 0))
    (fun s hs r hr ↦ by
      obtain ⟨d, hd0, hd⟩ := exists_hasDerivWithinAt_exp_bilinInterp_sub hτc hηc hτ hη hmτ hmη
        hU hV heU heV hantiU hantiV hs.1
      exact hd.liminf_right_slope_le (hd0.trans_lt hr))
    ⟨ht, le_rfl⟩
  have hG0 : G 0 = dist (U 0) (V 0) ^ 2 / 2 := by
    simp [G, (NNReal.coe_pos.2 hτ).ne', (NNReal.coe_pos.2 hη).ne', halfDistSq]
  have hpU := stepWeightDiffPrimitive_le (τ := τ) (t := t) (NNReal.coe_nonneg τ) hantiU
  have hpV := stepWeightDiffPrimitive_le (τ := η) (t := t) (NNReal.coe_nonneg η) hantiV
  simp only [smul_eq_mul] at hpU hpV
  have hcan : exp (K * t) * exp (-K * t) = 1 := by rw [← exp_add]; simp [neg_mul]
  have hmul := mul_le_mul_of_nonneg_left (by linarith [hgr, hG0, hpU, hpV] :
      exp (-K * t) * gridBilinearInterpolant τ η (halfDistSq U V) t t ≤
        dist (U 0) (V 0) ^ 2 / 2 + ((τ : ℝ) / 2) * (eU 0 - eU (⌊t / τ⌋₊ + 1)) +
          ((η : ℝ) / 2) * (eV 0 - eV (⌊t / η⌋₊ + 1))) (by positivity : 0 ≤ 2 * exp (K * t))
  rw [← mul_assoc, mul_assoc 2, hcan, mul_one] at hmul; exact hmul.trans_eq (by ring)

/-- **Quantitative two-step error bound for minimizing movements.** Under
`TauCeti.PenalizedConvex m τ φ` and `TauCeti.PenalizedConvex m η φ` with `(-m) * τ ≤ 1 / 2` and
`(-m) * η ≤ 1 / 2`, the piecewise constant interpolants of two minimizing movement sequences with
real energies satisfy an explicit bound in terms of `d(U 0, V 0)²`, `τ` times the energy dissipated
by `U` up to step `⌊t / τ⌋₊ + 1`, and `η` times the energy dissipated by `V` up to step
`⌊t / η⌋₊ + 1`. -/
theorem dist_ceil_sq_le_of_penalizedConvex {X : Type*} [PseudoMetricSpace X]
    {m : ℝ} {τ η : ℝ≥0} {φ : X → EReal} (hτc : PenalizedConvex m τ φ)
    (hηc : PenalizedConvex m η φ) (hτ : 0 < τ) (hη : 0 < η) (hmτ : (-m) * τ ≤ 1 / 2)
    (hmη : (-m) * η ≤ 1 / 2) {U V : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ η (V k))
    {eU eV : ℕ → ℝ} (heU : ∀ n, φ (U n) = eU n) (heV : ∀ k, φ (V k) = eV k)
    {t : ℝ} (ht : 0 ≤ t) :
    dist (U ⌈t / τ⌉₊) (V ⌈t / η⌉₊) ^ 2 ≤
      2 * exp (max 0 (-2 * m + 2 * m ^ 2 * τ + 2 * m ^ 2 * η) * t) * dist (U 0) (V 0) ^ 2 +
        (2 * exp (max 0 (-2 * m + 2 * m ^ 2 * τ + 2 * m ^ 2 * η) * t) + 8) *
          (τ * (eU 0 - eU (⌊t / τ⌋₊ + 1)) + η * (eV 0 - eV (⌊t / η⌋₊ + 1))) := by
  have hanti {δ : ℝ≥0} {W : ℕ → X} (hW : ∀ i, W (i + 1) ∈ moreauYosidaResolvent φ δ (W i))
      {e : ℕ → ℝ} (he : ∀ i, φ (W i) = e i) : Antitone e := fun i j hij ↦
    EReal.coe_le_coe_iff.1 (he j ▸ he i ▸ antitone_comp_of_forall_mem_moreauYosidaResolvent hW hij)
  have hantiU := hanti hU heU; have hantiV := hanti hV heV
  have hstep {δ : ℝ≥0} {W : ℕ → X} (hW : ∀ i, W (i + 1) ∈ moreauYosidaResolvent φ δ (W i))
      {e : ℕ → ℝ} (he : ∀ i, φ (W i) = e i) (ha : Antitone e) (i : ℕ) :
      dist (W i) (W (i + 1)) ^ 2 ≤ 2 * δ * (e 0 - e (i + 1)) := by
    have h1 := toReal_edist_sq_le_mul_sub_of_forall_mem_moreauYosidaResolvent hW
      (Nat.le_add_right i 1) (he i) (he (i + 1))
    simp only [← dist_edist, Nat.add_sub_cancel_left, Nat.cast_one, one_mul] at h1
    exact h1.trans <|
      mul_le_mul_of_nonneg_left (sub_le_sub_right (ha (Nat.zero_le i)) _) (by positivity)
  set n := ⌊t / (τ : ℝ)⌋₊; set k := ⌊t / (η : ℝ)⌋₊
  set ΔU := dist (U n) (U (n + 1)); set ΔV := dist (V k) (V (k + 1))
  have hΔU := hstep hU heU hantiU n; have hΔV := hstep hV heV hantiV k
  have hcd (W : ℕ → X) (δ : ℝ≥0) {a : ℕ} (ha : a = ⌊t / δ⌋₊ ∨ a = ⌊t / δ⌋₊ + 1) :
      dist (W ⌈t / δ⌉₊) (W a) ≤ dist (W ⌊t / δ⌋₊) (W (⌊t / δ⌋₊ + 1)) := by
    rcases ceil_eq_floor_or_add_one (t / (δ : ℝ)) with hc | hc <;>
      rcases ha with rfl | rfl <;> simp [hc, dist_comm]
  have hcell (i j : ℕ) (hi : i = n ∨ i = n + 1) (hj : j = k ∨ j = k + 1) :
      (dist (U ⌈t / τ⌉₊) (V ⌈t / η⌉₊) ^ 2 - 4 * ΔU ^ 2 - 4 * ΔV ^ 2) / 4 ≤
        halfDistSq U V i j := by
    have htri : dist (U ⌈t / τ⌉₊) (V ⌈t / η⌉₊) ≤ dist (U i) (V j) + ΔU + ΔV :=
      (dist_triangle4 (U ⌈t / τ⌉₊) (U i) (V j) (V ⌈t / η⌉₊)).trans
        (by linarith [hcd U τ hi, dist_comm (V j) (V ⌈t / η⌉₊) ▸ hcd V η hj])
    have hsq : dist (U ⌈t / τ⌉₊) (V ⌈t / η⌉₊) ^ 2 ≤
        2 * dist (U i) (V j) ^ 2 + 4 * ΔU ^ 2 + 4 * ΔV ^ 2 := by
      nlinarith [sq_nonneg (dist (U i) (V j) - ΔU - ΔV), sq_nonneg (ΔU - ΔV),
        pow_le_pow_left₀ dist_nonneg htri 2]
    dsimp only [halfDistSq]; linarith
  have hbilin := le_gridBilinearInterpolant (NNReal.coe_pos.2 hτ) (NNReal.coe_pos.2 hη) ht ht
    (hcell n k (.inl rfl) (.inl rfl)) (hcell (n + 1) k (.inr rfl) (.inl rfl))
    (hcell n (k + 1) (.inl rfl) (.inr rfl)) (hcell (n + 1) (k + 1) (.inr rfl) (.inr rfl))
  have hb := two_mul_bilinInterp_le_of_penalizedConvex hτc hηc hτ hη hmτ hmη hU hV heU heV
    hantiU hantiV ht
  dsimp only [twoStepRate] at hb; linarith [hΔU, hΔV, hb, hbilin]

end TwoStepBound

end TauCeti

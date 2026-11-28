/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Algebra.Order.Floor.GridInterpolation
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import TauCeti.Topology.ContinuousOn.GridInterpolation

/-!
# Derivatives and primitives for uniform-grid interpolation

For `τ > 0`, this file provides right-hand derivatives of `TauCeti.gridPiecewise`,
`TauCeti.stepWeight`, `TauCeti.gridLinearInterpolant`, and `TauCeti.gridBilinearInterpolant`,
together with the piecewise quadratic primitive `TauCeti.stepWeightDiffPrimitive` of
`t ↦ stepWeight τ ⌊t / τ⌋₊ t • (c ⌊t / τ⌋₊ - c (⌊t / τ⌋₊ + 1))`.

## Main definitions
* `TauCeti.stepWeightDiffPrimitive`.

## Main results
* `TauCeti.hasDerivWithinAt_gridPiecewise_iff`, `TauCeti.hasDerivAt_stepWeight`.
* `TauCeti.continuousOn_stepWeightDiffPrimitive`,
  `TauCeti.hasDerivWithinAt_stepWeightDiffPrimitive`, `TauCeti.stepWeightDiffPrimitive_le`.
* `TauCeti.hasDerivWithinAt_gridLinearInterpolant`.
* `TauCeti.hasDerivWithinAt_gridBilinearInterpolant_right`,
  `TauCeti.hasDerivWithinAt_gridBilinearInterpolant_left`,
  `TauCeti.hasDerivWithinAt_gridBilinearInterpolant_diag`.
-/

public section

noncomputable section

open Set Topology

namespace TauCeti

/-- Right-hand derivative of `gridPiecewise τ g` at `t ≥ 0` agrees with `g ⌊t / τ⌋₊` without any
matching condition at grid points. -/
theorem hasDerivWithinAt_gridPiecewise_iff {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousSMul ℝ E] {τ : ℝ} (hτ : 0 < τ) {g : ℕ → ℝ → E}
    {t : ℝ} (ht : 0 ≤ t) {f' : E} :
    HasDerivWithinAt (gridPiecewise τ g) f' (Ici t) t ↔
      HasDerivWithinAt (g ⌊t / τ⌋₊) f' (Ici t) t :=
  (gridPiecewise_eventuallyEq_nhdsWithin_Ici hτ g ht).hasFDerivWithinAt_iff
    (gridPiecewise_def τ g t)

/-- The derivative of `stepWeight τ n` at every `t : ℝ` is `-τ⁻¹`. -/
theorem hasDerivAt_stepWeight (τ : ℝ) (n : ℕ) (t : ℝ) : HasDerivAt (stepWeight τ n) (-τ⁻¹) t := by
  rw [funext (stepWeight_def τ n)]
  exact (((hasDerivAt_id' t).const_sub (((n : ℝ) + 1) * τ)).div_const τ).congr_deriv
    (by simp [neg_div, one_div])

/-! ### Piecewise quadratic primitive of weighted forward differences -/

section StepWeightDiffPrimitive

/-- Piecewise quadratic primitive of
`t ↦ stepWeight τ ⌊t / τ⌋₊ t • (c ⌊t / τ⌋₊ - c (⌊t / τ⌋₊ + 1))` starting at `0`. -/
def stepWeightDiffPrimitive {E : Type*} [AddCommGroup E] [Module ℝ E]
    (τ : ℝ) (c : ℕ → E) : ℝ → E :=
  gridPiecewise τ fun n t ↦
    (τ / 2) • (c 0 - c (n + 1) + stepWeight τ n t ^ 2 • (c (n + 1) - c n))

/-- Unconditional defining equation of `stepWeightDiffPrimitive`. -/
theorem stepWeightDiffPrimitive_def {E : Type*} [AddCommGroup E] [Module ℝ E]
    (τ : ℝ) (c : ℕ → E) (t : ℝ) :
    stepWeightDiffPrimitive τ c t = (τ / 2) • (c 0 - c (⌊t / τ⌋₊ + 1) +
      stepWeight τ ⌊t / τ⌋₊ t ^ 2 • (c (⌊t / τ⌋₊ + 1) - c ⌊t / τ⌋₊)) :=
  gridPiecewise_def τ (fun n t ↦
    (τ / 2) • (c 0 - c (n + 1) + stepWeight τ n t ^ 2 • (c (n + 1) - c n))) t

/-- At `0` (with `τ ≠ 0`), `stepWeightDiffPrimitive τ c` vanishes. -/
@[simp] theorem stepWeightDiffPrimitive_apply_zero {E : Type*} [AddCommGroup E] [Module ℝ E]
    {τ : ℝ} (hτ : τ ≠ 0) (c : ℕ → E) : stepWeightDiffPrimitive τ c 0 = 0 := by
  simp [stepWeightDiffPrimitive_def, hτ]

/-- At `n * τ` (with `τ ≠ 0`), `stepWeightDiffPrimitive τ c` equals `(τ / 2) • (c 0 - c n)`. -/
@[simp] theorem stepWeightDiffPrimitive_natCast_mul {E : Type*} [AddCommGroup E] [Module ℝ E]
    {τ : ℝ} (hτ : τ ≠ 0) (c : ℕ → E) (n : ℕ) :
    stepWeightDiffPrimitive τ c ((n : ℝ) * τ) = (τ / 2) • (c 0 - c n) := by
  simp only [stepWeightDiffPrimitive, gridPiecewise_natCast_mul hτ, stepWeight_natCast_mul hτ,
    one_pow, one_smul]; module

/-- For antitone `c` and `τ ≥ 0`, `stepWeightDiffPrimitive τ c t` is bounded by
`(τ / 2) • (c 0 - c (⌊t / τ⌋₊ + 1))`. -/
theorem stepWeightDiffPrimitive_le {E : Type*} [AddCommGroup E] [PartialOrder E]
    [IsOrderedAddMonoid E] [Module ℝ E] [PosSMulMono ℝ E]
    {τ t : ℝ} (hτ : 0 ≤ τ) {c : ℕ → E} (hc : Antitone c) :
    stepWeightDiffPrimitive τ c t ≤ (τ / 2) • (c 0 - c (⌊t / τ⌋₊ + 1)) := by
  rw [stepWeightDiffPrimitive_def]
  exact smul_le_smul_of_nonneg_left (add_le_of_nonpos_right
    (smul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (sub_nonpos.2 (hc (Nat.le_succ _)))))
    (by positivity)

/-- For `τ > 0`, `stepWeightDiffPrimitive τ c` is continuous on `[0, ∞)`. -/
theorem continuousOn_stepWeightDiffPrimitive {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {τ : ℝ} (hτ : 0 < τ) (c : ℕ → E) : ContinuousOn (stepWeightDiffPrimitive τ c) (Ici 0) :=
  continuousOn_gridPiecewise hτ (fun _ ↦ by simp [hτ.ne']) fun _ ↦ by fun_prop

/-- For `τ > 0` and `t ≥ 0`, `stepWeightDiffPrimitive τ c` has right-hand derivative
`stepWeight τ ⌊t / τ⌋₊ t • (c ⌊t / τ⌋₊ - c (⌊t / τ⌋₊ + 1))` at `t`. -/
theorem hasDerivWithinAt_stepWeightDiffPrimitive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {τ : ℝ} (hτ : 0 < τ) (c : ℕ → E) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (stepWeightDiffPrimitive τ c)
      (stepWeight τ ⌊t / τ⌋₊ t • (c ⌊t / τ⌋₊ - c (⌊t / τ⌋₊ + 1))) (Ici t) t := by
  unfold stepWeightDiffPrimitive; rw [hasDerivWithinAt_gridPiecewise_iff hτ ht]
  have hd := (((((hasDerivAt_stepWeight τ ⌊t / τ⌋₊ t).pow 2).smul_const
    (c (⌊t / τ⌋₊ + 1) - c ⌊t / τ⌋₊)).const_add (c 0 - c (⌊t / τ⌋₊ + 1))).const_smul (τ / 2))
  refine (hd.congr_deriv ?_).hasDerivWithinAt; have : τ ≠ 0 := hτ.ne'
  rw [← neg_sub (c ⌊t / τ⌋₊), smul_neg, ← neg_smul, smul_smul]; congr 1
  simp only [Nat.add_one_sub_one, pow_one, Nat.cast_ofNat]; field_simp

end StepWeightDiffPrimitive

/-! ### Derivatives of linear and bilinear grid interpolants -/

/-- For `τ > 0` and `t ≥ 0`, `gridLinearInterpolant τ c` has right-hand derivative
`τ⁻¹ • (c (⌊t / τ⌋₊ + 1) - c ⌊t / τ⌋₊)` at `t`. -/
theorem hasDerivWithinAt_gridLinearInterpolant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {τ : ℝ} (hτ : 0 < τ) (c : ℕ → E) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (gridLinearInterpolant τ c)
      (τ⁻¹ • (c (⌊t / τ⌋₊ + 1) - c ⌊t / τ⌋₊)) (Ici t) t := by
  have hlin : gridLinearInterpolant τ c = gridPiecewise τ fun n t ↦
      stepWeight τ n t • c n + (1 - stepWeight τ n t) • c (n + 1) :=
    funext fun u ↦ (gridLinearInterpolant_def τ c u).trans
      (gridPiecewise_def τ
        (fun n t ↦ stepWeight τ n t • c n + (1 - stepWeight τ n t) • c (n + 1)) u).symm
  rw [hlin, hasDerivWithinAt_gridPiecewise_iff hτ ht]
  have hd := ((hasDerivAt_stepWeight τ ⌊t / τ⌋₊ t).smul_const (c ⌊t / τ⌋₊)).add
    (((hasDerivAt_stepWeight τ ⌊t / τ⌋₊ t).const_sub 1).smul_const (c (⌊t / τ⌋₊ + 1)))
  exact (hd.congr_deriv (by simp only [neg_neg]; module)).hasDerivWithinAt

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Right-hand partial derivative in the second argument of `gridBilinearInterpolant` at `t ≥ 0`. -/
theorem hasDerivWithinAt_gridBilinearInterpolant_right (τ : ℝ) {η : ℝ} (hη : 0 < η)
    (a : ℕ → ℕ → E) (s : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (gridBilinearInterpolant τ η a s)
      (η⁻¹ • (gridLinearInterpolant τ (a · (⌊t / η⌋₊ + 1)) s -
        gridLinearInterpolant τ (a · ⌊t / η⌋₊) s)) (Ici t) t := by
  simpa only [funext (gridBilinearInterpolant_def τ η a s)] using
    hasDerivWithinAt_gridLinearInterpolant hη (fun k ↦ gridLinearInterpolant τ (a · k) s) ht

/-- Right-hand partial derivative in the first argument of `gridBilinearInterpolant` at `s ≥ 0`. -/
theorem hasDerivWithinAt_gridBilinearInterpolant_left {τ : ℝ} (hτ : 0 < τ) (η : ℝ)
    (a : ℕ → ℕ → E) {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    HasDerivWithinAt (gridBilinearInterpolant τ η a · t)
      (τ⁻¹ • (gridLinearInterpolant η (a (⌊s / τ⌋₊ + 1)) t -
        gridLinearInterpolant η (a ⌊s / τ⌋₊) t)) (Ici s) s :=
  (hasDerivWithinAt_gridLinearInterpolant hτ (fun n ↦ gridLinearInterpolant η (a n) t) hs).congr
    (fun u _ ↦ (gridBilinearInterpolant_swap τ η a u t).symm.trans
      (gridBilinearInterpolant_def η τ (Function.swap a) t u))
    ((gridBilinearInterpolant_swap τ η a s t).symm.trans
      (gridBilinearInterpolant_def η τ (Function.swap a) t s))

/-- Right-hand derivative of the diagonal `u ↦ gridBilinearInterpolant τ η a u u` at `t ≥ 0`. -/
theorem hasDerivWithinAt_gridBilinearInterpolant_diag {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η)
    (a : ℕ → ℕ → E) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun u ↦ gridBilinearInterpolant τ η a u u)
      ((stepWeight η ⌊t / η⌋₊ t / τ) • (a (⌊t / τ⌋₊ + 1) ⌊t / η⌋₊ - a ⌊t / τ⌋₊ ⌊t / η⌋₊) +
        ((1 - stepWeight η ⌊t / η⌋₊ t) / τ) •
          (a (⌊t / τ⌋₊ + 1) (⌊t / η⌋₊ + 1) - a ⌊t / τ⌋₊ (⌊t / η⌋₊ + 1)) +
        (stepWeight τ ⌊t / τ⌋₊ t / η) • (a ⌊t / τ⌋₊ (⌊t / η⌋₊ + 1) - a ⌊t / τ⌋₊ ⌊t / η⌋₊) +
        ((1 - stepWeight τ ⌊t / τ⌋₊ t) / η) •
          (a (⌊t / τ⌋₊ + 1) (⌊t / η⌋₊ + 1) - a (⌊t / τ⌋₊ + 1) ⌊t / η⌋₊))
      (Ici t) t := by
  have hdiag : (fun u ↦ gridBilinearInterpolant τ η a u u) =
      gridPiecewise η fun k u ↦ stepWeight η k u • gridLinearInterpolant τ (a · k) u +
        (1 - stepWeight η k u) • gridLinearInterpolant τ (a · (k + 1)) u :=
    funext fun u ↦ (gridBilinearInterpolant_def τ η a u u).trans
      ((gridLinearInterpolant_def _ _ u).trans
        (gridPiecewise_def η (fun k u ↦ stepWeight η k u • gridLinearInterpolant τ (a · k) u +
          (1 - stepWeight η k u) • gridLinearInterpolant τ (a · (k + 1)) u) u).symm)
  rw [hdiag, hasDerivWithinAt_gridPiecewise_iff hη ht]
  have hd1 := ((hasDerivAt_stepWeight η ⌊t / η⌋₊ t).hasDerivWithinAt).smul
    (hasDerivWithinAt_gridLinearInterpolant hτ (a · ⌊t / η⌋₊) ht)
  have hd2 := (((hasDerivAt_stepWeight η ⌊t / η⌋₊ t).const_sub 1).hasDerivWithinAt).smul
    (hasDerivWithinAt_gridLinearInterpolant hτ (a · (⌊t / η⌋₊ + 1)) ht)
  refine (hd1.add hd2).congr_deriv ?_
  simp only [gridLinearInterpolant_def, neg_neg, div_eq_mul_inv, smul_add, smul_sub,
    smul_smul, neg_smul, sub_smul, one_smul]; module

end Normed

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.OneSubExpNegDivSelf.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# An integral formula for the filled exponential quotient

This file identifies the filled quotient `(1 - exp (-a)) / a` with the integral of the
exponential along the line segment from `0` to `-a`. The formula remains valid when `a` is not
invertible. This representation describes the analytic factor in the differential of a
Lie-group exponential map.

## Main result

* `oneSubExpNegDivSelf_eq_integral_exp`:
  `oneSubExpNegDivSelf ℝ a = ∫ t in 0..1, exp (t • -a)`.
-/

public section

open NormedSpace
open TopologicalSpace

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The regularized exponential quotient is the integral of the exponential along the line
segment from `0` to `-a`. -/
theorem oneSubExpNegDivSelf_eq_integral_exp (a : A) :
    oneSubExpNegDivSelf ℝ a = ∫ t in (0 : ℝ)..1, exp (t • (-a)) := by
  let f (n : ℕ) : C(ℝ, A) :=
    ⟨fun t ↦ t ^ n • ((n.factorial⁻¹ : ℝ) • (-a) ^ n), by fun_prop⟩
  have hf (n : ℕ) (t : ℝ) :
      f n t = (n.factorial⁻¹ : ℝ) • (t • (-a)) ^ n := by
    simp only [f, ContinuousMap.coe_mk, smul_pow, smul_smul, mul_comm]
  -- On `[0, 1]`, the monomials have norm at most one, so the exponential series dominates.
  have hsum : Summable fun n : ℕ ↦
      ‖(f n).restrict (⟨Set.uIcc 0 1, isCompact_uIcc⟩ : Compacts ℝ)‖ := by
    refine (norm_expSeries_summable' (𝕂 := ℝ) (-a)).of_nonneg_of_le
      (fun n ↦ norm_nonneg _) ?_
    intro n
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 ?_
    intro t
    have ht : (0 : ℝ) ≤ t ∧ (t : ℝ) ≤ 1 := by simpa using t.property
    have ht_abs : |(t : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    simp only [ContinuousMap.restrict_apply, f, ContinuousMap.coe_mk, norm_smul,
      Real.norm_eq_abs, abs_pow]
    exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (abs_nonneg _) ht_abs)
  have hint (n : ℕ) :
      ∫ t in (0 : ℝ)..1, f n t = (((n + 1).factorial)⁻¹ : ℝ) • (-a) ^ n := by
    simp [f, intervalIntegral.integral_smul_const, integral_pow, smul_smul,
      Nat.factorial_succ, mul_comm]
  rw [oneSubExpNegDivSelf_eq_tsum]
  calc
    ∑' n : ℕ, (((n + 1).factorial)⁻¹ : ℝ) • (-a) ^ n =
        ∑' n : ℕ, ∫ t in (0 : ℝ)..1, f n t := tsum_congr fun n ↦ (hint n).symm
    _ = ∫ t in (0 : ℝ)..1, ∑' n : ℕ, f n t :=
      intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hsum
    _ = ∫ t in (0 : ℝ)..1, exp (t • (-a)) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      simp only [exp_eq_tsum ℝ, hf]

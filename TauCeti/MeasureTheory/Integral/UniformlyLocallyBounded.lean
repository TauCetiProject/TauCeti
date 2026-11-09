/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import TauCeti.MeasureTheory.Measure.Interval
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.MeasureTheory.Integral.CompactlySupported
import TauCeti.Topology.ContinuousMap.CompactlySupported

/-!
# Integrals against uniformly locally bounded measures on `ℝ`

A measure `η` on `ℝ` is uniformly locally bounded if its unit windows `[a, a + 1]` all have mass
at most some `C`. Integrals against such a measure are bounded in terms of the length of the
window outside which the integrand vanishes. Consequently, for a compactly supported continuous
`f`, the integrals `x ↦ ∫ y, f (y - x) ∂η` of the translates of `f` form a bounded, uniformly
continuous function of `x`.

## Main results

* `MeasureTheory.Measure.abs_integral_le_of_measure_Icc_add_one_le`: a function bounded by `A`
  and vanishing off `[a, a + n]` has integral at most `A * ((n + 1) * C)` in absolute value.
* `MeasureTheory.Measure.exists_abs_integral_apply_sub_le`: the integrals of the translates of a
  compactly supported continuous function are uniformly bounded.
* `MeasureTheory.Measure.uniformContinuous_integral_apply_sub`: they depend uniformly
  continuously on the translation.
-/

public section

open Set Metric
open scoped NNReal ENNReal CompactlySupported

namespace MeasureTheory.Measure

variable {η : Measure ℝ} {C : ℝ≥0}

/-- A bounded function vanishing off a window `[a, a + n]` has integral at most
`A * ((n + 1) * C)` in absolute value against a measure whose unit windows have mass at most
`C`. -/
theorem abs_integral_le_of_measure_Icc_add_one_le (hC : ∀ a : ℝ, η (Icc a (a + 1)) ≤ C)
    {φ : ℝ → ℝ} {A : ℝ} (hφA : ∀ y, |φ y| ≤ A) (a : ℝ) (n : ℕ)
    (hφ : ∀ y, y ∉ Icc a (a + n) → φ y = 0) :
    |∫ y, φ y ∂η| ≤ A * ((n + 1) * C) := by
  have hmass := measure_Icc_add_natCast_le (fun a ↦ hC a) a n
  have hfin : η (Icc a (a + n)) < ∞ := hmass.trans_lt (by finiteness)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hφ, ← Real.norm_eq_abs]
  refine (norm_setIntegral_le_of_norm_le_const hfin fun y _ ↦ hφA y).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ ((abs_nonneg _).trans (hφA 0))
  have hreal : ((n + 1 : ℝ≥0∞) * C).toReal = (n + 1) * C := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp
  rw [measureReal_def, ← hreal]
  exact ENNReal.toReal_mono (by finiteness) hmass

/-- The integrals of the translates `y ↦ f (y - x)` of a compactly supported continuous function
against a uniformly locally bounded measure are uniformly bounded. -/
theorem exists_abs_integral_apply_sub_le (hC : ∀ a : ℝ, η (Icc a (a + 1)) ≤ C)
    (f : C_c(ℝ, ℝ)) : ∃ B, ∀ x, |∫ y, f (y - x) ∂η| ≤ B := by
  obtain ⟨R, hR⟩ := f.exists_natCast_apply_sub_eq_zero
  obtain ⟨A, hA⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  refine ⟨A * ((2 * R + 1) * C), fun x ↦ ?_⟩
  -- The translate vanishes off the window `[x - R, x + R]` of length `2 * R`.
  have := abs_integral_le_of_measure_Icc_add_one_le hC (φ := fun y ↦ f (y - x))
    (fun y ↦ by simpa using hA (y - x)) (x - R) (2 * R) fun y hy ↦ hR y x (by
      simp only [mem_Icc, not_and_or, not_le] at hy
      push_cast at hy
      rcases hy with hy | hy
      exacts [Or.inl (by linarith), Or.inr (by linarith)])
  simpa using this

/-- The integrals of the translates `y ↦ f (y - x)` of a compactly supported continuous function
against a uniformly locally bounded measure depend uniformly continuously on `x`. -/
theorem uniformContinuous_integral_apply_sub (hC : ∀ a : ℝ, η (Icc a (a + 1)) ≤ C)
    (f : C_c(ℝ, ℝ)) : UniformContinuous fun x ↦ ∫ y, f (y - x) ∂η := by
  have := isLocallyFiniteMeasure_of_measure_Icc_add_one_le hC
  obtain ⟨R, hR⟩ := f.exists_natCast_apply_sub_eq_zero
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  -- `K` exceeds the mass bound `(2 * R + 3) * C` of the windows of length `2 * R + 2`.
  set K : ℝ := (2 * R + 3) * C + 1
  have hK : 0 < K := by positivity
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.1
    (f.hasCompactSupport.uniformContinuous_of_continuous f.continuous) (ε / (2 * K))
    (by positivity)
  refine ⟨min δ 1, by positivity, fun {x x'} hxx' ↦ ?_⟩
  have hxx'1 : |x - x'| < 1 := by
    simpa [Real.dist_eq] using hxx'.trans_le (min_le_right _ _)
  rw [abs_lt] at hxx'1
  rw [Real.dist_eq, ← integral_sub (f.integrable_apply_sub x) (f.integrable_apply_sub x')]
  -- The difference of the two translates is small and vanishes off `[x - R - 1, x + R + 1]`.
  have := abs_integral_le_of_measure_Icc_add_one_le hC
    (φ := fun y ↦ f (y - x) - f (y - x')) (A := ε / (2 * K))
    (fun y ↦ by
      have := hfδ (a := y - x) (b := y - x') (by
        rw [dist_sub_left]
        exact hxx'.trans_le (min_le_left _ _))
      rw [Real.dist_eq] at this
      exact this.le)
    (x - R - 1) (2 * R + 2)
    fun y hy ↦ by
      simp only [mem_Icc, not_and_or, not_le] at hy
      push_cast at hy
      have h₁ : y < x - R ∨ x + R < y := by
        rcases hy with hy | hy
        exacts [Or.inl (by linarith), Or.inr (by linarith)]
      have h₂ : y < x' - R ∨ x' + R < y := by
        rcases hy with hy | hy
        exacts [Or.inl (by linarith), Or.inr (by linarith)]
      rw [hR y x h₁, hR y x' h₂, sub_zero]
  refine this.trans_lt ?_
  have hCK : ((2 * R + 2 : ℕ) + 1) * (C : ℝ) < K := by push_cast; linarith
  calc ε / (2 * K) * ((((2 * R + 2 : ℕ) : ℝ) + 1) * C) ≤ ε / (2 * K) * K := by
        gcongr
    _ < ε := by field_simp; linarith

end MeasureTheory.Measure

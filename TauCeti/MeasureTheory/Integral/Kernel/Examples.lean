/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Counterexamples for compact support of integral operators

On any nontrivial finite-dimensional real normed space equipped with an open-positive measure that
is finite on compacts, the constant identity kernel `(x, y) ↦ id` sends a smooth compactly
supported function to a nonzero constant, which fails to have compact support
(`TauCeti.exists_hasCompactSupport_not_hasCompactSupport_integral_const`).
-/

public section

open MeasureTheory
open scoped ContDiff

namespace TauCeti

/-- On any nontrivial finite-dimensional real normed space (which is in particular noncompact)
equipped with an open-positive measure that is finite on compacts, the constant identity kernel
`(x, y) ↦ id` sends a smooth compactly supported `u` to a nonzero constant, which fails to have
compact support. -/
theorem exists_hasCompactSupport_not_hasCompactSupport_integral_const {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [OpensMeasurableSpace E] (μ : Measure E := by volume_tac)
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ (∫ y, u y ∂μ) ≠ 0 ∧
      ¬HasCompactSupport fun _ : E ↦ ∫ y, (ContinuousLinearMap.id ℝ ℝ) (u y) ∂μ := by
  let b : ContDiffBump (0 : E) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have hint : Integrable b μ := b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
  have hpos : (∫ y : E, b y ∂μ) ≠ 0 :=
    ((integral_pos_iff_support_of_nonneg b.nonneg' hint).mpr
      (b.support_eq.symm ▸ Metric.measure_ball_pos μ 0 b.rOut_pos)).ne'
  refine ⟨b, b.contDiff, b.hasCompactSupport, hpos, fun hc ↦ ?_⟩
  simp only [ContinuousLinearMap.id_apply, HasCompactSupport] at hc
  rw [tsupport, Function.support_const hpos, closure_univ] at hc
  exact NoncompactSpace.noncompact_univ hc

end TauCeti

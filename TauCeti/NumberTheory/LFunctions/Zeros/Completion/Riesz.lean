/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Hadamard.Riesz
public import TauCeti.Analysis.Meromorphic.ZeroFree
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.ContinuedL

/-!
# Riesz zero-series bounds for L-function records

A zero-free half-plane for the continued L-function bounds the Riesz zero contribution of
its entire completion.
-/

public section

namespace TauCeti.LFunctions.AnalyticLFunctionData.HasMeromorphicContinuation

/-- If the entire completion has order below two, a zero-free half-plane right of `σ` for the
continued L-function gives a bound `C * y ^ σ` on the norm of the first Riesz zero series for
`y ≥ 1`. The constant is independent of `σ`. -/
theorem exists_norm_rieszZeroSeries_le_of_zeroFreeRightOf {d : AnalyticLFunctionData}
    (h : d.HasMeromorphicContinuation) {A : ℝ} (hord : OrderLE d.entireCompletion A) (hA : A < 2) :
    ∃ C ≥ 0, ∀ σ : ℝ, ZeroFreeRightOf σ d.continuedL → ∀ y ≥ 1,
      ‖rieszZeroSeries d.entireCompletion y‖ ≤ C * y ^ σ := by
  refine ⟨_, tsum_nonneg (fun _ ↦ norm_nonneg _), fun σ hσ y hy ↦
    hord.norm_rieszZeroSeries_le h.differentiable_entireCompletion hA ?_ hy⟩
  intro ρ hρ
  have hpos := h.meromorphicOrderAt_continuedL_pos_of_entireCompletion_eq_zero hρ
  exact le_of_not_gt fun hlt ↦ hpos.not_ge ((zeroFreeRightOf_iff.mp hσ) ρ hlt)

end TauCeti.LFunctions.AnalyticLFunctionData.HasMeromorphicContinuation

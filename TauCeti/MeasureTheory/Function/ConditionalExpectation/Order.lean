/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Strict positivity of conditional expectations

Conditioning an integrable, almost everywhere strictly positive real random variable
preserves strict positivity. This applies in particular to positive terminal densities,
including conditioning at a bounded stopping time. No deterministic positive lower bound
on the random variable is required.
-/

public section

open Filter Set

namespace MeasureTheory

/-- The conditional expectation of an integrable strictly positive real random variable
is strictly positive almost everywhere. -/
theorem Integrable.condExp_pos {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {f : Ω → ℝ} (hf : Integrable f μ) (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    (hpos : ∀ᵐ ω ∂μ, 0 < f ω) : ∀ᵐ ω ∂μ, 0 < μ[f | m] ω := by
  let A := {ω | μ[f | m] ω = 0}
  have hA : MeasurableSet[m] A :=
    stronglyMeasurable_condExp.measurable (measurableSet_singleton 0)
  have hint : ∫ ω in A, f ω ∂μ = 0 := by
    rw [← setIntegral_condExp hm hf hA]
    exact setIntegral_eq_zero_of_forall_eq_zero fun ω hω ↦ hω
  have hz : f =ᵐ[μ.restrict A] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_ae (hpos.mono fun _ h ↦ h.le))
      hf.integrableOn).mp hint
  have hnull : μ A = 0 := by
    have hfalse : ∀ᵐ _ ∂μ.restrict A, False := by
      filter_upwards [hz, ae_restrict_of_ae hpos] with _ hω hωpos
      exact (ne_of_gt hωpos) hω
    simpa using hfalse
  have hne : ∀ᵐ ω ∂μ, μ[f | m] ω ≠ 0 := by
    simpa only [ae_iff, not_not] using hnull
  filter_upwards [hne, condExp_nonneg (hpos.mono fun _ h ↦ h.le)] with ω hω hωnonneg
  exact lt_of_le_of_ne hωnonneg hω.symm

end MeasureTheory

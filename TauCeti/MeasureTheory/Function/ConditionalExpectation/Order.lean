/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Strict positivity of conditional expectations

For a nonnegative integrable real random variable, its conditional expectation is
strictly positive almost everywhere on the event where the variable is strictly positive.
This applies to terminal densities, including conditioning at a bounded stopping time.
-/

public section

open Filter Set

namespace MeasureTheory

/-- The conditional expectation of a nonnegative integrable real random variable
is strictly positive almost everywhere on the event where the variable is strictly positive. -/
theorem Integrable.ae_pos_imp_condExp_pos {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {f : Ω → ℝ} (hf : Integrable f μ) (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    (hf₀ : 0 ≤ᵐ[μ] f) : ∀ᵐ ω ∂μ, 0 < f ω → 0 < μ[f | m] ω := by
  let A := {ω | μ[f | m] ω = 0}
  have hA : MeasurableSet[m] A :=
    stronglyMeasurable_condExp.measurable (measurableSet_singleton 0)
  have hint : ∫ ω in A, f ω ∂μ = 0 := by
    rw [← setIntegral_condExp hm hf hA]
    exact setIntegral_eq_zero_of_forall_eq_zero fun ω hω ↦ hω
  have hz : f =ᵐ[μ.restrict A] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_ae hf₀) hf.integrableOn).mp hint
  filter_upwards [ae_imp_of_ae_restrict hz, condExp_nonneg (m := m) hf₀] with ω hzero hnonneg hpos
  exact lt_of_le_of_ne hnonneg fun heq ↦ hpos.ne' (hzero heq.symm)

/-- The conditional expectation of an integrable strictly positive real random variable
is strictly positive almost everywhere. -/
theorem Integrable.condExp_pos {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {f : Ω → ℝ} (hf : Integrable f μ) (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    (hpos : ∀ᵐ ω ∂μ, 0 < f ω) : ∀ᵐ ω ∂μ, 0 < μ[f | m] ω :=
  hpos.mp (hf.ae_pos_imp_condExp_pos hm (hpos.mono fun _ h ↦ h.le))

end MeasureTheory

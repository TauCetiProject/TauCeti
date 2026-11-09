/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Interval
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.Normed.Group.Defs

/-!
# Continuous repaired accumulated integrals

For a nonnegative extended-valued function `f`, turn it off at each point where its
original accumulated integral is infinite. The accumulated integral of the resulting
function is continuous, even if the original integral becomes infinite immediately
to the right of a point. Values remain in `ℝ≥0∞`; continuity does not assert finiteness.

The square-energy specialization provides the pathwise clock used to localize
stochastic integrals. The result requires neither local integrability nor a moment
assumption, and applies separately to every path.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [FirstCountableTopology α] [DenselyOrdered α]
  [MeasurableSpace α] [OpensMeasurableSpace α]

/-- The accumulated lower integral becomes continuous after turning the integrand off
where its original accumulated integral is infinite. No measurability or finiteness
assumption on `f` is needed. -/
theorem continuous_setLIntegral_indicator_cumulative_lt_top (μ : Measure α)
    [NullSingletonClass μ] (f : α → ℝ≥0∞) (a : α) :
    Continuous (fun t ↦ ∫⁻ s in Ioc a t,
      {u | ∫⁻ v in Ioc a u, f v ∂μ < ∞}.indicator f s ∂μ) := by
  let ν := (μ.restrict (Ioi a)).withDensity f
  have hν (t : α) : ν (Iic t) = ∫⁻ s in Ioc a t, f s ∂μ := by
    simp only [ν, withDensity_apply _ measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioi]
  have hmono : Monotone (fun u ↦ ν (Iic u)) :=
    fun _ _ h ↦ measure_mono (Iic_subset_Iic.mpr h)
  have hD : MeasurableSet {u | ν (Iic u) < ∞} := hmono.measurable measurableSet_Iio
  have h := ν.continuous_cumulative_restrict_lt_top
  have heq (t : α) : (ν.restrict {u | ν (Iic u) < ∞}) (Iic t) =
      ∫⁻ s in Ioc a t, {u | ∫⁻ v in Ioc a u, f v ∂μ < ∞}.indicator f s ∂μ := by
    rw [restrict_withDensity hD, ← withDensity_indicator hD,
      withDensity_apply _ measurableSet_Iic]
    simp only [Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioi, hν]
  simpa only [heq] using h

/-- The square energy of the cutoff `H* = H 1_{A < ∞}`, where `A` is the original
accumulated square energy, is continuous as an extended-valued function. In particular
this holds pathwise on nonnegative real time, without any integrability hypothesis. -/
theorem continuous_setLIntegral_enorm_sq_indicator_cumulative_lt_top (μ : Measure α)
    [NullSingletonClass μ] {E : Type*} [TopologicalSpace E] [ESeminormedAddMonoid E]
    (H : α → E) (a : α) :
    Continuous (fun t ↦ ∫⁻ s in Ioc a t,
      ‖{u | ∫⁻ v in Ioc a u, ‖H v‖ₑ ^ 2 ∂μ < ∞}.indicator H s‖ₑ ^ 2 ∂μ) := by
  have heq (s : α) :
      ‖{u | ∫⁻ v in Ioc a u, ‖H v‖ₑ ^ 2 ∂μ < ∞}.indicator H s‖ₑ ^ 2 =
        {u | ∫⁻ v in Ioc a u, ‖H v‖ₑ ^ 2 ∂μ < ∞}.indicator (fun v ↦ ‖H v‖ₑ ^ 2) s := by
    by_cases hs : ∫⁻ v in Ioc a s, ‖H v‖ₑ ^ 2 ∂μ < ∞ <;> simp [hs]
  simpa only [heq] using
    μ.continuous_setLIntegral_indicator_cumulative_lt_top (fun v ↦ ‖H v‖ₑ ^ 2) a

end MeasureTheory.Measure

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Bochner integrals against counting measure on arbitrary discrete measurable spaces

Mathlib's `MeasureTheory.integral_countable` expresses `∫ x, f x ∂μ` as an unconditional sum when
the domain `X` is countable, and `MeasureTheory.integral_count` specializes to `Measure.count` when
`X` is finite. For counting measure on an arbitrary measurable space with measurable singletons,
any integrable function `f : X → E` has countable support because `Summable (‖f ·‖)` forces the
support of `f` to be countable. Restricting to `Function.support f` therefore evaluates
`∫ x, f x ∂Measure.count` as `∑' x, f x` without assuming `Countable X` or
`SecondCountableTopology E`.

## Main statements

* `MeasureTheory.Integrable.integral_count`: `∫ x, f x ∂Measure.count = ∑' x, f x` for any
  counting-measure integrable function into a Banach space.
* `MeasureTheory.Integrable.hasSum_count`: `HasSum f (∫ x, f x ∂Measure.count)` under the same
  hypotheses.
-/

public section

namespace MeasureTheory

variable {X E : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- On any measurable space with measurable singletons — without assuming countability of `X` or
second countability of `E` — the Bochner integral of a counting-measure integrable function is its
unconditional sum `∑' x, f x`. -/
theorem Integrable.integral_count {f : X → E} (hf : Integrable f Measure.count) :
    ∫ x, f x ∂Measure.count = ∑' x, f x := by
  have hs : (Function.support f).Countable := by
    simpa only [Function.support, Ne, norm_eq_zero] using
      (integrable_count_iff.mp hf).countable_support
  calc ∫ x, f x ∂Measure.count = ∫ x in Function.support f, f x ∂Measure.count :=
        setIntegral_support.symm
    _ = ∑' x : Function.support f, (Measure.count : Measure X).real {(x : X)} • f x :=
        setIntegral_countable f hs hf.integrableOn
    _ = ∑' x : Function.support f, f x := by simp
    _ = ∑' x, f x := tsum_subtype_eq_of_support_subset Set.Subset.rfl

/-- A counting-measure integrable function into a Banach space has unconditional sum equal to its
Bochner integral. -/
theorem Integrable.hasSum_count {f : X → E} (hf : Integrable f Measure.count) :
    HasSum f (∫ x, f x ∂Measure.count) :=
  hf.integral_count ▸ (integrable_count_iff.mp hf).of_norm.hasSum

end MeasureTheory

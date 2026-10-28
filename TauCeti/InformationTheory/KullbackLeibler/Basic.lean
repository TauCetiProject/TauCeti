/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import TauCeti.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# Basic properties of Kullback–Leibler divergence

This file records general-purpose properties of log-likelihood ratios and Kullback–Leibler
divergence.

## Main results

* `MeasureTheory.Measure.llr_eq_log_real_div_real_singleton`: on a measurable singleton of
  nonzero finite reference mass, the log-likelihood ratio is the logarithm of the quotient of
  the two real singleton masses.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- On a measurable singleton of nonzero finite reference mass, the log-likelihood ratio is the
logarithm of the quotient of the two real singleton masses. -/
theorem llr_eq_log_real_div_real_singleton (π R : Measure α) [π.HaveLebesgueDecomposition R]
    (x : α)
    (hR : R {x} ≠ 0) (hRtop : R {x} ≠ ∞) :
    llr π R x = Real.log (π.real {x} / R.real {x}) := by
  rw [llr, rnDeriv_eq_measure_singleton_div hR hRtop, ENNReal.toReal_div]
  rw [Measure.real, Measure.real]

end MeasureTheory.Measure

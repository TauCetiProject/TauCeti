/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The precise representative of a `W^{1,p}` function

A Sobolev function is locally integrable on its domain, so by the Lebesgue differentiation
theorem it agrees almost everywhere there with its precise representative
`TauCeti.MeasureTheory.preciseRepresentative`, the limit of its averages over shrinking balls.

## Main declarations

* `TauCeti.W1p.ae_eq_preciseRepresentative`: a Sobolev function agrees almost everywhere with its
  precise representative.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A Sobolev function agrees almost everywhere on its domain with its precise representative. -/
theorem W1p.ae_eq_preciseRepresentative (u : W1p mu Omega p) :
    W1p.value u =ᵐ[mu.restrict Omega] preciseRepresentative mu (W1p.value u) :=
  ae_eq_restrict_preciseRepresentative Omega.isOpen (W1p.hasWeakFDerivOn u).locallyIntegrableOn

end TauCeti

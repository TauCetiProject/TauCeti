/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The precise representative of a `W^{k,p}` function

A Sobolev function is locally integrable on its domain, so by the Lebesgue differentiation
theorem it agrees almost everywhere there with its precise representative
`TauCeti.MeasureTheory.preciseRepresentative`, the limit of its averages over shrinking balls.

## Main declarations

* `TauCeti.Wkp.ae_eq_preciseRepresentative`: a Sobolev function agrees almost everywhere with its
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

/-- **Sobolev functions agree with their precise representative.** For `u ∈ W^{k,p}(Ω)`, the
value of `u` agrees almost everywhere on `Ω` with its precise representative, the limit of its
averages over shrinking closed balls. -/
theorem Wkp.ae_eq_preciseRepresentative (k : ℕ) (u : Wkp mu Omega p k) :
    Wkp.value k u =ᵐ[mu.restrict Omega] preciseRepresentative mu (Wkp.value k u) :=
  ae_eq_restrict_preciseRepresentative Omega.isOpen
    (Lp.locallyIntegrableOn (Wkp.value k u) Fact.out)

end TauCeti

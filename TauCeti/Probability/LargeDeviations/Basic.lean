/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Large deviation principles

A family of measures `μ i` on a topological space `X`, indexed along a filter `l`, satisfies a
*large deviation principle* (LDP) with speed `ε` and rate function `I : X → ℝ≥0∞` when
`ε i * log (μ i G)` has `liminf` at least `-inf_G I` for open `G`, and `limsup` at most
`-inf_F I` for closed `F`.

Logarithms are `ENNReal.log : ℝ≥0∞ → EReal`, so that `log 0 = ⊥`. The speed `ε` is a family of
nonnegative reals (for example `1 / n`, normally positive and tending to `0`); the bounds are stated
with `ε i` as a multiplier in `EReal`, where `0 * ⊥ = 0`, so a speed `ε i = 0` is degenerate.

## Main definitions

* `TauCeti.Probability.IsGoodRateFunction I`: `I` is lower semicontinuous with compact sublevel
  sets `{x | I x ≤ α}` for `α < ∞`.
* `TauCeti.Probability.HasLDP l ε μ I`: the open-set lower and closed-set upper bounds.
The contraction principle is in `TauCeti.Probability.LargeDeviations.Contraction`, and the
Dirac-mass example in `TauCeti.Probability.LargeDeviations.Dirac`.

## References

* Dembo–Zeitouni, *Large Deviations Techniques and Applications*, §1.2 and §4.2.
-/

public section

open Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ι X : Type*}

/-- A rate function is *good* if it is lower semicontinuous and has compact sublevel sets at every
finite level. -/
structure IsGoodRateFunction [TopologicalSpace X] (I : X → ℝ≥0∞) : Prop where
  lowerSemicontinuous : LowerSemicontinuous I
  isCompact_sublevel : ∀ α : ℝ≥0∞, α ≠ ∞ → IsCompact {x | I x ≤ α}

/-- The family `μ i`, `i` along the filter `l`, satisfies a large deviation principle with speed
`ε` and rate function `I`. The rate function is lower semicontinuous, and the bounds are
`-inf_G I ≤ liminf ε i * log (μ i G)` for open `G` and
`limsup ε i * log (μ i F) ≤ -inf_F I` for closed `F`. -/
structure HasLDP [TopologicalSpace X] [MeasurableSpace X] (l : Filter ι) (ε : ι → ℝ≥0)
    (μ : ι → Measure X) (I : X → ℝ≥0∞) : Prop where
  lowerSemicontinuous : LowerSemicontinuous I
  lower_bound : ∀ G : Set X, IsOpen G →
    -((⨅ x ∈ G, I x : ℝ≥0∞) : EReal) ≤
      liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i G)) l
  upper_bound : ∀ F : Set X, IsClosed F →
    limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i F)) l ≤
      -((⨅ x ∈ F, I x : ℝ≥0∞) : EReal)

end TauCeti.Probability

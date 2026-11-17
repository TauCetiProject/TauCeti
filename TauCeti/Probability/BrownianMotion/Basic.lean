/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
import TauCeti.Probability.HasLaw

/-!
# Basic properties of real Brownian motion

Any measure supporting a standard real pre-Brownian motion (`ProbabilityTheory.IsPreBrownianReal`)
assigns zero mass to every singleton (`MeasureTheory.NullSingletonClass`), since evaluation at
time `1` has the nondegenerate Gaussian law `gaussianReal 0 1`.

## Main results

* `ProbabilityTheory.IsPreBrownianReal.nullSingletonClass`: any measure supporting a pre-Brownian
  motion assigns zero mass to singletons.
-/

public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Any measure supporting a pre-Brownian motion assigns zero mass to every single sample point. -/
theorem IsPreBrownianReal.nullSingletonClass (hB : IsPreBrownianReal B P) :
    NullSingletonClass P where
  measure_singleton ω := by
    have := nullSingletonClass_gaussianReal (μ := 0) one_ne_zero
    exact (hB.hasLaw_eval 1).measure_singleton_eq_zero ω

end ProbabilityTheory

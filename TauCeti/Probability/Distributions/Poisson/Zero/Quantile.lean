/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Poisson.Zero.Truncated
public import TauCeti.Probability.Distributions.Zero.Quantile

/-!
# Endpoint limits of zero-truncated Poisson quantiles

At positive rate, the real cast of a zero-truncated Poisson law has lower quantile endpoint
one and upper endpoint positive infinity. At rate zero, truncation removes all mass, so
the endpoint theorems require nonzero rate.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal

namespace TauCeti.Probability

variable {r : ℝ≥0}

/-- Zero-truncated Poisson quantiles tend to one as the level tends to zero from above. -/
theorem tendsto_quantile_map_cast_poissonMeasure_cond_compl_zero_nhdsGT_zero (hr : r ≠ 0) :
    Tendsto (fun u ↦ ((((poissonMeasure r)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 1) := by
  exact (poissonMeasure r).tendsto_quantile_map_natCast_cond_compl_zero_nhdsGT_zero
    ((poissonMeasure_singleton_ne_zero_iff r 1).2 (Or.inl hr))

/-- Zero-truncated Poisson quantiles tend to positive infinity as the level tends to one
from below. -/
theorem tendsto_quantile_map_cast_poissonMeasure_cond_compl_zero_nhdsLT_one (hr : r ≠ 0) :
    Tendsto (fun u ↦ ((((poissonMeasure r)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) := by
  apply (poissonMeasure r).tendsto_quantile_map_natCast_cond_compl_zero_nhdsLT_one
  simpa [hr] using tendsto_quantile_map_cast_poissonMeasure_nhdsLT_one r

end TauCeti.Probability

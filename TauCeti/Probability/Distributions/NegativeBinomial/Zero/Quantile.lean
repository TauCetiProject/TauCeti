/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.NegativeBinomial.Zero.Truncated
public import TauCeti.Probability.Distributions.Zero.Quantile

/-!
# Endpoint limits of zero-truncated negative-binomial quantiles

For positive shape and success probability strictly between zero and one, zero-truncated
negative-binomial quantiles tend to one at the lower endpoint and positive infinity at the
upper endpoint. At shape zero or success probability one, truncation removes all mass;
these zero measures are excluded from the probability endpoint statements.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {r p : ℝ}

/-- Zero-truncated negative-binomial quantiles tend to one as the level tends to zero
from above. -/
theorem tendsto_quantile_map_cast_negativeBinomialMeasure_cond_compl_zero_nhdsGT_zero
    (hr : 0 < r) (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun u ↦
      ((((negativeBinomialMeasure r p)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 1) := by
  have := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1.le
  exact (negativeBinomialMeasure r p).tendsto_quantile_map_natCast_cond_compl_zero_nhdsGT_zero
    ((negativeBinomialMeasure_singleton_ne_zero_iff hr.le hp hp1.le 1).2 (Or.inr ⟨hr, hp1⟩))

/-- Zero-truncated negative-binomial quantiles tend to positive infinity as the level tends
to one from below. -/
theorem tendsto_quantile_map_cast_negativeBinomialMeasure_cond_compl_zero_nhdsLT_one
    (hr : 0 < r) (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun u ↦
      ((((negativeBinomialMeasure r p)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) := by
  have := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1.le
  apply (negativeBinomialMeasure r p).tendsto_quantile_map_natCast_cond_compl_zero_nhdsLT_one
  simpa [hr.ne', hp1.ne] using
    tendsto_quantile_map_cast_negativeBinomialMeasure_nhdsLT_one hr.le hp hp1.le

end TauCeti.Probability

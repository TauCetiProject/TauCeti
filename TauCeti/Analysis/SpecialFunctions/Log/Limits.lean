/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Limits of the logarithm

The logarithmic scale of a fixed nonzero numerator divided by a variable approaching zero
tends to infinity. This supplies the diverging scale in logarithmic cutoff estimates.

## Main results

* `Real.tendsto_log_div_nhdsNE_zero`: for `δ ≠ 0`, `log (δ / ε) → ∞` as `ε → 0`, `ε ≠ 0`.

Adapted from Giada Franz’s formalization in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory),
`ForTauCeti/Geometry/Manifold/Riemannian/Surface/LogCutoff/Tendsto.lean`.
-/

public section

open Filter Topology

namespace Real

/-- For fixed `δ ≠ 0`, the scale `log (δ / ε)` tends to infinity as `ε → 0`
through nonzero values. -/
theorem tendsto_log_div_nhdsNE_zero {δ : ℝ} (hδ : δ ≠ 0) :
    Tendsto (fun ε ↦ Real.log (δ / ε)) (𝓝[≠] 0) atTop := by
  have h := tendsto_atTop_add_const_left _ (Real.log δ)
    (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsNE_zero)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp only [Function.comp_apply, Real.log_div hδ hε]
  ring


end Real

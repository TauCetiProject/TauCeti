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
tends to infinity. Consequently, for any two nonzero constants `a` and `b`, the ratio
`log (a / ε) / log (b / ε)` tends to `1` as `ε → 0` through nonzero values. These limits supply
the diverging scale in logarithmic cutoff estimates and rescaling invariance of logarithmic
moduli of continuity.

## Main results

* `Real.tendsto_log_div_nhdsNE_zero`: for `δ ≠ 0`, `log (δ / ε) → ∞` as `ε → 0`, `ε ≠ 0`.
* `Real.tendsto_log_div_div_log_div_nhdsNE_zero`: for `a ≠ 0` and `b ≠ 0`,
  `log (a / ε) / log (b / ε) → 1` as `ε → 0`, `ε ≠ 0`.

`Real.tendsto_log_div_nhdsNE_zero` is adapted from Giada Franz’s formalization in
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

/-- For fixed nonzero constants `a` and `b`, the ratio `log (a / ε) / log (b / ε)` tends to `1`
as `ε → 0` through nonzero values. -/
theorem tendsto_log_div_div_log_div_nhdsNE_zero {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Tendsto (fun ε ↦ Real.log (a / ε) / Real.log (b / ε)) (𝓝[≠] 0) (𝓝 1) := by
  have hb_top := tendsto_log_div_nhdsNE_zero hb
  have h1 : Tendsto (fun ε ↦ 1 + (Real.log a - Real.log b) / Real.log (b / ε)) (𝓝[≠] 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hb_top)
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hb_top.eventually_ne_atTop 0] with ε hε hlog_ne
  rw [one_add_div hlog_ne, Real.log_div ha hε, Real.log_div hb hε]
  congr 1
  ring

end Real

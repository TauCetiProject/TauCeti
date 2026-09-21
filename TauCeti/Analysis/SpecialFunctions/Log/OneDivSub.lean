/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The divergence of `log (1 / (s - a))` as `s` decreases to `a`

`s ↦ log (1 / (s - a))` diverges to `+∞` on a right neighbourhood of `a`, for any real `a`. That
single limit is what this file provides.

The ratio statement it feeds is `TauCeti.tendsto_div_nhds_one_of_le_add_const_of_sub_const_le`,
and lives there rather than here: once a denominator diverges, any numerator agreeing with it up
to a bounded additive error gives a quotient tending to `1`. A Dirichlet density argument uses
the case `a = 1`, with a prime sum estimated as `log (1 / (s - 1)) + O(1)` as the numerator, and
reads the density off the quotient — the divergence is exactly what makes the `O(1)` immaterial.
Nothing here is specific to that application, and the file contains no number theory.

## Main results

* `Real.tendsto_log_one_div_sub_atTop` — `log (1 / (s - a))` tends to `atTop` along `𝓝[>] a`.

## References

Adapted from `tendsto_log_one_div_sub_one_atTop` in
`CebotarevDensity/ForMathlib/LogOneDivSubOne.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. The source states it at
`a = 1`; the statement here is at an arbitrary real translation point.
-/

public section

namespace Real

open Filter Topology

/-- `log (1 / (s - a))` tends to `+∞` as `s` decreases to `a`. At `a = 1` this is the divergence
driving the Dirichlet density asymptotics. -/
theorem tendsto_log_one_div_sub_atTop (a : ℝ) :
    Tendsto (fun s : ℝ ↦ Real.log (1 / (s - a))) (𝓝[>] a) atTop := by
  refine Real.tendsto_log_atTop.comp ?_
  have h1 : Tendsto (fun s : ℝ ↦ s - a) (𝓝[>] a) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((continuous_sub_right a).tendsto' a 0 (by ring)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun s hs ↦ by
        simp only [Set.mem_Ioi] at hs ⊢
        linarith)
  simpa only [one_div, Pi.inv_def] using h1.inv_tendsto_nhdsGT_zero

end Real

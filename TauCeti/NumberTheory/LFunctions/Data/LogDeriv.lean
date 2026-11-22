/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.Basic

import TauCeti.Analysis.Calculus.LogDeriv.Symmetry

/-!
# Logarithmic derivatives of the completed functional equation

The functional equation of an analytic L-function record reflects the logarithmic derivative
of its completed function to minus that of the dual. The root number cancels. The identity
holds as punctured germs even at poles, whose pointwise representatives are unconstrained.
At points where both representatives are continuous it holds pointwise as well, including
zeros. These are the reflection identities used to shift contours in explicit formulas.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory* (2004), §5.1.
-/

public section

open Filter Topology

namespace TauCeti.LFunctions.AnalyticLFunctionData

variable {d : AnalyticLFunctionData}

/-- The completed functional equation reflects logarithmic derivatives as punctured germs,
including at poles. No condition on the value at the centre is imposed. -/
theorem HasFunctionalEquation.logDeriv_eventuallyEq (h : d.HasFunctionalEquation) (s : ℂ) :
    logDeriv d.completed =ᶠ[𝓝[≠] s] fun z ↦ -logDeriv d.dual.completed (1 - z) := by
  filter_upwards [logDeriv_congr_nhdsNE (h.eventuallyEq s)] with z hz
  rw [hz, logDeriv_const_mul z _ h.rootNumber_ne_zero, logDeriv_comp_const_sub]

/-- Where the two completed representatives are continuous, the logarithmic functional
equation holds pointwise, even at zeros. Continuity excludes arbitrary values assigned at poles. -/
theorem HasFunctionalEquation.logDeriv_eq (h : d.HasFunctionalEquation) {s : ℂ}
    (hs : ContinuousAt d.completed s) (hd : ContinuousAt d.dual.completed (1 - s)) :
    logDeriv d.completed s = -logDeriv d.dual.completed (1 - s) := by
  have hcont : ContinuousAt (fun z : ℂ ↦ d.rootNumber * d.dual.completed (1 - z)) s :=
    continuousAt_const.mul (hd.comp (by fun_prop))
  have hg := (hs.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hcont).mp (h.eventuallyEq s)
  rw [(logDeriv_congr_nhds hg).eq_of_nhds, logDeriv_const_mul s _ h.rootNumber_ne_zero,
    logDeriv_comp_const_sub]

end TauCeti.LFunctions.AnalyticLFunctionData

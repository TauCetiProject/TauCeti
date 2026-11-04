/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor

/-!
# The divisor at a point of analyticity

At a point `z ∈ U`, Mathlib's `MeromorphicOn.divisor f U` evaluates to
`(meromorphicOrderAt f z).untop₀`, while zero counts of analytic functions are stated in terms of
`analyticOrderNatAt f z`. This file records the bridge between the two vocabularies at a point
where `f` is analytic.

## Main results

* `MeromorphicOn.divisor_eq_analyticOrderNatAt` — at a point where `f` is analytic, the divisor
  reads `analyticOrderNatAt f z`.
-/

public section

/-- At a point `z ∈ U` where a function meromorphic on `U` is analytic, its divisor on `U`
equals its order of vanishing `analyticOrderNatAt f z`. This includes a point near which `f`
vanishes identically: there the analytic order is infinite and both sides read `0`.

The divisor is defined through `meromorphicOrderAt`, while zero counts of analytic functions are
stated through `analyticOrderNatAt`; this lemma translates between the two, so that a statement
about divisor values of a function analytic on `U` becomes one about its orders of vanishing. It
says nothing at a pole, where `f` is not analytic. -/
theorem MeromorphicOn.divisor_eq_analyticOrderNatAt {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {U : Set 𝕜} {z : 𝕜}
    (hm : MeromorphicOn f U) (hf : AnalyticAt 𝕜 f z) (hz : z ∈ U) :
    divisor f U z = (analyticOrderNatAt f z : ℤ) := by
  rw [hm.divisor_apply hz, hf.meromorphicOrderAt_eq, analyticOrderNatAt]
  cases analyticOrderAt f z <;> simp

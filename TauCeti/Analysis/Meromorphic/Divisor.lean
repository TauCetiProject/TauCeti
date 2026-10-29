/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor

/-!
# The divisor at a point of analyticity

Mathlib's `MeromorphicOn.divisor` evaluates to `(meromorphicOrderAt f z).untop₀`, while zero
counts of analytic functions are stated in terms of `analyticOrderNatAt f z`. This file records
the bridge between the two vocabularies at a point where `f` is analytic.

## Main results

* `MeromorphicOn.divisor_eq_analyticOrderNatAt` — at a point where `f` is analytic, the divisor
  reads `analyticOrderNatAt f z`.
-/

public section

/-- Where a meromorphic function is analytic, its divisor records the order of vanishing. The
identity also holds at a point of infinite order, where both sides read `0`.

This is the bridge between `MeromorphicOn.divisor` — whose support is finite on a ball by
`MeromorphicOn.divisor_ball_support_finite` — and the `analyticOrderNatAt` vocabulary that zero
counts are stated in, so zero-counting arguments can reuse it instead of rebuilding the
correspondence. Note the finiteness is of the divisor's *support*, equivalently of the zeros of
finite order: a point where `f` vanishes identically has divisor value `0` and is absent from it. -/
theorem MeromorphicOn.divisor_eq_analyticOrderNatAt {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {U : Set 𝕜} {z : 𝕜}
    (hm : MeromorphicOn f U) (hf : AnalyticAt 𝕜 f z) (hz : z ∈ U) :
    divisor f U z = (analyticOrderNatAt f z : ℤ) := by
  rw [hm.divisor_apply hz, hf.meromorphicOrderAt_eq, analyticOrderNatAt]
  cases analyticOrderAt f z <;> simp

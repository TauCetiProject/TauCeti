/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Bump functions with support in a ball

On a real normed space with smooth bump functions, every open ball contains the topological
support of a smooth bump function centred at its centre.

## Main results

* `TauCeti.exists_contDiffBump_tsupport_subset_ball`: a bump centred at `c` whose topological
  support lies in the ball of radius `r` around `c`.
-/

public section

open Metric

namespace TauCeti

/-- A smooth bump function centred at `c` whose topological support lies in the ball of radius
`r > 0` around `c`. -/
theorem exists_contDiffBump_tsupport_subset_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [HasContDiffBump E] (c : E) {r : ℝ} (hr : 0 < r) :
    ∃ b : ContDiffBump c, tsupport b ⊆ ball c r :=
  -- the bump of radii `r / 4` and `r / 2`
  ⟨⟨r / 4, r / 2, by positivity, by linarith⟩, by
    rw [ContDiffBump.tsupport_eq]
    exact closedBall_subset_ball (half_lt_self hr)⟩

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Translating `C^n` functions on balls

Translating the argument of a function `f` by `a` moves the ball on which `f` is `C^n`:
if `f` is `C^n` on `ball x R`, then `y ↦ f (y + a)` is `C^n` on `ball (x - a) R`. The case
`a = x` recentres a ball computation at the origin.

## Main declarations

* `ContDiffOn.comp_add_right_ball`: translation of a `C^n` function on a ball.
-/

public section

namespace TauCeti

open Metric

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : WithTop ℕ∞} {f : E → F} {x : E} {R : ℝ}

/-- If `f` is `C^n` on the ball `ball x R`, then its translate `y ↦ f (y + a)` is `C^n` on the
translated ball `ball (x - a) R`. -/
theorem _root_.ContDiffOn.comp_add_right_ball (hf : ContDiffOn 𝕜 n f (ball x R)) (a : E) :
    ContDiffOn 𝕜 n (fun y ↦ f (y + a)) (ball (x - a) R) :=
  hf.comp (contDiffOn_id.add contDiffOn_const) fun y hy ↦ by
    simpa [mem_ball, dist_eq_norm, sub_sub_eq_add_sub] using hy

end TauCeti

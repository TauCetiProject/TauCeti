/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Pointwise

/-!
# Pointwise sums with closed balls in seminormed groups

A point lies outside `s + closedBall 0 r` whenever the closed ball of radius `r` around it misses
`s`. This locates the support of a convolution with a kernel supported in `closedBall 0 r`.

## Main declarations

* `TauCeti.notMem_add_closedBall_zero_of_disjoint`: a point whose closed `r`-ball misses `s` is
  not in `s + closedBall 0 r`.
-/

public section

open Metric Set
open scoped Pointwise

namespace TauCeti

/-- A point whose closed ball of radius `r` misses `s` is not in `s + closedBall 0 r`. -/
theorem notMem_add_closedBall_zero_of_disjoint {E : Type*} [SeminormedAddCommGroup E]
    {s : Set E} {y : E} {r : ℝ} (hy : Disjoint (closedBall y r) s) :
    y ∉ s + closedBall (0 : E) r := by
  rintro ⟨b, hb, a, ha, rfl⟩
  refine hy.notMem_of_mem_left ?_ hb
  rw [mem_closedBall, dist_eq_norm]
  simpa [norm_neg] using ha

end TauCeti

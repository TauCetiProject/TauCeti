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

Adding a closed ball of radius `R₁` about `0` to an annulus `closedBall 0 R₂ \ ball 0 r` gives a
subset of the annulus `closedBall 0 (R₁ + R₂) \ ball 0 (r - R₁)`: the outer radius grows and the
inner radius shrinks by `R₁`. This locates the frequencies of a product of a function with
frequencies in a ball and a function with frequencies in an annulus.

## Main declarations

* `TauCeti.notMem_add_closedBall_zero_of_disjoint`: a point whose closed `r`-ball misses `s` is
  not in `s + closedBall 0 r`.
* `TauCeti.closedBall_zero_add_diff_ball_subset`: the sum of a closed ball about `0` and an
  annulus lies in an annulus.
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

/-- The sum of the closed ball of radius `R₁` about `0` and the annulus
`closedBall 0 R₂ \ ball 0 r` lies in the annulus `closedBall 0 (R₁ + R₂) \ ball 0 (r - R₁)`. -/
theorem closedBall_zero_add_diff_ball_subset {E : Type*} [SeminormedAddCommGroup E]
    (R₁ R₂ r : ℝ) :
    closedBall (0 : E) R₁ + (closedBall 0 R₂ \ ball 0 r) ⊆
      closedBall 0 (R₁ + R₂) \ ball 0 (r - R₁) := by
  rintro _ ⟨x, hx, y, ⟨hy, hy'⟩, rfl⟩
  simp only [mem_closedBall_zero_iff, mem_ball_zero_iff, not_lt, mem_sdiff] at hx hy hy' ⊢
  have := norm_sub_le (x + y) x
  rw [add_sub_cancel_left] at this
  exact ⟨(norm_add_le x y).trans (add_le_add hx hy), by linarith⟩

end TauCeti

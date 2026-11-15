/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Convex functions bounded above on a whole space are constant

A convex function `f : E → ℝ` on a real vector space which is bounded above is constant
(`ConvexOn.eq_of_bddAbove`). On a line this is the monotonicity of slopes: if `f 1 < f 0`, then
for `t < 0` the slope of `f` on `[t, 0]` is at most the slope `f 1 - f 0 < 0` on `[0, 1]`, so
`f t ≥ f 0 + (f 0 - f 1) (-t)` grows without bound as `t → -∞`. The general case restricts `f`
to the line through two points.

This is the elementary form of the maximum principle used for convexity arguments on a whole
line. A nonnegative function with `f'' ≥ κ f` for some `κ > 0` is convex, so if it is bounded it
is constant; then `f'' = 0`, and `κ f ≤ 0` forces `f = 0`
(`TauCeti.eq_zero_of_hasDerivAt_of_mul_le_of_bddAbove`).
-/

public section

open Set

/-- On the real line, a convex function bounded above has `f 0 ≤ f 1`. -/
private theorem ConvexOn.apply_zero_le_apply_one_of_bddAbove {f : ℝ → ℝ}
    (hf : ConvexOn ℝ univ f) (hb : BddAbove (range f)) : f 0 ≤ f 1 := by
  by_contra! h
  obtain ⟨C, hC⟩ := hb
  -- For `t < 0`, the slope on `[t, 0]` is at most the slope `f 1 - f 0 < 0` on `[0, 1]`.
  have hgrow (t : ℝ) (ht : t < 0) : f 0 + (f 0 - f 1) * -t ≤ f t := by
    have hs := hf.slope_mono_adjacent (mem_univ t) (mem_univ 1) ht zero_lt_one
    rw [zero_sub, div_le_iff₀ (neg_pos.2 ht)] at hs
    linarith
  set t := -((C - f 0) / (f 0 - f 1) + 1) with ht_def
  have hpos : 0 < f 0 - f 1 := sub_pos.2 h
  have ht : t < 0 := by
    have : f 0 ≤ C := hC (mem_range_self 0)
    rw [ht_def, neg_neg_iff_pos]
    positivity
  have hle := (hgrow t ht).trans (hC (mem_range_self t))
  rw [ht_def, neg_neg, mul_add, mul_div_cancel₀ _ hpos.ne'] at hle
  linarith

/-- **A convex function bounded above is constant.** A convex function on a whole real vector
space whose values are bounded above takes the same value at any two points. -/
theorem ConvexOn.eq_of_bddAbove {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hb : BddAbove (range f)) (x y : E) : f x = f y := by
  -- Restrict `f` to the line through `x` and `y`, in both directions.
  have hline (x y : E) : f x ≤ f y := by
    have hc : ConvexOn ℝ univ (f ∘ AffineMap.lineMap (k := ℝ) x y) := hf.comp_affineMap _
    have hbl : BddAbove (range (f ∘ AffineMap.lineMap (k := ℝ) x y)) :=
      hb.mono (range_comp_subset_range _ _)
    simpa using hc.apply_zero_le_apply_one_of_bddAbove hbl
  exact (hline x y).antisymm (hline y x)

namespace TauCeti

/-- **A bounded nonnegative function with `f'' ≥ κ f` vanishes.** Let `f : ℝ → ℝ` be twice
differentiable, nonnegative and bounded above, with `κ f ≤ f''` for some `κ > 0`. Then `f = 0`. -/
theorem eq_zero_of_hasDerivAt_of_mul_le_of_bddAbove {f f' f'' : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hle : ∀ x, κ * f x ≤ f'' x) (h0 : ∀ x, 0 ≤ f x) (hb : BddAbove (range f)) (x : ℝ) :
    f x = 0 := by
  have hderiv : deriv f = f' := funext fun x ↦ (hf x).deriv
  -- `f'' ≥ κ f ≥ 0`, so `f` is convex, hence constant.
  have hconv : ConvexOn ℝ univ f := by
    refine convexOn_univ_of_deriv2_nonneg (fun x ↦ (hf x).differentiableAt)
      (hderiv ▸ fun x ↦ (hf' x).differentiableAt) fun x ↦ ?_
    rw [Function.iterate_succ_apply, Function.iterate_one, hderiv, (hf' x).deriv]
    exact (mul_nonneg hκ.le (h0 x)).trans (hle x)
  have hconst : f = fun _ ↦ f 0 := funext fun y ↦ hconv.eq_of_bddAbove hb y 0
  -- A constant function has vanishing first and second derivatives.
  have hf'0 : f' = fun _ ↦ 0 := funext fun y ↦ by
    rw [← (hf y).deriv, hconst, deriv_const]
  have hf''0 : f'' x = 0 := by
    rw [← (hf' x).deriv, hf'0, deriv_const]
  have := hle x
  rw [hf''0] at this
  exact le_antisymm (nonpos_of_mul_nonpos_right this hκ) (h0 x)

end TauCeti

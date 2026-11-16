/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Second differences of maps with Lipschitz derivative

Let `f` be differentiable on a convex set `s`, with derivative of norm at most `C` and
`L`-Lipschitz on `s`. Then the second difference of `f` satisfies

`‖(f (a + b) - f a) - (f (a' + b') - f a')‖ ≤ C ‖b - b'‖ + L ‖b'‖ ‖a - a'‖`

whenever `a`, `a'`, `a + b`, `a + b'` and `a' + b'` lie in `s`
(`Convex.norm_image_sub_sub_sub_le_of_norm_fderiv_le`). The first term changes the increment `b`
into `b'` at the base point `a`; the second moves the base point of `y ↦ f (y + b') - f y`, whose
derivative `Df(y + b') - Df(y)` is at most `L ‖b'‖`, from `a'` to `a`. Both steps are Mathlib's
mean value inequality `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`.

This is the estimate that makes a nonlinear coefficient `x ↦ J(u(x))` Lipschitz in the map `u` for
Hölder norms.
-/

public section

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {f : E → G} {s : Set E} {C L : ℝ}

/-- **Second-difference estimate.** If `f` is differentiable on the convex set `s`, with
`‖Df‖ ≤ C` and `Df` `L`-Lipschitz there, then
`‖(f (a + b) - f a) - (f (a' + b') - f a')‖ ≤ C ‖b - b'‖ + L ‖b'‖ ‖a - a'‖`
when `a`, `a'`, `a + b`, `a + b'` and `a' + b'` lie in `s`. -/
theorem Convex.norm_image_sub_sub_sub_le_of_norm_fderiv_le (hs : Convex ℝ s)
    (hd : ∀ x ∈ s, DifferentiableAt ℝ f x) (hC : ∀ x ∈ s, ‖fderiv ℝ f x‖ ≤ C)
    (hL : ∀ x ∈ s, ∀ y ∈ s, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x - y‖)
    {a a' b b' : E} (ha : a ∈ s) (ha' : a' ∈ s) (hab : a + b ∈ s) (hab' : a + b' ∈ s)
    (ha'b' : a' + b' ∈ s) :
    ‖(f (a + b) - f a) - (f (a' + b') - f a')‖ ≤ C * ‖b - b'‖ + L * ‖b'‖ * ‖a - a'‖ := by
  -- The first step changes `b` into `b'` at the base point `a`.
  have hfirst : ‖f (a + b) - f (a + b')‖ ≤ C * ‖b - b'‖ := by
    simpa using hs.norm_image_sub_le_of_norm_fderiv_le hd hC hab' hab
  -- The second step moves the base point of `y ↦ f (y + b') - f y` from `a'` to `a`.
  have hseg : ∀ y ∈ segment ℝ a' a, y ∈ s ∧ y + b' ∈ s := fun y hy ↦ by
    refine ⟨hs.segment_subset ha' ha hy, hs.segment_subset ha'b' hab' ?_⟩
    have h : b' + y ∈ segment ℝ (b' + a') (b' + a) := by
      rw [← segment_translate_image]
      exact ⟨y, hy, rfl⟩
    simpa only [add_comm b'] using h
  have hsecond : ‖(f (a + b') - f a) - (f (a' + b') - f a')‖ ≤ L * ‖b'‖ * ‖a - a'‖ := by
    have hφd : ∀ y ∈ segment ℝ a' a, HasFDerivWithinAt (fun y ↦ f (y + b') - f y)
        (fderiv ℝ f (y + b') - fderiv ℝ f y) (segment ℝ a' a) y := fun y hy ↦ by
      have hshift := (hd _ (hseg y hy).2).hasFDerivAt.comp y ((hasFDerivAt_id y).add_const b')
      rw [ContinuousLinearMap.comp_id] at hshift
      exact (hshift.sub (hd y (hseg y hy).1).hasFDerivAt).hasFDerivWithinAt
    refine (convex_segment a' a).norm_image_sub_le_of_norm_hasFDerivWithin_le hφd
      (fun y hy ↦ ?_) (left_mem_segment ℝ a' a) (right_mem_segment ℝ a' a)
    simpa using hL _ (hseg y hy).2 y (hseg y hy).1
  calc _ = ‖(f (a + b) - f (a + b')) + ((f (a + b') - f a) - (f (a' + b') - f a'))‖ := by
        congr 1; abel
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add hfirst hsecond)

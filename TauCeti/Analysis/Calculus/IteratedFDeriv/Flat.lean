/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Iterated derivatives of functions flat at a point

If the derivatives of order `1 ≤ i ≤ k` of a `C^{k+1}` function `f` vanish at `x`, then iterating
the mean value inequality down the tower of derivatives bounds how far each derivative of order at
most `k` moves away from `x`: on a convex set where `‖D^{k+1} f‖ ≤ M`, the derivative of order
`k - j` moves by at most `M * ‖y - x‖ ^ (j + 1)`
(`TauCeti.norm_iteratedFDeriv_sub_le_of_iteratedFDeriv_eq_zero`).
-/

public section

namespace TauCeti

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : E → F} {k : ℕ} {s : Set E}

/-- If `f` is `C^{k+1}` on a convex set `s` with `‖D^{k+1} f‖ ≤ M` there, and the derivatives of
order `1 ≤ i ≤ k` vanish at `x ∈ s`, then for every `j ≤ k` the derivative of order `k - j` moves
by at most `M * ‖y - x‖ ^ (j + 1)` between `x` and `y ∈ s`. Each step of the descending induction
is one application of the mean value inequality along the segment from `x` to `y`. -/
theorem norm_iteratedFDeriv_sub_le_of_iteratedFDeriv_eq_zero {M : ℝ} {x : E}
    (hf : ∀ y ∈ s, ContDiffAt ℝ (k + 1 : ℕ) f y) (hs : Convex ℝ s) (hx : x ∈ s)
    (hM : ∀ y ∈ s, ‖iteratedFDeriv ℝ (k + 1) f y‖ ≤ M)
    (hzero : ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0) :
    ∀ j ≤ k, ∀ y ∈ s, ‖iteratedFDeriv ℝ (k - j) f y - iteratedFDeriv ℝ (k - j) f x‖
      ≤ M * ‖y - x‖ ^ (j + 1) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x hx)
  have hdiff : ∀ i ≤ k, ∀ y ∈ s, DifferentiableAt ℝ (iteratedFDeriv ℝ i f) y := fun i hi y hy ↦
    (hf y hy).differentiableAt_iteratedFDeriv (mod_cast Nat.lt_succ_of_le hi)
  intro j
  induction j with
  | zero =>
    intro _ y hy
    simpa using hs.norm_image_sub_le_of_norm_fderiv_le (fun z hz ↦ hdiff k le_rfl z hz)
      (fun z hz ↦ by rw [norm_fderiv_iteratedFDeriv]; exact hM z hz) hx hy
  | succ j ih =>
    intro hjk y hy
    have hj : j ≤ k := by omega
    have hstep : k - (j + 1) + 1 = k - j := by omega
    have hvanish : ∀ z ∈ s, ‖iteratedFDeriv ℝ (k - j) f z‖ ≤ M * ‖z - x‖ ^ (j + 1) := by
      intro z hz
      simpa [hzero (k - j) (by omega) (by omega)] using ih hj z hz
    have hseg : segment ℝ x y ⊆ s := hs.segment_subset hx hy
    have hbound : ∀ z ∈ segment ℝ x y,
        ‖fderiv ℝ (iteratedFDeriv ℝ (k - (j + 1)) f) z‖ ≤ M * ‖y - x‖ ^ (j + 1) := by
      intro z hz
      rw [norm_fderiv_iteratedFDeriv, hstep]
      refine (hvanish z (hseg hz)).trans ?_
      gcongr
      exact norm_sub_le_of_mem_segment hz
    have := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz ↦ hdiff _ (by omega) z (hseg hz)) hbound (left_mem_segment ℝ x y)
      (right_mem_segment ℝ x y)
    calc ‖iteratedFDeriv ℝ (k - (j + 1)) f y - iteratedFDeriv ℝ (k - (j + 1)) f x‖
        ≤ M * ‖y - x‖ ^ (j + 1) * ‖y - x‖ := this
      _ = M * ‖y - x‖ ^ (j + 1 + 1) := by rw [mul_assoc, ← pow_succ]

end TauCeti

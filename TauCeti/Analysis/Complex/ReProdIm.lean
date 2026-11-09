/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Complex.Basic

/-!
# The sets `s ×ℂ t` and periodicity in the coordinate directions

Facts about the sets `s ×ℂ t = {z | z.re ∈ s ∧ z.im ∈ t}` that are used for functions on `ℂ`
periodic under `z ↦ z + 1` or `z ↦ z + i`.

* `Complex.reProdIm_union_right`: `s ×ℂ (t ∪ t') = s ×ℂ t ∪ s ×ℂ t'`.
* `Complex.sub_floor_mem_reProdIm`: subtracting the lattice vector `⌊z.re⌋ + ⌊z.im⌋ i` moves `z`
  into the unit square `[0, 1) ×ℂ [0, 1)`.
* `Function.Periodic.exists_bound_of_continuousOn_reProdIm_univ`: a function periodic under
  `z ↦ z + i` and continuous on a vertical band `s ×ℂ univ` over a compact `s` is bounded there.
-/

public section

open Function Set

namespace Complex

/-- The set `s ×ℂ t` distributes over unions in the imaginary factor. -/
theorem reProdIm_union_right (s t t' : Set ℝ) : s ×ℂ (t ∪ t') = s ×ℂ t ∪ s ×ℂ t' := by
  ext z
  simp only [mem_reProdIm, mem_union, and_or_left]

/-- Subtracting the lattice vector `⌊z.re⌋ + ⌊z.im⌋ i` moves `z` into the unit square. -/
theorem sub_floor_mem_reProdIm (z : ℂ) :
    z - ((⌊z.re⌋ : ℂ) + ⌊z.im⌋ * I) ∈ Ico 0 1 ×ℂ Ico 0 1 := by
  simp only [mem_reProdIm, sub_re, add_re, intCast_re, mul_re, intCast_im, I_re, I_im, mul_zero,
    mul_one, sub_zero, add_zero, sub_im, add_im, mul_im, zero_add, mem_Ico, sub_nonneg]
  exact ⟨⟨Int.floor_le _, by linarith [Int.lt_floor_add_one z.re]⟩,
    Int.floor_le _, by linarith [Int.lt_floor_add_one z.im]⟩

end Complex

namespace Function

open Complex

/-- A function periodic under `z ↦ z + i` and continuous on the vertical band `s ×ℂ univ` over a
compact set `s` is bounded on that band. -/
theorem Periodic.exists_bound_of_continuousOn_reProdIm_univ {E : Type*} [SeminormedAddGroup E]
    {g : ℂ → E} (hg : Periodic g I) {s : Set ℝ} (hs : IsCompact s)
    (hc : ContinuousOn g (s ×ℂ univ)) : ∃ C, ∀ z ∈ s ×ℂ univ, ‖g z‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hs.reProdIm isCompact_Icc).exists_bound_of_continuousOn
    (hc.mono fun z (hz : z ∈ s ×ℂ Icc 0 1) ↦ ⟨hz.1, mem_univ _⟩)
  refine ⟨C, fun z hz ↦ ?_⟩
  -- Move `z` into one period by an integer multiple of `i`.
  have hmem : z - ⌊z.im⌋ * I ∈ s ×ℂ Icc 0 1 := by
    simp only [mem_reProdIm, sub_re, mul_re, intCast_re, intCast_im, I_re, I_im, mul_zero,
      mul_one, sub_zero, sub_im, mul_im, add_zero, mem_Icc, sub_nonneg]
    exact ⟨hz.1, Int.floor_le _, by linarith [Int.lt_floor_add_one z.im]⟩
  rw [← hg.sub_int_mul_eq ⌊z.im⌋]
  exact hC _ hmem

end Function

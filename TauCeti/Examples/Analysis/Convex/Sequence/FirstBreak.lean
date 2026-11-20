/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.FirstBreak

/-!
# First breaks: a genuine break and a near miss

Two infinite height sequences through the points `(0, 0)` and `(1, 1)`, on which the line of slope
`1` through the origin supports the points.

* The points `(n, 2 n - 1)` for `n ≥ 1` also lie on the line of slope `2` through `(1, 1)`, so the
  lower convex envelope has a first break at `1` of slope `1`
  (`TauCeti.FirstBreakExample.isFirstBreak_steep`).
* The points `(n, n + 1 / n)` for `n ≥ 2` lie strictly above the line of slope `1`, which touches
  the points exactly at `0` and `1` (`TauCeti.FirstBreakExample.supportingFace_approaching`). They
  approach that line, so no line of larger slope through `(1, 1)` supports them, and the lower
  convex envelope has no first break at `1`
  (`TauCeti.FirstBreakExample.not_isFirstBreak_approaching`). Pointwise strict inequalities beyond
  the candidate break therefore do not imply a break for an infinite sequence.
-/

public section

namespace TauCeti.FirstBreakExample

/-- The points `(0, 0)` and `(n, 2 n - 1)` for `n ≥ 1`. -/
noncomputable def steep (n : ℕ) : WithTop ℝ :=
  ((if n = 0 then 0 else 2 * n - 1 : ℝ) : WithTop ℝ)

/-- The line of slope `1` through the origin supports `steep`. -/
theorem isSupportingLine_steep : IsSupportingLine steep 1 0 :=
  isSupportingLine_iff_forall.mpr fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [steep]
    · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      simp only [steep, hn.ne', ↓reduceIte, WithTop.coe_le_coe]
      linarith

/-- The lower convex envelope of `steep` has a first break at `1` of slope `1`. -/
theorem isFirstBreak_steep : IsFirstBreak (lowerConvexEnvelope steep) 1 0 1 := by
  refine ((isLowerConvexEnvelope_lowerConvexEnvelope
    isSupportingLine_steep.isAdmissible).isFirstBreak_iff).mpr
    ⟨zero_lt_one, fun n hn => absurd hn (Nat.not_lt_zero n), 0, isSupportingLine_steep,
      mem_supportingFace.mpr (by simp [steep]), mem_supportingFace.mpr (by norm_num [steep]), 2,
      by norm_num, isSupportingLine_iff_forall.mpr fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [steep, ↓reduceIte, WithTop.coe_le_coe]
    norm_num
  · simp only [steep, hn.ne', ↓reduceIte, WithTop.coe_le_coe]
    norm_num

/-- The points `(0, 0)`, `(1, 1)` and `(n, n + 1 / n)` for `n ≥ 2`. -/
noncomputable def approaching (n : ℕ) : WithTop ℝ :=
  ((n + if n ≤ 1 then 0 else (n : ℝ)⁻¹ : ℝ) : WithTop ℝ)

/-- The line of slope `1` through the origin supports `approaching`. -/
theorem isSupportingLine_approaching : IsSupportingLine approaching 1 0 :=
  isSupportingLine_iff_forall.mpr fun n => by
    simp only [approaching, zero_add, one_mul, WithTop.coe_le_coe, le_add_iff_nonneg_right]
    split_ifs
    · exact le_rfl
    · positivity

/-- The line of slope `1` through the origin touches `approaching` exactly at `0` and `1`: every
later point lies strictly above it. -/
theorem supportingFace_approaching : supportingFace approaching 1 0 = {0, 1} := by
  ext n
  simp only [mem_supportingFace, approaching, zero_add, one_mul, WithTop.coe_eq_coe,
    add_eq_left, Set.mem_insert_iff, Set.mem_singleton_iff]
  split_ifs with hn
  · simp only [true_iff]
    omega
  · simp only [inv_eq_zero, Nat.cast_eq_zero]
    omega

/-- The lower convex envelope of `approaching` has no first break at `1`: although its points
beyond `1` lie strictly above the line of slope `1` through the first two points, no line of
larger slope through `(1, 1)` lies below all of them. -/
theorem not_isFirstBreak_approaching : ¬IsFirstBreak (lowerConvexEnvelope approaching) 1 0 1 := by
  rw [(isLowerConvexEnvelope_lowerConvexEnvelope
    isSupportingLine_approaching.isAdmissible).isFirstBreak_iff]
  rintro ⟨-, -, c, -, -, h1, τ, hτ, hc⟩
  have hc0 : c = 0 := by
    have := WithTop.coe_injective (mem_supportingFace.mp h1)
    norm_num at this
    linarith
  subst hc0
  -- A point far enough out lies below the steeper line through `(1, 1)`.
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (τ - 1) + 1)
  have hτ1 : 0 < τ - 1 := sub_pos.mpr hτ
  have hpos : 0 < 1 / (τ - 1) := one_div_pos.mpr hτ1
  have hn2 : ¬n ≤ 1 := fun h => by
    have : (n : ℝ) ≤ 1 := by exact_mod_cast h
    linarith
  have hle := isSupportingLine_iff_forall.mp hc n
  simp only [approaching, hn2, ↓reduceIte, WithTop.coe_le_coe, Nat.cast_one] at hle
  have hinv : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hbig : 1 < (τ - 1) * (n - 1) := by
    have := mul_lt_mul_of_pos_left (show 1 / (τ - 1) < n - 1 by linarith) hτ1
    rwa [mul_one_div_cancel hτ1.ne'] at this
  nlinarith

end TauCeti.FirstBreakExample

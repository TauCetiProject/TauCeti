/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.FirstBreak
public import TauCeti.Analysis.Convex.Sequence.Envelope

/-!
# Pointwise strict inequalities do not force a first break

For a sequence with finitely many finite points, such as the coefficient heights of a
polynomial, the lower convex envelope has its first break at `j` with slope `m` as soon as a line
of slope `m` supports the points, passes through the first point and the point at `j`, and lies
strictly below every later point (`TauCeti.IsLowerConvexEnvelope.isFirstBreak_iff_of_finite`).
This example shows that the finiteness cannot be dropped.

The heights `0, 0, 1/2, 1/3, 1/4, …` lie on the horizontal line through the points at `0` and
`1`, and strictly above it after `1`. Since they tend to `0`, their lower convex envelope is the
horizontal ray of height `0`, which has no first break at all.
-/

public section

namespace TauCeti.FirstBreakExample

/-- The heights `0, 0, 1/2, 1/3, 1/4, …`: zero at `0` and `1`, and `1 / n` at every `n ≥ 2`. -/
noncomputable def heights (n : ℕ) : WithTop ℝ :=
  if n ≤ 1 then 0 else (((n : ℝ)⁻¹ : ℝ) : WithTop ℝ)

/-- Every point after `1` lies strictly above the horizontal line through the points at `0` and
`1`. -/
theorem zero_lt_heights {n : ℕ} (hn : 1 < n) : (0 : WithTop ℝ) < heights n := by
  rw [heights, ite_eq_right (not_le.mpr hn), ← WithTop.coe_zero, WithTop.coe_lt_coe]
  exact inv_pos.mpr (Nat.cast_pos.mpr (by omega))

/-- The horizontal line of height `0` supports the heights. -/
theorem isSupportingLine_heights : IsSupportingLine heights 0 0 := by
  refine isSupportingLine_iff_forall.mpr fun n ↦ ?_
  rw [zero_mul, add_zero, WithTop.coe_zero]
  rcases le_or_gt n 1 with hn | hn
  · rw [heights, ite_eq_left hn]
  · exact (zero_lt_heights hn).le

/-- The lower convex envelope of the heights `0, 0, 1/2, 1/3, …` has no first break, although
the horizontal line through its first two points lies strictly below all later points. -/
theorem not_isFirstBreak_lowerConvexEnvelope_heights (m : ℝ) (j : ℕ) :
    ¬IsFirstBreak (lowerConvexEnvelope heights) m j := by
  have hh := isLowerConvexEnvelope_lowerConvexEnvelope isSupportingLine_heights.isAdmissible
  have h0 : heights 0 = 0 := by rw [heights, ite_eq_left zero_le_one]
  have h1 : heights 1 = 0 := by rw [heights, ite_eq_left le_rfl]
  rw [hh.isFirstBreak_iff (a := 0) (by rw [h0]; exact WithTop.coe_ne_top)
    fun n hn ↦ absurd hn (Nat.not_lt_zero n)]
  rintro ⟨hj, c, hc, hc0, hcj, τ, hτ, hτc⟩
  rw [mem_supportingFace, h0, Nat.cast_zero, mul_zero, add_zero, ← WithTop.coe_zero,
    WithTop.coe_eq_coe] at hc0
  subst hc0
  -- The supporting line through `(0, 0)` cannot rise, as it lies below the point `(1, 0)`.
  have hm : m ≤ 0 := by
    have := isSupportingLine_iff_forall.mp hc 1
    rwa [h1, ← WithTop.coe_zero, WithTop.coe_le_coe, Nat.cast_one, mul_one, zero_add] at this
  rw [mem_supportingFace] at hcj
  rcases (Nat.one_le_iff_ne_zero.mpr hj.ne').eq_or_lt with rfl | hj2
  · -- At `j = 1` the slope is `0`, and no steeper line stays below the heights `1 / n`.
    rw [h1, ← WithTop.coe_zero, WithTop.coe_eq_coe, Nat.cast_one, mul_one, zero_add] at hcj
    subst hcj
    set n := ⌈τ⁻¹⌉₊ + 1
    have hτn := isSupportingLine_iff_forall.mp hτc n
    rw [heights, ite_eq_right (by omega), WithTop.coe_le_coe] at hτn
    have hn : τ⁻¹ < n := by
      simp only [n, Nat.cast_add, Nat.cast_one]
      linarith [Nat.le_ceil τ⁻¹]
    have h1n : ((1 + n : ℕ) : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by
      push_cast
      linarith [(inv_pos.mpr hτ).trans hn])
    have : 1 < τ * n := by
      rwa [inv_lt_iff_one_lt_mul₀ hτ, mul_comm] at hn
    linarith
  · -- For `j ≥ 2` the point `(j, 1 / j)` lies above every line of nonpositive slope through
    -- `(0, 0)`.
    rw [heights, ite_eq_right (by omega), WithTop.coe_eq_coe, zero_add] at hcj
    have hjpos : (0 : ℝ) < j := Nat.cast_pos.mpr hj
    have : (0 : ℝ) < (j : ℝ)⁻¹ := inv_pos.mpr hjpos
    nlinarith

end TauCeti.FirstBreakExample

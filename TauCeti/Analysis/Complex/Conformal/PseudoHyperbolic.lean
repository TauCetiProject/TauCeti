/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.UnitDisc.Basic

/-!
# The pseudo-hyperbolic expression on the unit disc

This file records the scalar pseudo-hyperbolic expression
`‖(z - w) / (1 - conj w * z)‖` used in the Schwarz--Pick layer of the conformal-mapping
roadmap.  The main API proves that the denominator is nonzero on the open unit disc, the
expression is symmetric, and it is strictly less than one for two points of the unit disc.

This L2 material is coordinated with the upstream Mathlib RMT effort in
leanprover-community/mathlib4#33505.  Mathlib already contains the preceding human-curated
work in `Analysis/Complex/RiemannMapping.lean` and `Analysis/Complex/BranchLogRoot.lean`;
any Tau Ceti overlap with the L0--L3 prerequisites is a temporary shim to be deleted or
refactored to Mathlib once the corresponding upstream API lands.
-/

public section

namespace TauCeti

open Complex Metric Set
open scoped ComplexConjugate

/-- The pseudo-hyperbolic expression on `ℂ`, written as a total real-valued function.

On the open unit disc this is the pseudo-hyperbolic distance.  Outside the disc the same
formula is still meaningful as a total expression in Lean, with division by zero evaluating
to zero as usual. -/
noncomputable def pseudoHyperbolicDist (z w : ℂ) : ℝ :=
  ‖(z - w) / (1 - (starRingEnd ℂ) w * z)‖

/-- The defining formula for the pseudo-hyperbolic expression. -/
lemma pseudoHyperbolicDist_def (z w : ℂ) :
    pseudoHyperbolicDist z w = ‖(z - w) / (1 - (starRingEnd ℂ) w * z)‖ :=
  by rfl

@[simp]
lemma pseudoHyperbolicDist_nonneg (z w : ℂ) : 0 ≤ pseudoHyperbolicDist z w :=
  norm_nonneg _

/-- The pseudo-hyperbolic expression from a point to itself is zero. -/
@[simp]
lemma pseudoHyperbolicDist_self (z : ℂ) : pseudoHyperbolicDist z z = 0 := by
  simp [pseudoHyperbolicDist]

/-- The denominator `1 - conj w * z` is nonzero whenever `‖w‖ * ‖z‖ < 1`. -/
lemma one_sub_conj_mul_ne_zero_of_norm_mul_lt_one {z w : ℂ} (h : ‖w‖ * ‖z‖ < 1) :
    1 - (starRingEnd ℂ) w * z ≠ 0 := by
  exact (isUnit_one_sub_of_norm_lt_one (x := (starRingEnd ℂ) w * z)
    (by simpa [norm_mul, norm_conj] using h)).ne_zero

/-- The denominator `1 - conj w * z` is nonzero for two points of norm less than one. -/
lemma one_sub_conj_mul_ne_zero_of_norm_lt_one {z w : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    1 - (starRingEnd ℂ) w * z ≠ 0 :=
  one_sub_conj_mul_ne_zero_of_norm_mul_lt_one
    (mul_lt_one_of_nonneg_of_lt_one_right hw.le (norm_nonneg _) hz)

/-- The denominator `1 - conj w * z` is nonzero for two points of the open unit ball. -/
lemma one_sub_conj_mul_ne_zero_of_mem_ball {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    1 - (starRingEnd ℂ) w * z ≠ 0 :=
  one_sub_conj_mul_ne_zero_of_norm_lt_one (by simpa [mem_ball_zero_iff] using hz)
    (by simpa [mem_ball_zero_iff] using hw)

/-- The denominator `1 - conj w * z` is nonzero for two bundled unit-disc points. -/
lemma one_sub_conj_mul_ne_zero_unitDisc (z w : Complex.UnitDisc) :
    1 - (starRingEnd ℂ) (w : ℂ) * (z : ℂ) ≠ 0 :=
  one_sub_conj_mul_ne_zero_of_norm_lt_one z.norm_lt_one w.norm_lt_one

private lemma norm_one_sub_conj_mul_comm (z w : ℂ) :
    ‖1 - (starRingEnd ℂ) w * z‖ = ‖1 - (starRingEnd ℂ) z * w‖ := by
  calc
    ‖1 - (starRingEnd ℂ) w * z‖ =
        ‖(starRingEnd ℂ) (1 - (starRingEnd ℂ) w * z)‖ := by rw [norm_conj]
    _ = ‖1 - (starRingEnd ℂ) z * w‖ := by
      congr 1
      simp [mul_comm]

/-- The pseudo-hyperbolic expression is symmetric in its two arguments. -/
lemma pseudoHyperbolicDist_comm (z w : ℂ) :
    pseudoHyperbolicDist z w = pseudoHyperbolicDist w z := by
  unfold pseudoHyperbolicDist
  rw [norm_div, norm_div, norm_sub_rev, norm_one_sub_conj_mul_comm]

/-- If the two points are equal, their pseudo-hyperbolic expression is zero. -/
lemma pseudoHyperbolicDist_eq_zero_of_eq {z w : ℂ} (h : z = w) :
    pseudoHyperbolicDist z w = 0 := by
  simp [h]

/-- The pseudo-hyperbolic expression with right endpoint zero is the norm. -/
@[simp]
lemma pseudoHyperbolicDist_zero_right (z : ℂ) : pseudoHyperbolicDist z 0 = ‖z‖ := by
  simp [pseudoHyperbolicDist]

/-- The pseudo-hyperbolic expression with left endpoint zero is the norm. -/
@[simp]
lemma pseudoHyperbolicDist_zero_left (w : ℂ) : pseudoHyperbolicDist 0 w = ‖w‖ := by
  simp [pseudoHyperbolicDist]

/-- If the denominator is nonzero, zero pseudo-hyperbolic expression characterizes equality. -/
lemma pseudoHyperbolicDist_eq_zero_iff_of_den_ne_zero {z w : ℂ}
    (hden : 1 - (starRingEnd ℂ) w * z ≠ 0) :
    pseudoHyperbolicDist z w = 0 ↔ z = w := by
  rw [pseudoHyperbolicDist, norm_eq_zero, div_eq_zero_iff]
  simp only [hden, or_false]
  exact sub_eq_zero

/-- On the open unit disc, zero pseudo-hyperbolic expression characterizes equality. -/
lemma pseudoHyperbolicDist_eq_zero_iff_of_norm_lt_one {z w : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    pseudoHyperbolicDist z w = 0 ↔ z = w :=
  pseudoHyperbolicDist_eq_zero_iff_of_den_ne_zero
    (one_sub_conj_mul_ne_zero_of_norm_lt_one hz hw)

/-- For points in the open unit ball, zero pseudo-hyperbolic expression characterizes equality. -/
lemma pseudoHyperbolicDist_eq_zero_iff_of_mem_ball {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    pseudoHyperbolicDist z w = 0 ↔ z = w :=
  pseudoHyperbolicDist_eq_zero_iff_of_norm_lt_one (by simpa [mem_ball_zero_iff] using hz)
    (by simpa [mem_ball_zero_iff] using hw)

/-- For bundled unit-disc points, zero pseudo-hyperbolic expression characterizes equality. -/
@[simp]
lemma pseudoHyperbolicDist_eq_zero_iff_unitDisc (z w : Complex.UnitDisc) :
    pseudoHyperbolicDist (z : ℂ) (w : ℂ) = 0 ↔ z = w := by
  rw [pseudoHyperbolicDist_eq_zero_iff_of_norm_lt_one z.norm_lt_one w.norm_lt_one]
  exact Subtype.ext_iff.symm

private lemma normSq_one_sub_conj_mul_sub_normSq_sub (z w : ℂ) :
    Complex.normSq (1 - (starRingEnd ℂ) w * z) - Complex.normSq (z - w) =
      (1 - Complex.normSq z) * (1 - Complex.normSq w) := by
  rw [Complex.normSq_sub, Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_conj,
    Complex.normSq_one]
  have hre : (1 * (starRingEnd ℂ) ((starRingEnd ℂ) w * z)).re =
      (z * (starRingEnd ℂ) w).re := by
    simp [mul_comm]
  rw [hre]
  ring_nf

/-- For two points of norm less than one, the numerator norm is smaller than the denominator
norm in the pseudo-hyperbolic expression. -/
lemma norm_sub_lt_norm_one_sub_conj_mul_of_norm_lt_one {z w : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    ‖z - w‖ < ‖1 - (starRingEnd ℂ) w * z‖ := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  have hpos : 0 < (1 - Complex.normSq z) * (1 - Complex.normSq w) := by
    have hzpos : 0 < 1 - Complex.normSq z := sub_pos.mpr <| by
      rw [Complex.normSq_eq_norm_sq]
      rw [sq_lt_one_iff_abs_lt_one, abs_norm]
      exact hz
    have hwpos : 0 < 1 - Complex.normSq w := sub_pos.mpr <| by
      rw [Complex.normSq_eq_norm_sq]
      rw [sq_lt_one_iff_abs_lt_one, abs_norm]
      exact hw
    exact mul_pos hzpos hwpos
  have hdiff := normSq_one_sub_conj_mul_sub_normSq_sub z w
  nlinarith

/-- The pseudo-hyperbolic expression of two points of norm less than one is strictly less
than one. -/
lemma pseudoHyperbolicDist_lt_one_of_norm_lt_one {z w : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    pseudoHyperbolicDist z w < 1 := by
  have hden : 0 < ‖1 - (starRingEnd ℂ) w * z‖ :=
    norm_pos_iff.mpr (one_sub_conj_mul_ne_zero_of_norm_lt_one hz hw)
  have hlt := norm_sub_lt_norm_one_sub_conj_mul_of_norm_lt_one hz hw
  rw [pseudoHyperbolicDist, norm_div]
  rwa [div_lt_one hden]

/-- The pseudo-hyperbolic expression of two points in the open unit ball is strictly less
than one. -/
lemma pseudoHyperbolicDist_lt_one_of_mem_ball {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    pseudoHyperbolicDist z w < 1 :=
  pseudoHyperbolicDist_lt_one_of_norm_lt_one (by simpa [mem_ball_zero_iff] using hz)
    (by simpa [mem_ball_zero_iff] using hw)

/-- The pseudo-hyperbolic expression of two bundled unit-disc points is strictly less
than one. -/
lemma pseudoHyperbolicDist_lt_one_unitDisc (z w : Complex.UnitDisc) :
    pseudoHyperbolicDist (z : ℂ) (w : ℂ) < 1 :=
  pseudoHyperbolicDist_lt_one_of_norm_lt_one z.norm_lt_one w.norm_lt_one

end TauCeti

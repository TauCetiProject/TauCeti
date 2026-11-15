/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UnitDisc.Basic
public import TauCeti.Analysis.Complex.Basic

/-!
# The pseudo-hyperbolic expression on the unit disc

This file records the scalar pseudo-hyperbolic expression `‖(z - w) / (1 - conj w * z)‖`, on
which the Schwarz--Pick lemma and the hyperbolic distance on the disc are built.  The main API
proves that the denominator is nonzero on the open unit disc — hence of positive norm
(`TauCeti.norm_one_sub_conj_mul_pos_of_norm_le_one_of_norm_lt_one`), a positivity side condition
used when manipulating inequalities involving that denominator — that the hyperbolic defect
`1 - ‖z‖ ^ 2` is positive there (`TauCeti.one_sub_sq_norm_pos_of_norm_lt_one`), that the
expression is symmetric, that it is strictly less than one for two points of the unit disc —
hence lies in `Ioo (-1) 1`
(`TauCeti.pseudoHyperbolicExpr_mem_Ioo_of_norm_lt_one`), the interval on which `Real.artanh` is a
bijection onto `ℝ` — and that it is jointly continuous there
(`TauCeti.continuousOn_pseudoHyperbolicExpr`).
The Poincaré defect identity `TauCeti.norm_sq_one_sub_conj_mul_sub_norm_sq_sub` compares the
numerator and the denominator, and yields
`TauCeti.norm_sub_eq_of_pseudoHyperbolicExpr_eq`: between points of prescribed norms, the
pseudo-hyperbolic expression determines the Euclidean distance.

## References

* The Riemann mapping theorem development of leanprover-community/mathlib4#33505, and the parts
  of it already in Mathlib: `Mathlib/Analysis/Complex/RiemannMapping.lean` and
  `Mathlib/Analysis/Complex/BranchLogRoot.lean`.
-/

public section

namespace TauCeti

open Complex Metric Set
open scoped ComplexConjugate

/-- The pseudo-hyperbolic expression on `ℂ`, written as a total real-valued function.

On the open unit disc this is the pseudo-hyperbolic expression.  Outside the disc the same
formula is still meaningful as a total expression in Lean, with division by zero evaluating
to zero as usual. -/
noncomputable def pseudoHyperbolicExpr (z w : ℂ) : ℝ :=
  ‖(z - w) / (1 - (starRingEnd ℂ) w * z)‖

/-- The defining formula for the pseudo-hyperbolic expression. -/
-- `by rfl`, not a term-mode `rfl`: this theorem is exported, so a term proof would require
-- `pseudoHyperbolicExpr` to be `@[expose]`d for importing modules to unfold it.
lemma pseudoHyperbolicExpr_def (z w : ℂ) :
    pseudoHyperbolicExpr z w = ‖(z - w) / (1 - (starRingEnd ℂ) w * z)‖ :=
  by rfl

/-- The pseudo-hyperbolic expression as a quotient of two real norms, the form in which it is
compared with the Euclidean distance `‖z - w‖`. -/
lemma pseudoHyperbolicExpr_eq_norm_div_norm (z w : ℂ) :
    pseudoHyperbolicExpr z w = ‖z - w‖ / ‖1 - (starRingEnd ℂ) w * z‖ := by
  rw [pseudoHyperbolicExpr_def, norm_div]

/-- The pseudo-hyperbolic expression is nonnegative. -/
@[simp]
lemma pseudoHyperbolicExpr_nonneg (z w : ℂ) : 0 ≤ pseudoHyperbolicExpr z w :=
  norm_nonneg _

/-- The pseudo-hyperbolic expression from a point to itself is zero. -/
@[simp]
lemma pseudoHyperbolicExpr_self (z : ℂ) : pseudoHyperbolicExpr z z = 0 := by
  simp [pseudoHyperbolicExpr]

/-- The pseudo-hyperbolic expression is symmetric in its two arguments. -/
lemma pseudoHyperbolicExpr_comm (z w : ℂ) :
    pseudoHyperbolicExpr z w = pseudoHyperbolicExpr w z := by
  rw [pseudoHyperbolicExpr_eq_norm_div_norm, pseudoHyperbolicExpr_eq_norm_div_norm, norm_sub_rev,
    norm_one_sub_conj_mul_comm]

/-- **Conjugation invariance.** Conjugating both arguments leaves the pseudo-hyperbolic
expression unchanged: conjugation is the orientation-reversing symmetry of the disc. -/
@[simp]
lemma pseudoHyperbolicExpr_conj (z w : ℂ) :
    pseudoHyperbolicExpr ((starRingEnd ℂ) z) ((starRingEnd ℂ) w) = pseudoHyperbolicExpr z w := by
  rw [pseudoHyperbolicExpr_def, pseudoHyperbolicExpr_def,
    ← norm_conj ((z - w) / (1 - (starRingEnd ℂ) w * z)), map_div₀]
  simp

/-- The pseudo-hyperbolic expression with right endpoint zero is the norm. -/
@[simp]
lemma pseudoHyperbolicExpr_zero_right (z : ℂ) : pseudoHyperbolicExpr z 0 = ‖z‖ := by
  simp [pseudoHyperbolicExpr]

/-- The pseudo-hyperbolic expression with left endpoint zero is the norm. -/
@[simp]
lemma pseudoHyperbolicExpr_zero_left (w : ℂ) : pseudoHyperbolicExpr 0 w = ‖w‖ := by
  simp [pseudoHyperbolicExpr]

/-- **Rotation invariance.** Multiplying both arguments by a unit-modulus constant leaves the
pseudo-hyperbolic expression unchanged.  This is a purely algebraic identity valid for all
`z`, `w`; it is the rotation half of the disc-automorphism group. -/
@[simp]
lemma pseudoHyperbolicExpr_const_mul {c : ℂ} (hc : ‖c‖ = 1) (z w : ℂ) :
    pseudoHyperbolicExpr (c * z) (c * w) = pseudoHyperbolicExpr z w := by
  have hcc : (starRingEnd ℂ) c * c = 1 := by simp [Complex.conj_mul', hc]
  have hden : (starRingEnd ℂ) (c * w) * (c * z) = (starRingEnd ℂ) w * z := by
    rw [map_mul]
    linear_combination (starRingEnd ℂ) w * z * hcc
  rw [pseudoHyperbolicExpr_def, pseudoHyperbolicExpr_def, hden, ← mul_sub, mul_div_assoc, norm_mul,
    hc, one_mul]

/-- If the denominator is nonzero, zero pseudo-hyperbolic expression characterizes equality. -/
lemma pseudoHyperbolicExpr_eq_zero_iff_of_den_ne_zero {z w : ℂ}
    (hden : 1 - (starRingEnd ℂ) w * z ≠ 0) :
    pseudoHyperbolicExpr z w = 0 ↔ z = w := by
  rw [pseudoHyperbolicExpr_def, norm_eq_zero, div_eq_zero_iff, or_iff_left hden, sub_eq_zero]

/-- The denominator in the pseudo-hyperbolic expression is nonzero when `z` lies in the closed
unit disc and `w` in the open unit disc. -/
lemma one_sub_conj_mul_ne_zero_of_norm_le_one_of_norm_lt_one {z w : ℂ}
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ < 1) :
    1 - (starRingEnd ℂ) w * z ≠ 0 :=
  (isUnit_one_sub_of_norm_lt_one (x := (starRingEnd ℂ) w * z)
    (by
      rw [norm_mul, norm_conj]
      exact (mul_le_of_le_one_right (norm_nonneg _) hz).trans_lt hw)).ne_zero

/-- If one point is inside the unit disc and the other is on its boundary, both the
pseudo-hyperbolic numerator and denominator are nonzero. -/
lemma sub_ne_zero_and_one_sub_conj_mul_ne_zero_of_norm_lt_one_of_norm_eq_one {w z : ℂ}
    (hw : ‖w‖ < 1) (hz : ‖z‖ = 1) :
    z - w ≠ 0 ∧ 1 - (starRingEnd ℂ) w * z ≠ 0 :=
  ⟨sub_ne_zero.2 (by rintro rfl; linarith),
    one_sub_conj_mul_ne_zero_of_norm_le_one_of_norm_lt_one hz.le hw⟩

/-- For points in the open unit ball, the denominator in the pseudo-hyperbolic expression is
nonzero. -/
lemma one_sub_conj_mul_ne_zero_of_mem_ball {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    1 - (starRingEnd ℂ) w * z ≠ 0 :=
  one_sub_conj_mul_ne_zero_of_norm_le_one_of_norm_lt_one (mem_ball_zero_iff.mp hz).le
    (mem_ball_zero_iff.mp hw)

/-- For bundled unit-disc points, the denominator in the pseudo-hyperbolic expression is
nonzero. -/
lemma one_sub_conj_mul_ne_zero_unitDisc (z w : Complex.UnitDisc) :
    1 - (starRingEnd ℂ) (w : ℂ) * (z : ℂ) ≠ 0 :=
  one_sub_conj_mul_ne_zero_of_norm_le_one_of_norm_lt_one z.norm_lt_one.le w.norm_lt_one

/-- On the open unit disc, the hyperbolic defect `1 - ‖z‖ ^ 2` is positive. -/
lemma one_sub_sq_norm_pos_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : 0 < 1 - ‖z‖ ^ 2 :=
  sub_pos.2 (pow_lt_one₀ (norm_nonneg z) hz two_ne_zero)

/-- When `z` lies in the closed unit disc and `w` in the open unit disc, the denominator in the
pseudo-hyperbolic expression has positive norm. This is a positivity side condition used when
manipulating inequalities involving this denominator. -/
lemma norm_one_sub_conj_mul_pos_of_norm_le_one_of_norm_lt_one {z w : ℂ}
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ < 1) :
    0 < ‖1 - (starRingEnd ℂ) w * z‖ :=
  norm_pos_iff.mpr (one_sub_conj_mul_ne_zero_of_norm_le_one_of_norm_lt_one hz hw)

/-- For a point of norm at most one, the denominator of the Moebius factor evaluated at the
factor's own center has norm `1 - ‖w‖ ^ 2`. -/
lemma norm_one_sub_conj_mul_self_of_norm_le_one {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖(1 : ℂ) - (starRingEnd ℂ) w * w‖ = 1 - ‖w‖ ^ 2 := by
  rw [Complex.conj_mul']
  exact_mod_cast Complex.norm_of_nonneg (sub_nonneg.2 (pow_le_one₀ (norm_nonneg w) hw))

/-- For `z` in the closed unit disc and `w` in the open unit disc, zero pseudo-hyperbolic
expression characterizes equality. -/
lemma pseudoHyperbolicExpr_eq_zero_iff_of_norm_le_one_of_norm_lt_one {z w : ℂ}
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ < 1) :
    pseudoHyperbolicExpr z w = 0 ↔ z = w :=
  pseudoHyperbolicExpr_eq_zero_iff_of_den_ne_zero
    (one_sub_conj_mul_ne_zero_of_norm_le_one_of_norm_lt_one hz hw)

/-- For points in the open unit ball, zero pseudo-hyperbolic expression characterizes equality. -/
lemma pseudoHyperbolicExpr_eq_zero_iff_of_mem_ball {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    pseudoHyperbolicExpr z w = 0 ↔ z = w :=
  pseudoHyperbolicExpr_eq_zero_iff_of_norm_le_one_of_norm_lt_one (mem_ball_zero_iff.mp hz).le
    (mem_ball_zero_iff.mp hw)

/-- For bundled unit-disc points, zero pseudo-hyperbolic expression characterizes equality. -/
@[simp]
lemma pseudoHyperbolicExpr_eq_zero_iff_unitDisc (z w : Complex.UnitDisc) :
    pseudoHyperbolicExpr (z : ℂ) (w : ℂ) = 0 ↔ z = w := by
  rw [pseudoHyperbolicExpr_eq_zero_iff_of_norm_le_one_of_norm_lt_one z.norm_lt_one.le
    w.norm_lt_one, Complex.UnitDisc.coe_inj]

/-- **Poincaré defect identity (norm form).** The difference of the squared norms of the Moebius
denominator and numerator factors is the product of the two hyperbolic defects:
`‖1 - conj w * z‖ ^ 2 - ‖z - w‖ ^ 2 = (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)`. -/
lemma norm_sq_one_sub_conj_mul_sub_norm_sq_sub (z w : ℂ) :
    ‖(1 : ℂ) - (starRingEnd ℂ) w * z‖ ^ 2 - ‖z - w‖ ^ 2 = (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re,
    Complex.one_im]
  ring

/-- **Equal norms plus equal pseudo-hyperbolic expression force equal distance.** For four points
of the open unit disc with `‖z'‖ = ‖z‖` and `‖w'‖ = ‖w‖`, the pseudo-hyperbolic expression
determines the Euclidean distance. -/
lemma norm_sub_eq_of_pseudoHyperbolicExpr_eq {z w z' w' : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) (hnz : ‖z'‖ = ‖z‖) (hnw : ‖w'‖ = ‖w‖)
    (h : pseudoHyperbolicExpr z' w' = pseudoHyperbolicExpr z w) :
    ‖z' - w'‖ = ‖z - w‖ := by
  have hD : 0 < (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) :=
    mul_pos (one_sub_sq_norm_pos_of_norm_lt_one hz) (one_sub_sq_norm_pos_of_norm_lt_one hw)
  have hB := norm_sq_one_sub_conj_mul_sub_norm_sq_sub z w
  have hB' := norm_sq_one_sub_conj_mul_sub_norm_sq_sub z' w'
  rw [hnz, hnw] at hB'
  rw [pseudoHyperbolicExpr_eq_norm_div_norm, pseudoHyperbolicExpr_eq_norm_div_norm,
    div_eq_div_iff
      (norm_one_sub_conj_mul_pos_of_norm_le_one_of_norm_lt_one (hnz.trans_lt hz).le
        (hnw.trans_lt hw)).ne'
      (norm_one_sub_conj_mul_pos_of_norm_le_one_of_norm_lt_one hz.le hw).ne'] at h
  -- Squaring `h` and substituting the Poincaré defect identity for both pairs, which share the
  -- same defect product, leaves the difference of the squared numerators times that product.
  have key : (‖z' - w'‖ ^ 2 - ‖z - w‖ ^ 2) * ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) = 0 := by
    linear_combination (‖z' - w'‖ * ‖1 - (starRingEnd ℂ) w * z‖ +
      ‖z - w‖ * ‖1 - (starRingEnd ℂ) w' * z'‖) * h - ‖z' - w'‖ ^ 2 * hB + ‖z - w‖ ^ 2 * hB'
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    (sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_right hD.ne'))

/-- For two points of norm less than one, the numerator norm is smaller than the denominator
norm in the pseudo-hyperbolic expression. -/
lemma norm_sub_lt_norm_one_sub_conj_mul_of_norm_lt_one {z w : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    ‖z - w‖ < ‖1 - (starRingEnd ℂ) w * z‖ := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)]
  have := norm_sq_one_sub_conj_mul_sub_norm_sq_sub z w
  have := mul_pos (one_sub_sq_norm_pos_of_norm_lt_one hz) (one_sub_sq_norm_pos_of_norm_lt_one hw)
  linarith

/-- The pseudo-hyperbolic expression of two points of norm less than one is strictly less
than one. -/
lemma pseudoHyperbolicExpr_lt_one_of_norm_lt_one {z w : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    pseudoHyperbolicExpr z w < 1 := by
  rw [pseudoHyperbolicExpr_eq_norm_div_norm,
    div_lt_one (norm_one_sub_conj_mul_pos_of_norm_le_one_of_norm_lt_one hz.le hw)]
  exact norm_sub_lt_norm_one_sub_conj_mul_of_norm_lt_one hz hw

/-- The pseudo-hyperbolic expression of two points in the open unit ball is strictly less
than one. -/
lemma pseudoHyperbolicExpr_lt_one_of_mem_ball {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    pseudoHyperbolicExpr z w < 1 :=
  pseudoHyperbolicExpr_lt_one_of_norm_lt_one (mem_ball_zero_iff.mp hz) (mem_ball_zero_iff.mp hw)

/-- The pseudo-hyperbolic expression of two bundled unit-disc points is strictly less
than one. -/
lemma pseudoHyperbolicExpr_lt_one_unitDisc (z w : Complex.UnitDisc) :
    pseudoHyperbolicExpr (z : ℂ) (w : ℂ) < 1 :=
  pseudoHyperbolicExpr_lt_one_of_norm_lt_one z.norm_lt_one w.norm_lt_one

/-- The pseudo-hyperbolic expression of two points of norm less than one lies in the interval
`Ioo (-1) 1` on which `Real.artanh` is a strictly monotone bijection onto `ℝ`. This is the side
condition of the `Real.artanh` lemmas applied to it to define the hyperbolic distance. -/
lemma pseudoHyperbolicExpr_mem_Ioo_of_norm_lt_one {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    pseudoHyperbolicExpr z w ∈ Ioo (-1 : ℝ) 1 :=
  ⟨neg_one_lt_zero.trans_le (pseudoHyperbolicExpr_nonneg z w),
    pseudoHyperbolicExpr_lt_one_of_norm_lt_one hz hw⟩

/-- The pseudo-hyperbolic expression is continuous on the product of two copies of the open
unit disc, where its Moebius denominator does not vanish. -/
lemma continuousOn_pseudoHyperbolicExpr :
    ContinuousOn (fun p : ℂ × ℂ ↦ pseudoHyperbolicExpr p.1 p.2)
      (ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) := by
  refine ContinuousOn.congr ?_ fun p _ ↦ pseudoHyperbolicExpr_def p.1 p.2
  refine (ContinuousOn.div (by fun_prop) (by fun_prop) ?_).norm
  exact fun p hp ↦ one_sub_conj_mul_ne_zero_of_mem_ball hp.1 hp.2

end TauCeti

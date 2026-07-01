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

@[simp]
lemma pseudoHyperbolicDist_nonneg (z w : ℂ) : 0 ≤ pseudoHyperbolicDist z w :=
  norm_nonneg _

@[simp]
lemma pseudoHyperbolicDist_self (z : ℂ) : pseudoHyperbolicDist z z = 0 := by
  simp [pseudoHyperbolicDist]

lemma one_sub_conj_mul_ne_zero_of_norm_lt_one {z w : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    1 - (starRingEnd ℂ) w * z ≠ 0 := by
  intro h
  have hmul : (starRingEnd ℂ) w * z = 1 := by
    simpa using (sub_eq_zero.mp h).symm
  have hnorm : ‖w‖ * ‖z‖ = 1 := by
    calc
      ‖w‖ * ‖z‖ = ‖(starRingEnd ℂ) w‖ * ‖z‖ := by rw [norm_conj]
      _ = ‖(starRingEnd ℂ) w * z‖ := by rw [norm_mul]
      _ = 1 := by rw [hmul, norm_one]
  have hlt : ‖w‖ * ‖z‖ < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_right hw.le (norm_nonneg _) hz
  linarith

lemma one_sub_conj_mul_ne_zero_of_mem_ball {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    1 - (starRingEnd ℂ) w * z ≠ 0 :=
  one_sub_conj_mul_ne_zero_of_norm_lt_one (by simpa [mem_ball_zero_iff] using hz)
    (by simpa [mem_ball_zero_iff] using hw)

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

lemma pseudoHyperbolicDist_comm (z w : ℂ) :
    pseudoHyperbolicDist z w = pseudoHyperbolicDist w z := by
  unfold pseudoHyperbolicDist
  rw [norm_div, norm_div, norm_sub_rev, norm_one_sub_conj_mul_comm]

lemma pseudoHyperbolicDist_eq_zero_of_eq {z w : ℂ} (h : z = w) :
    pseudoHyperbolicDist z w = 0 := by
  subst h
  simp

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

lemma pseudoHyperbolicDist_lt_one_of_norm_lt_one {z w : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    pseudoHyperbolicDist z w < 1 := by
  have hden : 0 < ‖1 - (starRingEnd ℂ) w * z‖ :=
    norm_pos_iff.mpr (one_sub_conj_mul_ne_zero_of_norm_lt_one hz hw)
  have hlt := norm_sub_lt_norm_one_sub_conj_mul_of_norm_lt_one hz hw
  rw [pseudoHyperbolicDist, norm_div]
  rwa [div_lt_one hden]

lemma pseudoHyperbolicDist_lt_one_of_mem_ball {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    pseudoHyperbolicDist z w < 1 :=
  pseudoHyperbolicDist_lt_one_of_norm_lt_one (by simpa [mem_ball_zero_iff] using hz)
    (by simpa [mem_ball_zero_iff] using hw)

lemma pseudoHyperbolicDist_lt_one_unitDisc (z w : Complex.UnitDisc) :
    pseudoHyperbolicDist (z : ℂ) (w : ℂ) < 1 :=
  pseudoHyperbolicDist_lt_one_of_norm_lt_one z.norm_lt_one w.norm_lt_one

end TauCeti

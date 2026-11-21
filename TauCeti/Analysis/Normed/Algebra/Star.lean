/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Star.Module
public import Mathlib.Analysis.CStarAlgebra.Basic
public import TauCeti.Analysis.Normed.Ring.Basic

/-!
# Normed star algebra perturbation and symmetrization bounds

Elementary norm estimates for self-adjoint symmetrization (`selfAdjointPart`), skew-adjointness
defects under perturbation, and star-product defects in seminormed star rings and star modules.

## Main results

* `TauCeti.norm_selfAdjointPart_sub`, `TauCeti.norm_selfAdjointPart_mul_self_sub_le`:
  distance and idempotency-defect bounds for `selfAdjointPart ℝ e`.
* `TauCeti.norm_sub_star_le_of_norm_sub`: skew-adjointness defect under perturbation.
* `TauCeti.norm_star_mul_self_sub_le`, `TauCeti.norm_star_mul_self_sub_lt_of_norm_le`:
  star-product perturbation bounds separating approximation and defect terms.
-/

public section

namespace TauCeti

/-- The self-adjoint part `selfAdjointPart ℝ e` lies at distance `(1 / 2) * ‖e - star e‖`
from `e`. -/
theorem norm_selfAdjointPart_sub {A : Type*} [SeminormedAddCommGroup A] [StarAddMonoid A]
    [NormedSpace ℝ A] [StarModule ℝ A] (e : A) :
    ‖(selfAdjointPart ℝ e : A) - e‖ = (1 / 2) * ‖e - star e‖ := by
  have hsub : (selfAdjointPart ℝ e : A) - e = (2 : ℝ)⁻¹ • (star e - e) :=
    smul_right_injective A (by norm_num : (2 : ℝ) ≠ 0) <| by
      simp only [selfAdjointPart_apply_coe, invOf_eq_inv, smul_sub, smul_smul]; norm_num
      simp only [one_smul, ← one_add_one_eq_two, add_smul]; abel
  rw [hsub, norm_smul, Real.norm_of_nonneg (by positivity), norm_sub_rev, one_div]

/-- The idempotency defect of `selfAdjointPart ℝ e` satisfies
`‖a * a - a‖ ≤ ‖e * e - e‖ + (1 / 4) * ‖e - star e‖ ^ 2`. -/
theorem norm_selfAdjointPart_mul_self_sub_le {A : Type*} [NonUnitalSeminormedRing A] [StarRing A]
    [NormedStarGroup A] [NormedSpace ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    [StarModule ℝ A] (e : A) :
    ‖(selfAdjointPart ℝ e : A) * (selfAdjointPart ℝ e : A) - (selfAdjointPart ℝ e : A)‖ ≤
      ‖e * e - e‖ + (1 / 4) * ‖e - star e‖ ^ 2 := by
  set a : A := (selfAdjointPart ℝ e : A)
  have hid : a * a - a = (2 : ℝ)⁻¹ • ((e * e - e) + star (e * e - e)) -
      (4 : ℝ)⁻¹ • ((e - star e) * (e - star e)) :=
    smul_right_injective A (by norm_num : (4 : ℝ) ≠ 0) <| by
      simp only [a, selfAdjointPart_apply_coe, invOf_eq_inv, smul_mul_smul_comm, smul_sub,
        smul_smul]; norm_num
      simp only [one_smul, ← one_add_one_eq_two, add_smul, mul_add, add_mul, sub_mul, mul_sub]; abel
  rw [hid]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    linarith [norm_add_le (e * e - e) (star (e * e - e)), norm_star (e * e - e)]
  · rw [norm_smul, Real.norm_of_nonneg (by positivity), one_div, sq]; gcongr; exact norm_mul_le _ _

/-- Skew-adjointness defect under perturbation:
`‖y - star y‖ ≤ ‖x - star x‖ + 2 * ‖y - x‖`. -/
theorem norm_sub_star_le_of_norm_sub {A : Type*} [SeminormedAddCommGroup A] [StarAddMonoid A]
    [NormedStarGroup A] (x y : A) :
    ‖y - star y‖ ≤ ‖x - star x‖ + 2 * ‖y - x‖ := by
  have hdecomp : y - star y = (y - x) + ((x - star x) - star (y - x)) := by
    rw [star_sub]; abel
  rw [hdecomp]
  linarith [norm_add_le (y - x) ((x - star x) - star (y - x)),
    norm_sub_le (x - star x) (star (y - x)), norm_star (y - x)]

/-- Star-product defect bound for `star z * z - p` via an approximation `y` of `z`, an
approximation `y'` of `star y`, and a target `d` near `y' * y`:
`‖star z * z - p‖ ≤ (‖z‖ + ‖y‖) * ‖z - y‖ + ‖star y - y'‖ * ‖y‖ + ‖y' * y - d‖ + ‖p - d‖`. -/
theorem norm_star_mul_self_sub_le {A : Type*} [NonUnitalSeminormedRing A] [StarRing A]
    [NormedStarGroup A] (z y y' d p : A) :
    ‖star z * z - p‖ ≤
      (‖z‖ + ‖y‖) * ‖z - y‖ + ‖star y - y'‖ * ‖y‖ + ‖y' * y - d‖ + ‖p - d‖ := by
  have h1 : ‖star z * z - star y * y‖ ≤ (‖z‖ + ‖y‖) * ‖z - y‖ := by
    refine (norm_mul_sub_mul_le (star z) z (star y) y).trans_eq ?_
    rw [← star_sub, norm_star, norm_star, mul_comm ‖z - y‖ ‖z‖, add_mul]
  have h2 : ‖star y * y - d‖ ≤ ‖star y - y'‖ * ‖y‖ + ‖y' * y - d‖ :=
    norm_mul_sub_le_right y (star y) y' d
  have h3 : ‖star z * z - p‖ ≤ ‖star z * z - star y * y‖ + (‖star y * y - d‖ + ‖d - p‖) :=
    (norm_sub_le_norm_sub_add_norm_sub (star z * z) (star y * y) p).trans
      (add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub (star y * y) d p))
  rw [norm_sub_rev d p] at h3
  linarith

/-- Strict star-product defect bound with variable norm bounds `‖z‖ ≤ M₁` and `‖y‖ ≤ M₂`:
`‖star z * z - p‖ < (M₁ + M₂) * α + (M₂ + 1) * δ + β`. -/
theorem norm_star_mul_self_sub_lt_of_norm_le {A : Type*} [NonUnitalSeminormedRing A] [StarRing A]
    [NormedStarGroup A] {z y y' d p : A} {M₁ M₂ α δ β : ℝ} (hz : ‖z‖ ≤ M₁) (hy : ‖y‖ ≤ M₂)
    (hzy : ‖z - y‖ ≤ α) (hstar : ‖star y - y'‖ < δ) (hmul : ‖y' * y - d‖ < δ)
    (hpd : ‖p - d‖ < β) :
    ‖star z * z - p‖ < (M₁ + M₂) * α + (M₂ + 1) * δ + β := by
  have hδ : 0 < δ := (norm_nonneg _).trans_lt hmul
  have h1 : (‖z‖ + ‖y‖) * ‖z - y‖ ≤ (M₁ + M₂) * α :=
    mul_le_mul (add_le_add hz hy) hzy (norm_nonneg _) (by linarith [norm_nonneg z, norm_nonneg y])
  have h2 : ‖star y - y'‖ * ‖y‖ ≤ δ * M₂ :=
    mul_le_mul hstar.le hy (norm_nonneg _) hδ.le
  linarith [norm_star_mul_self_sub_le z y y' d p]

end TauCeti

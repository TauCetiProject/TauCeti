/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.ODE.Gronwall.TwoSided
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Quantitative bounds for second-order trajectories

For `y' = v` and `‖v'‖ ≤ C * ‖y‖` on a closed real interval, Grönwall's inequality
bounds the pair in the maximum norm. If the initial position is zero, successive
polynomial majorants give linear position growth, a quadratic velocity remainder and a
cubic position remainder with coefficient `1 / 6`. Only derivatives within the interval
are used; no completeness or continuity of the acceleration is required.

These estimates apply to ordinary Jacobi equations `v' = -R y` with bounded operator
coefficient. The half-norm bound supplies the quantitative nonvanishing input for
small-radius exponential-map comparison. Identifying an intrinsic Jacobi field with
such a trajectory requires a parallel trivialization and is a separate geometric step.

## References

* Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Theorem 5.6 and Lemma 5.7,
  for the geometric compactness application.
* [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions).
* [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a b C : ℝ} {y v v' : ℝ → E}

/-- The maximum norm of a second-order trajectory has an exponential bound from its initial
state. The acceleration bound is pointwise and may have any real coefficient. -/
theorem max_norm_le_exp_of_second_order
    (hy : ∀ s ∈ Icc a b, HasDerivWithinAt y (v s) (Icc a b) s)
    (hv : ∀ s ∈ Icc a b, HasDerivWithinAt v (v' s) (Icc a b) s)
    (hbound : ∀ s ∈ Icc a b, ‖v' s‖ ≤ C * ‖y s‖)
    {t : ℝ} (ht : t ∈ Icc a b) :
    max ‖y t‖ ‖v t‖ ≤ max ‖y a‖ ‖v a‖ * Real.exp (max 1 C * (t - a)) := by
  have h := norm_le_gronwallBound_of_norm_derivWithin_le
    (f := fun s ↦ (y s, v s)) (f' := fun s ↦ (v s, v' s))
    (K := max 1 C) (ε := 0) ⟨le_rfl, ht.1.trans ht.2⟩
    (fun s hs ↦ (hy s hs).prodMk (hv s hs)) le_rfl
    (fun s hs ↦ by
      simp only [Prod.norm_def, add_zero]
      apply max_le
      · exact (le_max_right _ _).trans
          (le_mul_of_one_le_left (le_max_of_le_left (norm_nonneg _)) (le_max_left _ _))
      · exact (hbound s hs).trans
          ((mul_le_mul_of_nonneg_right (le_max_right 1 C) (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left (le_max_left _ _)
              (zero_le_one.trans (le_max_left 1 C))))) t ht
  simpa only [Prod.norm_def, gronwallBound_ε0, abs_of_nonneg (sub_nonneg.mpr ht.1)] using h

/-- Zero initial position bounds velocity uniformly by the initial exponential scale. -/
theorem norm_velocity_le_exp_of_second_order
    (hy : ∀ s ∈ Icc a b, HasDerivWithinAt y (v s) (Icc a b) s)
    (hv : ∀ s ∈ Icc a b, HasDerivWithinAt v (v' s) (Icc a b) s)
    (hbound : ∀ s ∈ Icc a b, ‖v' s‖ ≤ C * ‖y s‖) (hy0 : y a = 0)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖v t‖ ≤ ‖v a‖ * Real.exp (max 1 C * (b - a)) := by
  have h := max_norm_le_exp_of_second_order hy hv hbound ht
  rw [hy0, norm_zero, max_eq_right (norm_nonneg _)] at h
  exact ((le_max_right _ _).trans h).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a)
        (zero_le_one.trans (le_max_left 1 C)))) (norm_nonneg _))

/-- A zero initial position grows at most linearly with the uniform velocity scale. -/
theorem norm_position_le_mul_exp_of_second_order
    (hy : ∀ s ∈ Icc a b, HasDerivWithinAt y (v s) (Icc a b) s)
    (hv : ∀ s ∈ Icc a b, HasDerivWithinAt v (v' s) (Icc a b) s)
    (hbound : ∀ s ∈ Icc a b, ‖v' s‖ ≤ C * ‖y s‖) (hy0 : y a = 0)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖y t‖ ≤ (‖v a‖ * Real.exp (max 1 C * (b - a))) * (t - a) := by
  simpa only [hy0, sub_zero] using
    norm_image_sub_le_of_norm_deriv_le_segment' hy
      (fun s hs ↦ norm_velocity_le_exp_of_second_order hy hv hbound hy0
        (Ico_subset_Icc_self hs)) t ht

/-- The velocity remainder is quadratic in elapsed time when the initial position is zero. -/
theorem norm_velocity_sub_le_sq_of_second_order
    (hy : ∀ s ∈ Icc a b, HasDerivWithinAt y (v s) (Icc a b) s)
    (hv : ∀ s ∈ Icc a b, HasDerivWithinAt v (v' s) (Icc a b) s)
    (hbound : ∀ s ∈ Icc a b, ‖v' s‖ ≤ C * ‖y s‖) (hy0 : y a = 0) (hC : 0 ≤ C)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖v t - v a‖ ≤ C * (‖v a‖ * Real.exp (max 1 C * (b - a))) * (t - a) ^ 2 / 2 := by
  let M := ‖v a‖ * Real.exp (max 1 C * (b - a))
  apply image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun s hs ↦ ((hv s hs).sub_const (v a)).continuousWithinAt)
    (fun s hs ↦ ((hv s (Ico_subset_Icc_self hs)).sub_const (v a)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)) (by simp)
    (B := fun s ↦ C * M * (s - a) ^ 2 / 2)
    (B' := fun s ↦ C * M * (s - a)) ?_ ?_ ht
  · intro s
    convert ((((hasDerivAt_id s).sub_const a).pow 2).const_mul (C * M)).div_const 2 using 1
    · rfl
    · norm_num
      ring
  · intro s hs
    exact (hbound s (Ico_subset_Icc_self hs)).trans
      (by simpa only [M, mul_assoc] using (mul_le_mul_of_nonneg_left
        (norm_position_le_mul_exp_of_second_order hy hv hbound hy0
          (Ico_subset_Icc_self hs)) hC))

/-- The position differs from its initial affine trajectory by a cubic remainder with exact
coefficient `1 / 6`, without completeness or continuity of the acceleration. -/
theorem norm_position_sub_le_cube_of_second_order
    (hy : ∀ s ∈ Icc a b, HasDerivWithinAt y (v s) (Icc a b) s)
    (hv : ∀ s ∈ Icc a b, HasDerivWithinAt v (v' s) (Icc a b) s)
    (hbound : ∀ s ∈ Icc a b, ‖v' s‖ ≤ C * ‖y s‖) (hy0 : y a = 0) (hC : 0 ≤ C)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖y t - (t - a) • v a‖ ≤
      C * (‖v a‖ * Real.exp (max 1 C * (b - a))) * (t - a) ^ 3 / 6 := by
  let M := ‖v a‖ * Real.exp (max 1 C * (b - a))
  have hd (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivWithinAt (fun r ↦ y r - (r - a) • v a) (v s - v a) (Icc a b) s := by
    exact (hy s hs).sub (by simpa using
      (((hasDerivAt_id s).sub_const a).smul_const (v a)).hasDerivWithinAt)
  apply image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun s hs ↦ (hd s hs).continuousWithinAt)
    (fun s hs ↦ (hd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)) (by simp [hy0])
    (B := fun s ↦ C * M * (s - a) ^ 3 / 6)
    (B' := fun s ↦ C * M * (s - a) ^ 2 / 2) ?_ ?_ ht
  · intro s
    convert ((((hasDerivAt_id s).sub_const a).pow 3).const_mul (C * M)).div_const 6 using 1
    · rfl
    · norm_num
      ring
  · intro s hs
    exact norm_velocity_sub_le_sq_of_second_order hy hv hbound hy0 hC
      (Ico_subset_Icc_self hs)

/-- A small second-order coefficient preserves half of the initial linear norm. -/
theorem half_mul_norm_velocity_le_norm_position_of_second_order
    (hy : ∀ s ∈ Icc a b, HasDerivWithinAt y (v s) (Icc a b) s)
    (hv : ∀ s ∈ Icc a b, HasDerivWithinAt v (v' s) (Icc a b) s)
    (hbound : ∀ s ∈ Icc a b, ‖v' s‖ ≤ C * ‖y s‖) (hy0 : y a = 0) (hC : 0 ≤ C)
    {t : ℝ} (ht : t ∈ Icc a b)
    (hsmall : C * Real.exp (max 1 C * (b - a)) * (t - a) ^ 2 ≤ 3) :
    (t - a) * ‖v a‖ / 2 ≤ ‖y t‖ := by
  have hrem := norm_position_sub_le_cube_of_second_order hy hv hbound hy0 hC ht
  have htri := norm_sub_norm_le ((t - a) • v a) (y t)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.1), norm_sub_rev] at htri
  have h := mul_le_mul_of_nonneg_right hsmall
    (mul_nonneg (sub_nonneg.mpr ht.1) (norm_nonneg (v a)))
  nlinarith only [hrem, htri, h]

end TauCeti

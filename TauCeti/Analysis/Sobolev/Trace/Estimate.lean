/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The one-dimensional energy estimate for traces

A `C¹` function with values in a real inner product space has both endpoint norms controlled
by its value and derivative energies on a finite interval, with an explicit width-dependent
constant. No compact support is needed for this finite-interval estimate.

A compactly supported `C¹` real function has its squared value at the endpoint of a half-line
bounded by the integral of its value and derivative squared on that half-line. Integrating this
estimate over the transverse variables supplies the flat-boundary `H¹` trace inequality.

The estimate follows the fundamental-theorem-of-calculus proof of the trace theorem in
L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.5.
-/

public section

namespace TauCeti

open MeasureTheory Set

/-- Both endpoint norms of a curve that is `C¹` near a closed interval are controlled by
its energy on that interval.
The coefficient of the value energy depends on the interval width; no compact support or
integrability outside the interval is required. -/
theorem norm_sq_add_norm_sq_le_integral_norm_sq_add_norm_deriv_sq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {g : ℝ → F} {a b : ℝ} (hg : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 g t)
    (hab : a < b) :
    ‖g a‖ ^ 2 + ‖g b‖ ^ 2 ≤
      ∫ t in a..b, (2 / (b - a) + 1) * ‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2 := by
  -- A signed affine weight gives the sum of both endpoint energies in one FTC identity.
  let q : ℝ → ℝ := fun t ↦ (2 * t - a - b) / (b - a)
  have hgc : ContinuousOn g (Icc a b) :=
    fun t ht ↦ (hg t ht).continuousAt.continuousWithinAt
  have hdc : ContinuousOn (deriv g) (Icc a b) :=
    fun t ht ↦ ((hg t ht).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hd (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt (fun t ↦ q t * ‖g t‖ ^ 2)
      (2 / (b - a) * ‖g t‖ ^ 2 + q t * (2 * inner ℝ (g t) (deriv g t))) t := by
    simpa only [q, mul_one, id_eq] using!
      ((((hasDerivAt_id t).const_mul 2).sub_const a |>.sub_const b).div_const
        (b - a)).mul ((hg t ht).differentiableAt one_ne_zero).hasDerivAt.norm_sq
  have hcq : Continuous q := by fun_prop
  have hleft := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hd t ((uIcc_of_le hab.le) ▸ ht))
    (ContinuousOn.intervalIntegrable_of_Icc hab.le
      ((continuousOn_const.mul (hgc.norm.pow 2)).add
        (hcq.continuousOn.mul (continuousOn_const.mul (hgc.inner hdc)))))
  have hqa : q a = -1 := by dsimp [q]; field_simp [sub_ne_zero.mpr hab.ne']; ring
  have hqb : q b = 1 := by dsimp [q]; field_simp [sub_ne_zero.mpr hab.ne']; ring
  rw [hqa, hqb] at hleft
  -- The weight has absolute value at most one; use Cauchy–Schwarz and Young's inequality.
  have hbound (t : ℝ) (ht : t ∈ Icc a b) :
      2 / (b - a) * ‖g t‖ ^ 2 + q t * (2 * inner ℝ (g t) (deriv g t)) ≤
        (2 / (b - a) + 1) * ‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2 := by
    have hq : |q t| ≤ 1 := by
      rw [abs_le]
      dsimp [q]
      constructor
      · rw [le_div_iff₀ (sub_pos.mpr hab)]; linarith [ht.1]
      · rw [div_le_iff₀ (sub_pos.mpr hab)]; linarith [ht.2]
    have hi := abs_real_inner_le_norm (g t) (deriv g t)
    have hmul : q t * inner ℝ (g t) (deriv g t) ≤ ‖g t‖ * ‖deriv g t‖ := by
      calc
        _ ≤ |q t * inner ℝ (g t) (deriv g t)| := le_abs_self _
        _ = |q t| * |inner ℝ (g t) (deriv g t)| := abs_mul _ _
        _ ≤ 1 * (‖g t‖ * ‖deriv g t‖) :=
          mul_le_mul hq hi (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    nlinarith [sq_nonneg (‖g t‖ - ‖deriv g t‖)]
  -- Integrate the pointwise estimate and substitute the endpoint identity.
  have hmono : (∫ t in a..b,
      2 / (b - a) * ‖g t‖ ^ 2 + q t * (2 * inner ℝ (g t) (deriv g t))) ≤
      ∫ t in a..b, (2 / (b - a) + 1) * ‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2 :=
    intervalIntegral.integral_mono_on hab.le
    (ContinuousOn.intervalIntegrable_of_Icc hab.le
      ((continuousOn_const.mul (hgc.norm.pow 2)).add
        (hcq.continuousOn.mul (continuousOn_const.mul (hgc.inner hdc)))))
    (((continuousOn_const.mul (hgc.norm.pow 2)).add
      (hdc.norm.pow 2)).intervalIntegrable_of_Icc hab.le) hbound
  rw [hleft] at hmono
  nlinarith

/-- The endpoint value is controlled by the `H¹` energy on the right half-line. -/
theorem sq_le_integral_Ioi_sq_add_deriv_sq {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hs : HasCompactSupport g) (a : ℝ) :
    g a ^ 2 ≤ ∫ t in Ioi a, g t ^ 2 + deriv g t ^ 2 := by
  have hd : ∀ t, deriv (fun s ↦ g s * g s) t = 2 * g t * deriv g t := by
    intro t
    exact ((hg.differentiable one_ne_zero t).hasDerivAt.mul
      (hg.differentiable one_ne_zero t).hasDerivAt).deriv.trans (by ring)
  have hi := (hs.mul_right (f' := g)).integral_Ioi_deriv_eq (hg.mul hg) a
  simp only [hd] at hi
  have hdc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hs2 : HasCompactSupport (fun t ↦ g t ^ 2) :=
    hs.mono (fun t ht hzero ↦ ht (by simp [hzero]))
  have hds2 : HasCompactSupport (fun t ↦ deriv g t ^ 2) :=
    hs.deriv.mono (fun t ht hzero ↦ ht (by simp [hzero]))
  have hprod : Integrable (fun t ↦ 2 * g t * deriv g t) volume :=
    ((continuous_const.mul hg.continuous).mul hdc).integrable_of_hasCompactSupport
      (hs.mono (fun t ht hzero ↦ ht (by simp [hzero])))
  have henergy : Integrable (fun t ↦ g t ^ 2 + deriv g t ^ 2) volume :=
    ((hg.continuous.pow 2).add (hdc.pow 2)).integrable_of_hasCompactSupport (hs2.add hds2)
  calc
    g a ^ 2 = ∫ t in Ioi a, -(2 * g t * deriv g t) := by
      rw [integral_neg, hi]
      ring
    _ ≤ ∫ t in Ioi a, g t ^ 2 + deriv g t ^ 2 := by
      apply integral_mono hprod.neg.integrableOn henergy.integrableOn
      intro t
      dsimp only [Pi.neg_apply]
      nlinarith [sq_nonneg (g t + deriv g t)]

/-- A point value is bounded by the whole-line `H¹` energy. -/
theorem sq_le_integral_sq_add_deriv_sq {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hs : HasCompactSupport g) (a : ℝ) :
    g a ^ 2 ≤ ∫ t, g t ^ 2 + deriv g t ^ 2 := by
  refine (sq_le_integral_Ioi_sq_add_deriv_sq hg hs a).trans ?_
  have hs2 : HasCompactSupport (fun t ↦ g t ^ 2) :=
    hs.mono (fun t ht hzero ↦ ht (by simp [hzero]))
  have hds2 : HasCompactSupport (fun t ↦ deriv g t ^ 2) :=
    hs.deriv.mono (fun t ht hzero ↦ ht (by simp [hzero]))
  have hc := (hg.continuous.pow 2).add ((hg.continuous_deriv le_rfl).pow 2)
  exact setIntegral_le_integral (hc.integrable_of_hasCompactSupport (hs2.add hds2))
    (Filter.Eventually.of_forall fun t ↦ add_nonneg (sq_nonneg _) (sq_nonneg _))

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Radial cutoffs with almost optimal Lipschitz constant

When `E` is nontrivial, a function equal to one on `closedBall x₀ r` and vanishing off
`ball x₀ R` has Lipschitz constant at least `1 / (R - r)`, and the piecewise affine radial profile
attains this bound but is not smooth. This file shows that every larger constant is attained by a
smooth cutoff (`TauCeti.exists_contDiff_cutoff_closedBall_lipschitzWith`), so for nontrivial `E`
the bound `1 / (R - r)` is the infimum of the Lipschitz constants of smooth cutoffs.

Cutoffs with a universal but non-optimal constant `c / (R - r)` suffice for iteration arguments.
Limits in which the width `R - r` of the transition shell shrinks to zero need the sharp constant
instead: there the gradient term of a Leibniz estimate converges to a derivative of the measure of
the shell only when the cutoff's slope is asymptotically `1 / (R - r)`. This is how the perimeter of
the intersection of a set with a ball is bounded.

The radial profile is a primitive of a normalized bump function on `ℝ` supported in a slightly
smaller interval than `(r, R)`. Its slope is bounded by the reciprocal of the length of the
interval on which the bump equals one (`ContDiffBump.normed_le_div_measure_closedBall_rIn`), and
that length can be taken as close to `R - r` as desired.
-/

public section

open Function Metric Set
open scoped ContDiff NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Smooth radial cutoffs with almost optimal Lipschitz constant.** For radii `0 ≤ r < R` and
every constant `K > 1 / (R - r)`, there is a smooth `ψ` with values in `[0, 1]`, equal to one on
`closedBall x₀ r`, vanishing off `ball x₀ R`, and `K`-Lipschitz. When `E` is nontrivial, the
bound `1 / (R - r)` is the optimal Lipschitz constant of such a function. -/
theorem exists_contDiff_cutoff_closedBall_lipschitzWith (x₀ : E) {r R : ℝ} (hr : 0 ≤ r)
    (hrR : r < R) {K : ℝ≥0} (hK : (R - r)⁻¹ < K) :
    ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ range ψ ⊆ Icc 0 1 ∧ EqOn ψ 1 (closedBall x₀ r) ∧
      support ψ ⊆ ball x₀ R ∧ LipschitzWith K ψ := by
  have hκ : 0 < (K : ℝ) := (inv_pos.2 (sub_pos.2 hrR)).trans hK
  have hKinv : (K : ℝ)⁻¹ < R - r := (inv_lt_comm₀ (sub_pos.2 hrR) hκ).1 hK
  -- The bump lives on `(a, R)`, where `r < a`, and equals one on an interval of length `1 / K`.
  set a := r + (R - r - (K : ℝ)⁻¹) / 2 with ha_def
  have hra : r < a := by rw [ha_def]; linarith
  have hKa : (K : ℝ)⁻¹ < R - a := by rw [ha_def]; linarith
  let f : ContDiffBump ((a + R) / 2) :=
    { rIn := (2 * K)⁻¹
      rOut := (R - a) / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by rw [mul_inv]; linarith }
  set ρ := f.normed MeasureTheory.volume with hρ_def
  have hρs : ContDiff ℝ ∞ ρ := f.contDiff_normed (n := ⊤)
  have hρc : Continuous ρ := hρs.continuous
  have hρ_supp : support ρ ⊆ Ioo a R := by
    rw [f.support_normed_eq, Real.ball_eq_Ioo]
    exact Ioo_subset_Ioo (by simp only [f]; linarith) (by simp only [f]; linarith)
  have hρ_zero {t : ℝ} (ht : t ∉ Ioo a R) : ρ t = 0 := notMem_support.1 fun h => ht (hρ_supp h)
  have hρ_le (t : ℝ) : ρ t ≤ K := by
    refine (f.normed_le_div_measure_closedBall_rIn _ t).trans_eq ?_
    rw [MeasureTheory.measureReal_def, Real.volume_closedBall,
      ENNReal.toReal_ofReal (by simp only [f]; positivity)]
    simp only [f]
    field_simp
  -- The radial profile `G`, a primitive of `ρ`, increases from `0` on `(-∞, a]` to `1` on
  -- `[R, ∞)` with slope at most `K`.
  set G : ℝ → ℝ := fun s => ∫ t in a..s, ρ t with hG_def
  have hG (s : ℝ) : HasDerivAt G (ρ s) s := (hρc.integral_hasStrictDerivAt a s).hasDerivAt
  have hGd : Differentiable ℝ G := fun s => (hG s).differentiableAt
  have hGderiv : deriv G = ρ := funext fun s => (hG s).deriv
  have hGsmooth : ContDiff ℝ ∞ G :=
    contDiff_infty_iff_deriv.2 ⟨hGd, hGderiv ▸ hρs⟩
  have hGmono : Monotone G := monotone_of_hasDerivAt_nonneg hG f.nonneg_normed
  have hG_left {s : ℝ} (hs : s ≤ a) : G s = 0 := by
    refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_).trans
      intervalIntegral.integral_zero
    rw [uIcc_of_ge hs] at ht
    exact hρ_zero fun h => (h.1.trans_le ht.2).false
  have hG_right {s : ℝ} (hs : R ≤ s) : G s = 1 := by
    simp only [hG_def]
    rw [intervalIntegral.integral_eq_integral_of_support_subset
      (hρ_supp.trans (Ioo_subset_Ioc_self.trans (Ioc_subset_Ioc_right hs))), f.integral_normed]
  have hGlip : LipschitzWith K G := lipschitzWith_of_nnnorm_deriv_le hGd fun s => by
    rw [hGderiv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_of_nonneg (f.nonneg_normed s)]
    exact hρ_le s
  refine ⟨fun x => 1 - G ‖x - x₀‖, ?_, ?_, ?_, ?_, ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x = x₀
    · -- Near the centre the cutoff is constant.
      subst hx
      refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
        (Filter.eventually_of_mem (ball_mem_nhds x (hr.trans_lt hra)) fun y hy => ?_)
      dsimp only
      rw [hG_left (mem_ball_iff_norm.1 hy).le, sub_zero]
    · exact contDiffAt_const.sub (hGsmooth.contDiffAt.comp x
        ((contDiffAt_norm ℝ (sub_ne_zero.2 hx)).comp x (contDiffAt_id.sub contDiffAt_const)))
  · rintro _ ⟨x, rfl⟩
    have h0 : 0 ≤ G ‖x - x₀‖ :=
      (hG_left (min_le_right _ a)).symm.le.trans (hGmono (min_le_left _ _))
    have h1 : G ‖x - x₀‖ ≤ 1 := (hGmono (le_max_left _ R)).trans (hG_right (le_max_right _ _)).le
    exact ⟨by linarith, by linarith⟩
  · intro x hx
    dsimp only
    rw [hG_left ((mem_closedBall_iff_norm.1 hx).trans hra.le), sub_zero, Pi.one_apply]
  · intro x hx
    by_contra hxR
    refine hx ?_
    dsimp only
    rw [hG_right (not_lt.1 fun h => hxR (mem_ball_iff_norm.2 h)), sub_self]
  · have h := hGlip.comp (LipschitzWith.dist_left x₀)
    rw [mul_one] at h
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_sub_left]
    simpa only [comp_apply, dist_eq_norm] using h.dist_le_mul x y

end TauCeti

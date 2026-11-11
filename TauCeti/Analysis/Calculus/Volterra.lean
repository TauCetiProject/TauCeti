/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The DifferentialGeometry contributors, Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import TauCeti.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating Volterra convolutions

For a continuously differentiable scalar weight `b` and continuous vector-valued forcing `k`,
the derivative of `∫ r in a..t, b (t - r) • k r` is the boundary term `b 0 • k t` plus the
integral with differentiated weight. No global boundedness is required, and the interval is
oriented, so times may lie on either side of the initial time. With vanishing boundary weight,
the result holds in an arbitrary real normed space; the general boundary term requires a
complete target.

This is the time differentiation step in the Duhamel formula for frozen heat evolution.

Public formalization references:
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture

Original source notice:
Copyright (c) 2026 The DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A Volterra integral with vanishing boundary weight is differentiated under the integral
sign. The target need not be complete. -/
theorem hasDerivAt_integral_smul_sub_of_eq_zero {b db : ℝ → ℝ} {k : ℝ → F}
    (hb : ∀ q, HasDerivAt b (db q) q) (hdb : Continuous db) (hk : Continuous k)
    (hb₀ : b 0 = 0) (a t : ℝ) :
    HasDerivAt (fun q ↦ ∫ r in a..q, b (q - r) • k r)
      (∫ r in a..t, db (t - r) • k r) t := by
  have hbc : Continuous b := continuous_iff_continuousAt.mpr fun q ↦ (hb q).continuousAt
  have hcont (q : ℝ) : Continuous (fun r ↦ b (q - r) • k r) :=
    (hbc.comp (continuous_const.sub continuous_id)).smul hk
  have hfixed : HasDerivAt (fun q ↦ ∫ r in a..t, b (q - r) • k r)
      (∫ r in a..t, db (t - r) • k r) t := by
    have hderiv (q r : ℝ) : HasDerivAt (fun s ↦ b (s - r) • k r) (db (q - r) • k r) q := by
      simpa only [Function.comp_apply, id_eq, mul_one] using
        ((hb (q - r)).comp q ((hasDerivAt_id q).sub_const r)).smul_const (k r)
    have hfderiv (q r : ℝ) : fderiv ℝ (fun s ↦ b (s - r) • k r) q =
        (1 : ℝ →L[ℝ] ℝ).smulRight (db (q - r) • k r) :=
      (hderiv q r).hasFDerivAt.fderiv
    have hjoint : Continuous (fun p : ℝ × ℝ ↦
        (1 : ℝ →L[ℝ] ℝ).smulRight (db (p.1 - p.2) • k p.2)) :=
      (ContinuousLinearMap.smulRightL ℝ ℝ F 1).continuous.comp
        ((hdb.comp (continuous_fst.sub continuous_snd)).smul (hk.comp continuous_snd))
    have h := intervalIntegral.hasFDerivAt_integral_of_continuousOn_fderiv
      (𝕜 := ℝ) (μ := volume) (a := a) (b := t)
      (f := fun q r ↦ b (q - r) • k r) (x₀ := t) (u := Set.univ)
      Filter.univ_mem
      (((hbc.comp (continuous_fst.sub continuous_snd)).smul
        (hk.comp continuous_snd)).continuousOn)
      (fun r _ q _ ↦ (hderiv q r).differentiableAt.differentiableWithinAt)
      (by simpa only [hfderiv] using hjoint.continuousOn)
    have hL : Continuous (fun r ↦
        (1 : ℝ →L[ℝ] ℝ).smulRight (db (t - r) • k r)) :=
      hjoint.comp (continuous_const.prodMk continuous_id)
    have heval : (∫ r in a..t, fderiv ℝ (fun q ↦ b (q - r) • k r) t) 1 =
        ∫ r in a..t, db (t - r) • k r := by
      simp only [hfderiv]
      rw [ContinuousLinearMap.intervalIntegral_apply (hL.intervalIntegrable a t)]
      simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]
    simpa only [heval] using h.hasDerivAt
  have htail : HasDerivAt (fun q ↦ ∫ r in t..q, b (q - r) • k r) 0 t :=
    hasDerivAt_intervalIntegral_diag_of_eq_zero
      (((hbc.comp (continuous_fst.sub continuous_snd)).smul
        (hk.comp continuous_snd)).continuousAt) (by simp [hb₀])
  have hsplit (q : ℝ) :
      (∫ r in a..t, b (q - r) • k r) + (∫ r in t..q, b (q - r) • k r) =
        ∫ r in a..q, b (q - r) • k r :=
    intervalIntegral.integral_add_adjacent_intervals
      ((hcont q).intervalIntegrable a t) ((hcont q).intervalIntegrable t q)
  convert hfixed.add htail using 1
  · funext q
    exact (hsplit q).symm
  · exact (add_zero _).symm

/-- The derivative of a Volterra convolution consists of its boundary value and the integral
with differentiated weight. -/
theorem hasDerivAt_integral_smul_sub [CompleteSpace F] {b db : ℝ → ℝ} {k : ℝ → F}
    (hb : ∀ q, HasDerivAt b (db q) q) (hdb : Continuous db) (hk : Continuous k) (a t : ℝ) :
    HasDerivAt (fun q ↦ ∫ r in a..q, b (q - r) • k r)
      (b 0 • k t + ∫ r in a..t, db (t - r) • k r) t := by
  have hbc : Continuous b := continuous_iff_continuousAt.mpr fun q ↦ (hb q).continuousAt
  have hz := hasDerivAt_integral_smul_sub_of_eq_zero
    (b := fun q ↦ b q - b 0) (fun q ↦ (hb q).sub_const (b 0)) hdb hk (sub_self _) a t
  have hc : HasDerivAt (fun q ↦ ∫ r in a..q, b 0 • k r) (b 0 • k t) t :=
    (((continuous_const (y := b 0)).smul hk).integral_hasStrictDerivAt a t).hasDerivAt
  have hsplit (q : ℝ) :
      (∫ r in a..q, b 0 • k r) + (∫ r in a..q, (b (q - r) - b 0) • k r) =
        ∫ r in a..q, b (q - r) • k r := by
    have hzcont : Continuous (fun r ↦ (b (q - r) - b 0) • k r) :=
      ((hbc.comp (continuous_const.sub continuous_id)).sub continuous_const).smul hk
    have hccont : Continuous (fun r ↦ b 0 • k r) := continuous_const.smul hk
    rw [← intervalIntegral.integral_add (hccont.intervalIntegrable a q)
      (hzcont.intervalIntegrable a q)]
    congr 1
    funext r
    rw [← add_smul, add_sub_cancel]
  convert hc.add hz using 1
  funext q
  exact (hsplit q).symm

end TauCeti

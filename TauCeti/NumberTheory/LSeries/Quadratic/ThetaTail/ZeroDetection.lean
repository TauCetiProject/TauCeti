/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.Quadratic.ThetaTail.Basic
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import TauCeti.Analysis.MellinTransform.Basic
import TauCeti.Analysis.MellinTransform.Folding
import TauCeti.Analysis.MellinTransform.StripBounds
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed.GaussianTheta
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Mollifier
import TauCeti.NumberTheory.LSeries.GaussianTheta.Mellin
import TauCeti.NumberTheory.LSeries.ThetaInversion

/-!
# Detecting zeros of Dirichlet L-functions with theta tails

For primitive nonprincipal characters, a zero to the right of the critical line forces a
large joint tail of the theta series of the character and its Möbius twist. The conductor
bound puts the theta inversion point above the cutoff, so folding controls the critical-line
value of the completed L-function by the same tail that bounds the truncated mollifier.

This uses the argument of `New.three_lines_bound_of_LFunction_eq_zero` and
`New.eventually_rpow_lt_thetaTailIntegral` in `grh/src/Lib/Analytic/QuadraticTwist.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), revision `72fead1`.
-/

public section

open Complex Complex.HadamardThreeLines Filter MeasureTheory Set TauCeti
open scoped ArithmeticFunction.Moebius Real

namespace DirichletCharacter

private theorem norm_completedLFunction_div_two_le_tail {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hn : χ ≠ 1) {j : Fin 2}
    (hpar : χ (-1) = (-1) ^ j.val) {T : ℝ} (hT : 0 < T) (hN : (N : ℝ) ≤ T ^ 2)
    {s : ℂ} (hs : s.re = 1 / 2) :
    ‖χ.completedLFunction s / 2‖ ≤
      2 * ∫ u in Ioi T⁻¹, ‖gaussianThetaSeries j (fun n ↦ χ n) u‖ / u := by
  let f := gaussianThetaSeries j (fun n ↦ χ n)
  have hq : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hcut : T⁻¹ ≤ (√(N : ℝ))⁻¹ := by
    refine inv_anti₀ (Real.sqrt_pos.mpr hq) ?_
    simpa only [Real.sqrt_sq hT.le] using Real.sqrt_le_sqrt hN
  have hsym (u : ℝ) : ‖f (((√(N : ℝ))⁻¹) ^ 2 / u)‖ = ‖f u‖ := by
    rw [inv_pow, Real.sq_sqrt hq.le, div_eq_mul_inv, ← mul_inv, ← one_div]
    simpa only [f, gaussianThetaSeries_def, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      gaussianTheta_eq_gaussianDirichletTheta, gaussianDirichletTheta_def] using
      (hχ.norm_gaussian_theta_inversion hn (Nat.le_of_lt_succ j.isLt) hpar u).symm
  have hi := integrableOn_norm_gaussianThetaSeries_div (j := j) (c := fun n ↦ χ n)
    (fun n ↦ χ.norm_le_one n) (inv_pos.mpr hT)
  have heq : (fun u : ℝ ↦ u⁻¹ • (Ioi T⁻¹).indicator (fun t ↦ ‖f t‖) u) =
      (Ioi T⁻¹).indicator (fun u ↦ ‖f u‖ / u) := by
    funext u
    rw [← indicator_smul_apply (Ioi T⁻¹) (fun t : ℝ ↦ t⁻¹) (fun t ↦ ‖f t‖) u]
    simp only [smul_eq_mul, div_eq_inv_mul]
  have hsub : Ioi T⁻¹ ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi (inv_nonneg.mpr hT.le)
  have htail : IntegrableOn (fun u ↦ ‖f u‖) (Ioi T⁻¹) multHaar := by
    rwa [← integrable_indicator_iff measurableSet_Ioi, integrable_multHaar_iff, heq,
      integrableOn_indicator_iff measurableSet_Ioi.nullMeasurableSet, inter_eq_left.mpr hsub]
  have h := (mellinConvergent_and_norm_mellin_le_of_sq_div hcut
    (by simp [sub_re, hs] : (s - 1 / 2).re = 0)
    measurable_gaussianThetaSeries.aestronglyMeasurable (ae_of_all _ hsym) htail).2
  rw [(χ.hasMellin_gaussianThetaSeries_completedLFunction hn hpar s).2,
    ← integral_indicator measurableSet_Ioi, integral_multHaar_eq_setIntegral, heq,
    setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr hsub] at h
  exact h

private theorem norm_gaussianMollifier_le_tail {N : ℕ} {χ : DirichletCharacter ℂ N}
    (j : Fin 2) {T : ℝ} (hT : 0 < T) {s : ℂ} (hs : s.re = 1 / 2) :
    ‖χ.gaussianMollifier j.val T⁻¹ s‖ ≤
      ∫ u in Ioi T⁻¹, ‖gaussianThetaSeries j (fun n ↦ χ n * μ n) u‖ / u := by
  rw [gaussianMollifier_def]
  refine (norm_integral_le_integral_norm _).trans_eq
    (setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_)
  have hu₀ : 0 < u := (inv_pos.mpr hT).trans hu
  rw [← gaussianTheta_eq_gaussianDirichletTheta, norm_mul, norm_cpow_eq_rpow_re_of_pos hu₀,
    sub_re, one_re, hs, gaussianThetaSeries_def, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  conv_rhs => rw [div_eq_inv_mul, ← mul_assoc, Real.sqrt_eq_rpow, ← Real.rpow_neg_one,
    ← Real.rpow_add hu₀]
  ring_nf

private theorem gaussianMollifier_mellin_bounds {N : ℕ} (χ : DirichletCharacter ℂ N)
    (j : Fin 2) {r : ℝ} (hr : 0 < r) :
    DiffContOnCl ℂ (χ.gaussianMollifier j.val r) (verticalStrip (1 / 2) 2) ∧
      BddAbove ((norm ∘ χ.gaussianMollifier j.val r) '' verticalClosedStrip (1 / 2) 2) := by
  let c (n : ℕ) := χ n * (μ n : ℂ)
  have heq : χ.gaussianMollifier j.val r = mellin ((Ioi r).indicator (gaussianTheta j c)) := by
    funext s
    rw [gaussianMollifier_def, mellin_indicator_Ioi _ hr.le]
    simp only [smul_eq_mul, c, gaussianTheta_eq_gaussianDirichletTheta]
  rw [heq]
  have hc (n : ℕ+) : ‖c n‖ ≤ 1 := χ.norm_mul_moebius_le_one n
  refine ⟨(differentiable_mellin_indicator_Ioi_gaussianTheta j hc hr).diffContOnCl, ?_⟩
  obtain ⟨B, hB⟩ := (mellinConvergent_indicator_Ioi_gaussianTheta j hc hr
    ((1 / 2 : ℝ) : ℂ)).exists_norm_mellin_le_on_strip
      (mellinConvergent_indicator_Ioi_gaussianTheta j hc hr ((2 : ℝ) : ℂ))
  exact ⟨B, by rintro _ ⟨z, hz, rfl⟩; exact hB z hz⟩

private theorem thetaTail_mollifier_hypotheses {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hn : χ ≠ 1) {j : Fin 2}
    (hpar : χ (-1) = (-1) ^ j.val) {T : ℝ} (hT : 0 < T) (hN : (N : ℝ) ≤ T ^ 2) :
    let J := quadraticTwistGaussianThetaTailIntegral j (fun n ↦ χ n) T
    (∀ z : ℂ, z.re = 1 / 2 → ‖χ.completedLFunction z / 2‖ ≤ 2 * J) ∧
      (∀ z : ℂ, z.re = 1 / 2 → ‖χ.gaussianMollifier j.val T⁻¹ z‖ ≤ J) := by
  intro J
  have hi := integrableOn_quadraticTwistGaussianThetaTailIntegrand (j := j)
    (c := fun n ↦ χ n) (fun n ↦ χ.norm_le_one n) hT
  have h₁ := integrableOn_norm_gaussianThetaSeries_div (j := j)
    (c := fun n ↦ χ n) (fun n ↦ χ.norm_le_one n) (inv_pos.mpr hT)
  have h₂ := integrableOn_norm_gaussianThetaSeries_div (j := j)
    (c := fun n ↦ χ n * μ n) (fun n ↦ χ.norm_mul_moebius_le_one n) (inv_pos.mpr hT)
  refine ⟨fun z hz ↦ (norm_completedLFunction_div_two_le_tail hχ hn hpar hT hN hz).trans
    (mul_le_mul_of_nonneg_left ?_ zero_le_two),
    fun z hz ↦ (norm_gaussianMollifier_le_tail j hT hz).trans ?_⟩
  all_goals
    dsimp only [J]
    rw [quadraticTwistGaussianThetaTailIntegral_def]
    refine setIntegral_mono_on (by assumption) hi measurableSet_Ioi (fun u hu ↦ ?_)
    have hu₀ : 0 < u := (inv_pos.mpr hT).trans hu
    gcongr; simp

private theorem exists_gaussianMollifier_right_bound (j : Fin 2) :
    ∃ D : ℝ, ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N},
      χ (-1) = (-1) ^ j.val → ∀ {T : ℝ}, 0 < T → ∀ z : ℂ, z.re = 2 →
      ‖χ.completedLFunction z / 2 * χ.gaussianMollifier j.val T⁻¹ z -
        (χ.gammaFactor z / 2) ^ 2‖ ≤ D / T := by
  obtain ⟨D, _, hD⟩ := norm_LFunction_mul_gaussianMollifier_sub j.val
  refine ⟨D, fun {N} _ {χ} hj {T} hT z hz ↦ ?_⟩
  have hΓ : χ.gammaFactor z = Gammaℝ (z + j.val) := by
    fin_cases j
    · have he : χ.Even := by simpa [Even] using hj
      simp [he.gammaFactor_def]
    · have ho : χ.Odd := by simpa [Odd] using hj
      simp [ho.gammaFactor_def]
  rw [χ.completedLFunction_eq_gammaFactor_mul_LFunction (by linarith), hΓ]
  simpa only [div_eq_mul_inv, mul_right_comm] using hD χ (inv_nonneg.mpr hT.le) hz

/-- For primitive nonprincipal characters of conductor at most `T²`, if the joint theta tail is
at most `T^(2δ)`, the square of the half gamma factor at a zero with `Re s ≥ 1/2 + 9δ` is bounded
by `C T^(-2δ)`. The constant is independent of `T`, the conductor and the character. -/
theorem norm_gammaFactor_div_two_sq_le_of_thetaTail_le (j : Fin 2) :
    ∃ C > 0, ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → χ ≠ 1 →
      χ (-1) = (-1) ^ j.val → ∀ {T δ : ℝ}, 0 < T → (N : ℝ) ≤ T ^ 2 → 0 ≤ δ →
      quadraticTwistGaussianThetaTailIntegral j (fun n ↦ χ n) T ≤ T ^ (2 * δ) →
      ∀ {s : ℂ}, 1 / 2 + 9 * δ ≤ s.re → χ.LFunction s = 0 →
      ‖χ.gammaFactor s / 2‖ ^ 2 ≤ C * T ^ (-2 * δ) := by
  obtain ⟨D, hD⟩ := exists_gaussianMollifier_right_bound j
  obtain ⟨C, hC₀, hC⟩ :=
    TauCeti.DirichletCharacter.norm_gammaFactor_div_two_sq_le_of_LFunction_eq_zero D
  refine ⟨C, hC₀, fun {N} _ {χ} hp hn hj {T δ} hT hN hδ hJ {s} hs hz ↦ ?_⟩
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hT₁ : 1 ≤ T := by nlinarith [hN₁.trans hN]
  obtain ⟨hd, hb⟩ := gaussianMollifier_mellin_bounds χ j (inv_pos.mpr hT)
  obtain ⟨hl, hm⟩ := thetaTail_mollifier_hypotheses hp hn hj hT hN
  refine hC hn hT₁ hδ hd hb (fun z hz ↦ (hl z hz).trans
    (mul_le_mul_of_nonneg_left hJ zero_le_two)) (fun z hz ↦ (hm z hz).trans hJ)
    (hD hj hT) hs hz

/-- Uniformly for primitive nonprincipal characters of conductor at most `T²` and matching
parity, a zero with `Re s ≥ 1/2 + 9δ` and `|Im s| ≤ H` forces the joint theta tail above
`T^(2δ)` for all sufficiently large `T`. -/
theorem eventually_rpow_lt_quadraticTwistGaussianThetaTailIntegral (j : Fin 2)
    (H : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N},
      χ.IsPrimitive → χ ≠ 1 → χ (-1) = (-1) ^ j.val → (N : ℝ) ≤ T ^ 2 →
      ∀ {s : ℂ}, 1 / 2 + 9 * δ ≤ s.re → |s.im| ≤ H → χ.LFunction s = 0 →
      T ^ (2 * δ) < quadraticTwistGaussianThetaTailIntegral j (fun n ↦ χ n) T := by
  obtain ⟨D, hD⟩ := exists_gaussianMollifier_right_bound j
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    TauCeti.DirichletCharacter.eventually_LFunction_ne_zero_of_mollifier_bounds D H hδ]
    with T hT hfree N _ χ hp hn hj hN s hs hH hz
  refine lt_of_not_ge fun hJ ↦ ?_
  obtain ⟨hd, hb⟩ := gaussianMollifier_mellin_bounds χ j (inv_pos.mpr hT)
  obtain ⟨hl, hm⟩ := thetaTail_mollifier_hypotheses hp hn hj hT hN
  exact hfree hn hd hb (fun z hz ↦ (hl z hz).trans (mul_le_mul_of_nonneg_left hJ zero_le_two))
    (fun z hz ↦ (hm z hz).trans hJ) (hD hj hT) hs hH hz

end DirichletCharacter

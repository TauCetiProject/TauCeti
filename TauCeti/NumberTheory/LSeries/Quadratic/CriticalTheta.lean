/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.LSeries.Quadratic.ThetaTail
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean
import TauCeti.MeasureTheory.Integral.Bochner.Reciprocal
import TauCeti.NumberTheory.LSeries.ThetaInversion

/-!
# The critical-line bound from a Dirichlet theta tail

For a primitive nonprincipal Dirichlet character, the norm of its normalized theta series is
invariant under reciprocal reflection at the inverse square root of the conductor. This folds the
absolute theta integral onto its upper half. On the critical line the Mellin factor has modulus
one in logarithmic measure, so the joint theta tail bounds the completed L-function uniformly in
height when the conductor is at most the square of the cutoff parameter.

The Mellin representation and folding formula follow the normalization of
`New.hasMellin_thetaSeries_char` and `New.integral_norm_thetaSeries_div` in
`grh/src/Lib/Analytic/DirichletTheta.lean` of lsernau/grh-lean (revision `72fead1`). The
critical-line bound is that of `New.norm_gaussianMellin_mul_LFunction_le` in the same
repository, `grh/src/Lib/Analytic/QuadraticTwist.lean`.
-/

public section

open Complex MeasureTheory Real Set TauCeti
open Filter Topology Asymptotics

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {j : Fin 2}

local notation "θ" => gaussianThetaSeries j (fun n ↦ χ n)

private theorem norm_gaussianThetaSeries_reflect (hχ : χ.IsPrimitive) (hχ₀ : χ ≠ 1)
    (hpar : χ (-1) = (-1) ^ (j : ℕ)) (t : ℝ) :
    ‖θ ((√(N : ℝ))⁻¹ ^ 2 / t)‖ = ‖θ t‖ := by
  rw [inv_pow, sq_sqrt (by positivity : 0 ≤ (N : ℝ)), ← one_div, div_div]
  simp only [gaussianThetaSeries_def, norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sqrt_nonneg _), gaussianTheta_def]
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ χ n * gaussianMonomial j (n * t)),
    tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ χ n * gaussianMonomial j (n * (1 / (N * t))))]
  have h := (hχ.norm_gaussian_theta_inversion hχ₀ (by omega : (j : ℕ) ≤ 1) hpar t).symm
  fin_cases j <;> simpa using h

omit [NeZero N] in
private theorem isBigO_gaussianThetaSeries_atTop :
    θ =O[atTop] (fun t ↦ Real.exp (-1 * t)) := by
  refine IsBigO.of_bound 3 (eventually_atTop.2 ⟨1, fun t ht ↦ ?_⟩)
  simpa only [neg_one_mul, Real.norm_eq_abs, abs_of_pos (exp_pos _)] using
    (norm_gaussianThetaSeries_le (j := j) (fun n : ℕ+ ↦ χ.norm_le_one n) t).trans
      (div_le_self (by positivity) (by simpa using (Real.sqrt_le_sqrt ht)))

private theorem isBigO_gaussianThetaSeries_atZero (hχ : χ.IsPrimitive) (hχ₀ : χ ≠ 1)
    (hpar : χ (-1) = (-1) ^ (j : ℕ)) :
    θ =O[𝓝[>] 0] (fun t ↦ t ^ (1 / 2 : ℝ)) := by
  let a := (√(N : ℝ))⁻¹
  have ha : 0 < a := inv_pos.mpr (sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N)))
  refine IsBigO.of_bound (3 / a) ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [← norm_gaussianThetaSeries_reflect hχ hχ₀ hpar t, ← Real.sqrt_eq_rpow,
    Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _)]
  calc
    _ ≤ 3 * Real.exp (-(a ^ 2 / t)) / √(a ^ 2 / t) :=
      norm_gaussianThetaSeries_le (fun n : ℕ+ ↦ χ.norm_le_one n) _
    _ ≤ 3 / √(a ^ 2 / t) := by
      have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (sq_nonneg a) ht.le))
      simpa only [mul_one] using div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 3)) (sqrt_nonneg _)
    _ = _ := by rw [sqrt_div (sq_nonneg a), sqrt_sq ha.le, div_div_eq_mul_div, div_mul_eq_mul_div]

private theorem mellin_regular_gaussianThetaSeries (hχ : χ.IsPrimitive) (hχ₀ : χ ≠ 1)
    (hpar : χ (-1) = (-1) ^ (j : ℕ)) {w : ℂ} (hw : -(1 / 2 : ℝ) < w.re) :
    MellinConvergent θ w ∧ DifferentiableAt ℂ (mellin θ) w := by
  have hzero : θ =O[𝓝[>] 0] (fun t ↦ t ^ (-(-(1 / 2)) : ℝ)) := by
    simpa only [neg_neg] using isBigO_gaussianThetaSeries_atZero hχ hχ₀ hpar
  have hloc : LocallyIntegrableOn θ (Ioi 0) := by
    have hint := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := -(1 / 2)) (p := 1) (b := 1)
      (by norm_num) zero_lt_one zero_lt_one).const_mul 3
    apply IntegrableOn.locallyIntegrableOn
    refine hint.mono' measurable_gaussianThetaSeries.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    rw [Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow, Real.rpow_one, neg_mul, one_mul]
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm (√t)⁻¹] using
      (norm_gaussianThetaSeries_le (j := j) (c := fun n ↦ χ n) (fun n ↦ χ.norm_le_one n) t)
  exact ⟨mellinConvergent_of_isBigO_rpow_exp zero_lt_one hloc
    isBigO_gaussianThetaSeries_atTop hzero hw,
    mellin_differentiableAt_of_isBigO_rpow_exp zero_lt_one hloc
      isBigO_gaussianThetaSeries_atTop hzero hw⟩

/-- For a primitive nonprincipal character of parity `j`, the Mellin transform of its
square-root-normalized theta series at `s − 1/2` equals the L-function with its half-gamma
factor. The integral converges absolutely for `0 < Re s`. -/
theorem IsPrimitive.hasMellin_gaussianThetaSeries (hχ : χ.IsPrimitive) (hχ₀ : χ ≠ 1)
    (hpar : χ (-1) = (-1) ^ (j : ℕ)) {s : ℂ} (hs : 0 < s.re) :
    HasMellin θ (s - 1 / 2) (χ.LFunction s * (Gammaℝ (s + (j : ℕ)) / 2)) := by
  have hregular (z : ℂ) (hz : 0 < z.re) :=
    mellin_regular_gaussianThetaSeries hχ hχ₀ hpar (w := z - 1 / 2) (by simpa using hz)
  refine ⟨(hregular s hs).1, ?_⟩
  let U := {z : ℂ | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have hA : AnalyticOnNhd ℂ (fun z ↦ mellin θ (z - 1 / 2)) U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z (hz : 0 < z.re)
    exact ((hregular z hz).2.comp z (differentiableAt_id.sub_const _)).differentiableWithinAt
  have hB : AnalyticOnNhd ℂ (fun z ↦ χ.LFunction z * (Gammaℝ (z + (j : ℕ)) / 2)) U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z (hz : 0 < z.re)
    refine (differentiable_LFunction hχ₀ z).differentiableWithinAt.mul ?_
    refine ((differentiableAt_Gammaℝ (Gammaℝ_ne_zero_of_re_pos ?_)).comp z
      (differentiableAt_id.add_const ((j : ℕ) : ℂ))).differentiableWithinAt.div_const 2
    simpa using hz.trans_le (le_add_of_nonneg_right (Nat.cast_nonneg (j : ℕ)))
  refine hA.eqOn_of_preconnected_of_eventuallyEq hB (convex_halfSpace_re_gt 0).isPreconnected
    (z₀ := 2) (by norm_num [U]) ?_ hs
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (by
    norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z (hz : 1 < z.re)
  let f := gaussianDirichletTheta (j : ℕ) (fun n ↦ χ n)
  have hθ : EqOn θ (fun t : ℝ ↦ (t : ℂ) ^ (1 / 2 : ℂ) • f t) (Ioi 0) := by
    intro t (ht : 0 < t)
    rw [gaussianThetaSeries_def, sqrt_eq_rpow, ofReal_cpow ht.le]
    simp only [ofReal_div, ofReal_one, ofReal_ofNat, smul_eq_mul]
    congr 1
    dsimp only [f]
    rw [gaussianTheta_def, tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦
      χ n * gaussianMonomial j (n * t)), gaussianDirichletTheta_def]
    fin_cases j <;> simp
  calc
    mellin θ (z - 1 / 2) = mellin (fun t : ℝ ↦ (t : ℂ) ^ (1 / 2 : ℂ) • f t) (z - 1 / 2) := by
      exact setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ congrArg (_ • ·) (hθ ht)
    _ = mellin f z := by rw [mellin_cpow_smul, sub_add_cancel]
    _ = _ := ?_
  rw [LFunction_eq_LSeries χ hz]
  exact (hasMellin_gaussianDirichletTheta (j : ℕ) (χ.LSeriesSummable_of_one_lt_re hz)
    (by linarith [Nat.cast_nonneg (α := ℝ) (j : ℕ)])).2

/-- The full absolute theta integral of a primitive nonprincipal character is twice the tail
above the inverse square root of its conductor. -/
theorem IsPrimitive.integral_norm_gaussianThetaSeries_div (hχ : χ.IsPrimitive) (hχ₀ : χ ≠ 1)
    (hpar : χ (-1) = (-1) ^ (j : ℕ)) :
    (∫ t in Ioi (0 : ℝ), ‖θ t‖ / t) =
      2 * ∫ t in Ioi (√(N : ℝ))⁻¹, ‖θ t‖ / t := by
  have ha := inv_pos.mpr (sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N) : 0 < (N : ℝ)))
  simpa only [smul_eq_mul, ← div_eq_inv_mul] using
    (integral_inv_smul_eq_two_smul_integral_Ioi_of_div_eq (f := fun t ↦ ‖θ t‖) ha
      (fun t _ ↦ norm_gaussianThetaSeries_reflect hχ hχ₀ hpar t)
      (by
        simpa only [smul_eq_mul, ← div_eq_inv_mul] using
          integrableOn_norm_gaussianThetaSeries_div (j := j) (c := fun n ↦ χ n)
            (fun n ↦ χ.norm_le_one n) ha)).2

/-- On the critical line, the norm of the L-function with its half-gamma factor is at most
twice the joint theta tail, provided the conductor does not exceed `T²`. -/
theorem IsPrimitive.norm_halfGamma_mul_LFunction_le_thetaTail
    (hχ : χ.IsPrimitive) (hχ₀ : χ ≠ 1) (hpar : χ (-1) = (-1) ^ (j : ℕ))
    {T : ℝ} (hT : 0 < T) (hN : (N : ℝ) ≤ T ^ 2) {s : ℂ} (hs : s.re = 1 / 2) :
    ‖(Gammaℝ (s + (j : ℕ)) / 2) * χ.LFunction s‖ ≤
      2 * quadraticTwistGaussianThetaTailIntegral j (fun n ↦ χ n) T := by
  have hM := hχ.hasMellin_gaussianThetaSeries hχ₀ hpar (s := s) (by linarith)
  have hnorm (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      ‖(t : ℂ) ^ (s - 1 / 2 - 1) • θ t‖ = ‖θ t‖ / t := by
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht]
    simp [hs, Real.rpow_neg ht.le, div_eq_inv_mul]
  have hc (n : ℕ+) : ‖χ n‖ ≤ 1 := χ.norm_le_one n
  have hcut : T⁻¹ ≤ (√(N : ℝ))⁻¹ := by
    apply inv_anti₀ (sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N)))
    simpa [sqrt_sq hT.le] using (Real.sqrt_le_sqrt hN)
  rw [mul_comm, ← hM.2, mellin, quadraticTwistGaussianThetaTailIntegral_def]
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖θ t‖ / t := by
      rw [← setIntegral_congr_fun measurableSet_Ioi hnorm]
      exact norm_integral_le_integral_norm _
    _ = 2 * ∫ t in Ioi (√(N : ℝ))⁻¹, ‖θ t‖ / t :=
      hχ.integral_norm_gaussianThetaSeries_div hχ₀ hpar
    _ ≤ 2 * ∫ t in Ioi T⁻¹, ‖θ t‖ / t := by
      refine mul_le_mul_of_nonneg_left (setIntegral_mono_set
        (integrableOn_norm_gaussianThetaSeries_div hc (inv_pos.mpr hT)) ?_ ?_) (by norm_num)
      · exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦
          div_nonneg (norm_nonneg _) ((inv_pos.mpr hT).trans ht).le
      · exact Filter.Eventually.of_forall (Ioi_subset_Ioi hcut)
    _ ≤ _ := by
      refine mul_le_mul_of_nonneg_left (setIntegral_mono_on
        (integrableOn_norm_gaussianThetaSeries_div hc (inv_pos.mpr hT))
        (integrableOn_quadraticTwistGaussianThetaTailIntegrand (c := fun n ↦ χ n) hc hT)
        measurableSet_Ioi ?_) (by norm_num)
      intro t ht
      exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (norm_nonneg _))
        ((inv_pos.mpr hT).trans ht).le

end DirichletCharacter

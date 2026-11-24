/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Power series for exponential integrals

An exponential envelope permits termwise integration of the exponential series. We allow
a real weight in the integral so that the same series applies to the partition function and
its directional derivatives. The proof uses Mathlib's `NormedSpace.expSeries` for each
integrand and `hasSum_integral_of_dominated_convergence` to integrate its coefficients.

## References

* L. D. Brown, *Fundamentals of Statistical Exponential Families* (1986), Theorem 2.2.
-/

public section

noncomputable section

open MeasureTheory Real ContinuousMultilinearMap
open scoped ENNReal Nat NNReal RealInnerProductSpace

namespace TauCeti

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ν : Measure X} {T : X → E} {w : X → ℝ} {η : E} {r : ℝ≥0}

/-- The integrand of an exponential series coefficient is the corresponding coefficient
of the real exponential composed with the linear functional associated to the statistic. -/
private def exponentialIntegralTerm (T : X → E) (w : X → ℝ) (η : E) (n : ℕ) (x : X) :
    E [×n]→L[ℝ] ℝ :=
  (exp ⟪η, T x⟫ * w x) •
    (NormedSpace.expSeries ℝ ℝ n).compContinuousLinearMap (fun _ ↦ innerSL ℝ (T x))

/-- The exponential series integrated coefficientwise against a real weight. -/
def exponentialIntegralSeries (ν : Measure X) (T : X → E) (w : X → ℝ) (η : E) :
    FormalMultilinearSeries ℝ E ℝ :=
  fun n ↦ ∫ x, exponentialIntegralTerm T w η n x ∂ν

private theorem aestronglyMeasurable_exponentialIntegralTerm
    (hT : AEStronglyMeasurable T ν) (hw : AEStronglyMeasurable w ν) (n : ℕ) :
    AEStronglyMeasurable (exponentialIntegralTerm T w η n) ν := by
  let multilinearComp := compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin n ↦ E) (fun _ ↦ ℝ) ℝ
  have hc : Continuous fun y : E ↦
      (NormedSpace.expSeries ℝ ℝ n).compContinuousLinearMap (fun _ ↦ innerSL ℝ y) := by
    have h := (multilinearComp.cont.comp
      (continuous_pi fun _ ↦ (innerSL ℝ (E := E)).continuous))
    convert h.clm_apply (continuous_const (y := NormedSpace.expSeries ℝ ℝ n)) using 1
    funext y
    exact (compContinuousLinearMapContinuousMultilinear_apply_apply ℝ _ _ ℝ
      (fun _ : Fin n ↦ innerSL ℝ y) (NormedSpace.expSeries ℝ ℝ n)).symm
  exact ((hT.const_inner.aemeasurable.exp.aestronglyMeasurable).mul hw).smul
    (hc.comp_aestronglyMeasurable hT)

omit [MeasurableSpace X] in
private theorem norm_exponentialIntegralTerm_le (n : ℕ) (x : X) :
    ‖exponentialIntegralTerm T w η n x‖ ≤
      exp ⟪η, T x⟫ * ‖w x‖ * (‖T x‖ ^ n / n !) := by
  have hnorm : ‖NormedSpace.expSeries ℝ ℝ n‖ = ((n ! : ℕ) : ℝ)⁻¹ := by
    simp [NormedSpace.expSeries, norm_smul]
  rw [exponentialIntegralTerm, norm_smul, norm_mul, Real.norm_eq_abs (exp _),
    abs_of_pos (exp_pos _)]
  gcongr
  simpa [hnorm, Finset.prod_const, div_eq_inv_mul] using
    (NormedSpace.expSeries ℝ ℝ n).norm_compContinuousLinearMap_le
      (fun _ ↦ innerSL ℝ (T x))

omit [MeasurableSpace X] in
private theorem norm_exponentialIntegralTerm_mul_pow_le (n : ℕ) (x : X) :
    ‖exponentialIntegralTerm T w η n x‖ * (r : ℝ) ^ n ≤
      (exp ⟪η, T x⟫ * ‖w x‖) * (((r : ℝ) * ‖T x‖) ^ n / n !) := by
  rw [mul_pow]
  convert mul_le_mul_of_nonneg_right (norm_exponentialIntegralTerm_le (T := T)
    (w := w) (η := η) n x) (pow_nonneg r.coe_nonneg n) using 1
  ring

omit [MeasurableSpace X] in
private theorem norm_exponentialIntegralTerm_mul_pow_le_exp (n : ℕ) (x : X) :
    ‖exponentialIntegralTerm T w η n x‖ * (r : ℝ) ^ n ≤
      exp (⟪η, T x⟫ + (r : ℝ) * ‖T x‖) * ‖w x‖ := by
  refine (norm_exponentialIntegralTerm_mul_pow_le n x).trans ?_
  have h := pow_div_factorial_le_exp (x := (r : ℝ) * ‖T x‖) (by positivity) n
  calc
    _ ≤ (exp ⟪η, T x⟫ * ‖w x‖) * exp ((r : ℝ) * ‖T x‖) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [exp_add]; ring

private theorem integrable_exponentialIntegralTerm
    (hT : AEStronglyMeasurable T ν) (hw : AEStronglyMeasurable w ν) (hr : 0 < r)
    (h : Integrable (fun x ↦ exp (⟪η, T x⟫ + (r : ℝ) * ‖T x‖) * ‖w x‖) ν) (n : ℕ) :
    Integrable (exponentialIntegralTerm T w η n) ν := by
  have hrn : 0 < (r : ℝ) ^ n := pow_pos (by exact_mod_cast hr) _
  refine (h.div_const ((r : ℝ) ^ n)).mono' (aestronglyMeasurable_exponentialIntegralTerm hT hw n)
    (ae_of_all _ fun x ↦ (le_div_iff₀ hrn).2 (norm_exponentialIntegralTerm_mul_pow_le_exp n x))

/-- Evaluating a coefficient gives the corresponding mixed moment divided by a factorial. -/
theorem exponentialIntegralSeries_apply
    (hT : AEStronglyMeasurable T ν) (hw : AEStronglyMeasurable w ν) (hr : 0 < r)
    (h : Integrable (fun x ↦ exp (⟪η, T x⟫ + (r : ℝ) * ‖T x‖) * ‖w x‖) ν)
    {n : ℕ} (v : Fin n → E) :
    exponentialIntegralSeries ν T w η n v =
      ∫ x, (exp ⟪η, T x⟫ * w x) * ((∏ i, ⟪T x, v i⟫) / n !) ∂ν := by
  rw [exponentialIntegralSeries, ContinuousMultilinearMap.integral_apply
    (integrable_exponentialIntegralTerm hT hw hr h n)]
  congr with x
  simp [exponentialIntegralTerm, NormedSpace.expSeries, div_eq_inv_mul, List.prod_ofFn]

omit [MeasurableSpace X] in
private theorem hasSum_exponentialIntegralTerm (x : X) (y : E) :
    HasSum (fun n ↦ exponentialIntegralTerm T w η n x (fun _ ↦ y))
      (exp ⟪η + y, T x⟫ * w x) := by
  simpa only [exponentialIntegralTerm, compContinuousLinearMap_apply, smul_apply, smul_eq_mul,
    innerSL_apply_apply, real_inner_comm (T x) y, ← exp_eq_exp_ℝ, inner_add_left, exp_add,
    mul_right_comm (exp ⟪η, T x⟫)] using
    (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) ⟪y, T x⟫).mul_left (exp ⟪η, T x⟫ * w x)

/-- An integrable exponential envelope justifies integrating the power series in a ball.
The result also applies in infinite dimensions when the envelope is available. -/
theorem hasFPowerSeriesOnBall_exponentialIntegral
    (hT : AEStronglyMeasurable T ν) (hw : AEStronglyMeasurable w ν) (hr : 0 < r)
    (h : Integrable (fun x ↦ exp (⟪η, T x⟫ + (r : ℝ) * ‖T x‖) * ‖w x‖) ν) :
    HasFPowerSeriesOnBall (fun t ↦ ∫ x, exp ⟪t, T x⟫ * w x ∂ν)
      (exponentialIntegralSeries ν T w η) η r := by
  refine ⟨?_, by exact_mod_cast hr, ?_⟩
  · refine FormalMultilinearSeries.le_radius_of_bound _
      (∫ x, exp (⟪η, T x⟫ + (r : ℝ) * ‖T x‖) * ‖w x‖ ∂ν) (r := r) fun n ↦ ?_
    rw [exponentialIntegralSeries, mul_comm, ← Real.norm_of_nonneg (pow_nonneg r.coe_nonneg n),
      ← norm_smul, ← integral_smul]
    exact norm_integral_le_of_norm_le h (ae_of_all _ fun x ↦ by
      simpa [norm_smul, abs_of_nonneg r.coe_nonneg, mul_comm] using
        (norm_exponentialIntegralTerm_mul_pow_le_exp (r := r) (T := T) (w := w) (η := η) n x))
  · intro y hy
    have hy' : ‖y‖ ≤ r := by
      rw [Metric.mem_eball, edist_zero_right, eNorm_eq_nnNorm, ENNReal.coe_lt_coe] at hy
      exact_mod_cast hy.le
    let bound (n : ℕ) (x : X) :=
      (exp ⟪η, T x⟫ * ‖w x‖) * (((r : ℝ) * ‖T x‖) ^ n / n !)
    have hsum (x : X) : HasSum (fun n ↦ bound n x)
        (exp (⟪η, T x⟫ + (r : ℝ) * ‖T x‖) * ‖w x‖) := by
      simpa [bound, ← exp_eq_exp_ℝ, exp_add, mul_right_comm (exp ⟪η, T x⟫)] using
        (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * ‖T x‖)).mul_left
          (exp ⟪η, T x⟫ * ‖w x‖)
    have hb (n : ℕ) (x : X) : ‖exponentialIntegralTerm T w η n x (fun _ ↦ y)‖ ≤ bound n x := by
      refine (le_opNorm _ _).trans ?_
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      calc
        _ ≤ ‖exponentialIntegralTerm T w η n x‖ * (r : ℝ) ^ n := by gcongr
        _ ≤ bound n x := norm_exponentialIntegralTerm_mul_pow_le n x
    have hl := hasSum_integral_of_dominated_convergence bound
      (fun n ↦ (ContinuousMultilinearMap.apply ℝ _ ℝ (fun _ : Fin n ↦ y)).continuous
        |>.comp_aestronglyMeasurable (aestronglyMeasurable_exponentialIntegralTerm hT hw n))
      (fun n ↦ ae_of_all _ (hb n)) (ae_of_all _ fun x ↦ (hsum x).summable)
      (by simpa only [funext fun x ↦ (hsum x).tsum_eq] using h)
      (ae_of_all _ fun x ↦ hasSum_exponentialIntegralTerm (T := T) (w := w) (η := η) x y)
    simpa only [exponentialIntegralSeries, ContinuousMultilinearMap.apply_apply,
      ContinuousMultilinearMap.integral_apply
      (integrable_exponentialIntegralTerm hT hw hr h _)] using hl

/-- The derivative of an exponential integral is its first weighted moment. -/
theorem fderiv_exponentialIntegral_apply
    (hT : AEStronglyMeasurable T ν) (hw : AEStronglyMeasurable w ν) (hr : 0 < r)
    (h : Integrable (fun x ↦ exp (⟪η, T x⟫ + (r : ℝ) * ‖T x‖) * ‖w x‖) ν) (v : E) :
    fderiv ℝ (fun t ↦ ∫ x, exp ⟪t, T x⟫ * w x ∂ν) η v =
      ∫ x, exp ⟪η, T x⟫ * w x * ⟪v, T x⟫ ∂ν := by
  rw [(hasFPowerSeriesOnBall_exponentialIntegral hT hw hr h).hasFPowerSeriesAt.hasFDerivAt.fderiv]
  simp [exponentialIntegralSeries_apply hT hw hr h, real_inner_comm v]

end TauCeti

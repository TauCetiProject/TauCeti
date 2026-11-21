/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.Contour.Cycle.Circle
public import TauCeti.Analysis.Green.Cycle
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.Dual
import TauCeti.Probability.Distributions.CircularLaw

/-!
# Complex Green–Stokes formulas on contour cycles

For a contour cycle `C` lying in an open set `U` (`C.IsIn U`) and null-homologous in `U`
(`C.IsNullHomologous U`), and a scalar map `F : ℂ → ℂ` that is real `C¹` on `U`
(`ContDiffOn ℝ 1 F U`), applying `TauCeti.Contour.Cycle.green_winding` to the real coordinate
pairs `(Re F, -Im F)` and `(Im F, Re F)` yields the scalar complex Green formula
`C.integral F = (2 * I) * ∫ z in U, (C.windingWeight z : ℂ) * conjWirtingerDeriv F z 1`.
Pairing with continuous `ℂ`-linear functionals (`SeparatingDual`) extends this to maps `F : ℂ → E`
into any complex normed space `E`:
`C.integral F = (2 * I : ℂ) • ∫ z in U, C.windingWeight z • conjWirtingerDeriv F z 1`.

Applying the scalar `dz` formula to `conj ∘ F` and conjugating yields the dual `F dbar z`
circulation formula on contour cycles (under the same `U`, `C.IsIn U`, `C.IsNullHomologous U`, and
`ContDiffOn ℝ 1 F U` hypotheses) and, for `R ≥ 0` and `F` real `C¹` on an open neighborhood `U` of
`closedBall c R`, the circle Stokes formula
`∫ θ in 0..2 * π, F (circleMap c R θ) * conj (deriv (circleMap c R) θ) =`
`  (-2 * I) * ∫ z in ball c R, wirtingerDeriv F z 1`.
A private Stokes cross-check also verifies agreement with
`TauCeti.Probability.integral_pow_mul_conj_pow_circularLaw`.

## Main results

* `TauCeti.re_deriv_mul_eq_circulationFun`, `im_deriv_mul_eq_circulationFun`,
  `TauCeti.Contour.Cycle.re_integral_eq_sum_circulationFun`, `im_integral_eq_sum_circulationFun`
* `TauCeti.curl_re_neg_im_eq_neg_two_mul_im_conjWirtingerDeriv`,
  `curl_im_re_eq_two_mul_re_conjWirtingerDeriv`
* `TauCeti.Contour.Cycle.integral_eq_two_mul_I_mul_integral_windingWeight_conjWirtingerDeriv`,
  `TauCeti.Contour.Cycle.integral_eq_two_mul_I_smul_integral_windingWeight_conjWirtingerDeriv`
* `Contour.Cycle.circulation_dzBar_eq_neg_two_mul_I_mul_integral_windingWeight_wirtingerDeriv`,
  `TauCeti.circulation_dzBar_circleMap_eq_neg_two_mul_I_mul_integral_ball_wirtingerDeriv`,
  `TauCeti.integral_mul_conj_deriv_circleMap_eq_neg_two_mul_I_mul_integral_ball_wirtingerDeriv`

## References

* A. Rainer, *Advanced Complex Analysis*, §10, p. 23, Proposition 10.1.
* L. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979, Chapter 4, §4.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Section 1.2.
-/

public section

noncomputable section

open Complex ComplexConjugate Filter MeasureTheory Metric Set
open scoped Interval Real Topology

namespace TauCeti

/-! ### Coordinate comparison between complex contour integrands and planar circulation -/

/-- Along any curve `γ`, the real part of `γ' t * F (γ t)` is the planar circulation integrand of
`(Re F, -Im F)`. -/
theorem re_deriv_mul_eq_circulationFun (F : ℂ → ℂ) (γ : ℝ → ℂ) (t : ℝ) :
    (deriv γ t * F (γ t)).re =
      Green.circulationFun (fun z ↦ (F z).re) (fun z ↦ -(F z).im) γ t := by
  simp only [Green.circulationFun, mul_re]; ring

/-- Along any curve `γ`, the imaginary part of `γ' t * F (γ t)` is the planar circulation integrand
of `(Im F, Re F)`. -/
theorem im_deriv_mul_eq_circulationFun (F : ℂ → ℂ) (γ : ℝ → ℂ) (t : ℝ) :
    (deriv γ t * F (γ t)).im =
      Green.circulationFun (fun z ↦ (F z).im) (fun z ↦ (F z).re) γ t := by
  simp only [Green.circulationFun, mul_im]; ring

/-- Along any curve `γ`, `γ' t * F (γ t)` decomposes into the planar circulation integrands of
`(Re F, -Im F)` and `(Im F, Re F)`. -/
theorem deriv_mul_eq_circulationFun (F : ℂ → ℂ) (γ : ℝ → ℂ) (t : ℝ) :
    deriv γ t * F (γ t) =
      (Green.circulationFun (fun z ↦ (F z).re) (fun z ↦ -(F z).im) γ t : ℂ) +
        I * (Green.circulationFun (fun z ↦ (F z).im) (fun z ↦ (F z).re) γ t : ℂ) := by
  apply Complex.ext <;> simp [Green.circulationFun] <;> ring

/-- Along any curve `γ`, `F (γ t) * conj (γ' t)` decomposes into the planar circulation integrands
of `(Re F, Im F)` and `(Im F, -Re F)`, corresponding to
`F dbar z = (u dx + v dy) + i (v dx - u dy)`. -/
theorem mul_conj_deriv_eq_circulationFun (F : ℂ → ℂ) (γ : ℝ → ℂ) (t : ℝ) :
    F (γ t) * conj (deriv γ t) =
      (Green.circulationFun (fun z ↦ (F z).re) (fun z ↦ (F z).im) γ t : ℂ) +
        I * (Green.circulationFun (fun z ↦ (F z).im) (fun z ↦ -(F z).re) γ t : ℂ) := by
  apply Complex.ext <;> simp [Green.circulationFun]; ring

namespace Contour.Cycle

/-- For `F` continuous on the trace of `C`, the real part of `C.integral F` equals the
coefficient-weighted sum of the real circulations of `(Re F, -Im F)` over the supported
generators. -/
theorem re_integral_eq_sum_circulationFun (C : Cycle) {F : ℂ → ℂ} (hF : ContinuousOn F C.trace) :
    (C.integral F).re =
      ∑ γ ∈ FreeAddCommGroup.support C, (FreeAddCommGroup.coeff γ C : ℝ) *
        ∫ t in γ.a..γ.b, Green.circulationFun (fun z ↦ (F z).re) (fun z ↦ -(F z).im) γ t := by
  rw [integral_eq_sum_support, Complex.re_sum]
  refine Finset.sum_congr rfl fun γ hγ ↦ ?_
  rw [← Complex.reCLM_apply, map_zsmul, zsmul_eq_mul,
    ← Complex.reCLM.intervalIntegral_comp_comm (C.intervalIntegrable_of_mem_support hF hγ)]
  exact congrArg _ (intervalIntegral.integral_congr fun t _ ↦
    re_deriv_mul_eq_circulationFun F γ t)

/-- For `F` continuous on the trace of `C`, the imaginary part of `C.integral F` equals the
coefficient-weighted sum of the real circulations of `(Im F, Re F)` over the supported
generators. -/
theorem im_integral_eq_sum_circulationFun (C : Cycle) {F : ℂ → ℂ} (hF : ContinuousOn F C.trace) :
    (C.integral F).im =
      ∑ γ ∈ FreeAddCommGroup.support C, (FreeAddCommGroup.coeff γ C : ℝ) *
        ∫ t in γ.a..γ.b, Green.circulationFun (fun z ↦ (F z).im) (fun z ↦ (F z).re) γ t := by
  rw [integral_eq_sum_support, Complex.im_sum]
  refine Finset.sum_congr rfl fun γ hγ ↦ ?_
  rw [← Complex.imCLM_apply, map_zsmul, zsmul_eq_mul,
    ← Complex.imCLM.intervalIntegral_comp_comm (C.intervalIntegrable_of_mem_support hF hγ)]
  exact congrArg _ (intervalIntegral.integral_congr fun t _ ↦
    im_deriv_mul_eq_circulationFun F γ t)

end Contour.Cycle

/-! ### Planar curls of the `dz` and `dbar z` coordinate pairs -/

section CurlWirtinger

/-- For real-differentiable `F = u + i v`, the curl of `(u, -v)` is `-2 Im (\bar∂ F)`. -/
theorem curl_re_neg_im_eq_neg_two_mul_im_conjWirtingerDeriv {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℝ F z) :
    Green.curl (fun w ↦ (F w).re) (fun w ↦ -(F w).im) z =
      -2 * (conjWirtingerDeriv F z 1).im := by
  rw [Green.curl, fderiv_fun_neg]
  simp_rw [← Complex.reCLM_apply, ← Complex.imCLM_apply]
  rw [fderiv_fun_comp z Complex.imCLM.differentiableAt hF,
    fderiv_fun_comp z Complex.reCLM.differentiableAt hF,
    Complex.imCLM.fderiv, Complex.reCLM.fderiv, conjWirtingerDeriv_apply]
  simp
  ring

/-- For real-differentiable `F = u + i v`, the curl of `(v, u)` is `2 Re (\bar∂ F)`. -/
theorem curl_im_re_eq_two_mul_re_conjWirtingerDeriv {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℝ F z) :
    Green.curl (fun w ↦ (F w).im) (fun w ↦ (F w).re) z =
      2 * (conjWirtingerDeriv F z 1).re := by
  rw [Green.curl]
  simp_rw [← Complex.reCLM_apply, ← Complex.imCLM_apply]
  rw [fderiv_fun_comp z Complex.reCLM.differentiableAt hF,
    fderiv_fun_comp z Complex.imCLM.differentiableAt hF,
    Complex.reCLM.fderiv, Complex.imCLM.fderiv, conjWirtingerDeriv_apply]
  simp
  ring

end CurlWirtinger

/-! ### Complex Green–Stokes formulas on contour cycles -/

namespace Contour.Cycle

/-- For `C` in an open set `U` and null-homologous in `U`, `z ↦ C.windingWeight z • \bar∂ F(z)` is
integrable on `U` whenever `F` is real `C¹` on `U`. -/
theorem integrableOn_windingWeight_smul_conjWirtingerDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (C : Cycle) {U : Set ℂ} {F : ℂ → E} (hU : IsOpen U) (htrace : C.IsIn U)
    (hnull : C.IsNullHomologous U) (hF : ContDiffOn ℝ 1 F U) :
    IntegrableOn (fun z ↦ C.windingWeight z • conjWirtingerDeriv F z 1) U :=
  C.integrableOn_windingWeight_smul htrace hnull
    (hF.conjWirtingerDeriv_apply_of_isOpen hU (m := 0) (by simp) 1).continuousOn

/-- For `C` in an open set `U` and null-homologous in `U`, `z ↦ C.windingWeight z • ∂ F(z)` is
integrable on `U` whenever `F` is real `C¹` on `U`. -/
theorem integrableOn_windingWeight_smul_wirtingerDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (C : Cycle) {U : Set ℂ} {F : ℂ → E} (hU : IsOpen U) (htrace : C.IsIn U)
    (hnull : C.IsNullHomologous U) (hF : ContDiffOn ℝ 1 F U) :
    IntegrableOn (fun z ↦ C.windingWeight z • wirtingerDeriv F z 1) U :=
  C.integrableOn_windingWeight_smul htrace hnull
    (hF.wirtingerDeriv_apply_of_isOpen hU (m := 0) (by simp) 1).continuousOn

private theorem setIntegral_windingWeight_mul_curl_eq (C : Cycle) {U : Set ℂ} {P Q : ℂ → ℝ}
    {g : ℂ → ℂ} (hU : IsOpen U) (c : ℝ) (L : ℂ →L[ℝ] ℝ)
    (hint : IntegrableOn (fun z ↦ (C.windingWeight z : ℂ) * g z) U)
    (hcurl : ∀ z ∈ U, Green.curl P Q z = c * L (g z)) :
    (∫ z in U, C.windingWeight z * Green.curl P Q z) =
      c * L (∫ z in U, (C.windingWeight z : ℂ) * g z) := by
  calc
    (∫ z in U, C.windingWeight z * Green.curl P Q z)
        = ∫ z in U, c * L ((C.windingWeight z : ℂ) * g z) :=
          setIntegral_congr_fun hU.measurableSet fun z hz ↦ by
            rw [hcurl z hz, ← real_smul, map_smul, smul_eq_mul]; ring
    _ = c * L (∫ z in U, (C.windingWeight z : ℂ) * g z) := by
          rw [integral_const_mul, L.integral_comp_comm hint]

/-- **Scalar complex Green formula on a contour cycle.** For `F : ℂ → ℂ` real `C¹` on an open set
`U` and a cycle `C` in `U` that is null-homologous in `U`,
`C.integral F = (2 * I) * ∫ z in U, C.windingWeight z * conjWirtingerDeriv F z 1`. -/
theorem integral_eq_two_mul_I_mul_integral_windingWeight_conjWirtingerDeriv (C : Cycle)
    {U : Set ℂ} {F : ℂ → ℂ} (hU : IsOpen U) (htrace : C.IsIn U) (hnull : C.IsNullHomologous U)
    (hF : ContDiffOn ℝ 1 F U) :
    C.integral F =
      (2 * I) * ∫ z in U, (C.windingWeight z : ℂ) * conjWirtingerDeriv F z 1 := by
  have hu : ContDiffOn ℝ 1 (fun z ↦ (F z).re) U := Complex.reCLM.contDiff.comp_contDiffOn hF
  have hv : ContDiffOn ℝ 1 (fun z ↦ (F z).im) U := Complex.imCLM.contDiff.comp_contDiffOn hF
  have hFtr : ContinuousOn F C.trace := hF.continuousOn.mono (C.isIn_iff.mp htrace)
  have hint : IntegrableOn (fun z ↦ (C.windingWeight z : ℂ) * conjWirtingerDeriv F z 1) U := by
    simpa only [real_smul] using
      C.integrableOn_windingWeight_smul_conjWirtingerDeriv hU htrace hnull hF
  have hre : (C.integral F).re =
      -2 * (∫ z in U, (C.windingWeight z : ℂ) * conjWirtingerDeriv F z 1).im := by
    rw [C.re_integral_eq_sum_circulationFun hFtr, (C.green_winding hU htrace hu hv.neg hnull).2.2]
    exact setIntegral_windingWeight_mul_curl_eq C hU (-2) Complex.imCLM hint fun z hz ↦
      curl_re_neg_im_eq_neg_two_mul_im_conjWirtingerDeriv
        ((hF.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)
  have him : (C.integral F).im =
      2 * (∫ z in U, (C.windingWeight z : ℂ) * conjWirtingerDeriv F z 1).re := by
    rw [C.im_integral_eq_sum_circulationFun hFtr, (C.green_winding hU htrace hv hu hnull).2.2]
    exact setIntegral_windingWeight_mul_curl_eq C hU 2 Complex.reCLM hint fun z hz ↦
      curl_im_re_eq_two_mul_re_conjWirtingerDeriv
        ((hF.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)
  apply Complex.ext <;> simp [hre, him]

/-- **Complex Green formula on a contour cycle (vector-valued).** For `F : ℂ → E` real `C¹` on an
open set `U` with values in any complex normed space `E`, and any cycle `C` in `U` that is
null-homologous in `U`,
`C.integral F = (2 * I) • ∫ z in U, C.windingWeight z • conjWirtingerDeriv F z 1`. -/
theorem integral_eq_two_mul_I_smul_integral_windingWeight_conjWirtingerDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (C : Cycle) {U : Set ℂ} {F : ℂ → E}
    (hU : IsOpen U) (htrace : C.IsIn U) (hnull : C.IsNullHomologous U)
    (hF : ContDiffOn ℝ 1 F U) :
    C.integral F =
      (2 * I : ℂ) • ∫ z in U, C.windingWeight z • conjWirtingerDeriv F z 1 := by
  by_cases hE : CompleteSpace E
  · rw [← sub_eq_zero]
    refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ) fun ℓ ↦ ?_
    have hFtr : ContinuousOn F C.trace := hF.continuousOn.mono (C.isIn_iff.mp htrace)
    have hℓF : ContDiffOn ℝ 1 (fun z ↦ ℓ (F z)) U :=
      (ℓ.restrictScalars ℝ).contDiff.comp_contDiffOn hF
    rw [map_sub, ← C.integral_comp_comm (fun _ ↦ C.intervalIntegrable_of_mem_support hFtr) ℓ,
      map_smul, ← ℓ.integral_comp_comm
        (C.integrableOn_windingWeight_smul_conjWirtingerDeriv hU htrace hnull hF),
      smul_eq_mul, sub_eq_zero,
      C.integral_eq_two_mul_I_mul_integral_windingWeight_conjWirtingerDeriv hU htrace hnull hℓF]
    refine congrArg _ (setIntegral_congr_fun hU.measurableSet fun z hz ↦ ?_)
    have hdiff : DifferentiableAt ℝ F z :=
      (hF.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero
    have hcomp : conjWirtingerDeriv (fun w ↦ ℓ (F w)) z 1 = ℓ (conjWirtingerDeriv F z 1) := by
      rw [← Function.comp_def, conjWirtingerDeriv_comp ℓ.differentiableAt hdiff, ℓ.fderiv,
        ContinuousLinearMap.comp_apply]
    rw [hcomp, ← real_smul]
    exact ((ℓ.restrictScalars ℝ).map_smul _ _).symm
  · rw [integral_eq_sum_support, Finset.sum_eq_zero fun _ _ ↦ by
        simp [intervalIntegral, integral_of_not_completeSpace hE],
      integral_of_not_completeSpace hE, smul_zero]

private theorem conj_integral_conj_eq_neg_two_mul_I_mul_integral_windingWeight_wirtingerDeriv
    (C : Cycle) {U : Set ℂ} {F : ℂ → ℂ} (hU : IsOpen U) (htrace : C.IsIn U)
    (hnull : C.IsNullHomologous U) (hF : ContDiffOn ℝ 1 F U) :
    conj (C.integral (fun z ↦ conj (F z))) =
      (-2 * I) * ∫ z in U, (C.windingWeight z : ℂ) * wirtingerDeriv F z 1 := by
  have hFc : ContDiffOn ℝ 1 (fun z ↦ conj (F z)) U :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn hF
  have hdz := congrArg conj
    (C.integral_eq_two_mul_I_mul_integral_windingWeight_conjWirtingerDeriv hU htrace hnull hFc)
  rw [map_mul, map_mul, map_ofNat, conj_I, ← integral_conj] at hdz
  have htwo : (2 : ℂ) * -I = -2 * I := by ring
  rw [htwo] at hdz
  refine hdz.trans (congrArg ((-2 * I) * ·) (setIntegral_congr_fun hU.measurableSet fun z _ ↦ ?_))
  rw [map_mul, Complex.conj_ofReal, conjWirtingerDeriv_conj_comp_apply, starRingEnd_self_apply]

/-- **Complex circulation Stokes formula for `F dbar z` on a contour cycle.** For `F = u + i v`
real `C¹` on an open set `U` and a cycle `C` in `U` that is null-homologous in `U`, the complex
combination `(∮_C u dx + v dy) + i (∮_C v dx - u dy)` of the two real `Cycle.green_winding`
circulations equals `(-2 * I) * ∫ z in U, C.windingWeight z * wirtingerDeriv F z 1`. -/
theorem circulation_dzBar_eq_neg_two_mul_I_mul_integral_windingWeight_wirtingerDeriv (C : Cycle)
    {U : Set ℂ} {F : ℂ → ℂ} (hU : IsOpen U) (htrace : C.IsIn U) (hnull : C.IsNullHomologous U)
    (hF : ContDiffOn ℝ 1 F U) :
    ((∑ γ ∈ FreeAddCommGroup.support C, (FreeAddCommGroup.coeff γ C : ℝ) *
        ∫ t in γ.a..γ.b, Green.circulationFun (fun z ↦ (F z).re) (fun z ↦ (F z).im) γ t : ℝ) : ℂ) +
      I * ((∑ γ ∈ FreeAddCommGroup.support C, (FreeAddCommGroup.coeff γ C : ℝ) *
        ∫ t in γ.a..γ.b,
          Green.circulationFun (fun z ↦ (F z).im) (fun z ↦ -(F z).re) γ t : ℝ) : ℂ) =
      (-2 * I) * ∫ z in U, (C.windingWeight z : ℂ) * wirtingerDeriv F z 1 := by
  have hFtr : ContinuousOn (fun z ↦ conj (F z)) C.trace :=
    Complex.continuous_conj.comp_continuousOn (hF.continuousOn.mono (C.isIn_iff.mp htrace))
  have hre : (C.integral (fun z ↦ conj (F z))).re =
      ∑ γ ∈ FreeAddCommGroup.support C, (FreeAddCommGroup.coeff γ C : ℝ) *
        ∫ t in γ.a..γ.b, Green.circulationFun (fun z ↦ (F z).re) (fun z ↦ (F z).im) γ t := by
    simpa [Green.circulationFun] using C.re_integral_eq_sum_circulationFun hFtr
  have him : -(C.integral (fun z ↦ conj (F z))).im =
      ∑ γ ∈ FreeAddCommGroup.support C, (FreeAddCommGroup.coeff γ C : ℝ) *
        ∫ t in γ.a..γ.b, Green.circulationFun (fun z ↦ (F z).im) (fun z ↦ -(F z).re) γ t := by
    rw [C.im_integral_eq_sum_circulationFun hFtr, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun γ _ ↦ ?_
    rw [← mul_neg, ← intervalIntegral.integral_neg]
    refine congrArg _ (intervalIntegral.integral_congr fun t _ ↦ ?_)
    simp [Green.circulationFun]; ring
  rw [← hre, ← him, ← conj_integral_conj_eq_neg_two_mul_I_mul_integral_windingWeight_wirtingerDeriv
    C hU htrace hnull hF]
  apply Complex.ext <;> simp

end Contour.Cycle

private theorem intervalIntegral_circulationFun_circleCurve (c : ℂ) (R : ℝ) (P Q : ℂ → ℝ) :
    (∫ t in (Contour.circleCurve c R).a..(Contour.circleCurve c R).b,
        Green.circulationFun P Q (Contour.circleCurve c R) t) =
      ∫ θ in 0..2 * π, Green.circulationFun P Q (circleMap c R) θ := by
  set γf : ℝ → ℂ := ⇑(Contour.circleCurve c R)
  rw [Contour.circleCurve_a, Contour.circleCurve_b]
  have heq : EqOn γf (circleMap c R) (uIoo 0 (2 * π)) :=
    fun _ ht ↦ Contour.circleCurve_apply (uIoo_subset_uIcc_self ht)
  exact intervalIntegral.integral_congr_uIoo fun θ hθ ↦ by
    simp only [Green.circulationFun, heq hθ, heq.deriv isOpen_Ioo hθ]

private theorem isIn_and_isNullHomologous_circleCycle {c : ℂ} {R : ℝ} {U : Set ℂ} (hR : 0 ≤ R)
    (hball : closedBall c R ⊆ U) :
    (Contour.circleCycle c R).IsIn U ∧ (Contour.circleCycle c R).IsNullHomologous U := by
  refine ⟨?_, ?_⟩
  · rw [Contour.Cycle.isIn_iff, Contour.Cycle.trace_circleCycle, abs_of_nonneg hR]
    exact sphere_subset_closedBall.trans hball
  · rw [Contour.Cycle.isNullHomologous_iff]
    intro z hzU
    exact Contour.Cycle.windingNumber_circleCycle_eq_zero_of_lt_dist hR
      (not_le.mp fun hle ↦ hzU (hball (mem_closedBall.mpr hle)))

private theorem setIntegral_windingWeight_circleCycle_eq_ball {c : ℂ} {R : ℝ} {U : Set ℂ}
    (hR : 0 ≤ R) (hball : closedBall c R ⊆ U) (g : ℂ → ℂ) :
    (∫ z in U, ((Contour.circleCycle c R).windingWeight z : ℂ) * g z) =
      ∫ z in ball c R, g z := by
  rw [Contour.Cycle.windingWeight_circleCycle c hR]
  have hfun : (fun z ↦ (((ball c R).indicator (1 : ℂ → ℝ) z : ℝ) : ℂ) * g z) =
      (ball c R).indicator g := by
    ext z; by_cases hz : z ∈ ball c R <;> simp [hz]
  rw [hfun, setIntegral_indicator measurableSet_ball,
    inter_eq_right.mpr (ball_subset_closedBall.trans hball)]

/-- **Circle Stokes formula for `F dbar z`.** For `R ≥ 0` and `F = u + i v` real `C¹` on an open
set `U` containing `closedBall c R`, the real/imaginary circulation combination
`∮_{|z - c| = R} F dbar z` along `circleMap c R` equals
`(-2 * I) * ∫ z in ball c R, wirtingerDeriv F z 1`. -/
theorem circulation_dzBar_circleMap_eq_neg_two_mul_I_mul_integral_ball_wirtingerDeriv
    {c : ℂ} {R : ℝ} {U : Set ℂ} {F : ℂ → ℂ} (hR : 0 ≤ R) (hU : IsOpen U)
    (hball : closedBall c R ⊆ U) (hF : ContDiffOn ℝ 1 F U) :
    ((∫ θ in 0..2 * π,
        Green.circulationFun (fun z ↦ (F z).re) (fun z ↦ (F z).im) (circleMap c R) θ : ℝ) : ℂ) +
      I * ((∫ θ in 0..2 * π,
        Green.circulationFun (fun z ↦ (F z).im) (fun z ↦ -(F z).re) (circleMap c R) θ : ℝ) : ℂ) =
      (-2 * I) * ∫ z in ball c R, wirtingerDeriv F z 1 := by
  obtain ⟨htr, hnull⟩ := isIn_and_isNullHomologous_circleCycle hR hball
  have hmain := (Contour.circleCycle c R)
    |>.circulation_dzBar_eq_neg_two_mul_I_mul_integral_windingWeight_wirtingerDeriv
      hU htr hnull hF
  rw [setIntegral_windingWeight_circleCycle_eq_ball hR hball] at hmain
  simpa only [Contour.circleCycle_def, FreeAddCommGroup.support_of, Finset.sum_singleton,
    FreeAddCommGroup.coeff_of_self, Int.cast_one, one_mul,
    intervalIntegral_circulationFun_circleCurve] using hmain

/-- **Complex circle Stokes formula for `F dbar z`.** For `R ≥ 0` and `F` real `C¹` on an open
neighborhood `U` of `closedBall c R`,
`∫ θ in 0..2 * π, F (circleMap c R θ) * conj (deriv (circleMap c R) θ) =
  (-2 * I) * ∫ z in ball c R, wirtingerDeriv F z 1`. -/
theorem integral_mul_conj_deriv_circleMap_eq_neg_two_mul_I_mul_integral_ball_wirtingerDeriv
    {c : ℂ} {R : ℝ} {U : Set ℂ} {F : ℂ → ℂ} (hR : 0 ≤ R) (hU : IsOpen U)
    (hball : closedBall c R ⊆ U) (hF : ContDiffOn ℝ 1 F U) :
    (∫ θ in 0..2 * π, F (circleMap c R θ) * conj (deriv (circleMap c R) θ)) =
      (-2 * I) * ∫ z in ball c R, wirtingerDeriv F z 1 := by
  obtain ⟨htr, hnull⟩ := isIn_and_isNullHomologous_circleCycle hR hball
  have hmain := (Contour.circleCycle c R)
    |>.conj_integral_conj_eq_neg_two_mul_I_mul_integral_windingWeight_wirtingerDeriv
      hU htr hnull hF
  rw [setIntegral_windingWeight_circleCycle_eq_ball hR hball,
    Contour.Cycle.integral_circleCycle, circleIntegral] at hmain
  have hFc : Continuous fun θ : ℝ ↦ deriv (circleMap c R) θ * conj (F (circleMap c R θ)) := by
    have hderiv : Continuous (deriv (circleMap c R)) :=
      (funext (deriv_circleMap c R)).symm ▸ (continuous_circleMap 0 R).mul continuous_const
    exact hderiv.mul (Complex.continuous_conj.comp (hF.continuousOn.comp_continuous
      (continuous_circleMap c R) fun θ ↦
        hball (sphere_subset_closedBall (circleMap_mem_sphere c hR θ))))
  have hconj : conj (∫ θ in 0..2 * π, deriv (circleMap c R) θ * conj (F (circleMap c R θ))) =
      ∫ θ in 0..2 * π, F (circleMap c R θ) * conj (deriv (circleMap c R) θ) := by
    have hcomm := (Complex.conjCLE : ℂ →L[ℝ] ℂ).intervalIntegral_comp_comm
      (μ := volume) (hFc.intervalIntegrable 0 (2 * π))
    simpa [Complex.conjCLE_apply, mul_comm] using hcomm.symm
  simpa only [smul_eq_mul, hconj] using hmain

section MonomialMomentHelpers

private theorem wirtingerDeriv_monomial_div (m n : ℕ) (z : ℂ) :
    wirtingerDeriv (fun w : ℂ ↦ ((m : ℂ) + 1)⁻¹ * (w ^ (m + 1) * conj w ^ n)) z 1 =
      z ^ m * conj z ^ n := by
  have hm1 : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hconst : (fun w : ℂ ↦ ((m : ℂ) + 1)⁻¹ * (w ^ (m + 1) * conj w ^ n)) =
      ((m : ℂ) + 1)⁻¹ • fun w : ℂ ↦ (w ^ (m + 1)) • conj (w ^ n) := by
    ext w; simp [smul_eq_mul]
  have hg : DifferentiableAt ℂ (fun w : ℂ ↦ w ^ (m + 1)) z :=
    (hasDerivAt_pow (m + 1) z).differentiableAt
  have hgn : DifferentiableAt ℂ (fun w : ℂ ↦ w ^ n) z := (hasDerivAt_pow n z).differentiableAt
  have hh : DifferentiableAt ℝ (fun w : ℂ ↦ conj (w ^ n)) z :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp z (hgn.restrictScalars ℝ)
  rw [hconst, wirtingerDeriv_const_smul, smul_apply,
    wirtingerDeriv_smul_apply (hg.restrictScalars ℝ) hh 1,
    hgn.wirtingerDeriv_conj_comp_eq_zero]
  simp [(hasDerivAt_pow (m + 1) z).hasFDerivAt.fderiv]
  field_simp [hm1]

private theorem integral_unitCircle_monomial_conj_deriv (m n : ℕ) :
    (∫ θ in 0..2 * π,
        (((m : ℂ) + 1)⁻¹ * (circleMap 0 1 θ ^ (m + 1) * conj (circleMap 0 1 θ) ^ n)) *
          conj (deriv (circleMap 0 1) θ)) =
      -((m : ℂ) + 1)⁻¹ * ∮ z in C(0, 1), (z - 0) ^ ((m : ℤ) - n - 1) := by
  rw [circleIntegral, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ ↦ ?_
  set w : ℂ := circleMap 0 1 θ
  have hw_norm : ‖w‖ = 1 := by simp [w]
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw_norm
  have hpow : w ^ (m + 1) * w⁻¹ ^ n * (w⁻¹ * -I) = -(w * I * w ^ ((m : ℤ) - n - 1)) := by
    calc
      w ^ (m + 1) * w⁻¹ ^ n * (w⁻¹ * -I)
          = -I * (w ^ ((m + 1 : ℕ) : ℤ) * w ^ (-(n : ℤ)) * w ^ (-1 : ℤ)) := by
            rw [zpow_natCast, zpow_neg, zpow_natCast, inv_pow, zpow_neg_one]; ring
      _ = -I * (w * w ^ ((m : ℤ) - n - 1)) := by
            rw [← zpow_add₀ hw0, ← zpow_add₀ hw0, ← zpow_one_add₀ hw0]; congr 2; push_cast; ring
      _ = -(w * I * w ^ ((m : ℤ) - n - 1)) := by ring
  have hdw : deriv (circleMap 0 1) θ = w * I := by simp [deriv_circleMap, w]
  simp only [hdw, map_mul, conj_I, (Complex.inv_eq_conj hw_norm).symm, sub_zero, smul_eq_mul]
  calc
    ((m : ℂ) + 1)⁻¹ * (w ^ (m + 1) * w⁻¹ ^ n) * (w⁻¹ * -I)
        = ((m : ℂ) + 1)⁻¹ * (w ^ (m + 1) * w⁻¹ ^ n * (w⁻¹ * -I)) := by ring
    _ = -((m : ℂ) + 1)⁻¹ * (w * I * w ^ ((m : ℤ) - n - 1)) := by rw [hpow]; ring

private theorem integral_unitBall_pow_mul_conj_pow_stokes (m n : ℕ) :
    (∫ z in ball (0 : ℂ) 1, z ^ m * conj z ^ n) =
      if m = n then (Real.pi : ℂ) / ((m : ℂ) + 1) else 0 := by
  have hm1 : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  let F : ℂ → ℂ := fun z ↦ ((m : ℂ) + 1)⁻¹ * (z ^ (m + 1) * conj z ^ n)
  have hF : ContDiff ℝ 1 F :=
    contDiff_const.mul ((contDiff_id.pow (m + 1)).mul (Complex.conjCLE.contDiff.pow n))
  have hstokes :=
    integral_mul_conj_deriv_circleMap_eq_neg_two_mul_I_mul_integral_ball_wirtingerDeriv (c := 0)
      zero_le_one isOpen_univ (subset_univ _) hF.contDiffOn
  simp_rw [F, wirtingerDeriv_monomial_div, integral_unitCircle_monomial_conj_deriv] at hstokes
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num) I_ne_zero : (-2 * I : ℂ) ≠ 0)
  rw [← hstokes]
  split_ifs with hmn
  · subst hmn
    rw [sub_self, zero_sub]
    simp_rw [zpow_neg_one]
    rw [circleIntegral.integral_sub_center_inv 0 one_ne_zero]
    field_simp [hm1]
  · rw [circleIntegral.integral_sub_zpow_of_ne (by omega : ((m : ℤ) - n - 1) ≠ -1),
      mul_zero, mul_zero]

-- Cross-check: the circle Stokes evaluation of `∫ z in ball 0 1, z ^ m * conj z ^ n` agrees
-- with `TauCeti.Probability.integral_pow_mul_conj_pow_circularLaw`.
example (m n : ℕ) :
    (∫ z in ball (0 : ℂ) 1, z ^ m * conj z ^ n) =
      (Real.pi : ℂ) * (if m = n then ((1 / (m + 1) : ℝ) : ℂ) else 0) := by
  rw [← TauCeti.Probability.integral_pow_mul_conj_pow_circularLaw,
    TauCeti.Probability.circularLaw_eq_smul_restrict, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr Real.pi_pos.le), Complex.real_smul,
    Complex.ofReal_inv, integral_unitBall_pow_mul_conj_pow_stokes]
  split_ifs <;> simp [Real.pi_ne_zero]

end MonomialMomentHelpers

end TauCeti

end

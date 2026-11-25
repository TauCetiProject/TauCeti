/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.Green.Cycle
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.Dual

/-!
# Complex Green–Stokes formulas on contour cycles

For a contour cycle `C` lying in an open set `U` (`C.IsIn U`) and null-homologous in `U`
(`C.IsNullHomologous U`), and a scalar map `F : ℂ → ℂ` that is real `C¹` on `U`
(`ContDiffOn ℝ 1 F U`), applying `TauCeti.Contour.Cycle.green_winding` to the real coordinate
pairs `(Re F, -Im F)` and `(Im F, Re F)` yields the scalar complex Green formula
`C.integral F = (2 * I) * ∫ z in U, (C.windingWeight z : ℂ) * conjWirtingerDeriv F z 1`.
For maps `F : ℂ → E` into a complex Banach space `E` (`CompleteSpace E`), pairing with
continuous `ℂ`-linear functionals (`SeparatingDual`) extends this to
`C.integral F = (2 * I : ℂ) • ∫ z in U, C.windingWeight z • conjWirtingerDeriv F z 1`; when `E`
is incomplete, the same identity holds trivially because both Bochner integrals vanish by
convention (`MeasureTheory.integral_of_not_completeSpace`).

Applying the scalar `dz` formula to `conj ∘ F` and conjugating yields the dual `F dbar z`
circulation formula on contour cycles (under the same `U`, `C.IsIn U`, `C.IsNullHomologous U`, and
`ContDiffOn ℝ 1 F U` hypotheses).

## Main results

* `TauCeti.re_deriv_mul_eq_circulationFun`, `im_deriv_mul_eq_circulationFun`,
  `TauCeti.Contour.Cycle.re_integral_eq_sum_circulationFun`, `im_integral_eq_sum_circulationFun`
* `TauCeti.curl_re_neg_im_eq_neg_two_mul_im_conjWirtingerDeriv`,
  `curl_im_re_eq_two_mul_re_conjWirtingerDeriv`
* `TauCeti.Contour.Cycle.integral_eq_two_mul_I_mul_integral_windingWeight_conjWirtingerDeriv`,
  `TauCeti.Contour.Cycle.integral_eq_two_mul_I_smul_integral_windingWeight_conjWirtingerDeriv`
* `Contour.Cycle.circulation_dzBar_eq_neg_two_mul_I_mul_integral_windingWeight_wirtingerDeriv`

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
  apply Complex.ext <;>
    simp only [Green.circulationFun, add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im,
      I_re, I_im] <;> ring

/-- Along any curve `γ`, `F (γ t) * conj (γ' t)` decomposes into the planar circulation integrands
of `(Re F, Im F)` and `(Im F, -Re F)`, corresponding to
`F dbar z = (u dx + v dy) + i (v dx - u dy)`. -/
theorem mul_conj_deriv_eq_circulationFun (F : ℂ → ℂ) (γ : ℝ → ℂ) (t : ℝ) :
    F (γ t) * conj (deriv γ t) =
      (Green.circulationFun (fun z ↦ (F z).re) (fun z ↦ (F z).im) γ t : ℂ) +
        I * (Green.circulationFun (fun z ↦ (F z).im) (fun z ↦ -(F z).re) γ t : ℂ) := by
  apply Complex.ext <;>
    simp only [Green.circulationFun, add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im,
      conj_re, conj_im, I_re, I_im] <;> ring

namespace Contour.Cycle

/-- When `t ↦ deriv γ t • F (γ t)` is interval-integrable along every curve `γ` in the support
of `C`, the real part of `C.integral F` equals the coefficient-weighted sum of the real
circulations of `(Re F, -Im F)` over the supported generators. -/
theorem re_integral_eq_sum_circulationFun (C : Cycle) {F : ℂ → ℂ}
    (hF : ∀ γ ∈ FreeAddCommGroup.support C,
      IntervalIntegrable (fun t ↦ deriv γ t • F (γ t)) volume γ.a γ.b) :
    (C.integral F).re =
      ∑ γ ∈ FreeAddCommGroup.support C, (FreeAddCommGroup.coeff γ C : ℝ) *
        ∫ t in γ.a..γ.b, Green.circulationFun (fun z ↦ (F z).re) (fun z ↦ -(F z).im) γ t := by
  rw [integral_eq_sum_support, Complex.re_sum]
  refine Finset.sum_congr rfl fun γ hγ ↦ ?_
  rw [← Complex.reCLM_apply, map_zsmul, zsmul_eq_mul,
    ← Complex.reCLM.intervalIntegral_comp_comm (hF γ hγ)]
  exact congrArg _ (intervalIntegral.integral_congr fun t _ ↦
    re_deriv_mul_eq_circulationFun F γ t)

/-- When `t ↦ deriv γ t • F (γ t)` is interval-integrable along every curve `γ` in the support
of `C`, the imaginary part of `C.integral F` equals the coefficient-weighted sum of the real
circulations of `(Im F, Re F)` over the supported generators. -/
theorem im_integral_eq_sum_circulationFun (C : Cycle) {F : ℂ → ℂ}
    (hF : ∀ γ ∈ FreeAddCommGroup.support C,
      IntervalIntegrable (fun t ↦ deriv γ t • F (γ t)) volume γ.a γ.b) :
    (C.integral F).im =
      ∑ γ ∈ FreeAddCommGroup.support C, (FreeAddCommGroup.coeff γ C : ℝ) *
        ∫ t in γ.a..γ.b, Green.circulationFun (fun z ↦ (F z).im) (fun z ↦ (F z).re) γ t := by
  rw [integral_eq_sum_support, Complex.im_sum]
  refine Finset.sum_congr rfl fun γ hγ ↦ ?_
  rw [← Complex.imCLM_apply, map_zsmul, zsmul_eq_mul,
    ← Complex.imCLM.intervalIntegral_comp_comm (hF γ hγ)]
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
  simp only [neg_apply, ContinuousLinearMap.comp_apply, Complex.imCLM_apply,
    Complex.reCLM_apply, smul_eq_mul, add_im, mul_im, inv_im, re_ofNat, im_ofNat, neg_zero,
    zero_div, zero_mul, inv_re, normSq_ofNat, div_self_mul_self', add_zero, I_re, I_im, one_mul,
    mul_one]
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
  simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    smul_eq_mul, add_re, mul_re, inv_re, re_ofNat, normSq_ofNat, inv_im, im_ofNat, neg_zero,
    zero_div, zero_mul, sub_zero, I_re, I_im, one_mul, mul_one]
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
    rw [C.re_integral_eq_sum_circulationFun (fun _ ↦ C.intervalIntegrable_of_mem_support hFtr),
      (C.green_winding hU htrace hu hv.neg hnull).2.2]
    exact setIntegral_windingWeight_mul_curl_eq C hU (-2) Complex.imCLM hint fun z hz ↦
      curl_re_neg_im_eq_neg_two_mul_im_conjWirtingerDeriv
        ((hF.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)
  have him : (C.integral F).im =
      2 * (∫ z in U, (C.windingWeight z : ℂ) * conjWirtingerDeriv F z 1).re := by
    rw [C.im_integral_eq_sum_circulationFun (fun _ ↦ C.intervalIntegrable_of_mem_support hFtr),
      (C.green_winding hU htrace hv hu hnull).2.2]
    exact setIntegral_windingWeight_mul_curl_eq C hU 2 Complex.reCLM hint fun z hz ↦
      curl_im_re_eq_two_mul_re_conjWirtingerDeriv
        ((hF.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)
  apply Complex.ext <;> simp [hre, him]

/-- **Complex Green formula on a contour cycle (vector-valued).** For `F : ℂ → E` real `C¹` on an
open set `U` and a cycle `C` in `U` that is null-homologous in `U`,
`C.integral F = (2 * I) • ∫ z in U, C.windingWeight z • conjWirtingerDeriv F z 1`. When `E` is a
complex Banach space (`CompleteSpace E`), this extends the scalar identity by Hahn–Banach
duality (`SeparatingDual`); when `E` is incomplete, both Bochner integrals vanish by convention
(`MeasureTheory.integral_of_not_completeSpace`). -/
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
  · rw [integral_of_not_completeSpace hE, MeasureTheory.integral_of_not_completeSpace hE,
      smul_zero]

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
    simpa [Green.circulationFun] using C.re_integral_eq_sum_circulationFun
      (F := fun z ↦ conj (F z)) (fun _ hγ ↦ C.intervalIntegrable_of_mem_support hFtr hγ)
  have him : -(C.integral (fun z ↦ conj (F z))).im =
      ∑ γ ∈ FreeAddCommGroup.support C, (FreeAddCommGroup.coeff γ C : ℝ) *
        ∫ t in γ.a..γ.b, Green.circulationFun (fun z ↦ (F z).im) (fun z ↦ -(F z).re) γ t := by
    rw [C.im_integral_eq_sum_circulationFun
        (fun _ hγ ↦ C.intervalIntegrable_of_mem_support hFtr hγ), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun γ _ ↦ ?_
    rw [← mul_neg, ← intervalIntegral.integral_neg]
    refine congrArg _ (intervalIntegral.integral_congr fun t _ ↦ ?_)
    simp only [Green.circulationFun, conj_re, conj_im]; ring
  rw [← hre, ← him, ← conj_integral_conj_eq_neg_two_mul_I_mul_integral_windingWeight_wirtingerDeriv
    C hU htrace hnull hF]
  apply Complex.ext <;> simp

end Contour.Cycle

end TauCeti

end

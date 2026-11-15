/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
public import TauCeti.Analysis.Contour.Cycle.Circle
public import TauCeti.Analysis.Green.Cycle
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Complex Green–Stokes formulas on contour cycles

For a complex-valued function `F = u + i v` on an open plane set `U` and a contour cycle
`C : TauCeti.Contour.Cycle` whose trace lies in `U` and which is null-homologous in `U`, the
complex contour integral `C.integral F` splits into the two real cycle circulations of
`u dx - v dy` and `v dx + u dy`. Applying `TauCeti.Contour.Cycle.green_winding` to both pairs and
expressing their planar curls through the conjugate Wirtinger derivative gives the winding-weighted
complex Green formula

`C.integral F = (2 * I) • ∫ z in U, C.windingWeight z • conjWirtingerDeriv F z 1`,

which holds more generally for maps `F : ℂ → E` into any complex normed space `E`.

Dualizing to the real one-forms `u dx + v dy` and `v dx - u dy` representing `F dbar z` expresses
their complex circulation combination on `C` as
`(-2 * I) * ∫ z in U, C.windingWeight z * wirtingerDeriv F z 1`, and specializing to a circle
yields `∮_{|z - c| = R} F dbar z = -2 i ∫_{|z - c| < R} ∂_z F dA`.

## Main results

* `TauCeti.re_deriv_mul_eq_circulationFun`, `im_deriv_mul_eq_circulationFun`,
  `TauCeti.Contour.Cycle.re_integral_eq_sum_circulationFun`,
  `im_integral_eq_sum_circulationFun`: coordinate comparison between `Cycle.integral F` and the
  real circulations of `(Re F, -Im F)` and `(Im F, Re F)`.
* `TauCeti.curl_re_neg_im_eq_neg_two_mul_im_conjWirtingerDeriv`,
  `curl_im_re_eq_two_mul_re_conjWirtingerDeriv`,
  `curl_re_im_eq_two_mul_im_wirtingerDeriv`,
  `curl_im_neg_re_eq_neg_two_mul_re_wirtingerDeriv`: planar curls in terms of `\bar∂ F` and `∂ F`.
* `TauCeti.Contour.Cycle.tsupport_windingWeight_subset` and
  `integrableOn_windingWeight_smul`: compact support of `C.windingWeight` inside a null-homology
  domain `U`, and integrability against any continuous map on `U`.
* `TauCeti.Contour.Cycle.integral_eq_two_mul_I_smul_integral_windingWeight_conjWirtingerDeriv`:
  complex Green formula for `F dz` on a null-homologous contour cycle, valued in any complex normed
  space.
* `TauCeti.Contour.Cycle.circulation_dzBar_eq_neg_two_mul_I_mul_integral_windingWeight`,
  `TauCeti.circulation_dzBar_circleMap_eq_neg_two_mul_I_mul_integral_ball_wirtingerDeriv`, and
  `TauCeti.integral_mul_conj_deriv_circleMap_eq_neg_two_mul_I_mul_integral_ball_wirtingerDeriv`:
  real/imaginary and complex circle Stokes formulas for `F dbar z`.
* `TauCeti.integral_unitBall_pow_mul_conj_pow`: unit-disk monomial moment identity
  `∫_{|z| < 1} z^m (conj z)^n dA = π / (m + 1)` if `m = n` and `0` otherwise.

## References

* L. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979, Chapter 4, §5.
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
  simp only [Green.circulationFun, mul_re]
  ring

/-- Along any curve `γ`, the imaginary part of `γ' t * F (γ t)` is the planar circulation integrand
of `(Im F, Re F)`. -/
theorem im_deriv_mul_eq_circulationFun (F : ℂ → ℂ) (γ : ℝ → ℂ) (t : ℝ) :
    (deriv γ t * F (γ t)).im =
      Green.circulationFun (fun z ↦ (F z).im) (fun z ↦ (F z).re) γ t := by
  simp only [Green.circulationFun, mul_im]
  ring

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
  apply Complex.ext
  · simp [Green.circulationFun]
  · simp [Green.circulationFun]
    ring

namespace Contour.Cycle

/-- For `F` continuous on the trace of `C`, the real part of `C.integral F` equals the
coefficient-weighted sum of the real circulations of `(Re F, -Im F)` over the supported
generators. -/
theorem re_integral_eq_sum_circulationFun (C : Cycle) {F : ℂ → ℂ} (hF : ContinuousOn F C.trace) :
    (C.integral F).re =
      ∑ γ ∈ FreeAbelianGroup.support C, (FreeAbelianGroup.coeff γ C : ℝ) *
        ∫ t in γ.a..γ.b, Green.circulationFun (fun z ↦ (F z).re) (fun z ↦ -(F z).im) γ t := by
  rw [integral_eq_sum_support, Complex.re_sum]
  refine Finset.sum_congr rfl fun γ hγ ↦ ?_
  have hint := C.intervalIntegrable_of_mem_support hF hγ
  rw [← Complex.reCLM_apply, map_zsmul, zsmul_eq_mul,
    ← Complex.reCLM.intervalIntegral_comp_comm hint]
  simp only [Complex.reCLM_apply]
  congr 1
  exact intervalIntegral.integral_congr fun t _ ↦ re_deriv_mul_eq_circulationFun F γ t

/-- For `F` continuous on the trace of `C`, the imaginary part of `C.integral F` equals the
coefficient-weighted sum of the real circulations of `(Im F, Re F)` over the supported
generators. -/
theorem im_integral_eq_sum_circulationFun (C : Cycle) {F : ℂ → ℂ} (hF : ContinuousOn F C.trace) :
    (C.integral F).im =
      ∑ γ ∈ FreeAbelianGroup.support C, (FreeAbelianGroup.coeff γ C : ℝ) *
        ∫ t in γ.a..γ.b, Green.circulationFun (fun z ↦ (F z).im) (fun z ↦ (F z).re) γ t := by
  rw [integral_eq_sum_support, Complex.im_sum]
  refine Finset.sum_congr rfl fun γ hγ ↦ ?_
  have hint := C.intervalIntegrable_of_mem_support hF hγ
  rw [← Complex.imCLM_apply, map_zsmul, zsmul_eq_mul,
    ← Complex.imCLM.intervalIntegral_comp_comm hint]
  simp only [Complex.imCLM_apply]
  congr 1
  exact intervalIntegral.integral_congr fun t _ ↦ im_deriv_mul_eq_circulationFun F γ t

end Contour.Cycle

/-! ### Planar curls of the `dz` and `dbar z` coordinate pairs -/

section CurlWirtinger

private theorem fderiv_re_comp {F : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℝ F z) (v : ℂ) :
    fderiv ℝ (fun w ↦ (F w).re) z v = (fderiv ℝ F z v).re := by
  have hcomp : (fun w ↦ (F w).re) = Complex.reCLM ∘ F := rfl
  rw [hcomp, (Complex.reCLM.hasFDerivAt.comp z hF.hasFDerivAt).fderiv]
  rfl

private theorem fderiv_im_comp {F : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℝ F z) (v : ℂ) :
    fderiv ℝ (fun w ↦ (F w).im) z v = (fderiv ℝ F z v).im := by
  have hcomp : (fun w ↦ (F w).im) = Complex.imCLM ∘ F := rfl
  rw [hcomp, (Complex.imCLM.hasFDerivAt.comp z hF.hasFDerivAt).fderiv]
  rfl

private theorem fderiv_neg_re_comp {F : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℝ F z) (v : ℂ) :
    fderiv ℝ (fun w ↦ -(F w).re) z v = -(fderiv ℝ F z v).re := by
  have hneg : (fun w ↦ -(F w).re) = -(fun w ↦ (F w).re) := rfl
  rw [hneg, fderiv_neg, neg_apply, fderiv_re_comp hF]

private theorem fderiv_neg_im_comp {F : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℝ F z) (v : ℂ) :
    fderiv ℝ (fun w ↦ -(F w).im) z v = -(fderiv ℝ F z v).im := by
  have hneg : (fun w ↦ -(F w).im) = -(fun w ↦ (F w).im) := rfl
  rw [hneg, fderiv_neg, neg_apply, fderiv_im_comp hF]

/-- For real-differentiable `F = u + i v`, the curl of `(u, -v)` is `-2 Im (\bar∂ F)`. -/
theorem curl_re_neg_im_eq_neg_two_mul_im_conjWirtingerDeriv {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℝ F z) :
    Green.curl (fun w ↦ (F w).re) (fun w ↦ -(F w).im) z =
      -2 * (conjWirtingerDeriv F z 1).im := by
  rw [Green.curl, fderiv_neg_im_comp hF, fderiv_re_comp hF, conjWirtingerDeriv_apply]
  simp
  ring

/-- For real-differentiable `F = u + i v`, the curl of `(v, u)` is `2 Re (\bar∂ F)`. -/
theorem curl_im_re_eq_two_mul_re_conjWirtingerDeriv {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℝ F z) :
    Green.curl (fun w ↦ (F w).im) (fun w ↦ (F w).re) z =
      2 * (conjWirtingerDeriv F z 1).re := by
  rw [Green.curl, fderiv_re_comp hF, fderiv_im_comp hF, conjWirtingerDeriv_apply]
  simp
  ring

/-- For real-differentiable `F = u + i v`, the curl of `(u, v)` is `2 Im (∂ F)`. -/
theorem curl_re_im_eq_two_mul_im_wirtingerDeriv {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℝ F z) :
    Green.curl (fun w ↦ (F w).re) (fun w ↦ (F w).im) z =
      2 * (wirtingerDeriv F z 1).im := by
  rw [Green.curl, fderiv_im_comp hF, fderiv_re_comp hF, wirtingerDeriv_apply]
  simp

/-- For real-differentiable `F = u + i v`, the curl of `(v, -u)` is `-2 Re (∂ F)`. -/
theorem curl_im_neg_re_eq_neg_two_mul_re_wirtingerDeriv {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℝ F z) :
    Green.curl (fun w ↦ (F w).im) (fun w ↦ -(F w).re) z =
      -2 * (wirtingerDeriv F z 1).re := by
  rw [Green.curl, fderiv_neg_re_comp hF, fderiv_im_comp hF, wirtingerDeriv_apply]
  simp
  ring

end CurlWirtinger

/-! ### Support, integrability, and complex Green–Stokes on contour cycles -/

namespace Contour.Cycle

/-- If `C` lies in an open set `U` and is null-homologous in `U`, then the topological support of
`C.windingWeight` is a compact subset of `U`. -/
theorem tsupport_windingWeight_subset (C : Cycle) {U : Set ℂ} (htrace : C.IsIn U)
    (hnull : C.IsNullHomologous U) : tsupport C.windingWeight ⊆ U := by
  intro z hz
  by_contra hzU
  have htr : z ∉ C.trace := fun h ↦ hzU (C.isIn_iff.mp htrace h)
  have hopen_compl : IsOpen (C.trace)ᶜ := C.isCompact_trace.isClosed.isOpen_compl
  have hfiber : IsOpen ((fun w : {w : ℂ // w ∉ C.trace} ↦ C.windingNumber w) ⁻¹' {0}) :=
    C.isLocallyConstant_windingNumber {0}
  obtain ⟨V, hV_open, hV_eq⟩ := isOpen_induced_iff.mp hfiber
  have hz0 : C.windingNumber z = 0 := C.isNullHomologous_iff.mp hnull z hzU
  have hzV : z ∈ V ∩ (C.trace)ᶜ := by
    refine ⟨?_, htr⟩
    have hmem : (⟨z, htr⟩ : {w : ℂ // w ∉ C.trace}) ∈ Subtype.val ⁻¹' V := by
      rw [hV_eq]
      exact hz0
    exact hmem
  have hev : C.windingWeight =ᶠ[𝓝 z] 0 := by
    filter_upwards [(hV_open.inter hopen_compl).mem_nhds hzV] with w ⟨hwV, hwtr⟩
    have hw0 : C.windingNumber w = 0 := by
      have hmem : (⟨w, hwtr⟩ : {w : ℂ // w ∉ C.trace}) ∈ Subtype.val ⁻¹' V := hwV
      rw [hV_eq] at hmem
      exact hmem
    rw [C.windingWeight_eq_of_notMem hwtr, hw0, zero_re, Pi.zero_apply]
  exact (notMem_tsupport_iff_eventuallyEq.mpr hev) hz

/-- For `C` in an open set `U` and null-homologous in `U`, `C.windingWeight` is integrable on
`U`. -/
theorem integrableOn_windingWeight (C : Cycle) {U : Set ℂ} (hU : IsOpen U) (htrace : C.IsIn U)
    (hnull : C.IsNullHomologous U) : IntegrableOn C.windingWeight U := by
  have hgreen := (C.green_winding (P := Function.const ℂ 0) (Q := Complex.reCLM) hU htrace
    contDiffOn_const Complex.reCLM.contDiff.contDiffOn hnull).2.1
  refine hgreen.congr_fun (fun z _ ↦ ?_) hU.measurableSet
  dsimp only
  rw [Green.curl, Complex.reCLM.hasFDerivAt.fderiv, fderiv_const]
  simp

/-- If `C` lies in an open set `U` and is null-homologous in `U`, then `C.windingWeight • g` is
integrable on `U` for every map `g : ℂ → E` continuous on `U`. -/
theorem integrableOn_windingWeight_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Cycle) {U : Set ℂ} {g : ℂ → E} (hU : IsOpen U) (htrace : C.IsIn U)
    (hnull : C.IsNullHomologous U) (hg : ContinuousOn g U) :
    IntegrableOn (fun z ↦ C.windingWeight z • g z) U := by
  set K := tsupport C.windingWeight
  have hK : IsCompact K := C.hasCompactSupport_windingWeight
  have hKU : K ⊆ U := C.tsupport_windingWeight_subset htrace hnull
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hg.mono hKU)
  have hmeas : AEStronglyMeasurable (K.indicator g) (volume.restrict U) :=
    (hg.aestronglyMeasurable hU.measurableSet).indicator hK.measurableSet
  have hbdd : ∀ᵐ z ∂volume.restrict U, ‖K.indicator g z‖ ≤ max M 0 := by
    refine ae_of_all _ fun z ↦ ?_
    by_cases hz : z ∈ K
    · rw [indicator_of_mem hz]
      exact (hM z hz).trans (le_max_left _ _)
    · rw [indicator_of_notMem hz, norm_zero]
      exact le_max_right _ _
  have hint : IntegrableOn (fun z ↦ C.windingWeight z • K.indicator g z) U :=
    (C.integrableOn_windingWeight hU htrace hnull).smul_bdd (max M 0) hmeas hbdd
  refine hint.congr_fun (fun z _ ↦ ?_) hU.measurableSet
  by_cases hz : z ∈ K
  · simp [hz]
  · dsimp only
    rw [image_eq_zero_of_notMem_tsupport hz, zero_smul, zero_smul]

/-- For `C` in an open set `U` and null-homologous in `U`, `z ↦ C.windingWeight z • \bar∂ F(z)` is
integrable on `U` whenever `F` is real `C¹` on `U`. -/
theorem integrableOn_windingWeight_smul_conjWirtingerDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (C : Cycle) {U : Set ℂ} {F : ℂ → E} (hU : IsOpen U) (htrace : C.IsIn U)
    (hnull : C.IsNullHomologous U) (hF : ContDiffOn ℝ 1 F U) :
    IntegrableOn (fun z ↦ C.windingWeight z • conjWirtingerDeriv F z 1) U :=
  C.integrableOn_windingWeight_smul hU htrace hnull
    (hF.conjWirtingerDeriv_apply_of_isOpen hU (m := 0) (by simp) 1).continuousOn

/-- For `C` in an open set `U` and null-homologous in `U`, `z ↦ C.windingWeight z • ∂ F(z)` is
integrable on `U` whenever `F` is real `C¹` on `U`. -/
theorem integrableOn_windingWeight_smul_wirtingerDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (C : Cycle) {U : Set ℂ} {F : ℂ → E} (hU : IsOpen U) (htrace : C.IsIn U)
    (hnull : C.IsNullHomologous U) (hF : ContDiffOn ℝ 1 F U) :
    IntegrableOn (fun z ↦ C.windingWeight z • wirtingerDeriv F z 1) U :=
  C.integrableOn_windingWeight_smul hU htrace hnull
    (hF.wirtingerDeriv_apply_of_isOpen hU (m := 0) (by simp) 1).continuousOn

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
  have hgreen₁ := (C.green_winding hU htrace hu hv.neg hnull).2.2
  have hgreen₂ := (C.green_winding hU htrace hv hu hnull).2.2
  have hint : IntegrableOn (fun z ↦ (C.windingWeight z : ℂ) * conjWirtingerDeriv F z 1) U := by
    simpa only [real_smul] using
      C.integrableOn_windingWeight_smul_conjWirtingerDeriv hU htrace hnull hF
  have hre : (C.integral F).re =
      -2 * (∫ z in U, (C.windingWeight z : ℂ) * conjWirtingerDeriv F z 1).im := by
    rw [C.re_integral_eq_sum_circulationFun hFtr, hgreen₁]
    calc
      (∫ z in U, C.windingWeight z * Green.curl (fun w ↦ (F w).re) (fun w ↦ -(F w).im) z)
          = ∫ z in U, (-2) * Complex.imCLM ((C.windingWeight z : ℂ) * conjWirtingerDeriv F z 1) :=
            setIntegral_congr_fun hU.measurableSet fun z hz ↦ by
              rw [curl_re_neg_im_eq_neg_two_mul_im_conjWirtingerDeriv
                ((hF.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)]
              simp [mul_left_comm]
      _ = -2 * (∫ z in U, (C.windingWeight z : ℂ) * conjWirtingerDeriv F z 1).im := by
            rw [integral_const_mul, Complex.imCLM.integral_comp_comm hint]
            rfl
  have him : (C.integral F).im =
      2 * (∫ z in U, (C.windingWeight z : ℂ) * conjWirtingerDeriv F z 1).re := by
    rw [C.im_integral_eq_sum_circulationFun hFtr, hgreen₂]
    calc
      (∫ z in U, C.windingWeight z * Green.curl (fun w ↦ (F w).im) (fun w ↦ (F w).re) z)
          = ∫ z in U, 2 * Complex.reCLM ((C.windingWeight z : ℂ) * conjWirtingerDeriv F z 1) :=
            setIntegral_congr_fun hU.measurableSet fun z hz ↦ by
              rw [curl_im_re_eq_two_mul_re_conjWirtingerDeriv
                ((hF.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)]
              simp [mul_left_comm]
      _ = 2 * (∫ z in U, (C.windingWeight z : ℂ) * conjWirtingerDeriv F z 1).re := by
            rw [integral_const_mul, Complex.reCLM.integral_comp_comm hint]
            rfl
  apply Complex.ext
  · simp [hre]
  · simp [him]

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
    have hint_area := C.integrableOn_windingWeight_smul_conjWirtingerDeriv hU htrace hnull hF
    have hFtr : ContinuousOn F C.trace := hF.continuousOn.mono (C.isIn_iff.mp htrace)
    rw [map_sub, ← C.integral_comp_comm (fun _ ↦ C.intervalIntegrable_of_mem_support hFtr) ℓ,
      map_smul, ← ℓ.integral_comp_comm hint_area, smul_eq_mul, sub_eq_zero]
    have hℓF : ContDiffOn ℝ 1 (fun z ↦ ℓ (F z)) U :=
      (ℓ.restrictScalars ℝ).contDiff.comp_contDiffOn hF
    rw [C.integral_eq_two_mul_I_mul_integral_windingWeight_conjWirtingerDeriv hU htrace hnull hℓF]
    congr 1
    refine setIntegral_congr_fun hU.measurableSet fun z hz ↦ ?_
    have hdiff : DifferentiableAt ℝ F z :=
      (hF.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero
    have hcomp : conjWirtingerDeriv (fun w ↦ ℓ (F w)) z 1 = ℓ (conjWirtingerDeriv F z 1) := by
      have hfun : (fun w ↦ ℓ (F w)) = ℓ ∘ F := rfl
      rw [hfun, conjWirtingerDeriv_comp ℓ.differentiableAt hdiff, ℓ.hasFDerivAt.fderiv]
      rfl
    have hsmul : ℓ (C.windingWeight z • conjWirtingerDeriv F z 1) =
        (C.windingWeight z : ℂ) * ℓ (conjWirtingerDeriv F z 1) := by
      rw [← real_smul]
      exact (ℓ.restrictScalars ℝ).map_smul (C.windingWeight z) (conjWirtingerDeriv F z 1)
    exact (hsmul.trans (congrArg _ hcomp.symm)).symm
  · have h₁ : C.integral F = 0 := by
      rw [integral_eq_sum_support]
      exact Finset.sum_eq_zero fun _ _ ↦ by
        simp [intervalIntegral, integral_of_not_completeSpace hE]
    have h₂ : (∫ z in U, C.windingWeight z • conjWirtingerDeriv F z 1) = 0 :=
      integral_of_not_completeSpace hE
    rw [h₁, h₂, smul_zero]

/-- **Complex circulation Stokes formula for `F dbar z` on a contour cycle.** For `F = u + i v`
real `C¹` on an open set `U` and a cycle `C` in `U` that is null-homologous in `U`, the complex
combination `(∮_C u dx + v dy) + i (∮_C v dx - u dy)` of the two real `Cycle.green_winding`
circulations equals `(-2 * I) * ∫ z in U, C.windingWeight z * wirtingerDeriv F z 1`. -/
theorem circulation_dzBar_eq_neg_two_mul_I_mul_integral_windingWeight (C : Cycle)
    {U : Set ℂ} {F : ℂ → ℂ} (hU : IsOpen U) (htrace : C.IsIn U) (hnull : C.IsNullHomologous U)
    (hF : ContDiffOn ℝ 1 F U) :
    ((∑ γ ∈ FreeAbelianGroup.support C, (FreeAbelianGroup.coeff γ C : ℝ) *
        ∫ t in γ.a..γ.b, Green.circulationFun (fun z ↦ (F z).re) (fun z ↦ (F z).im) γ t : ℝ) : ℂ) +
      I * ((∑ γ ∈ FreeAbelianGroup.support C, (FreeAbelianGroup.coeff γ C : ℝ) *
        ∫ t in γ.a..γ.b,
          Green.circulationFun (fun z ↦ (F z).im) (fun z ↦ -(F z).re) γ t : ℝ) : ℂ) =
      (-2 * I) * ∫ z in U, (C.windingWeight z : ℂ) * wirtingerDeriv F z 1 := by
  have hu : ContDiffOn ℝ 1 (fun z ↦ (F z).re) U := Complex.reCLM.contDiff.comp_contDiffOn hF
  have hv : ContDiffOn ℝ 1 (fun z ↦ (F z).im) U := Complex.imCLM.contDiff.comp_contDiffOn hF
  have hgreen₁ := (C.green_winding hU htrace hu hv hnull).2.2
  have hgreen₂ := (C.green_winding hU htrace hv hu.neg hnull).2.2
  have hint : IntegrableOn (fun z ↦ (C.windingWeight z : ℂ) * wirtingerDeriv F z 1) U := by
    simpa only [real_smul] using
      C.integrableOn_windingWeight_smul_wirtingerDeriv hU htrace hnull hF
  rw [hgreen₁, hgreen₂]
  have h₁ : (∫ z in U, C.windingWeight z *
        Green.curl (fun w ↦ (F w).re) (fun w ↦ (F w).im) z) =
      2 * (∫ z in U, (C.windingWeight z : ℂ) * wirtingerDeriv F z 1).im := by
    calc
      (∫ z in U, C.windingWeight z * Green.curl (fun w ↦ (F w).re) (fun w ↦ (F w).im) z)
          = ∫ z in U, 2 * Complex.imCLM ((C.windingWeight z : ℂ) * wirtingerDeriv F z 1) :=
            setIntegral_congr_fun hU.measurableSet fun z hz ↦ by
              rw [curl_re_im_eq_two_mul_im_wirtingerDeriv
                ((hF.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)]
              simp [mul_left_comm]
      _ = 2 * (∫ z in U, (C.windingWeight z : ℂ) * wirtingerDeriv F z 1).im := by
            rw [integral_const_mul, Complex.imCLM.integral_comp_comm hint]
            rfl
  have h₂ : (∫ z in U, C.windingWeight z *
        Green.curl (fun w ↦ (F w).im) (fun w ↦ -(F w).re) z) =
      -2 * (∫ z in U, (C.windingWeight z : ℂ) * wirtingerDeriv F z 1).re := by
    calc
      (∫ z in U, C.windingWeight z * Green.curl (fun w ↦ (F w).im) (fun w ↦ -(F w).re) z)
          = ∫ z in U, (-2) * Complex.reCLM ((C.windingWeight z : ℂ) * wirtingerDeriv F z 1) :=
            setIntegral_congr_fun hU.measurableSet fun z hz ↦ by
              rw [curl_im_neg_re_eq_neg_two_mul_re_wirtingerDeriv
                ((hF.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)]
              simp [mul_left_comm]
      _ = -2 * (∫ z in U, (C.windingWeight z : ℂ) * wirtingerDeriv F z 1).re := by
            rw [integral_const_mul, Complex.reCLM.integral_comp_comm hint]
            rfl
  rw [h₁, h₂]
  apply Complex.ext <;> simp

/-- For `R > 0`, the trace-zero `windingWeight` of `circleCycle c R` is the indicator of
`ball c R`. -/
theorem windingWeight_circleCycle (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (circleCycle c R).windingWeight = (ball c R).indicator 1 := by
  ext z
  rcases lt_trichotomy (dist z c) R with hlt | heq | hgt
  · have htr : z ∉ (circleCycle c R).trace := by
      rw [trace_circleCycle, abs_of_pos hR, mem_sphere]
      exact hlt.ne
    rw [windingWeight_eq_of_notMem _ htr, windingNumber_circleCycle_eq_one_of_dist_lt hlt,
      indicator_of_mem (mem_ball.mpr hlt), Pi.one_apply, one_re]
  · have htr : z ∈ (circleCycle c R).trace := by
      rw [trace_circleCycle, abs_of_pos hR, mem_sphere]
      exact heq
    rw [windingWeight_eq_zero_of_mem _ htr,
      indicator_of_notMem (by simp [mem_ball, heq])]
  · have htr : z ∉ (circleCycle c R).trace := by
      rw [trace_circleCycle, abs_of_pos hR, mem_sphere]
      exact hgt.ne'
    rw [windingWeight_eq_of_notMem _ htr,
      windingNumber_circleCycle_eq_zero_of_lt_dist hR.le hgt,
      indicator_of_notMem (by simp [mem_ball, hgt.le]), zero_re]

end Contour.Cycle

section CircleCurveHelpers

private theorem trace_of_circleCurve (c : ℂ) {R : ℝ} (hR : 0 < R) :
    Contour.Cycle.trace (FreeAbelianGroup.of (Contour.circleCurve c R)) = sphere c R := by
  rw [Contour.Cycle.trace_of]
  have hu : uIcc (Contour.circleCurve c R).a (Contour.circleCurve c R).b = uIcc 0 (2 * π) := by
    rw [Contour.circleCurve_a, Contour.circleCurve_b]
  rw [congrArg ((Contour.circleCurve c R : ℝ → ℂ) '' ·) hu,
    image_congr fun _ ht ↦ Contour.circleCurve_apply ht,
    Complex.image_circleMap_uIcc, abs_of_pos hR]

private theorem windingNumber_of_circleCurve_eq (c : ℂ) (R : ℝ) (w : ℂ) :
    Contour.Cycle.windingNumber w (FreeAbelianGroup.of (Contour.circleCurve c R)) =
      Contour.windingNumber (circleMap c R) 0 (2 * π) w := by
  rw [Contour.Cycle.windingNumber_of]
  set γf : ℝ → ℂ := ⇑(Contour.circleCurve c R)
  rw [Contour.circleCurve_a, Contour.circleCurve_b]
  exact Contour.windingNumber_congr_curve fun _ ht ↦
    Contour.circleCurve_apply (uIoo_subset_uIcc_self ht)

private theorem windingWeight_of_circleCurve (c : ℂ) {R : ℝ} (hR : 0 < R) :
    Contour.Cycle.windingWeight (FreeAbelianGroup.of (Contour.circleCurve c R)) =
      (ball c R).indicator 1 := by
  let S : Contour.Cycle := FreeAbelianGroup.of (Contour.circleCurve c R)
  have htr_eq : S.trace = sphere c R := trace_of_circleCurve c hR
  ext z
  rcases lt_trichotomy (dist z c) R with hlt | heq | hgt
  · rw [Contour.Cycle.windingWeight_eq_of_notMem _ (by rw [htr_eq, mem_sphere]; exact hlt.ne),
      windingNumber_of_circleCurve_eq, Contour.windingNumber_circleMap_eq_one_of_dist_lt hlt,
      indicator_of_mem (mem_ball.mpr hlt), Pi.one_apply, one_re]
  · rw [Contour.Cycle.windingWeight_eq_zero_of_mem _ (by rw [htr_eq, mem_sphere]; exact heq),
      indicator_of_notMem (by simp [mem_ball, heq])]
  · rw [Contour.Cycle.windingWeight_eq_of_notMem _ (by rw [htr_eq, mem_sphere]; exact hgt.ne'),
      windingNumber_of_circleCurve_eq, Contour.windingNumber_circleMap_eq_zero_of_lt_dist hR.le hgt,
      indicator_of_notMem (by simp [mem_ball, hgt.le]), zero_re]

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

end CircleCurveHelpers

/-- **Circle Stokes formula for `F dbar z`.** For `R > 0` and `F = u + i v` real `C¹` on an open
set `U` containing `closedBall c R`, the real/imaginary circulation combination
`∮_{|z - c| = R} F dbar z` along `circleMap c R` equals
`(-2 * I) * ∫ z in ball c R, wirtingerDeriv F z 1`. -/
theorem circulation_dzBar_circleMap_eq_neg_two_mul_I_mul_integral_ball_wirtingerDeriv
    {c : ℂ} {R : ℝ} {U : Set ℂ} {F : ℂ → ℂ} (hR : 0 < R) (hU : IsOpen U)
    (hball : closedBall c R ⊆ U) (hF : ContDiffOn ℝ 1 F U) :
    ((∫ θ in 0..2 * π,
        Green.circulationFun (fun z ↦ (F z).re) (fun z ↦ (F z).im) (circleMap c R) θ : ℝ) : ℂ) +
      I * ((∫ θ in 0..2 * π,
        Green.circulationFun (fun z ↦ (F z).im) (fun z ↦ -(F z).re) (circleMap c R) θ : ℝ) : ℂ) =
      (-2 * I) * ∫ z in ball c R, wirtingerDeriv F z 1 := by
  let S : Contour.Cycle := FreeAbelianGroup.of (Contour.circleCurve c R)
  have htr : S.IsIn U := by
    rw [Contour.Cycle.isIn_iff, trace_of_circleCurve c hR]
    exact sphere_subset_closedBall.trans hball
  have hnull : S.IsNullHomologous U := by
    rw [Contour.Cycle.isNullHomologous_iff]
    intro z hzU
    rw [windingNumber_of_circleCurve_eq]
    exact Contour.windingNumber_circleMap_eq_zero_of_lt_dist hR.le
      (not_le.mp fun hle ↦ hzU (hball (mem_closedBall.mpr hle)))
  have hmain := S.circulation_dzBar_eq_neg_two_mul_I_mul_integral_windingWeight hU htr hnull hF
  simp only [S, FreeAbelianGroup.support_of, Finset.sum_singleton,
    FreeAbelianGroup.coeff_of_self, Int.cast_one, one_mul,
    intervalIntegral_circulationFun_circleCurve] at hmain
  rw [hmain, windingWeight_of_circleCurve c hR]
  congr 1
  have hfun : (fun z ↦ (((ball c R).indicator (1 : ℂ → ℝ) z : ℝ) : ℂ) * wirtingerDeriv F z 1) =
      (ball c R).indicator fun z ↦ wirtingerDeriv F z 1 := by
    ext z
    by_cases hz : z ∈ ball c R <;> simp [hz]
  rw [hfun, setIntegral_indicator measurableSet_ball,
    inter_eq_right.mpr (ball_subset_closedBall.trans hball)]

/-- **Unit-circle Stokes formula for `F dbar z`.** For `F = u + i v` real `C¹` on an open
neighborhood `U` of the closed unit disk `closedBall 0 1`,
`∮_{|z| = 1} F dbar z = (-2 * I) * ∫_{|z| < 1} ∂_z F dA`. -/
theorem circulation_dzBar_unitCircle_eq_neg_two_mul_I_mul_integral_ball_wirtingerDeriv
    {U : Set ℂ} {F : ℂ → ℂ} (hU : IsOpen U) (hball : closedBall (0 : ℂ) 1 ⊆ U)
    (hF : ContDiffOn ℝ 1 F U) :
    ((∫ θ in 0..2 * π,
        Green.circulationFun (fun z ↦ (F z).re) (fun z ↦ (F z).im) (circleMap 0 1) θ : ℝ) : ℂ) +
      I * ((∫ θ in 0..2 * π,
        Green.circulationFun (fun z ↦ (F z).im) (fun z ↦ -(F z).re) (circleMap 0 1) θ : ℝ) : ℂ) =
      (-2 * I) * ∫ z in ball (0 : ℂ) 1, wirtingerDeriv F z 1 :=
  circulation_dzBar_circleMap_eq_neg_two_mul_I_mul_integral_ball_wirtingerDeriv
    zero_lt_one hU hball hF

/-- **Complex circle Stokes formula for `F dbar z`.** For `R > 0` and `F` real `C¹` on an open
neighborhood `U` of `closedBall c R`,
`∫ θ in 0..2 * π, F (circleMap c R θ) * conj (deriv (circleMap c R) θ) =
  (-2 * I) * ∫ z in ball c R, wirtingerDeriv F z 1`. -/
theorem integral_mul_conj_deriv_circleMap_eq_neg_two_mul_I_mul_integral_ball_wirtingerDeriv
    {c : ℂ} {R : ℝ} {U : Set ℂ} {F : ℂ → ℂ} (hR : 0 < R) (hU : IsOpen U)
    (hball : closedBall c R ⊆ U) (hF : ContDiffOn ℝ 1 F U) :
    (∫ θ in 0..2 * π, F (circleMap c R θ) * conj (deriv (circleMap c R) θ)) =
      (-2 * I) * ∫ z in ball c R, wirtingerDeriv F z 1 := by
  have hFc : Continuous fun θ : ℝ ↦ F (circleMap c R θ) :=
    hF.continuousOn.comp_continuous (continuous_circleMap c R) fun θ ↦
      hball (sphere_subset_closedBall (circleMap_mem_sphere c hR.le θ))
  have hderiv : Continuous (deriv (circleMap c R)) := by
    rw [funext (deriv_circleMap c R)]
    exact (continuous_circleMap 0 R).mul continuous_const
  have hcont (P Q : ℂ → ℝ) (hP : Continuous fun θ ↦ P (circleMap c R θ))
      (hQ : Continuous fun θ ↦ Q (circleMap c R θ)) :
      Continuous (Green.circulationFun P Q (circleMap c R)) :=
    (hP.mul (Complex.continuous_re.comp hderiv)).add
      (hQ.mul (Complex.continuous_im.comp hderiv))
  have hc₁ := hcont (fun z ↦ (F z).re) (fun z ↦ (F z).im)
    (Complex.continuous_re.comp hFc) (Complex.continuous_im.comp hFc)
  have hc₂ := hcont (fun z ↦ (F z).im) (fun z ↦ -(F z).re)
    (Complex.continuous_im.comp hFc) (Complex.continuous_re.comp hFc).neg
  have hint₁ : IntervalIntegrable
      (fun θ ↦ (Green.circulationFun (fun z ↦ (F z).re) (fun z ↦ (F z).im) (circleMap c R) θ : ℂ))
      volume 0 (2 * π) :=
    (Continuous.comp Complex.continuous_ofReal hc₁).intervalIntegrable _ _
  have hint₂ : IntervalIntegrable
      (fun θ ↦
        (Green.circulationFun (fun z ↦ (F z).im) (fun z ↦ -(F z).re) (circleMap c R) θ : ℂ))
      volume 0 (2 * π) :=
    (Continuous.comp Complex.continuous_ofReal hc₂).intervalIntegrable _ _
  simp_rw [mul_conj_deriv_eq_circulationFun]
  rw [intervalIntegral.integral_add hint₁ (hint₂.const_mul I),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]
  exact circulation_dzBar_circleMap_eq_neg_two_mul_I_mul_integral_ball_wirtingerDeriv
    hR hU hball hF

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
  have hconj0 := hgn.wirtingerDeriv_conj_comp_eq_zero
  rw [hconst, wirtingerDeriv_const_smul, smul_apply,
    wirtingerDeriv_smul_apply (hg.restrictScalars ℝ) hh 1,
    hconj0, zero_apply, smul_zero,
    zero_add, hg.wirtingerDeriv_eq_fderiv, (hasDerivAt_pow (m + 1) z).hasFDerivAt.fderiv,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul, Nat.add_sub_cancel]
  simp only [Nat.cast_add, Nat.cast_one, map_pow, smul_eq_mul]
  field_simp [hm1]

private theorem integral_unitCircle_monomial_conj_deriv (m n : ℕ) :
    (∫ θ in 0..2 * π,
        (((m : ℂ) + 1)⁻¹ * (circleMap 0 1 θ ^ (m + 1) * conj (circleMap 0 1 θ) ^ n)) *
          conj (deriv (circleMap 0 1) θ)) =
      -((m : ℂ) + 1)⁻¹ * ∮ z in C(0, 1), (z - 0) ^ ((m : ℤ) - n - 1) := by
  rw [circleIntegral]
  have hcongr (θ : ℝ) :
      (((m : ℂ) + 1)⁻¹ * (circleMap 0 1 θ ^ (m + 1) * conj (circleMap 0 1 θ) ^ n)) *
          conj (deriv (circleMap 0 1) θ) =
        -((m : ℂ) + 1)⁻¹ *
          (deriv (circleMap 0 1) θ • (circleMap 0 1 θ - 0) ^ ((m : ℤ) - n - 1)) := by
    set w : ℂ := circleMap 0 1 θ
    have hw_norm : ‖w‖ = 1 := by simp [w]
    have hw0 : w ≠ 0 := by intro h; simp [h] at hw_norm
    have hw_conj : conj w = w⁻¹ := (Complex.inv_eq_conj hw_norm).symm
    have hdw : deriv (circleMap 0 1) θ = w * I := by simp [deriv_circleMap, w]
    simp only [hdw, map_mul, conj_I, hw_conj, sub_zero, smul_eq_mul]
    have hpow : w ^ (m + 1) * w⁻¹ ^ n * (w⁻¹ * -I) = -(w * I * w ^ ((m : ℤ) - n - 1)) := by
      calc
        w ^ (m + 1) * w⁻¹ ^ n * (w⁻¹ * -I)
            = -I * (w ^ ((m + 1 : ℕ) : ℤ) * w ^ (-(n : ℤ)) * w ^ (-1 : ℤ)) := by
              rw [zpow_natCast, zpow_neg, zpow_natCast, inv_pow, zpow_neg_one]; ring
        _ = -I * (w * w ^ ((m : ℤ) - n - 1)) := by
              rw [← zpow_add₀ hw0, ← zpow_add₀ hw0, ← zpow_one_add₀ hw0]
              congr 2; push_cast; ring
        _ = -(w * I * w ^ ((m : ℤ) - n - 1)) := by ring
    calc
      ((m : ℂ) + 1)⁻¹ * (w ^ (m + 1) * w⁻¹ ^ n) * (w⁻¹ * -I)
          = ((m : ℂ) + 1)⁻¹ * (w ^ (m + 1) * w⁻¹ ^ n * (w⁻¹ * -I)) := by ring
      _ = -((m : ℂ) + 1)⁻¹ * (w * I * w ^ ((m : ℤ) - n - 1)) := by rw [hpow]; ring
  simp_rw [hcongr]
  rw [intervalIntegral.integral_const_mul]

end MonomialMomentHelpers

/-- **Unit-disk monomial moment identity.** Integrating `z ^ m * conj z ^ n` over the open unit
disk `ball 0 1` gives `π / (m + 1)` when `m = n` and `0` when `m ≠ n`. -/
theorem integral_unitBall_pow_mul_conj_pow (m n : ℕ) :
    (∫ z in ball (0 : ℂ) 1, z ^ m * conj z ^ n) =
      if m = n then (Real.pi : ℂ) / ((m : ℂ) + 1) else 0 := by
  let F : ℂ → ℂ := fun z ↦ ((m : ℂ) + 1)⁻¹ * (z ^ (m + 1) * conj z ^ n)
  have hm1 : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hF_smooth : ContDiff ℝ 1 F :=
    contDiff_const.mul ((contDiff_id.pow (m + 1)).mul (Complex.conjCLE.contDiff.pow n))
  have hstokes :=
    integral_mul_conj_deriv_circleMap_eq_neg_two_mul_I_mul_integral_ball_wirtingerDeriv (c := 0)
      zero_lt_one isOpen_univ (subset_univ _) hF_smooth.contDiffOn
  simp_rw [F, wirtingerDeriv_monomial_div, integral_unitCircle_monomial_conj_deriv] at hstokes
  have h2I : (-2 * I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) I_ne_zero
  apply mul_left_cancel₀ h2I
  rw [← hstokes]
  split_ifs with hmn
  · subst hmn
    have hexp : ((m : ℤ) - m - 1) = -1 := by omega
    rw [hexp]
    simp_rw [zpow_neg_one]
    rw [circleIntegral.integral_sub_center_inv 0 one_ne_zero]
    field_simp [hm1]
  · have hne : ((m : ℤ) - n - 1) ≠ -1 := by omega
    rw [circleIntegral.integral_sub_zpow_of_ne hne, mul_zero, mul_zero]

end TauCeti

end

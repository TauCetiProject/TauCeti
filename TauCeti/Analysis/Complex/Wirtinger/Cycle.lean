/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.Complex.Wirtinger.WindingWeight
public import TauCeti.Analysis.Green.Cycle
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.Dual
import TauCeti.Analysis.Complex.Wirtinger.Curl
import TauCeti.Analysis.Contour.Cycle.Circle

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
`ContDiffOn ℝ 1 F U` hypotheses), and specializing to `Contour.circleCycle c R` yields the
complex circle Stokes formula for `F dbar z` on any ball `ball c |R|`.

## Main results

* `TauCeti.Contour.Cycle.integral_eq_two_mul_I_mul_integral_windingWeight_conjWirtingerDeriv`,
  `TauCeti.Contour.Cycle.integral_eq_two_mul_I_smul_integral_windingWeight_conjWirtingerDeriv`
* `Contour.Cycle.conj_integral_conj_eq_neg_two_mul_I_mul_integral_windingWeight_wirtingerDeriv`
* `Contour.Cycle.circulation_dzBar_eq_neg_two_mul_I_mul_integral_windingWeight_wirtingerDeriv`
* `TauCeti.integral_mul_conj_deriv_circleMap_eq_neg_two_mul_I_mul_integral_ball_wirtingerDeriv`

## References

* A. Rainer, *Advanced Complex Analysis*, §10, p. 23, Proposition 10.1.
* L. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979, Chapter 4, §4.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Section 1.2.
-/

public section

noncomputable section

open Complex ComplexConjugate MeasureTheory Metric Set
open scoped Interval Real

namespace TauCeti

/-! ### Complex Green–Stokes formulas on contour cycles -/

namespace Contour.Cycle

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

/-- **Dual complex Green formula for `F dbar z` on a contour cycle.** For `F : ℂ → ℂ` real `C¹`
on an open set `U` and a cycle `C` in `U` that is null-homologous in `U`,
`conj (C.integral (fun z ↦ conj (F z)))` equals
`(-2 * I) * ∫ z in U, C.windingWeight z * wirtingerDeriv F z 1`. -/
theorem conj_integral_conj_eq_neg_two_mul_I_mul_integral_windingWeight_wirtingerDeriv
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

/-- **Complex circle Stokes formula for `F dbar z`.** For `F` real `C¹` on an open neighborhood `U`
of `closedBall c |R|`,
`∫ θ in 0..2 * π, F (circleMap c R θ) * conj (deriv (circleMap c R) θ) =`
`  (-2 * I) * ∫ z in ball c |R|, wirtingerDeriv F z 1`. -/
theorem integral_mul_conj_deriv_circleMap_eq_neg_two_mul_I_mul_integral_ball_wirtingerDeriv
    {c : ℂ} {R : ℝ} {U : Set ℂ} {F : ℂ → ℂ} (hU : IsOpen U)
    (hball : closedBall c |R| ⊆ U) (hF : ContDiffOn ℝ 1 F U) :
    (∫ θ in 0..2 * π, F (circleMap c R θ) * conj (deriv (circleMap c R) θ)) =
      (-2 * I) * ∫ z in ball c |R|, wirtingerDeriv F z 1 := by
  set S := Contour.circleCycle c R
  have htrace : S.IsIn U := by
    rw [Contour.Cycle.isIn_iff, Contour.Cycle.trace_circleCycle]
    exact sphere_subset_closedBall.trans hball
  have hnull : S.IsNullHomologous U := by
    rw [Contour.Cycle.isNullHomologous_iff]
    intro z hzU
    exact Contour.Cycle.windingNumber_circleCycle_eq_zero_of_abs_lt_dist
      (lt_of_not_ge fun hle ↦ hzU (hball (mem_closedBall.mpr hle)))
  have hS := S.conj_integral_conj_eq_neg_two_mul_I_mul_integral_windingWeight_wirtingerDeriv
    hU htrace hnull hF
  rw [Contour.Cycle.integral_circleCycle, circleIntegral,
    ← intervalIntegral.intervalIntegral_conj] at hS
  have h_lhs : (∫ θ in 0..2 * π, conj (deriv (circleMap c R) θ • conj (F (circleMap c R θ)))) =
      ∫ θ in 0..2 * π, F (circleMap c R θ) * conj (deriv (circleMap c R) θ) :=
    intervalIntegral.integral_congr fun θ _ ↦ by
      rw [smul_eq_mul, map_mul, starRingEnd_self_apply, mul_comm]
  have h_rhs : (∫ z in U, (S.windingWeight z : ℂ) * wirtingerDeriv F z 1) =
      ∫ z in ball c |R|, wirtingerDeriv F z 1 := by
    have hwt : (fun z ↦ (S.windingWeight z : ℂ) * wirtingerDeriv F z 1) =
        (ball c |R|).indicator fun z ↦ wirtingerDeriv F z 1 := by
      ext z
      rw [Contour.Cycle.windingWeight_circleCycle c R]
      by_cases hz : z ∈ ball c |R| <;> simp [hz]
    rw [hwt, setIntegral_indicator measurableSet_ball,
      inter_eq_right.mpr (ball_subset_closedBall.trans hball)]
  rwa [h_lhs, h_rhs] at hS

end TauCeti

end

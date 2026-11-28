/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Cycle
public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Complex.Pompeiu.Basic
import TauCeti.Analysis.Contour.Cycle.Circle
import TauCeti.MeasureTheory.Integral.Circle.Integral
import TauCeti.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Cauchy–Pompeiu formula on bounded domains with contour-cycle boundaries

Let `Δ` be an open plane set with `closure Δ ⊆ Ω` (`Ω` open), and let `C : Contour.Cycle` have
`C.IsIn Ω`. Off `C.trace`, suppose `C` has winding number `1` on `Δ` and `0` outside `Δ`. For a
real `C¹` map `f : ℂ → E` on `Ω` into a complex Banach space `E`, applying the winding-weighted
complex Green formula to `(z - ξ)⁻¹ • f z` on `C - circleCycle ξ ε` (for `ξ ∉ C.trace` and
`closedBall ξ ε ⊆ Δ`) and passing `ε → 0⁺` proves the full-boundary **Cauchy–Pompeiu formula**:

`f ξ = (2πi)⁻¹ • C.integral (fun z ↦ (z - ξ)⁻¹ • f z) - π⁻¹ • ∫ z in Δ, (z - ξ)⁻¹ • \bar∂ f(z)`,

together with its frontier-based specializations when `C.trace ⊆ frontier Δ`.

## Main results

* `TauCeti.Contour.Cycle.integral_sub_circleIntegral_sub_inv_smul_eq`
* `TauCeti.cauchyPompeiu_smul`, `TauCeti.cauchyPompeiu_smul_of_trace_subset_frontier`
* `TauCeti.cauchyPompeiu`, `TauCeti.cauchyPompeiu_of_trace_subset_frontier`

## References

* A. Rainer, *Advanced Complex Analysis*, Proposition 10.1, p. 23.
* L. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979, Chapter 4.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Section 1.2.
-/

public section

noncomputable section

open Bornology Complex Filter MeasureTheory Metric Set
open scoped Real Topology

namespace TauCeti

/-! ### Punctured Cauchy–Pompeiu identity -/

open scoped Classical in
/-- **Punctured Cauchy–Pompeiu identity.** For an open set `Ω`, a measurable set `Δ ⊆ Ω`, a
cycle `C` in `Ω` (`C.IsIn Ω`) whose winding number off `C.trace` is `1` on `Δ` and `0` outside
`Δ`, and a real `C¹` map `f : ℂ → E` on `Ω`, excising `closedBall ξ ε ⊆ Δ` (`ε > 0`) with
`ξ ∉ C.trace` expresses the difference between the outer cycle integral
`C.integral (fun z ↦ (z - ξ)⁻¹ • f z)` and the small-circle integral
`∮ z in C(ξ, ε), (z - ξ)⁻¹ • f z` as
`(2 * I) • ∫ z in Δ \ closedBall ξ ε, (z - ξ)⁻¹ • \bar∂ f(z)`. When `E` is a complex Banach space
(`CompleteSpace E`), this is the genuine punctured Cauchy–Pompeiu identity; when `E` is incomplete,
both Bochner integrals (and hence both sides) are `0` by convention
(`MeasureTheory.integral_of_not_completeSpace`). -/
theorem Contour.Cycle.integral_sub_circleIntegral_sub_inv_smul_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {Ω Δ : Set ℂ} (hΩ : IsOpen Ω)
    (hΔ : MeasurableSet Δ) (hΔΩ : Δ ⊆ Ω) (C : Contour.Cycle) (htrace : C.IsIn Ω)
    (hindex : ∀ z ∉ C.trace, C.windingNumber z = if z ∈ Δ then 1 else 0)
    {f : ℂ → E} (hf : ContDiffOn ℝ 1 f Ω) {ξ : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall ξ ε ⊆ Δ) (hξtr : ξ ∉ C.trace) :
    C.integral (fun z ↦ (z - ξ)⁻¹ • f z) - (∮ z in C(ξ, ε), (z - ξ)⁻¹ • f z) =
      (2 * I : ℂ) • ∫ z in Δ \ closedBall ξ ε, (z - ξ)⁻¹ • conjWirtingerDeriv f z 1 := by
  obtain ⟨r, hr0, hrε, htr_r, hnull_r⟩ :=
    C.isIn_and_isNullHomologous_sub_circleCycle hΔΩ htrace hindex hε hball hξtr
  set U_r : Set ℂ := Ω \ closedBall ξ r
  have hU_r : IsOpen U_r := hΩ.sdiff isClosed_closedBall
  have hne : ∀ z ∈ U_r, z - ξ ≠ 0 := fun z hz hsub ↦
    hz.2 (by rw [sub_eq_zero.mp hsub]; exact mem_closedBall_self hr0.le)
  have hF : ContDiffOn ℝ 1 (fun z ↦ (z - ξ)⁻¹ • f z) U_r :=
    ((contDiffOn_id.sub contDiffOn_const).fun_inv hne).smul (hf.mono sdiff_subset)
  have hgreen := (C - Contour.circleCycle ξ ε)
    |>.integral_eq_two_mul_I_smul_integral_windingWeight_conjWirtingerDeriv hU_r htr_r hnull_r hF
  rw [map_sub, Contour.Cycle.integral_circleCycle] at hgreen
  rw [hgreen]
  refine congrArg _ ?_
  calc
    (∫ z in U_r, (C - Contour.circleCycle ξ ε).windingWeight z •
        conjWirtingerDeriv (fun w ↦ (w - ξ)⁻¹ • f w) z 1)
        = ∫ z in U_r, (C - Contour.circleCycle ξ ε).windingWeight z •
            ((z - ξ)⁻¹ • conjWirtingerDeriv f z 1) :=
          setIntegral_congr_fun hU_r.measurableSet fun z hz ↦ by
            have hinv : DifferentiableAt ℂ (fun w ↦ (w - ξ)⁻¹) z :=
              (differentiableAt_id.sub (differentiableAt_const ξ)).inv (hne z hz)
            rw [conjWirtingerDeriv_smul_apply (hinv.restrictScalars ℝ)
                ((hf.contDiffAt (hΩ.mem_nhds hz.1)).differentiableAt one_ne_zero) 1,
              hinv.conjWirtingerDeriv_eq_zero, zero_apply, zero_smul, add_zero]
    _ = ∫ z in U_r, (Δ \ closedBall ξ ε).indicator
          (fun z ↦ (z - ξ)⁻¹ • conjWirtingerDeriv f z 1) z :=
          integral_congr_ae
            (((C.windingWeight_sub_circleCycle_ae_eq hindex hε hball).filter_mono
              ae_restrict_le).mono fun z hz ↦ by simp [hz, Set.indicator_apply])
    _ = ∫ z in Δ \ closedBall ξ ε, (z - ξ)⁻¹ • conjWirtingerDeriv f z 1 := by
          have hsub : Δ \ closedBall ξ ε ⊆ U_r := fun z ⟨hzΔ, hzcl⟩ ↦
            ⟨hΔΩ hzΔ, fun hzr ↦ hzcl (closedBall_subset_closedBall hrε.le hzr)⟩
          rw [setIntegral_indicator (hΔ.diff isClosed_closedBall.measurableSet),
            inter_eq_right.mpr hsub]

/-! ### Full-boundary Cauchy–Pompeiu formulas -/

open scoped Classical in
/-- **Full-boundary Cauchy–Pompeiu formula (Banach-valued).** For an open set `Ω`, an open set `Δ`
with `closure Δ ⊆ Ω`, a cycle `C` in `Ω` (`C.IsIn Ω`) whose winding number off `C.trace` is `1` on
`Δ` and `0` outside `Δ`, a real `C¹` map `f : ℂ → E` on `Ω` into a complex Banach space `E`, and
`ξ ∈ Δ` with `ξ ∉ C.trace`,
`f ξ = (2πi)⁻¹ • C.integral (fun z ↦ (z - ξ)⁻¹ • f z) - π⁻¹ • ∫ z in Δ, (z - ξ)⁻¹ • \bar∂ f(z)`.
Boundedness of `Δ` follows automatically from `hindex` and compactness of `C.trace` and
`tsupport C.windingWeight`. -/
theorem cauchyPompeiu_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {Ω Δ : Set ℂ} (hΩ : IsOpen Ω) (hΔ : IsOpen Δ) (hclosure : closure Δ ⊆ Ω)
    (C : Contour.Cycle) (htrace : C.IsIn Ω)
    (hindex : ∀ z ∉ C.trace, C.windingNumber z = if z ∈ Δ then 1 else 0)
    (f : ℂ → E) (hf : ContDiffOn ℝ 1 f Ω) {ξ : ℂ} (hξ : ξ ∈ Δ) (hξtr : ξ ∉ C.trace) :
    f ξ = (2 * (Real.pi : ℂ) * I)⁻¹ • C.integral (fun z ↦ (z - ξ)⁻¹ • f z) -
      (Real.pi : ℂ)⁻¹ • ∫ z in Δ, (z - ξ)⁻¹ • conjWirtingerDeriv f z 1 := by
  have hbounded : IsBounded Δ := by
    refine (C.isCompact_trace.union C.hasCompactSupport_windingWeight).isBounded.subset ?_
    intro z hz
    by_cases hztr : z ∈ C.trace
    · exact Or.inl hztr
    · refine Or.inr (subset_tsupport _ ?_)
      rw [Function.mem_support, C.windingWeight_eq_of_notMem hztr, hindex z hztr, ite_eq_left hz,
        one_re]
      exact one_ne_zero
  obtain ⟨δ, hδ, hballδ⟩ := Metric.isOpen_iff.mp hΔ ξ hξ
  have hcirc := hf.continuousOn.tendsto_circleIntegral_sub_inv_smul_nhdsGT
    (hΩ.mem_nhds (hclosure (subset_closure hξ)))
  have harea := (integrableOn_sub_inv_smul_conjWirtingerDeriv hΩ hbounded hclosure hf ξ)
    |>.tendsto_integral_sdiff_closedBall_nhdsGT
      (le_antisymm ((Measure.restrict_apply_le _ _).trans (measure_singleton ξ).le) zero_le)
  have hev : (fun ε ↦ ∮ z in C(ξ, ε), (z - ξ)⁻¹ • f z) =ᶠ[𝓝[>] 0]
      fun ε ↦ C.integral (fun z ↦ (z - ξ)⁻¹ • f z) -
        (2 * I : ℂ) • ∫ z in Δ \ closedBall ξ ε, (z - ξ)⁻¹ • conjWirtingerDeriv f z 1 := by
    filter_upwards [Ioo_mem_nhdsGT (half_pos hδ)] with ε ⟨hε, hεδ⟩
    have hsub_ε : closedBall ξ ε ⊆ Δ :=
      (closedBall_subset_ball (hεδ.trans (half_lt_self hδ))).trans hballδ
    have hpunct := C.integral_sub_circleIntegral_sub_inv_smul_eq hΩ hΔ.measurableSet
      (subset_closure.trans hclosure) htrace hindex hf hε hsub_ε hξtr
    rw [← hpunct]
    abel
  have heq : (2 * (Real.pi : ℂ) * I) • f ξ =
      C.integral (fun z ↦ (z - ξ)⁻¹ • f z) -
        (2 * I : ℂ) • ∫ z in Δ, (z - ξ)⁻¹ • conjWirtingerDeriv f z 1 :=
    tendsto_nhds_unique hcirc
      ((tendsto_const_nhds.sub (harea.const_smul (2 * I : ℂ))).congr' hev.symm)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hcoeff : (2 * (Real.pi : ℂ) * I)⁻¹ * (2 * I) = (Real.pi : ℂ)⁻¹ := by
    field_simp [hpi, I_ne_zero]
  calc
    f ξ = (2 * (Real.pi : ℂ) * I)⁻¹ • ((2 * (Real.pi : ℂ) * I) • f ξ) :=
          (inv_smul_smul₀ Complex.two_pi_I_ne_zero _).symm
    _ = (2 * (Real.pi : ℂ) * I)⁻¹ • C.integral (fun z ↦ (z - ξ)⁻¹ • f z) -
          (Real.pi : ℂ)⁻¹ • ∫ z in Δ, (z - ξ)⁻¹ • conjWirtingerDeriv f z 1 := by
          rw [heq, smul_sub, smul_smul, hcoeff]

open scoped Classical in
/-- **Frontier-based full-boundary Cauchy–Pompeiu formula (Banach-valued).** When
`C.trace ⊆ frontier Δ` and `closure Δ ⊆ Ω` with `Δ` open, `C.IsIn Ω` and `ξ ∉ C.trace` for
`ξ ∈ Δ` follow automatically from `cauchyPompeiu_smul`. -/
theorem cauchyPompeiu_smul_of_trace_subset_frontier {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {Ω Δ : Set ℂ} (hΩ : IsOpen Ω) (hΔ : IsOpen Δ)
    (hclosure : closure Δ ⊆ Ω) (C : Contour.Cycle) (htrace : C.trace ⊆ frontier Δ)
    (hindex : ∀ z ∉ C.trace, C.windingNumber z = if z ∈ Δ then 1 else 0)
    (f : ℂ → E) (hf : ContDiffOn ℝ 1 f Ω) {ξ : ℂ} (hξ : ξ ∈ Δ) :
    f ξ = (2 * (Real.pi : ℂ) * I)⁻¹ • C.integral (fun z ↦ (z - ξ)⁻¹ • f z) -
      (Real.pi : ℂ)⁻¹ • ∫ z in Δ, (z - ξ)⁻¹ • conjWirtingerDeriv f z 1 :=
  cauchyPompeiu_smul hΩ hΔ hclosure C
    (Contour.Cycle.isIn_iff.mpr (htrace.trans (frontier_subset_closure.trans hclosure)))
    hindex f hf hξ fun h ↦ (htrace h).2 (by rwa [hΔ.interior_eq])

open scoped Classical in
/-- **Full-boundary Cauchy–Pompeiu formula** for an open set `Ω`, an open region `Δ`
(`closure Δ ⊆ Ω`), a native contour cycle `C` in `Ω` (`C.IsIn Ω`) whose winding number off
`C.trace` is `1` inside `Δ` and `0` outside `Δ`, and a real `C¹` function `f : ℂ → ℂ` on `Ω`,
at any point `ξ ∈ Δ` with `ξ ∉ C.trace`, written with the real directional derivatives
`f_x + i f_y = 2 \bar∂ f`. -/
theorem cauchyPompeiu {Ω Δ : Set ℂ} (hΩ : IsOpen Ω) (hΔ : IsOpen Δ) (hclosure : closure Δ ⊆ Ω)
    (C : TauCeti.Contour.Cycle) (htrace : C.IsIn Ω)
    (hindex : ∀ z ∉ C.trace,
      TauCeti.Contour.Cycle.windingNumber z C = if z ∈ Δ then 1 else 0)
    (f : ℂ → ℂ) (hf : ContDiffOn ℝ 1 f Ω) {ξ : ℂ} (hξ : ξ ∈ Δ) (hξtr : ξ ∉ C.trace) :
    f ξ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        TauCeti.Contour.Cycle.integral (fun z => f z / (z - ξ)) C -
      (2 * (Real.pi : ℂ))⁻¹ *
        ∫ z in Δ, (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / (z - ξ) := by
  have hsmul : f ξ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        TauCeti.Contour.Cycle.integral (fun z ↦ f z / (z - ξ)) C -
      (Real.pi : ℂ)⁻¹ * ∫ z in Δ, conjWirtingerDeriv f z 1 / (z - ξ) := by
    simpa only [smul_eq_mul, inv_mul_eq_div] using
      cauchyPompeiu_smul hΩ hΔ hclosure C htrace hindex f hf hξ hξtr
  rw [hsmul]
  have hdbar : (fun z ↦ (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / (z - ξ)) =
      fun z ↦ (2 : ℂ) * (conjWirtingerDeriv f z 1 / (z - ξ)) := funext fun z ↦ by
    have h2 := fderiv_apply_one_add_I_smul_fderiv_apply_I f z
    simp only [smul_eq_mul] at h2
    rw [h2, mul_div_assoc]
  rw [hdbar, integral_const_mul, ← mul_assoc]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  congr 2; field_simp [hpi]

open scoped Classical in
/-- **Frontier-based full-boundary Cauchy–Pompeiu formula** for an open set `Ω`, an open region `Δ`
(`closure Δ ⊆ Ω`), a native contour cycle `C` with `C.trace ⊆ frontier Δ` whose winding number off
`C.trace` is `1` inside `Δ` and `0` outside `Δ`, and a real `C¹` function `f : ℂ → ℂ` on `Ω`,
at any point `ξ ∈ Δ`, written with the real directional derivatives `f_x + i f_y = 2 \bar∂ f`. -/
theorem cauchyPompeiu_of_trace_subset_frontier {Ω Δ : Set ℂ} (hΩ : IsOpen Ω) (hΔ : IsOpen Δ)
    (hclosure : closure Δ ⊆ Ω) (C : TauCeti.Contour.Cycle) (htrace : C.trace ⊆ frontier Δ)
    (hindex : ∀ z ∉ C.trace,
      TauCeti.Contour.Cycle.windingNumber z C = if z ∈ Δ then 1 else 0)
    (f : ℂ → ℂ) (hf : ContDiffOn ℝ 1 f Ω) {ξ : ℂ} (hξ : ξ ∈ Δ) :
    f ξ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        TauCeti.Contour.Cycle.integral (fun z => f z / (z - ξ)) C -
      (2 * (Real.pi : ℂ))⁻¹ *
        ∫ z in Δ, (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / (z - ξ) :=
  cauchyPompeiu hΩ hΔ hclosure C
    (Contour.Cycle.isIn_iff.mpr (htrace.trans (frontier_subset_closure.trans hclosure)))
    hindex f hf hξ fun h ↦ (htrace h).2 (by rwa [hΔ.interior_eq])

end TauCeti

end

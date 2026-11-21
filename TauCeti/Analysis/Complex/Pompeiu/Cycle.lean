/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyKernel
public import TauCeti.Analysis.Complex.Wirtinger.Cycle
public import TauCeti.Analysis.Contour.Cycle.Jordan
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.MeasureTheory.Integral.Circle.Integral
import TauCeti.MeasureTheory.Integral.DominatedConvergence

/-!
# The Cauchy–Pompeiu formula on bounded domains with contour-cycle boundaries

Let `Δ` be a bounded open plane set with `closure Δ ⊆ Ω` (`Ω` open), and let `C : Contour.Cycle`
have `C.trace ⊆ frontier Δ` and winding number `1` on `Δ` and `0` outside `Δ` off `C.trace`.
Applying the winding-weighted complex Green formula to `(z - ξ)⁻¹ • f z` on `C - circleCycle ξ ε`
and passing `ε → 0⁺` proves the full-boundary **Cauchy–Pompeiu formula**:

`f ξ = (2πi)⁻¹ • C.integral (fun z ↦ (z - ξ)⁻¹ • f z) - π⁻¹ • ∫ z in Δ, (z - ξ)⁻¹ • \bar∂ f(z)`,

together with its specialization to finitely connected Jordan regions via
`TauCeti.Contour.jordanBoundaryCycle`.

## Main results

* `TauCeti.integrableOn_sub_inv_smul_conjWirtingerDeriv`
* `TauCeti.Contour.Cycle.integral_sub_circleIntegral_sub_inv_smul_eq`
* `TauCeti.cauchyPompeiu_smul`, `TauCeti.cauchyPompeiu_conjWirtingerDeriv`, `TauCeti.cauchyPompeiu`
* `TauCeti.cauchyPompeiu_jordanBoundaryCycle_smul`, `TauCeti.cauchyPompeiu_jordanBoundaryCycle`

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

/-! ### Area integrability for the Cauchy–Pompeiu kernel -/

/-- If `Δ` is a bounded plane set with `closure Δ ⊆ Ω` (`Ω` open) and `f : ℂ → E` is real `C¹`
on `Ω`, then `z ↦ (z - ξ)⁻¹ • conjWirtingerDeriv f z 1` is integrable on `Δ` for every `ξ : ℂ`. -/
theorem integrableOn_sub_inv_smul_conjWirtingerDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {Ω Δ : Set ℂ} (hΩ : IsOpen Ω) (hbounded : IsBounded Δ)
    (hclosure : closure Δ ⊆ Ω) {f : ℂ → E} (hf : ContDiffOn ℝ 1 f Ω) (ξ : ℂ) :
    IntegrableOn (fun z ↦ (z - ξ)⁻¹ • conjWirtingerDeriv f z 1) Δ := by
  have hcont : ContinuousOn (fun z ↦ conjWirtingerDeriv f z 1) Ω :=
    (hf.conjWirtingerDeriv_apply_of_isOpen hΩ (m := 0) (by simp) 1).continuousOn
  obtain ⟨M, hM⟩ := (Metric.isCompact_of_isClosed_isBounded isClosed_closure
    hbounded.closure).exists_bound_of_continuousOn (hcont.mono hclosure)
  exact (integrableOn_sub_inv_smul_of_isBounded hbounded.closure
    ((hcont.mono hclosure).aestronglyMeasurable isClosed_closure.measurableSet)
    (ae_restrict_of_forall_mem isClosed_closure.measurableSet hM) ξ).mono_set subset_closure

/-! ### Punctured Cauchy–Pompeiu identity -/

section PuncturedHelpers

open scoped Classical in
private theorem isIn_and_isNullHomologous_sub_circleCycle {Ω Δ : Set ℂ} (hΔ : IsOpen Δ)
    (hclosure : closure Δ ⊆ Ω) (C : Contour.Cycle) (htrace : C.trace ⊆ frontier Δ)
    (hindex : ∀ z ∉ C.trace, C.windingNumber z = if z ∈ Δ then 1 else 0)
    {ξ : ℂ} {ε : ℝ} (hε : 0 < ε) (hball : closedBall ξ ε ⊆ Δ) :
    (C - Contour.circleCycle ξ ε).IsIn (Ω \ closedBall ξ (ε / 2)) ∧
      (C - Contour.circleCycle ξ ε).IsNullHomologous (Ω \ closedBall ξ (ε / 2)) := by
  have hhalf : closedBall ξ (ε / 2) ⊆ ball ξ ε := closedBall_subset_ball (half_lt_self hε)
  have htr_C : C.trace ⊆ Ω \ closedBall ξ (ε / 2) := by
    intro z hz
    obtain ⟨hzcl, hzint⟩ := htrace hz
    exact ⟨hclosure hzcl, fun hzh ↦ hzint (hΔ.interior_eq.symm ▸ hball (ball_subset_closedBall
      (hhalf hzh)))⟩
  have htr_S : (Contour.circleCycle ξ ε).trace ⊆ Ω \ closedBall ξ (ε / 2) := by
    rw [Contour.Cycle.trace_circleCycle, abs_of_pos hε]
    exact fun z hz ↦ ⟨hclosure (subset_closure (hball (sphere_subset_closedBall hz))),
      fun hzh ↦ (mem_ball.mp (hhalf hzh)).ne (mem_sphere.mp hz)⟩
  refine ⟨by rw [Contour.Cycle.isIn_iff]
             exact (Contour.Cycle.trace_sub_subset _ _).trans (union_subset htr_C htr_S), ?_⟩
  rw [Contour.Cycle.isNullHomologous_iff]
  intro z hzU
  rw [map_sub]
  by_cases hzh : z ∈ closedBall ξ (ε / 2)
  · rw [hindex z (fun h ↦ (htr_C h).2 hzh),
      ite_eq_left (hball (ball_subset_closedBall (hhalf hzh))),
      Contour.Cycle.windingNumber_circleCycle_eq_one_of_dist_lt (mem_ball.mp (hhalf hzh)),
      sub_self]
  · have hzΩ : z ∉ Ω := fun h ↦ hzU ⟨h, hzh⟩
    have hzΔ : z ∉ Δ := fun h ↦ hzΩ (hclosure (subset_closure h))
    rw [hindex z (fun h ↦ hzΩ (htr_C h).1), ite_eq_right hzΔ,
      Contour.Cycle.windingNumber_circleCycle_eq_zero_of_lt_dist hε.le
        (not_le.mp fun hle ↦ hzΔ (hball (mem_closedBall.mpr hle))), sub_zero]

open scoped Classical in
private theorem windingWeight_sub_circleCycle_ae_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {Δ : Set ℂ} (C : Contour.Cycle)
    (hindex : ∀ z ∉ C.trace, C.windingNumber z = if z ∈ Δ then 1 else 0)
    {ξ : ℂ} {ε : ℝ} (hε : 0 < ε) (hball : closedBall ξ ε ⊆ Δ) (g : ℂ → E) :
    (fun z ↦ (C - Contour.circleCycle ξ ε).windingWeight z • g z) =ᵐ[volume]
      (Δ \ closedBall ξ ε).indicator g := by
  have hae (D : Contour.Cycle) : ∀ᵐ z ∂volume, z ∉ D.trace := by
    rw [ae_iff]; simpa only [not_not, ofPred_mem_eq] using D.addHaar_trace_eq_zero volume
  filter_upwards [hae C, hae (Contour.circleCycle ξ ε)] with z hzC hzS
  have hzCS : z ∉ (C - Contour.circleCycle ξ ε).trace := fun h ↦
    (Contour.Cycle.trace_sub_subset _ _ h).elim hzC hzS
  have hzne : dist z ξ ≠ ε := by
    rwa [Contour.Cycle.trace_circleCycle, abs_of_pos hε, mem_sphere] at hzS
  rw [Contour.Cycle.windingWeight_eq_of_notMem _ hzCS, map_sub, hindex z hzC]
  by_cases hzΔ : z ∈ Δ
  · rcases lt_or_gt_of_ne hzne with hlt | hgt
    · rw [ite_eq_left hzΔ, Contour.Cycle.windingNumber_circleCycle_eq_one_of_dist_lt hlt,
        sub_self, zero_re, zero_smul,
        indicator_of_notMem (s := Δ \ closedBall ξ ε) fun h ↦ h.2 (mem_closedBall.mpr hlt.le)]
    · rw [ite_eq_left hzΔ, Contour.Cycle.windingNumber_circleCycle_eq_zero_of_lt_dist hε.le hgt,
        sub_zero, one_re, one_smul,
        indicator_of_mem (s := Δ \ closedBall ξ ε) ⟨hzΔ, fun h ↦ hgt.not_ge (mem_closedBall.mp h)⟩]
  · rw [ite_eq_right hzΔ, Contour.Cycle.windingNumber_circleCycle_eq_zero_of_lt_dist hε.le
        (not_le.mp fun hle ↦ hzΔ (hball (mem_closedBall.mpr hle))),
      sub_zero, zero_re, zero_smul,
      indicator_of_notMem (s := Δ \ closedBall ξ ε) fun h ↦ hzΔ h.1]

end PuncturedHelpers

open scoped Classical in
/-- **Punctured Cauchy–Pompeiu identity.** For an open set `Ω`, an open set `Δ` with
`closure Δ ⊆ Ω`, a cycle `C` with `C.trace ⊆ frontier Δ` and winding number `1` on `Δ` and `0`
outside `Δ` off `C.trace`, and a real `C¹` map `f : ℂ → E` on `Ω`, excising
`closedBall ξ ε ⊆ Δ` (`ε > 0`) around `ξ` expresses the difference between the outer cycle integral
`C.integral (fun z ↦ (z - ξ)⁻¹ • f z)` and the small-circle integral
`∮ z in C(ξ, ε), (z - ξ)⁻¹ • f z` as
`(2 * I) • ∫ z in Δ \ closedBall ξ ε, (z - ξ)⁻¹ • \bar∂ f(z)`. -/
theorem Contour.Cycle.integral_sub_circleIntegral_sub_inv_smul_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {Ω Δ : Set ℂ} (hΩ : IsOpen Ω) (hΔ : IsOpen Δ)
    (hclosure : closure Δ ⊆ Ω) (C : Contour.Cycle) (htrace : C.trace ⊆ frontier Δ)
    (hindex : ∀ z ∉ C.trace, C.windingNumber z = if z ∈ Δ then 1 else 0)
    {f : ℂ → E} (hf : ContDiffOn ℝ 1 f Ω) {ξ : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall ξ ε ⊆ Δ) :
    C.integral (fun z ↦ (z - ξ)⁻¹ • f z) - (∮ z in C(ξ, ε), (z - ξ)⁻¹ • f z) =
      (2 * I : ℂ) • ∫ z in Δ \ closedBall ξ ε, (z - ξ)⁻¹ • conjWirtingerDeriv f z 1 := by
  set U_ε : Set ℂ := Ω \ closedBall ξ (ε / 2)
  have hU_ε : IsOpen U_ε := hΩ.sdiff isClosed_closedBall
  obtain ⟨htr_ε, hnull_ε⟩ :=
    isIn_and_isNullHomologous_sub_circleCycle hΔ hclosure C htrace hindex hε hball
  have hne : ∀ z ∈ U_ε, z - ξ ≠ 0 := fun z hz hsub ↦
    hz.2 (by rw [sub_eq_zero.mp hsub]; exact mem_closedBall_self (half_pos hε).le)
  have hF : ContDiffOn ℝ 1 (fun z ↦ (z - ξ)⁻¹ • f z) U_ε :=
    ((contDiffOn_id.sub contDiffOn_const).fun_inv hne).smul (hf.mono sdiff_subset)
  have hgreen := (C - Contour.circleCycle ξ ε)
    |>.integral_eq_two_mul_I_smul_integral_windingWeight_conjWirtingerDeriv hU_ε htr_ε hnull_ε hF
  rw [map_sub, Contour.Cycle.integral_circleCycle] at hgreen
  rw [hgreen]
  refine congrArg _ ?_
  calc
    (∫ z in U_ε, (C - Contour.circleCycle ξ ε).windingWeight z •
        conjWirtingerDeriv (fun w ↦ (w - ξ)⁻¹ • f w) z 1)
        = ∫ z in U_ε, (C - Contour.circleCycle ξ ε).windingWeight z •
            ((z - ξ)⁻¹ • conjWirtingerDeriv f z 1) :=
          setIntegral_congr_fun hU_ε.measurableSet fun z hz ↦ by
            have hinv : DifferentiableAt ℂ (fun w ↦ (w - ξ)⁻¹) z :=
              (differentiableAt_id.sub (differentiableAt_const ξ)).inv (hne z hz)
            rw [conjWirtingerDeriv_smul_apply (hinv.restrictScalars ℝ)
                ((hf.contDiffAt (hΩ.mem_nhds hz.1)).differentiableAt one_ne_zero) 1,
              hinv.conjWirtingerDeriv_eq_zero, zero_apply, zero_smul, add_zero]
    _ = ∫ z in U_ε, (Δ \ closedBall ξ ε).indicator
          (fun z ↦ (z - ξ)⁻¹ • conjWirtingerDeriv f z 1) z :=
          integral_congr_ae
            ((windingWeight_sub_circleCycle_ae_eq C hindex hε hball _).filter_mono ae_restrict_le)
    _ = ∫ z in Δ \ closedBall ξ ε, (z - ξ)⁻¹ • conjWirtingerDeriv f z 1 := by
          have hsub : Δ \ closedBall ξ ε ⊆ U_ε := fun z ⟨hzΔ, hzcl⟩ ↦
            ⟨hclosure (subset_closure hzΔ),
              fun hzh ↦ hzcl (closedBall_subset_closedBall (half_le_self hε.le) hzh)⟩
          rw [setIntegral_indicator (hΔ.sdiff isClosed_closedBall).measurableSet,
            inter_eq_right.mpr hsub]

/-! ### Full-boundary Cauchy–Pompeiu formulas -/

open scoped Classical in
/-- **Full-boundary Cauchy–Pompeiu formula (Banach-valued).** For an open set `Ω`, a bounded open
set `Δ` with `closure Δ ⊆ Ω`, a cycle `C` with `C.trace ⊆ frontier Δ` and winding number `1` on `Δ`
and `0` outside `Δ` off `C.trace`, a real `C¹` map `f : ℂ → E` on `Ω` into a complex Banach space
`E`, and `ξ ∈ Δ`,
`f ξ = (2πi)⁻¹ • C.integral (fun z ↦ (z - ξ)⁻¹ • f z) - π⁻¹ • ∫ z in Δ, (z - ξ)⁻¹ • \bar∂ f(z)`. -/
theorem cauchyPompeiu_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {Ω Δ : Set ℂ} (hΩ : IsOpen Ω) (hΔ : IsOpen Δ) (hbounded : IsBounded Δ)
    (hclosure : closure Δ ⊆ Ω) (C : Contour.Cycle) (htrace : C.trace ⊆ frontier Δ)
    (hindex : ∀ z ∉ C.trace, C.windingNumber z = if z ∈ Δ then 1 else 0)
    (f : ℂ → E) (hf : ContDiffOn ℝ 1 f Ω) {ξ : ℂ} (hξ : ξ ∈ Δ) :
    f ξ = (2 * (Real.pi : ℂ) * I)⁻¹ • C.integral (fun z ↦ (z - ξ)⁻¹ • f z) -
      (Real.pi : ℂ)⁻¹ • ∫ z in Δ, (z - ξ)⁻¹ • conjWirtingerDeriv f z 1 := by
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
    have hpunct := C.integral_sub_circleIntegral_sub_inv_smul_eq hΩ hΔ hclosure htrace hindex hf
      hε ((closedBall_subset_ball (hεδ.trans (half_lt_self hδ))).trans hballδ)
    exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (sub_eq_iff_eq_add.mp hpunct).symm)
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
          (inv_smul_smul₀ (mul_ne_zero (mul_ne_zero two_ne_zero hpi) I_ne_zero) _).symm
    _ = (2 * (Real.pi : ℂ) * I)⁻¹ • C.integral (fun z ↦ (z - ξ)⁻¹ • f z) -
          (Real.pi : ℂ)⁻¹ • ∫ z in Δ, (z - ξ)⁻¹ • conjWirtingerDeriv f z 1 := by
          rw [heq, smul_sub, smul_smul, hcoeff]

open scoped Classical in
/-- **Full-boundary Cauchy–Pompeiu formula (`\bar∂` normalization).** Under the hypotheses of
`TauCeti.cauchyPompeiu_smul` (an open set `Ω`, a bounded open set `Δ` with `closure Δ ⊆ Ω`, a
cycle `C` with `C.trace ⊆ frontier Δ` and winding number `1` on `Δ` and `0` outside `Δ` off
`C.trace`), for `f : ℂ → ℂ` real `C¹` on `Ω` and `ξ ∈ Δ`,
`f ξ = (2πi)⁻¹ * C.integral (fun z ↦ f z / (z - ξ)) - π⁻¹ * ∫ z in Δ, \bar∂ f(z) / (z - ξ)`. -/
theorem cauchyPompeiu_conjWirtingerDeriv {Ω Δ : Set ℂ} (hΩ : IsOpen Ω) (hΔ : IsOpen Δ)
    (hbounded : IsBounded Δ) (hclosure : closure Δ ⊆ Ω)
    (C : Contour.Cycle) (htrace : C.trace ⊆ frontier Δ)
    (hindex : ∀ z ∉ C.trace, C.windingNumber z = if z ∈ Δ then 1 else 0)
    (f : ℂ → ℂ) (hf : ContDiffOn ℝ 1 f Ω) {ξ : ℂ} (hξ : ξ ∈ Δ) :
    f ξ = (2 * (Real.pi : ℂ) * I)⁻¹ * C.integral (fun z ↦ f z / (z - ξ)) -
      (Real.pi : ℂ)⁻¹ * ∫ z in Δ, conjWirtingerDeriv f z 1 / (z - ξ) := by
  simpa only [smul_eq_mul, inv_mul_eq_div] using
    cauchyPompeiu_smul hΩ hΔ hbounded hclosure C htrace hindex f hf hξ

open scoped Classical in
/-- **Full-boundary Cauchy–Pompeiu formula** for a bounded open region `Δ` with a native contour
cycle `C` whose trace lies in `frontier Δ` and whose winding number off `C.trace` is `1` inside `Δ`
and `0` outside `Δ`, written with the real directional derivatives `f_x + i f_y = 2 \bar∂ f`. -/
theorem cauchyPompeiu {Ω Δ : Set ℂ} (hΩ : IsOpen Ω) (hΔ : IsOpen Δ)
    (hbounded : Bornology.IsBounded Δ) (hclosure : closure Δ ⊆ Ω)
    (C : TauCeti.Contour.Cycle) (htrace : C.trace ⊆ frontier Δ)
    (hindex : ∀ z ∉ C.trace,
      TauCeti.Contour.Cycle.windingNumber z C = if z ∈ Δ then 1 else 0)
    (f : ℂ → ℂ) (hf : ContDiffOn ℝ 1 f Ω) {ξ : ℂ} (hξ : ξ ∈ Δ) :
    f ξ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        TauCeti.Contour.Cycle.integral (fun z => f z / (z - ξ)) C -
      (2 * (Real.pi : ℂ))⁻¹ *
        ∫ z in Δ, (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / (z - ξ) := by
  rw [cauchyPompeiu_conjWirtingerDeriv hΩ hΔ hbounded hclosure C htrace hindex f hf hξ]
  have hdbar : (fun z ↦ (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / (z - ξ)) =
      fun z ↦ (2 : ℂ) * (conjWirtingerDeriv f z 1 / (z - ξ)) := funext fun z ↦ by
    have h2 := fderiv_apply_one_add_I_smul_fderiv_apply_I f z
    simp only [smul_eq_mul] at h2
    rw [h2, mul_div_assoc]
  rw [hdbar, integral_const_mul, ← mul_assoc]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  congr 2; field_simp [hpi]

/-! ### Cauchy–Pompeiu on finitely connected Jordan regions -/

section JordanRegion

variable {ι : Type*}

/-- **Cauchy–Pompeiu formula on a finitely connected Jordan region (Banach-valued).** Given an
outer simple closed piecewise-`C¹` curve `γ₀` and simple closed piecewise-`C¹` hole curves
`(γ i)_{i ∈ s}` whose filled hulls are pairwise disjoint and contained in the inside of `γ₀`, let
`Δ := (filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \`
`⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b)` be the resulting finitely connected Jordan
region. For any real `C¹` map `f : ℂ → E` on an open neighborhood `Ω` of `closure Δ` into a
complex Banach space `E` and any `ξ ∈ Δ`, `f ξ` is represented by integrating over
`Contour.jordanBoundaryCycle γ₀ s γ` and over `Δ`. -/
theorem cauchyPompeiu_jordanBoundaryCycle_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {γ₀ : Contour.PiecewiseC1ClosedCurve} {s : Finset ι}
    {γ : ι → Contour.PiecewiseC1ClosedCurve} {Ω : Set ℂ}
    (hab₀ : γ₀.a < γ₀.b) (hinj₀ : InjOn γ₀ (Ico γ₀.a γ₀.b))
    (hab : ∀ i ∈ s, (γ i).a < (γ i).b) (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (γ i).a (γ i).b))
    (hsub : ∀ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
      filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b))
    (hΩ : IsOpen Ω)
    (hclosure : closure ((filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \
      ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b)) ⊆ Ω)
    (f : ℂ → E) (hf : ContDiffOn ℝ 1 f Ω) {ξ : ℂ}
    (hξ : ξ ∈ (filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \
      ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b)) :
    f ξ = (2 * (Real.pi : ℂ) * I)⁻¹ •
        (Contour.jordanBoundaryCycle γ₀ s γ).integral (fun z ↦ (z - ξ)⁻¹ • f z) -
      (Real.pi : ℂ)⁻¹ • ∫ z in (filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \
          ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b),
        (z - ξ)⁻¹ • conjWirtingerDeriv f z 1 := by
  have hJ₀ := γ₀.isJordanCurve_image hab₀ hinj₀
  exact cauchyPompeiu_smul hΩ
    (hJ₀.isClosed.isOpen_filledHull_sdiff_biUnion s fun i hi ↦
      ((γ i).isJordanCurve_image (hab i hi) (hinj i hi)).isClosed)
    ((isBounded_filledHull.mpr hJ₀.isCompact.isBounded).subset (sdiff_subset.trans sdiff_subset))
    hclosure (Contour.jordanBoundaryCycle γ₀ s γ)
    (Contour.Cycle.trace_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj).le
    (fun _ hz ↦ by
      rw [Contour.Cycle.windingNumber_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj hz]
      congr)
    f hf hξ

/-- **Scalar Cauchy–Pompeiu formula on a finitely connected Jordan region.** Given an outer simple
closed piecewise-`C¹` curve `γ₀` and simple closed piecewise-`C¹` hole curves `(γ i)_{i ∈ s}`
whose filled hulls are pairwise disjoint and contained in the inside of `γ₀`, let
`Δ := (filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \`
`⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b)` be the resulting finitely connected Jordan
region. For any real `C¹` function `f : ℂ → ℂ` on an open neighborhood `Ω` of `closure Δ` and
any `ξ ∈ Δ`, `f ξ` equals `(2πi)⁻¹` times the boundary integral of `z ↦ f z / (z - ξ)` over
`Contour.jordanBoundaryCycle γ₀ s γ` minus `π⁻¹` times the area integral of
`z ↦ \bar∂ f(z) / (z - ξ)` over `Δ`. -/
theorem cauchyPompeiu_jordanBoundaryCycle {γ₀ : Contour.PiecewiseC1ClosedCurve} {s : Finset ι}
    {γ : ι → Contour.PiecewiseC1ClosedCurve} {Ω : Set ℂ}
    (hab₀ : γ₀.a < γ₀.b) (hinj₀ : InjOn γ₀ (Ico γ₀.a γ₀.b))
    (hab : ∀ i ∈ s, (γ i).a < (γ i).b) (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (γ i).a (γ i).b))
    (hsub : ∀ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
      filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b))
    (hΩ : IsOpen Ω)
    (hclosure : closure ((filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \
      ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b)) ⊆ Ω)
    (f : ℂ → ℂ) (hf : ContDiffOn ℝ 1 f Ω) {ξ : ℂ}
    (hξ : ξ ∈ (filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \
      ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b)) :
    f ξ = (2 * (Real.pi : ℂ) * I)⁻¹ *
        (Contour.jordanBoundaryCycle γ₀ s γ).integral (fun z ↦ f z / (z - ξ)) -
      (Real.pi : ℂ)⁻¹ * ∫ z in (filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \
          ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b),
        conjWirtingerDeriv f z 1 / (z - ξ) := by
  simpa only [smul_eq_mul, inv_mul_eq_div] using
    cauchyPompeiu_jordanBoundaryCycle_smul hab₀ hinj₀ hab hinj hsub hdisj hΩ hclosure f hf hξ

end JordanRegion

end TauCeti

end

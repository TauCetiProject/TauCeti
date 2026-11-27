/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyKernel
public import TauCeti.Analysis.Complex.Wirtinger.Cycle
public import TauCeti.Analysis.Contour.Cycle.Jordan
public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Contour.Cycle.Circle
import TauCeti.MeasureTheory.Integral.Circle.Integral
import TauCeti.MeasureTheory.Integral.DominatedConvergence

/-!
# The Cauchy–Pompeiu formula on bounded domains with contour-cycle boundaries

Let `Δ` be an open plane set with `closure Δ ⊆ Ω` (`Ω` open), and let `C : Contour.Cycle` have
`C.IsIn Ω`. Off `C.trace`, suppose `C` has winding number `1` on `Δ` and `0` outside `Δ`. For a
real `C¹` map `f : ℂ → E` on `Ω` into a complex Banach space `E`, applying the winding-weighted
complex Green formula to `(z - ξ)⁻¹ • f z` on `C - circleCycle ξ ε` (for `ξ ∉ C.trace` and
`closedBall ξ ε ⊆ Δ`) and passing `ε → 0⁺` proves the full-boundary **Cauchy–Pompeiu formula**:

`f ξ = (2πi)⁻¹ • C.integral (fun z ↦ (z - ξ)⁻¹ • f z) - π⁻¹ • ∫ z in Δ, (z - ξ)⁻¹ • \bar∂ f(z)`,

together with its specialization to finitely connected Jordan regions via
`TauCeti.Contour.jordanRegion` and `TauCeti.Contour.jordanBoundaryCycle`.

## Main results

* `TauCeti.integrableOn_sub_inv_smul_conjWirtingerDeriv`
* `TauCeti.Contour.Cycle.integral_sub_circleIntegral_sub_inv_smul_eq`
* `TauCeti.cauchyPompeiu_smul`, `TauCeti.cauchyPompeiu`
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
private theorem isIn_and_isNullHomologous_sub_circleCycle {Ω Δ : Set ℂ}
    (hΔΩ : Δ ⊆ Ω) (C : Contour.Cycle) (htrace : C.IsIn Ω)
    (hindex : ∀ z ∉ C.trace, C.windingNumber z = if z ∈ Δ then 1 else 0)
    {ξ : ℂ} {ε : ℝ} (hε : 0 < ε) (hball : closedBall ξ ε ⊆ Δ) (hξtr : ξ ∉ C.trace) :
    ∃ r, 0 < r ∧ r < ε ∧
      (C - Contour.circleCycle ξ ε).IsIn (Ω \ closedBall ξ r) ∧
      (C - Contour.circleCycle ξ ε).IsNullHomologous (Ω \ closedBall ξ r) := by
  obtain ⟨δ, hδ, hballδ⟩ := Metric.isOpen_iff.mp C.isCompact_trace.isClosed.isOpen_compl ξ hξtr
  set r : ℝ := min (ε / 2) (δ / 2)
  have hr0 : 0 < r := lt_min (half_pos hε) (half_pos hδ)
  have hrε : r < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hrδ : r < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  have hmiss : Disjoint (closedBall ξ r) C.trace := Set.disjoint_left.mpr fun z hz htr ↦
    hballδ (mem_ball.mpr ((mem_closedBall.mp hz).trans_lt hrδ)) htr
  have htr_C : C.trace ⊆ Ω \ closedBall ξ r := fun z hz ↦
    ⟨C.isIn_iff.mp htrace hz, fun hzr ↦ Set.disjoint_left.mp hmiss hzr hz⟩
  have htr_S : (Contour.circleCycle ξ ε).trace ⊆ Ω \ closedBall ξ r := by
    rw [Contour.Cycle.trace_circleCycle, abs_of_pos hε]
    exact fun z hz ↦ ⟨hΔΩ (hball (sphere_subset_closedBall hz)),
      fun hzr ↦ (mem_closedBall.mp hzr).not_gt (hrε.trans_eq (mem_sphere.mp hz).symm)⟩
  refine ⟨r, hr0, hrε, ?_, ?_⟩
  · rw [Contour.Cycle.isIn_iff]
    exact (Contour.Cycle.trace_sub_subset _ _).trans (union_subset htr_C htr_S)
  · rw [Contour.Cycle.isNullHomologous_iff]
    intro z hzU
    rw [map_sub]
    by_cases hzr : z ∈ closedBall ξ r
    · have hzε : dist z ξ < ε := (mem_closedBall.mp hzr).trans_lt hrε
      rw [hindex z (fun h ↦ (htr_C h).2 hzr), ite_eq_left (hball (ball_subset_closedBall hzε)),
        Contour.Cycle.windingNumber_circleCycle_eq_one_of_dist_lt hzε, sub_self]
    · have hzΩ : z ∉ Ω := fun h ↦ hzU ⟨h, hzr⟩
      have hzΔ : z ∉ Δ := fun h ↦ hzΩ (hΔΩ h)
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
  have hae (D : Contour.Cycle) : ∀ᵐ z ∂volume, z ∉ D.trace :=
    compl_mem_ae_iff.mpr (D.addHaar_trace_eq_zero volume)
  filter_upwards [hae C, hae (Contour.circleCycle ξ ε)] with z hzC hzS
  have hzCS : z ∉ (C - Contour.circleCycle ξ ε).trace := fun h ↦
    (Contour.Cycle.trace_sub_subset _ _ h).elim hzC hzS
  have hwt : (C - Contour.circleCycle ξ ε).windingWeight z =
      Δ.indicator (1 : ℂ → ℝ) z - (ball ξ ε).indicator (1 : ℂ → ℝ) z := by
    rw [Contour.Cycle.windingWeight_eq_of_notMem _ hzCS, map_sub, sub_re, hindex z hzC,
      ← (Contour.circleCycle ξ ε).windingWeight_eq_of_notMem hzS,
      Contour.Cycle.windingWeight_circleCycle ξ hε.le]
    by_cases hzΔ : z ∈ Δ <;> simp [hzΔ]
  rw [hwt, ← Pi.sub_apply, ← Set.indicator_sdiff (ball_subset_closedBall.trans hball),
    ← congrFun (Set.indicator_smul_left _ _ _) z]
  simp only [Pi.one_apply, one_smul]
  have hne : dist z ξ ≠ ε := by
    rwa [Contour.Cycle.trace_circleCycle, abs_of_pos hε, mem_sphere] at hzS
  have hmem : z ∈ ball ξ ε ↔ z ∈ closedBall ξ ε := by
    rw [mem_ball, mem_closedBall]
    exact ⟨le_of_lt, fun hle ↦ lt_of_le_of_ne hle hne⟩
  simp only [indicator_apply, Set.mem_sdiff, hmem]

end PuncturedHelpers

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
    isIn_and_isNullHomologous_sub_circleCycle hΔΩ C htrace hindex hε hball hξtr
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
            ((windingWeight_sub_circleCycle_ae_eq C hindex hε hball _).filter_mono ae_restrict_le)
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

/-! ### Cauchy–Pompeiu on finitely connected Jordan regions -/

section JordanRegion

variable {ι : Type*}

/-- **Cauchy–Pompeiu formula on a finitely connected Jordan region (Banach-valued).** Given an
outer simple closed absolutely continuous curve `γ₀` and simple closed absolutely continuous hole
curves `(γ i)_{i ∈ s}` whose filled hulls are pairwise disjoint and contained in the inside of `γ₀`,
let `Δ := Contour.jordanRegion γ₀ s γ` be the resulting finitely connected Jordan region. For any
real `C¹` map `f : ℂ → E` on an open neighborhood `Ω` of `closure Δ` into a complex Banach space `E`
and any `ξ ∈ Δ`, `f ξ` is represented by integrating over `Contour.jordanBoundaryCycle γ₀ s γ` and
over `Δ`. -/
theorem cauchyPompeiu_jordanBoundaryCycle_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {γ₀ : Contour.AbsolutelyContinuousClosedCurve}
    {s : Finset ι} {γ : ι → Contour.AbsolutelyContinuousClosedCurve} {Ω : Set ℂ}
    (hab₀ : γ₀.a ≠ γ₀.b) (hinj₀ : InjOn γ₀ (Ico (min γ₀.a γ₀.b) (max γ₀.a γ₀.b)))
    (hab : ∀ i ∈ s, (γ i).a ≠ (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (min (γ i).a (γ i).b) (max (γ i).a (γ i).b)))
    (hsub : ∀ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
      filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b))
    (hΩ : IsOpen Ω) (hclosure : closure (Contour.jordanRegion γ₀ s γ) ⊆ Ω)
    (f : ℂ → E) (hf : ContDiffOn ℝ 1 f Ω) {ξ : ℂ} (hξ : ξ ∈ Contour.jordanRegion γ₀ s γ) :
    f ξ = (2 * (Real.pi : ℂ) * I)⁻¹ •
        (Contour.jordanBoundaryCycle γ₀ s γ).integral (fun z ↦ (z - ξ)⁻¹ • f z) -
      (Real.pi : ℂ)⁻¹ • ∫ z in Contour.jordanRegion γ₀ s γ,
        (z - ξ)⁻¹ • conjWirtingerDeriv f z 1 :=
  cauchyPompeiu_smul hΩ (Contour.isOpen_jordanRegion hab₀ hinj₀ hab hinj) hclosure
    (Contour.jordanBoundaryCycle γ₀ s γ)
    (Contour.Cycle.isIn_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj hclosure)
    (fun _ hz ↦ Contour.Cycle.windingNumber_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj hz)
    f hf hξ
    (Contour.Cycle.notMem_trace_jordanBoundaryCycle_of_mem hab₀ hinj₀ hab hinj hsub hdisj hξ)

/-- **Cauchy–Pompeiu formula on a finitely connected Jordan region.** Given an outer simple closed
absolutely continuous curve `γ₀` and simple closed absolutely continuous hole curves
`(γ i)_{i ∈ s}` whose filled hulls are pairwise disjoint and contained in the inside of `γ₀`, let
`Δ := Contour.jordanRegion γ₀ s γ` be the resulting finitely connected Jordan region. For any real
`C¹` function `f : ℂ → ℂ` on an open neighborhood `Ω` of `closure Δ` and any `ξ ∈ Δ`, `f ξ` is
represented by integrating over `Contour.jordanBoundaryCycle γ₀ s γ` and over `Δ`, written with the
real directional derivatives `f_x + i f_y = 2 \bar∂ f`. -/
theorem cauchyPompeiu_jordanBoundaryCycle {γ₀ : Contour.AbsolutelyContinuousClosedCurve}
    {s : Finset ι} {γ : ι → Contour.AbsolutelyContinuousClosedCurve} {Ω : Set ℂ}
    (hab₀ : γ₀.a ≠ γ₀.b) (hinj₀ : InjOn γ₀ (Ico (min γ₀.a γ₀.b) (max γ₀.a γ₀.b)))
    (hab : ∀ i ∈ s, (γ i).a ≠ (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (min (γ i).a (γ i).b) (max (γ i).a (γ i).b)))
    (hsub : ∀ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
      filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b))
    (hΩ : IsOpen Ω) (hclosure : closure (Contour.jordanRegion γ₀ s γ) ⊆ Ω)
    (f : ℂ → ℂ) (hf : ContDiffOn ℝ 1 f Ω) {ξ : ℂ} (hξ : ξ ∈ Contour.jordanRegion γ₀ s γ) :
    f ξ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (Contour.jordanBoundaryCycle γ₀ s γ).integral (fun z ↦ f z / (z - ξ)) -
      (2 * (Real.pi : ℂ))⁻¹ *
        ∫ z in Contour.jordanRegion γ₀ s γ,
          (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / (z - ξ) :=
  cauchyPompeiu hΩ (Contour.isOpen_jordanRegion hab₀ hinj₀ hab hinj) hclosure
    (Contour.jordanBoundaryCycle γ₀ s γ)
    (Contour.Cycle.isIn_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj hclosure)
    (fun _ hz ↦ Contour.Cycle.windingNumber_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj hz)
    f hf hξ
    (Contour.Cycle.notMem_trace_jordanBoundaryCycle_of_mem hab₀ hinj₀ hab hinj hsub hdisj hξ)

end JordanRegion

end TauCeti

end

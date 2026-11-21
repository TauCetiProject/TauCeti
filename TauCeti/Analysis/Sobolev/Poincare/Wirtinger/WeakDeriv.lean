/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Analysis.Convex.Exhaustion
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.Analysis.Sobolev.Mollification.Local
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.MeasureTheory.Function.LocallyAEConst
import TauCeti.MeasureTheory.Function.Lp.Const
import TauCeti.MeasureTheory.Function.LpSeminorm.Ball
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The Poincaré–Wirtinger inequality for weakly differentiable Banach-valued functions

Let `E` be a finite-dimensional real normed space of dimension `n` with an additive Haar measure
`μ`, let `F` be a real Banach space, and let `u : E → F` have weak Fréchet derivative `Du` on an
open set `Ω` (`TauCeti.HasWeakFDerivOn μ Ω u Du`). This file transfers the `C¹`
Poincaré–Wirtinger inequality (`TauCeti.eLpNorm_sub_setAverage_le_of_convex`) to weakly
differentiable functions by local mollification and convex exhaustion, with no inner-product
assumption on `E`, no measurability assumption on the averaging subset `S`, and no a priori `Lᵖ`
hypothesis on `u`.

On a bounded convex open set `Ω`, if `Du ∈ Lᵖ(Ω)` for `1 ≤ p < ∞`, then `u ∈ Lᵖ(Ω)` automatically
(`TauCeti.HasWeakFDerivOn.memLp_of_convex`), and for every subset `S ⊆ Ω` of positive measure,

`‖u - ⨍_S u‖_{Lᵖ(Ω)} ≤ μ(B(0, 1)) * (diam Ω) ^ (n + 1) / μ(S) * ‖Du‖_{Lᵖ(Ω)}`.

On a ball `B(x, r) ⊆ Ω`, the constant simplifies to `2 ^ (n + 1) * r`. Combining the `L¹` ball
estimate with Hölder's inequality bounds the mean oscillation on `B(x, r)` for every exponent
`1 ≤ p ≤ ∞`:

`⨍⁻ y in B(x, r), ‖u y - u_{B(x, r)}‖ₑ`
`  ≤ 2 ^ (n + 1) ω ^ (-1 / p) r ^ (1 - n / p) ‖Du‖_{Lᵖ(B(x, r))}`.

At the borderline exponent `p = n` (in positive dimension `n ≥ 1`), the radius cancels completely,
yielding a scale-invariant mean-oscillation bound. Two classical consequences follow immediately:

* A weakly differentiable function with vanishing weak derivative on a preconnected open set is
  almost everywhere constant (`TauCeti.HasWeakFDerivOn.exists_ae_eq_const_of_deriv_ae_eq_zero`).
* Globally defined weakly differentiable functions with `Du ∈ Lⁿ` have bounded and vanishing mean
  oscillation: `W^{1,n} ⊆ VMO ⊆ BMO` (`TauCeti.HasWeakFDerivOn.memBMO`,
  `TauCeti.HasWeakFDerivOn.memVMO`).

## Main declarations

* `TauCeti.HasWeakFDerivOn.memLp_of_convex`: on a bounded convex open set, `Du ∈ Lᵖ` implies
  `u ∈ Lᵖ` (`1 ≤ p < ∞`).
* `TauCeti.HasWeakFDerivOn.eLpNorm_sub_setAverage_le_of_convex` and
  `TauCeti.HasWeakFDerivOn.lintegral_enorm_sub_setAverage_rpow_le_of_convex`: the
  Poincaré–Wirtinger inequality on a bounded convex open set.
* `TauCeti.HasWeakFDerivOn.eLpNorm_sub_setAverage_ball_le` and
  `TauCeti.HasWeakFDerivOn.setLIntegral_enorm_sub_setAverage_ball_le`: the ball forms with
  constant `2 ^ (n + 1) * r`.
* `TauCeti.HasWeakFDerivOn.setLAverage_enorm_sub_setAverage_ball_le_mul_measure_rpow`,
  `TauCeti.HasWeakFDerivOn.setLAverage_enorm_sub_setAverage_ball_le_mul_rpow`, and
  `TauCeti.HasWeakFDerivOn.setLAverage_enorm_sub_setAverage_ball_le`: mean oscillation bounds on
  balls for all `1 ≤ p ≤ ∞` and at the scale-invariant exponent `p = n`.
* `TauCeti.HasWeakFDerivOn.exists_ae_eq_const_of_deriv_ae_eq_zero`: constancy on preconnected open
  sets when `Du = 0` a.e.
* `TauCeti.HasWeakFDerivOn.bmoSeminorm_le`, `TauCeti.HasWeakFDerivOn.memBMO`,
  `TauCeti.HasWeakFDerivOn.vmoModulus_le`, and `TauCeti.HasWeakFDerivOn.memVMO`: `W^{1,n}` embeds
  into `VMO` and `BMO`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 7.16.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 5.8.1.
* H. Brezis, L. Nirenberg, *Degree theory and BMO; Part I: Compact manifolds without boundaries*,
  Selecta Math. (N.S.) **1** (1995), 197–263.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped Convolution ENNReal NNReal Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {u : E → F} {Du : E → E →L[ℝ] F}

/-! ### Local approximation on a relatively compact convex subdomain -/

/-- The Poincaré–Wirtinger inequality on a convex open subdomain `U` with compact closure in `Ω`,
obtained by smoothing the zero extension of `u` from an intermediate neighbourhood `V`. -/
private theorem eLpNorm_sub_setAverage_le_of_isCompact_closure (hu : HasWeakFDerivOn μ Ω u Du)
    {U : Opens E} (hUc : Convex ℝ (U : Set E)) (hUcomp : IsCompact (closure (U : Set E)))
    (hUΩ : closure (U : Set E) ⊆ Ω) {S : Set E} (hSU : S ⊆ U) (hS0 : μ S ≠ 0)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hDu : MemLp Du p (μ.restrict Ω)) :
    eLpNorm (fun x => u x - ⨍ y in S, u y ∂μ) p (μ.restrict U) ≤
      ENNReal.ofReal (μ.real (ball 0 1) * diam (U : Set E) ^ (finrank ℝ E + 1) / μ.real S) *
        eLpNorm Du p (μ.restrict Ω) := by
  have : CompleteSpace F := hu.completeSpace
  have hUb : Bornology.IsBounded (U : Set E) := hUcomp.isBounded.subset subset_closure
  obtain ⟨-, -, V, hUV, hVΩ, -, huV, -, -, -, -⟩ := hu.exists_open_memLp_indicator hUcomp hUΩ
  have hDuV : MemLp Du p (μ.restrict V) := hDu.mono_measure (Measure.restrict_mono hVΩ le_rfl)
  obtain ⟨v, hv_cd, hv_deriv, hv_L1, -⟩ :=
    hu.exists_contDiff_tendsto_eLpNorm hUcomp hUV hVΩ le_rfl ENNReal.one_ne_top huV hp1 hp hDuV
  have hv_S : Tendsto (fun n => eLpNorm (v n - u) 1 (μ.restrict S)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hv_L1 (fun _ => zero_le)
      fun n => eLpNorm_mono_measure _ (Measure.restrict_mono hSU le_rfl)
  have hint : Tendsto (fun n => ∫ y in S, v n y ∂μ) atTop (𝓝 (∫ y in S, u y ∂μ)) :=
    tendsto_integral_of_L1' u
      (.of_forall fun n =>
        ((hv_cd n).continuous.continuousOn.integrableOn_compact hUcomp).mono_set
          (hSU.trans subset_closure))
      hv_S
  have havg : Tendsto (fun n => ⨍ y in S, v n y ∂μ) atTop (𝓝 (⨍ y in S, u y ∂μ)) := by
    simpa only [setAverage_eq] using hint.const_smul (μ.real S)⁻¹
  have hum : AEStronglyMeasurable u (μ.restrict U) :=
    hu.locallyIntegrableOn.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono (subset_closure.trans hUΩ) le_rfl)
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hv_L1).exists_seq_tendsto_ae
  calc eLpNorm (fun x => u x - ⨍ y in S, u y ∂μ) p (μ.restrict U)
      ≤ atTop.liminf fun k =>
          eLpNorm (fun x => v (ns k) x - ⨍ y in S, v (ns k) y ∂μ) p (μ.restrict U) :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm
          (fun k => (hv_cd (ns k)).continuous.aestronglyMeasurable.sub aestronglyMeasurable_const)
          _ (hum.sub aestronglyMeasurable_const)
          (hae.mono fun x hx => hx.sub (havg.comp hns.tendsto_atTop))
    _ ≤ atTop.liminf fun _ =>
          ENNReal.ofReal (μ.real (ball 0 1) * diam (U : Set E) ^ (finrank ℝ E + 1) / μ.real S) *
            eLpNorm Du p (μ.restrict Ω) :=
        liminf_le_liminf (.of_forall fun k =>
          (eLpNorm_sub_setAverage_le_of_convex hUc hUb
            ((hv_cd (ns k)).of_le (by simp)).contDiffOn hSU hS0 hp1 hp).trans
            (mul_le_mul_right ((hv_deriv (ns k)).trans
              (eLpNorm_mono_measure _ (Measure.restrict_mono hVΩ le_rfl))) _))
    _ = _ := liminf_const _

/-- The Poincaré–Wirtinger inequality on a bounded convex open set `Ω`, assuming `u` is integrable
on `S` and `Du ∈ Lᵖ(Ω)`. The averaging set `S` need not be measurable: it is replaced by its
measurable hull inside `Ω`, which induces the exact same restricted measure. -/
private theorem eLpNorm_sub_setAverage_le_of_convex_of_integrableOn
    (hu : HasWeakFDerivOn μ Ω u Du) (hΩc : Convex ℝ (Ω : Set E))
    (hΩb : Bornology.IsBounded (Ω : Set E)) {S : Set E} (hS : S ⊆ Ω) (hS0 : μ S ≠ 0)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) (huS : IntegrableOn u S μ)
    (hDu : MemLp Du p (μ.restrict Ω)) :
    eLpNorm (fun x => u x - ⨍ y in S, u y ∂μ) p (μ.restrict Ω) ≤
      ENNReal.ofReal (μ.real (ball 0 1) * diam (Ω : Set E) ^ (finrank ℝ E + 1) / μ.real S) *
        eLpNorm Du p (μ.restrict Ω) := by
  -- Replace `S` by the measurable set `S' = Ω ∩ toMeasurable μ S`, which has the same restriction.
  have hSfin : μ S ≠ ∞ := ne_top_of_le_ne_top hΩb.measure_lt_top.ne (measure_mono hS)
  set S' : Set E := (Ω : Set E) ∩ toMeasurable μ S
  have hS'm : MeasurableSet S' :=
    Ω.isOpen.measurableSet.inter (measurableSet_toMeasurable μ S)
  have hS'rest : μ.restrict S' = μ.restrict S :=
    Measure.restrict_inter_toMeasurable hSfin Ω.isOpen.measurableSet hS
  have hS'meas : μ S' = μ S := by
    rw [← Measure.restrict_apply_univ, hS'rest, Measure.restrict_apply_univ]
  have hS'real : μ.real S' = μ.real S := by rw [measureReal_def, hS'meas, measureReal_def]
  have hS'avg : (⨍ y in S', u y ∂μ) = ⨍ y in S, u y ∂μ := by rw [hS'rest]
  have huS' : IntegrableOn u S' μ := by rwa [IntegrableOn, hS'rest]
  rw [← hS'avg, ← hS'real]
  -- Exhaust `Ω` by relatively compact convex open sets `V n ↑ Ω`.
  obtain ⟨V, hVmono, hVopen, hVconv, hVcomp, -, hVclosure, hVunion⟩ :=
    exists_seq_isOpen_convex_isCompact_closure_subset_iUnion_eq Ω.isOpen hΩc
  have hS'0 : μ S' ≠ 0 := hS'meas ▸ hS0
  have hS'fin : μ S' ≠ ∞ := hS'meas ▸ hSfin
  have hS'Rpos : 0 < μ.real S' := ENNReal.toReal_pos hS'0 hS'fin
  have hS'V : S' ⊆ ⋃ n, V n := hVunion ▸ inter_subset_left
  have hmeasR : Tendsto (fun n => μ.real (S' ∩ V n)) atTop (𝓝 (μ.real S')) :=
    tendsto_measureReal_inter_of_monotone hVmono hS'V hS'fin
  have ha : Tendsto (fun n => ⨍ y in S' ∩ V n, u y ∂μ) atTop (𝓝 (⨍ y in S', u y ∂μ)) :=
    tendsto_setAverage_inter_of_monotone hVmono hS'V
      (fun n => (hS'm.inter (hVopen n).measurableSet).nullMeasurableSet) hS'fin huS'
  -- Bound each piece by Fatou along the exhaustion.
  set K : ℝ := μ.real (ball (0 : E) 1) * diam (Ω : Set E) ^ (finrank ℝ E + 1)
  have hlim := eLpNorm_sub_const_restrict_le_liminf (μ := μ) (p := p)
    hu.locallyIntegrableOn.aestronglyMeasurable
    (fun n => (hVopen n).measurableSet) hVmono hVunion ha
  have hbound : ∀ᶠ n in atTop,
      eLpNorm (fun x => u x - ⨍ y in S' ∩ V n, u y ∂μ) p (μ.restrict (V n)) ≤
        ENNReal.ofReal (K / μ.real (S' ∩ V n)) * eLpNorm Du p (μ.restrict Ω) := by
    filter_upwards [hmeasR.eventually (lt_mem_nhds hS'Rpos)] with n hn
    have hne : μ (S' ∩ V n) ≠ 0 := fun h0 => by
      rw [measureReal_def, h0] at hn
      simp at hn
    refine (eLpNorm_sub_setAverage_le_of_isCompact_closure (U := ⟨V n, hVopen n⟩) hu
      (hVconv n) (hVcomp n) (hVclosure n) inter_subset_right hne hp1 hp hDu).trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
    have hVsub : V n ⊆ (Ω : Set E) := subset_closure.trans (hVclosure n)
    have hdiam : diam (V n) ≤ diam (Ω : Set E) := diam_mono hVsub hΩb
    dsimp only [K, Opens.coe_mk]
    gcongr
  have htend : Tendsto (fun n => ENNReal.ofReal (K / μ.real (S' ∩ V n)) *
        eLpNorm Du p (μ.restrict Ω))
      atTop (𝓝 (ENNReal.ofReal (K / μ.real S') * eLpNorm Du p (μ.restrict Ω))) :=
    ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal (tendsto_const_nhds.div hmeasR hS'Rpos.ne'))
      (Or.inr hDu.eLpNorm_ne_top)
  calc eLpNorm (fun x => u x - ⨍ y in S', u y ∂μ) p (μ.restrict Ω)
      ≤ atTop.liminf fun n =>
          eLpNorm (fun x => u x - ⨍ y in S' ∩ V n, u y ∂μ) p (μ.restrict (V n)) := hlim
    _ ≤ atTop.liminf fun n =>
          ENNReal.ofReal (K / μ.real (S' ∩ V n)) * eLpNorm Du p (μ.restrict Ω) :=
        liminf_le_liminf hbound
    _ = ENNReal.ofReal (K / μ.real S') * eLpNorm Du p (μ.restrict Ω) := htend.liminf_eq

/-! ### Global `Lᵖ` membership and Poincaré–Wirtinger on bounded convex open sets -/

/-- **Weakly differentiable functions with `Lᵖ` derivative on a bounded convex open set lie in
`Lᵖ`.** No a priori integrability of `u` near the boundary is needed: `u` is integrable on an
interior ball, and the Poincaré–Wirtinger inequality controls `u - ⨍_B u` on the whole domain. -/
theorem HasWeakFDerivOn.memLp_of_convex (hu : HasWeakFDerivOn μ Ω u Du)
    (hΩc : Convex ℝ (Ω : Set E)) (hΩb : Bornology.IsBounded (Ω : Set E))
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hDu : MemLp Du p (μ.restrict Ω)) :
    MemLp u p (μ.restrict Ω) := by
  rcases (Ω : Set E).eq_empty_or_nonempty with hΩ | ⟨x₀, hx₀⟩
  · simp [hΩ]
  obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x₀ hx₀
  set r := R / 2
  have hr : 0 < r := half_pos hR
  have hcbΩ : closedBall x₀ r ⊆ Ω := (closedBall_subset_ball (half_lt_self hR)).trans hRΩ
  have hSΩ : ball x₀ r ⊆ Ω := ball_subset_closedBall.trans hcbΩ
  have hS0 : μ (ball x₀ r) ≠ 0 := (measure_ball_pos μ x₀ hr).ne'
  have huS : IntegrableOn u (ball x₀ r) μ :=
    (hu.locallyIntegrableOn.integrableOn_compact_subset hcbΩ
      (isCompact_closedBall x₀ r)).mono_set ball_subset_closedBall
  set m : F := ⨍ y in ball x₀ r, u y ∂μ
  have hsub_le := eLpNorm_sub_setAverage_le_of_convex_of_integrableOn hu hΩc hΩb hSΩ hS0
    hp1 hp huS hDu
  have hsub : MemLp (fun x => u x - m) p (μ.restrict Ω) :=
    hsub_le.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDu.eLpNorm_lt_top)
  have : IsFiniteMeasure (μ.restrict (Ω : Set E)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hΩb.measure_lt_top⟩
  have hadd : MemLp (fun x => (u x - m) + m) p (μ.restrict Ω) := hsub.add (memLp_const m)
  simpa only [sub_add_cancel] using hadd

/-- **The Poincaré–Wirtinger inequality for weakly differentiable functions on a bounded convex
open set.** Let `Ω` be a bounded convex open subset of a finite-dimensional real normed space `E`
of dimension `n`, let `u : E → F` have weak Fréchet derivative `Du` on `Ω`, and let `S ⊆ Ω` have
positive measure (no measurability assumption on `S` and no a priori `Lᵖ` assumption on `u` or
`Du`). For `1 ≤ p < ∞`,

`‖u - ⨍_S u‖_{Lᵖ(Ω)} ≤ μ(B(0, 1)) * (diam Ω) ^ (n + 1) / μ(S) * ‖Du‖_{Lᵖ(Ω)}`. -/
theorem HasWeakFDerivOn.eLpNorm_sub_setAverage_le_of_convex (hu : HasWeakFDerivOn μ Ω u Du)
    (hΩc : Convex ℝ (Ω : Set E)) (hΩb : Bornology.IsBounded (Ω : Set E))
    {S : Set E} (hS : S ⊆ Ω) (hS0 : μ S ≠ 0) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) :
    eLpNorm (fun x => u x - ⨍ y in S, u y ∂μ) p (μ.restrict Ω) ≤
      ENNReal.ofReal (μ.real (ball 0 1) * diam (Ω : Set E) ^ (finrank ℝ E + 1) / μ.real S) *
        eLpNorm Du p (μ.restrict Ω) := by
  have : CompleteSpace F := hu.completeSpace
  have hSfin : μ S ≠ ∞ := ne_top_of_le_ne_top hΩb.measure_lt_top.ne (measure_mono hS)
  rcases subsingleton_or_nontrivial E with hE | hE
  · have hzero : (fun x => u x - ⨍ y in S, u y ∂μ) = 0 := funext fun x =>
      eNorm_eq_zero.1 (enorm_sub_setAverage_eq_zero_of_subsingleton x hS0 hSfin)
    simp [hzero]
  by_cases hDu_top : eLpNorm Du p (μ.restrict Ω) = ∞
  · -- In positive dimension a nonempty open set has positive diameter, so the RHS is `∞`.
    have hSne : S.Nonempty := nonempty_of_measure_ne_zero hS0
    obtain ⟨x₀, hx₀S⟩ := hSne
    have hdiam_pos : 0 < diam (Ω : Set E) := Ω.isOpen.diam_pos hΩb (hS hx₀S)
    have hball_pos : 0 < μ.real (ball (0 : E) 1) :=
      ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
    have hS_pos : 0 < μ.real S := ENNReal.toReal_pos hS0 hSfin
    have hC_pos : 0 < μ.real (ball (0 : E) 1) * diam (Ω : Set E) ^ (finrank ℝ E + 1) / μ.real S :=
      div_pos (mul_pos hball_pos (pow_pos hdiam_pos _)) hS_pos
    rw [hDu_top, ENNReal.mul_top (ENNReal.ofReal_pos.2 hC_pos).ne']
    exact le_top
  · have hDu : MemLp Du p (μ.restrict Ω) := lt_top_iff_ne_top.2 hDu_top
    have huLp : MemLp u p (μ.restrict Ω) := hu.memLp_of_convex hΩc hΩb hp1 hp hDu
    have : IsFiniteMeasure (μ.restrict S) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hSfin.lt_top⟩
    have huS : IntegrableOn u S μ :=
      (huLp.mono_measure (Measure.restrict_mono hS le_rfl)).integrable hp1
    exact eLpNorm_sub_setAverage_le_of_convex_of_integrableOn hu hΩc hΩb hS hS0 hp1 hp huS hDu

/-- **The Poincaré–Wirtinger inequality on a bounded convex open set**, in `∫⁻` form for any
real exponent `1 ≤ p`. -/
theorem HasWeakFDerivOn.lintegral_enorm_sub_setAverage_rpow_le_of_convex
    (hu : HasWeakFDerivOn μ Ω u Du) (hΩc : Convex ℝ (Ω : Set E))
    (hΩb : Bornology.IsBounded (Ω : Set E)) {S : Set E} (hS : S ⊆ Ω) (hS0 : μ S ≠ 0)
    {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x in (Ω : Set E), ‖u x - ⨍ y in S, u y ∂μ‖ₑ ^ p ∂μ ≤
      ENNReal.ofReal ((μ.real (ball 0 1) * diam (Ω : Set E) ^ (finrank ℝ E + 1) / μ.real S) ^ p) *
        ∫⁻ y in (Ω : Set E), ‖Du y‖ₑ ^ p ∂μ := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  let q : ℝ≥0 := ⟨p, hp0.le⟩
  have hq0 : q ≠ 0 := NNReal.coe_ne_zero.1 hp0.ne'
  have hq1 : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast hp
  have hbase := hu.eLpNorm_sub_setAverage_le_of_convex hΩc hΩb hS hS0 hq1 ENNReal.coe_ne_top
  have hpow := ENNReal.rpow_le_rpow hbase q.coe_nonneg
  have hC0 : 0 ≤ μ.real (ball (0 : E) 1) * diam (Ω : Set E) ^ (finrank ℝ E + 1) / μ.real S :=
    div_nonneg (mul_nonneg measureReal_nonneg (pow_nonneg diam_nonneg _)) measureReal_nonneg
  have hum : AEStronglyMeasurable (fun x => u x - ⨍ y in S, u y ∂μ) (μ.restrict Ω) :=
    hu.locallyIntegrableOn.aestronglyMeasurable.sub aestronglyMeasurable_const
  rw [eLpNorm_nnreal_pow_eq_lintegral hq0 hum,
    ENNReal.mul_rpow_of_nonneg _ _ q.coe_nonneg, ENNReal.ofReal_rpow_of_nonneg hC0 q.coe_nonneg,
    eLpNorm_nnreal_pow_eq_lintegral hq0 hu.locallyIntegrableOn_deriv.aestronglyMeasurable] at hpow
  exact hpow

/-! ### Inequalities on balls and mean oscillation bounds -/

/-- **The Poincaré–Wirtinger inequality on a ball.** If `ball x r ⊆ Ω` and `1 ≤ p < ∞`, then

`‖u - u_{B(x, r)}‖_{Lᵖ(B(x, r))} ≤ 2 ^ (n + 1) * r * ‖Du‖_{Lᵖ(B(x, r))}`. -/
theorem HasWeakFDerivOn.eLpNorm_sub_setAverage_ball_le (hu : HasWeakFDerivOn μ Ω u Du)
    {x : E} {r : ℝ} (hball : ball x r ⊆ Ω) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) :
    eLpNorm (fun y => u y - ⨍ z in ball x r, u z ∂μ) p (μ.restrict (ball x r)) ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * r) * eLpNorm Du p (μ.restrict (ball x r)) := by
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  let B : Opens E := ⟨ball x r, isOpen_ball⟩
  have hB : HasWeakFDerivOn μ B u Du := hu.mono hball
  refine (hB.eLpNorm_sub_setAverage_le_of_convex (convex_ball x r) isBounded_ball
    subset_rfl (measure_ball_pos μ x hr).ne' hp1 hp).trans ?_
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
    (μ.addHaar_real_ball_mul_diam_ball_pow_div_le x hr)) _

/-- **The `L¹` Poincaré–Wirtinger inequality on a ball.** If `ball x r ⊆ Ω`, then

`∫⁻ y in B(x, r), ‖u y - u_{B(x, r)}‖ₑ ≤ 2 ^ (n + 1) * r * ∫⁻ y in B(x, r), ‖Du y‖ₑ`. -/
theorem HasWeakFDerivOn.setLIntegral_enorm_sub_setAverage_ball_le (hu : HasWeakFDerivOn μ Ω u Du)
    {x : E} {r : ℝ} (hball : ball x r ⊆ Ω) :
    ∫⁻ y in ball x r, ‖u y - ⨍ z in ball x r, u z ∂μ‖ₑ ∂μ ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * r) * ∫⁻ y in ball x r, ‖Du y‖ₑ ∂μ := by
  have h := hu.eLpNorm_sub_setAverage_ball_le hball le_rfl ENNReal.one_ne_top
  have hum : AEStronglyMeasurable (fun y => u y - ⨍ z in ball x r, u z ∂μ)
      (μ.restrict (ball x r)) :=
    (hu.locallyIntegrableOn.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono hball le_rfl)).sub aestronglyMeasurable_const
  have hDm : AEStronglyMeasurable Du (μ.restrict (ball x r)) :=
    hu.locallyIntegrableOn_deriv.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono hball le_rfl)
  rwa [eLpNorm_one_eq_lintegral_eNorm hum, eLpNorm_one_eq_lintegral_eNorm hDm] at h

/-- **Mean oscillation on a ball in terms of `‖Du‖_{Lᵖ(B)}`.** For every exponent `1 ≤ p ≤ ∞`
(including `p = ∞`) and every ball `B(x, r) ⊆ Ω`,

`⨍⁻ y in B(x, r), ‖u y - u_{B(x, r)}‖ₑ`
`  ≤ 2 ^ (n + 1) * r * μ(B(x, r)) ^ (-1 / p) * ‖Du‖_{Lᵖ(B(x, r))}`. -/
theorem HasWeakFDerivOn.setLAverage_enorm_sub_setAverage_ball_le_mul_measure_rpow
    (hu : HasWeakFDerivOn μ Ω u Du) {x : E} {r : ℝ} (hball : ball x r ⊆ Ω)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) :
    ⨍⁻ y in ball x r, ‖u y - ⨍ z in ball x r, u z ∂μ‖ₑ ∂μ ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * r) * μ (ball x r) ^ (-p.toReal⁻¹) *
        eLpNorm Du p (μ.restrict (ball x r)) := by
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hB0 : μ (ball x r) ≠ 0 := (measure_ball_pos μ x hr).ne'
  have hBtop : μ (ball x r) ≠ ∞ := measure_ball_lt_top.ne
  have hDm : AEStronglyMeasurable Du (μ.restrict (ball x r)) :=
    hu.locallyIntegrableOn_deriv.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono hball le_rfl)
  have hholder : ∫⁻ y in ball x r, ‖Du y‖ₑ ∂μ ≤
      eLpNorm Du p (μ.restrict (ball x r)) * μ (ball x r) ^ (1 - p.toReal⁻¹) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp1 hDm
    simpa only [eLpNorm_one_eq_lintegral_eNorm hDm, Measure.restrict_apply_univ, ENNReal.toReal_one,
      one_div, inv_one] using h
  calc ⨍⁻ y in ball x r, ‖u y - ⨍ z in ball x r, u z ∂μ‖ₑ ∂μ
      = (μ (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖u y - ⨍ z in ball x r, u z ∂μ‖ₑ ∂μ := by
        rw [setLAverage_eq, ENNReal.div_eq_inv_mul]
    _ ≤ (μ (ball x r))⁻¹ *
          (ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * r) * ∫⁻ y in ball x r, ‖Du y‖ₑ ∂μ) :=
        mul_le_mul_right (hu.setLIntegral_enorm_sub_setAverage_ball_le hball) _
    _ ≤ (μ (ball x r))⁻¹ *
          (ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * r) *
            (eLpNorm Du p (μ.restrict (ball x r)) * μ (ball x r) ^ (1 - p.toReal⁻¹))) := by
        gcongr
    _ = ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * r) *
          ((μ (ball x r))⁻¹ * μ (ball x r) ^ (1 - p.toReal⁻¹)) *
          eLpNorm Du p (μ.restrict (ball x r)) := by ring
    _ = ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * r) * μ (ball x r) ^ (-p.toReal⁻¹) *
          eLpNorm Du p (μ.restrict (ball x r)) := by
        congr 2
        rw [← ENNReal.rpow_neg_one, ← ENNReal.rpow_add _ _ hB0 hBtop]
        ring_nf

/-- **Mean oscillation on a ball with explicit power of the radius.** For every exponent
`1 ≤ p ≤ ∞` and every ball `B(x, r) ⊆ Ω` of positive radius `r`,

`⨍⁻ y in B(x, r), ‖u y - u_{B(x, r)}‖ₑ`
`  ≤ 2 ^ (n + 1) ω ^ (-1 / p) r ^ (1 - n / p) ‖Du‖_{Lᵖ(B(x, r))}`,

where `ω = μ.real (ball 0 1)`. -/
theorem HasWeakFDerivOn.setLAverage_enorm_sub_setAverage_ball_le_mul_rpow
    (hu : HasWeakFDerivOn μ Ω u Du) {x : E} {r : ℝ} (hr : 0 < r) (hball : ball x r ⊆ Ω)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) :
    ⨍⁻ y in ball x r, ‖u y - ⨍ z in ball x r, u z ∂μ‖ₑ ∂μ ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * μ.real (ball 0 1) ^ (-p.toReal⁻¹) *
          r ^ (1 - (finrank ℝ E : ℝ) / p.toReal)) *
        eLpNorm Du p (μ.restrict (ball x r)) := by
  refine (hu.setLAverage_enorm_sub_setAverage_ball_le_mul_measure_rpow hball hp1).trans_eq ?_
  congr 1
  have hBpos : 0 < μ.real (ball x r) :=
    ENNReal.toReal_pos (measure_ball_pos μ x hr).ne' measure_ball_lt_top.ne
  rw [← ENNReal.ofReal_toReal (measure_ball_lt_top (μ := μ) (x := x) (r := r)).ne,
    ← measureReal_def, ENNReal.ofReal_rpow_of_pos hBpos, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [μ.addHaar_real_ball_rpow x hr (-p.toReal⁻¹)]
  have hexp : r * r ^ ((finrank ℝ E : ℝ) * -p.toReal⁻¹) =
      r ^ (1 - (finrank ℝ E : ℝ) / p.toReal) := by
    conv_lhs => arg 1; rw [← Real.rpow_one r]
    rw [← Real.rpow_add hr]
    congr 1
    ring
  calc 2 ^ (finrank ℝ E + 1) * r *
        (r ^ ((finrank ℝ E : ℝ) * -p.toReal⁻¹) * μ.real (ball 0 1) ^ (-p.toReal⁻¹))
      = 2 ^ (finrank ℝ E + 1) * μ.real (ball 0 1) ^ (-p.toReal⁻¹) *
          (r * r ^ ((finrank ℝ E : ℝ) * -p.toReal⁻¹)) := by ring
    _ = _ := by rw [hexp]

/-- **Scale-invariant mean oscillation bound at the borderline exponent `p = n`.** In positive
dimension `n = finrank ℝ E ≥ 1`, for every ball `B(x, r) ⊆ Ω`,

`⨍⁻ y in B(x, r), ‖u y - u_{B(x, r)}‖ₑ ≤ 2 ^ (n + 1) ω ^ (-1 / n) ‖Du‖_{Lⁿ(B(x, r))}`.

The radius cancels completely. -/
theorem HasWeakFDerivOn.setLAverage_enorm_sub_setAverage_ball_le [Nontrivial E]
    (hu : HasWeakFDerivOn μ Ω u Du) {x : E} {r : ℝ} (hball : ball x r ⊆ Ω) :
    ⨍⁻ y in ball x r, ‖u y - ⨍ z in ball x r, u z ∂μ‖ₑ ∂μ ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * μ.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹)) *
        eLpNorm Du (finrank ℝ E) (μ.restrict (ball x r)) := by
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hn : 1 ≤ (finrank ℝ E : ℝ≥0∞) := by exact_mod_cast finrank_pos
  have hn0 : (finrank ℝ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 finrank_pos.ne'
  have h := hu.setLAverage_enorm_sub_setAverage_ball_le_mul_rpow hr hball hn
  simpa only [ENNReal.toReal_natCast, div_self hn0, sub_self, Real.rpow_zero, mul_one] using h

/-! ### Vanishing weak derivative on a preconnected open set -/

/-- **A weakly differentiable function with vanishing weak derivative on a preconnected open set
is almost everywhere constant.** -/
theorem HasWeakFDerivOn.exists_ae_eq_const_of_deriv_ae_eq_zero (hu : HasWeakFDerivOn μ Ω u Du)
    (hΩ : IsPreconnected (Ω : Set E)) (hDu : Du =ᵐ[μ.restrict Ω] 0) :
    ∃ c : F, ∀ᵐ x ∂μ.restrict Ω, u x = c := by
  refine hΩ.exists_ae_eq_const_of_forall_nhds (HereditarilyLindelofSpace.isLindelof _)
    fun x hx => ?_
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 Ω.isOpen x hx
  refine ⟨⨍ z in ball x r, u z ∂μ, ball x r, ball_mem_nhds x hr, ?_⟩
  refine ae_restrict_eq_setAverage_of_setLAverage_enorm_sub_setAverage_eq_zero
    (hu.locallyIntegrableOn.aestronglyMeasurable.mono_measure (Measure.restrict_mono hball le_rfl))
    measure_ball_lt_top.ne ?_
  have hDu_ball : Du =ᵐ[μ.restrict (ball x r)] 0 :=
    ae_restrict_of_ae_restrict_of_subset hball hDu
  have hnorm0 : (fun y => ‖Du y‖ₑ) =ᵐ[μ.restrict (ball x r)] fun _ => (0 : ℝ≥0∞) :=
    hDu_ball.mono fun y hy => by simp [hy, ← ofReal_norm]
  have hint0 : ∫⁻ y in ball x r, ‖Du y‖ₑ ∂μ = 0 := by
    rw [lintegral_congr_ae hnorm0, lintegral_zero]
  have hle := hu.setLIntegral_enorm_sub_setAverage_ball_le hball
  rw [hint0, mul_zero] at hle
  rw [setLAverage_eq, le_antisymm hle bot_le, ENNReal.zero_div]

/-! ### Borderline embedding `W^{1,n} ⊆ VMO ⊆ BMO` -/

/-- **BMO bound for globally weakly differentiable functions at the borderline exponent `p = n`.**
-/
theorem HasWeakFDerivOn.bmoSeminorm_le [Nontrivial E] (hu : HasWeakFDerivOn μ ⊤ u Du) :
    bmoSeminorm u μ ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * μ.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹)) *
        eLpNorm Du (finrank ℝ E) μ :=
  TauCeti.bmoSeminorm_le fun c r =>
    (hu.setLAverage_enorm_sub_setAverage_ball_le (x := c) (r := r) (subset_univ _)).trans
      (mul_le_mul_right (eLpNorm_mono_measure _ Measure.restrict_le_self) _)

/-- **Borderline embedding `W^{1,n} ⊆ BMO`.** A globally weakly differentiable function whose weak
derivative has finite `Lⁿ` seminorm has bounded mean oscillation. -/
theorem HasWeakFDerivOn.memBMO [Nontrivial E] (hu : HasWeakFDerivOn μ ⊤ u Du)
    (hDu : eLpNorm Du (finrank ℝ E) μ ≠ ∞) :
    MemBMO u μ :=
  memBMO_iff.2 ⟨locallyIntegrableOn_univ.1 hu.locallyIntegrableOn,
    hu.bmoSeminorm_le.trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hDu))⟩

/-- **VMO modulus bound at the borderline exponent `p = n`.** For every radius `r`, the VMO modulus
of `u` at scale `r` is controlled by the supremum over all centres `c` of `‖Du‖_{Lⁿ(B(c, r))}`. -/
theorem HasWeakFDerivOn.vmoModulus_le [Nontrivial E] (hu : HasWeakFDerivOn μ ⊤ u Du) (r : ℝ) :
    vmoModulus u μ r ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * μ.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹)) *
        ⨆ c : E, eLpNorm Du (finrank ℝ E) (μ.restrict (ball c r)) :=
  TauCeti.vmoModulus_le fun c s hs =>
    (hu.setLAverage_enorm_sub_setAverage_ball_le (x := c) (r := s) (subset_univ _)).trans <|
      mul_le_mul_right
        ((eLpNorm_mono_measure _ (Measure.restrict_mono (ball_subset_ball hs) le_rfl)).trans
          (le_iSup (fun c' => eLpNorm Du (finrank ℝ E) (μ.restrict (ball c' r))) c)) _

/-- **Borderline embedding `W^{1,n} ⊆ VMO`.** A globally weakly differentiable function whose weak
derivative has finite `Lⁿ` seminorm has vanishing mean oscillation. -/
theorem HasWeakFDerivOn.memVMO [Nontrivial E] (hu : HasWeakFDerivOn μ ⊤ u Du)
    (hDu : eLpNorm Du (finrank ℝ E) μ ≠ ∞) :
    MemVMO u μ := by
  refine memVMO_iff_tendsto.2 ⟨hu.memBMO hDu, ?_⟩
  have hn0 : (finrank ℝ E : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 finrank_pos.ne'
  have hntop : (finrank ℝ E : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hsup : Tendsto (fun r : ℝ => ⨆ c : E, eLpNorm Du (finrank ℝ E) (μ.restrict (ball c r)))
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_iSup_eLpNorm_restrict_ball_zero hn0 hntop hDu (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hrhs := ENNReal.Tendsto.const_mul hsup (Or.inr (ENNReal.ofReal_ne_top (r :=
    2 ^ (finrank ℝ E + 1) * μ.real (ball (0 : E) 1) ^ (-(finrank ℝ E : ℝ)⁻¹))))
  rw [mul_zero] at hrhs
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
    (fun _ => zero_le) hu.vmoModulus_le

end TauCeti

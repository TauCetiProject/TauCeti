/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PartialSups
public import TauCeti.Probability.Martingale.MaximalInequality.Event
import Mathlib.Analysis.Normed.Order.Lattice
import TauCeti.MeasureTheory.Function.L1Space.Integrable
import TauCeti.MeasureTheory.Function.Lp.Order
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.Lebesgue.Superlevel
import TauCeti.Order.Filter.PosPart

/-!
# Doob's event-refined `Lᵖ` and strong `Lᵖ` maximal inequalities

`TauCeti.Probability.Martingale.MaximalInequality.Basic` and
`TauCeti.Probability.Martingale.MaximalInequality.Event` establish Doob's weak, event-refined, and
positive-part `L¹` maximal inequalities together with almost sure finiteness of the running
supremum. This file upgrades the theory to `Lᵖ`:

* **Event-refined `Lᵖ` maximal inequalities (`1 ≤ p < ∞`)**: on the closed crossing event
  `A_ε = {ε ≤ ⨆ t ≤ T, ofReal (f_t)}`,
  `ε ^ p μ(A_ε) ≤ ∫⁻_{A_ε} ofReal (f_T) ^ p ∂μ` holds unconditionally, and
  `ε ^ p μ(A_ε) ≤ ofReal (∫_{A_ε} (f⁺)_T ^ p ∂μ)` holds (both on `A_ε` and on finite crossing
  events `{∃ t ∈ F, ε ≤ f_t}`) assuming `Lᵖ` integrability only at the terminal time `T`.
  Specializing to `M.norm` gives the Banach-valued martingale inequality
  `ε ^ p μ({ε ≤ ⨆ t ≤ T, ‖M_t‖ₑ}) ≤ ∫⁻_{...} ‖M_T‖ₑ ^ p ∂μ` (and the Bochner `setIntegral` form
  under `MemLp (M T) (ofReal p) μ`).
* **Doob's strong `Lᵖ` maximal inequalities (`1 < p < ∞`)**: combining the `L¹` superlevel bound
  with `TauCeti.eLpNorm_le_of_mul_meas_ofReal_lt_le_setLIntegral` yields the sharp constant
  `p / (p - 1)` for discrete `partialSups` over `[LinearOrder ι] [LocallyFiniteOrderBot ι]`,
  countable time sets, and right-continuous processes over `t ≤ T`, for both signed submartingales
  and Banach-valued martingales. In the `eLpNorm` and `lintegral` formulations no `MemLp`
  hypothesis is needed; when `(f⁺)_T` (or `f_T`) lies in `Lᵖ`, the running supremum of the positive
  part `(⨆ t ≤ T, ofReal (f t ω)).toReal` belongs to `Lᵖ` and its `p`-th moment is bounded by
  `(p / (p - 1)) ^ p` times the terminal `p`-th moment (matching `(f_T) ^ p`, and in discrete time
  `partialSups f n`, under terminal nonnegativity `0 ≤ᵐ[μ] f_T` or `0 ≤ᵐ[μ] f_n`).
* **Uniform `Lᵖ` path convergence**: terminal `Lᵖ` convergence (`1 < p < ∞`) of right-continuous
  Banach-valued martingales implies `Lᵖ` convergence of the uniform path error over `t ≤ T`.

## Main declarations

In `MeasureTheory.Submartingale`:
* `rpow_mul_measure_exists_mem_le_le_setIntegral_posPart`,
  `rpow_mul_measure_exists_mem_le_le_setIntegral`,
  `rpow_mul_measure_le_iSup_le_setIntegral_posPart`,
  `rpow_mul_measure_le_iSup_le_setIntegral`, `rpow_mul_measure_le_iSup_le_setLIntegral`:
  event-refined `Lᵖ` maximal inequalities (`1 ≤ p < ∞`).
* `eLpNorm_partialSups_posPart_le`, `eLpNorm_partialSups_le`,
  `integral_rpow_partialSups_posPart_le`, `integral_rpow_partialSups_le`: discrete-time Doob `Lᵖ`
  maximal inequalities (`1 < p < ∞`).
* `eLpNorm_biSup_ofReal_le_mul_eLpNorm_posPart`, `eLpNorm_biSup_ofReal_le`: countable-time Doob
  `Lᵖ` maximal inequalities (`1 < p < ∞`).
* `eLpNorm_iSup_ofReal_le_mul_eLpNorm_posPart`, `eLpNorm_iSup_ofReal_le`,
  `lintegral_iSup_ofReal_rpow_le`, `memLp_toReal_iSup_ofReal_posPart`, `memLp_toReal_iSup_ofReal`,
  `integral_toReal_iSup_ofReal_rpow_le_mul_integral_posPart_rpow`,
  `integral_toReal_iSup_ofReal_rpow_le`: continuous-time Doob `Lᵖ` maximal inequalities
  (`1 < p < ∞`).

In `MeasureTheory.Martingale`:
* `rpow_mul_measure_le_iSup_eNorm_le_setLIntegral`,
  `rpow_mul_measure_le_iSup_eNorm_le_setIntegral`: event-refined `Lᵖ` maximal inequalities for
  Banach-valued martingales (`1 ≤ p < ∞`).
* `eLpNorm_partialSups_norm_le`, `integral_rpow_partialSups_norm_le`, `eLpNorm_biSup_eNorm_le`,
  `lintegral_iSup_eNorm_rpow_le`, `eLpNorm_iSup_eNorm_le`, `memLp_toReal_iSup_eNorm`,
  `integral_toReal_iSup_eNorm_rpow_le`: Doob's `Lᵖ` maximal inequalities for Banach-valued
  martingales (`1 < p < ∞`).
* `tendsto_eLpNorm_iSup_eNorm_sub`: terminal `Lᵖ` convergence implies `Lᵖ` running-supremum
  convergence over `t ≤ T`.

## References

* J. L. Doob, *Stochastic Processes*, Wiley, 1953, Chapter VII, Theorem 3.4.
* D. Revuz, M. Yor, *Continuous Martingales and Brownian Motion*, third edition, Springer, 1999,
  Theorem II.1.7.
* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition, Springer,
  1991, Theorem 1.3.8.
-/

public section

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal

namespace MeasureTheory.Submartingale

variable {Ω ι : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Event-refined `Lᵖ` maximal inequalities (`1 ≤ p < ∞`) -/

section EventRefinedLp

variable [LinearOrder ι] [IsFiniteMeasure μ] {ℱ : Filtration ι m0} {f : ι → Ω → ℝ}

omit [IsFiniteMeasure μ] in
/-- Stopping `(f⁺)` at `T` and raising to `p ≥ 1` produces a pointwise nonnegative submartingale on
the whole index type `ι`, requiring `MemLp` only at the terminal time `T`. -/
private lemma submartingale_posPart_min_rpow
    (hf : Submartingale f ℱ μ) {T : ι} {p : ℝ} (hp : 1 ≤ p)
    (hT : MemLp ((f⁺) T) (ENNReal.ofReal p) μ) :
    Submartingale (fun t ω ↦ ((f⁺) (min t T) ω) ^ p)
      (ℱ.comp (monotone_id.min (monotone_const : Monotone fun _ : ι ↦ T))) μ := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hp_enn : 1 ≤ ENNReal.ofReal p := by
    rwa [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff hp0.le]
  let τ : ι → ι := fun t ↦ min t T
  have hτ : Monotone τ := monotone_id.min monotone_const
  have hg : Submartingale (fun t ↦ (f⁺) (τ t)) (ℱ.comp hτ) μ := hf.pos.comp hτ
  refine hg.rpow (fun t ↦ Eventually.of_forall fun _ ↦ posPart_nonneg _) hp fun t ↦ ?_
  have ht_mem : MemLp ((f⁺) (τ t)) (ENNReal.ofReal p) μ := by
    have hmax : τ (max t T) = T := min_eq_right (le_max_right t T)
    exact hg.memLp_of_le (le_max_left t T)
      (Eventually.of_forall fun _ ↦ posPart_nonneg _)
      hp_enn (by simpa only [hmax] using hT)
  exact ht_mem.integrable_rpow hp0

/-- **Event-refined `Lᵖ` Doob inequality on a finite set (positive-part Bochner form).** For
`1 ≤ p < ∞`, terminal `Lᵖ` integrability of `(f⁺) T` suffices to control `ε ^ p` times the measure
of the finite crossing event by the restricted `p`-th moment of `(f⁺) T`. -/
theorem rpow_mul_measure_exists_mem_le_le_setIntegral_posPart
    (hf : Submartingale f ℱ μ) (ε : ℝ≥0) {F : Finset ι} {T : ι} (hF : ∀ t ∈ F, t ≤ T)
    {p : ℝ} (hp : 1 ≤ p) (hT : MemLp ((f⁺) T) (ENNReal.ofReal p) μ) :
    (ε : ℝ≥0∞) ^ p * μ {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω} ≤
      ENNReal.ofReal (∫ ω in {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω}, ((f⁺) T ω) ^ p ∂μ) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  rcases eq_or_ne ε 0 with rfl | hε
  · simp [ENNReal.zero_rpow_of_pos hp0]
  have hε_pos : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hg := submartingale_posPart_min_rpow hf hp hT
  have hmax := hg.mul_measure_exists_mem_le_le_setIntegral
    (fun t ω ↦ Real.rpow_nonneg (posPart_nonneg (f (min t T) ω)) _) (ε ^ p) hF
  have hset : {ω | ∃ t ∈ F, ((ε ^ p : ℝ≥0) : ℝ) ≤ ((f⁺) (min t T) ω) ^ p} =
      {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω} := by
    ext ω
    simp only [mem_ofPred_eq, NNReal.coe_rpow]
    refine exists_congr fun t ↦ and_congr_right fun ht ↦ ?_
    rw [min_eq_left (hF t ht)]
    simp only [Pi.posPart_apply]
    rw [Real.rpow_le_rpow_iff ε.coe_nonneg (posPart_nonneg (f t ω)) hp0, posPart_def, le_max_iff]
    exact ⟨fun h ↦ h.resolve_right hε_pos.not_ge, Or.inl⟩
  rw [hset, min_self] at hmax
  simpa only [ENNReal.coe_rpow_of_nonneg _ hp0.le] using hmax

/-- **Event-refined `Lᵖ` Doob inequality on a finite set.** Requires `0 ≤ᵐ[μ] f T` and `MemLp`
only at the terminal time `T`. -/
theorem rpow_mul_measure_exists_mem_le_le_setIntegral
    (hf : Submartingale f ℱ μ) (ε : ℝ≥0) {F : Finset ι} {T : ι} (hF : ∀ t ∈ F, t ≤ T)
    (hposT : 0 ≤ᵐ[μ] f T) {p : ℝ} (hp : 1 ≤ p) (hT : MemLp (f T) (ENNReal.ofReal p) μ) :
    (ε : ℝ≥0∞) ^ p * μ {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω} ≤
      ENNReal.ofReal (∫ ω in {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω}, f T ω ^ p ∂μ) := by
  have hae : (f⁺) T =ᵐ[μ] f T := hposT.posPart_eq
  have hmeas : MeasurableSet {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω} := by
    simp only [← exists_prop, ofPred_exists]
    exact F.measurableSet_biUnion fun t _ ↦
      measurableSet_le measurable_const ((hf.stronglyAdapted t).mono (ℱ.le t)).measurable
  have hcongr : ∫ ω in {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω}, ((f⁺) T ω) ^ p ∂μ =
      ∫ ω in {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω}, f T ω ^ p ∂μ :=
    setIntegral_congr_ae hmeas (hae.mono fun _ hω _ ↦ congrArg (· ^ p) hω)
  rw [← hcongr]
  exact hf.rpow_mul_measure_exists_mem_le_le_setIntegral_posPart ε hF hp (hT.ae_eq hae.symm)

section ContinuousTimeEventLp

variable [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]

/-- **Closed-level event-refined `Lᵖ` Doob inequality (positive-part Bochner form).** Requires
`MemLp` only at the terminal time `T`. -/
theorem rpow_mul_measure_le_iSup_le_setIntegral_posPart
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    (ε : ℝ≥0) {p : ℝ} (hp : 1 ≤ p) (hT : MemLp ((f⁺) T) (ENNReal.ofReal p) μ) :
    (ε : ℝ≥0∞) ^ p * μ {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)} ≤
      ENNReal.ofReal (∫ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)},
        ((f⁺) T ω) ^ p ∂μ) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hg := submartingale_posPart_min_rpow hf hp hT
  have hg_cont : ∀ᵐ ω ∂μ, ∀ t < T,
      ContinuousWithinAt (fun u ↦ ((f⁺) (min u T) ω) ^ p) (Ioi t) t := by
    filter_upwards [hcont] with ω hω t ht
    have hpos_cont : ContinuousWithinAt (fun u ↦ (f⁺) u ω) (Ioi t) t := by
      simpa only [Pi.posPart_apply, posPart_def] using (hω t ht).sup continuousWithinAt_const
    have hcongr : (fun u ↦ ((f⁺) (min u T) ω) ^ p) =ᶠ[𝓝[>] t] (fun u ↦ ((f⁺) u ω) ^ p) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)] with u hu
      rw [min_eq_left hu.le]
    exact ((Real.continuous_rpow_const hp0.le).continuousAt.comp_continuousWithinAt
      hpos_cont).congr_of_eventuallyEq hcongr (by simp [min_eq_left ht.le])
  have hmax := hg.mul_measure_le_iSup_le_setIntegral
    (fun t ω ↦ Real.rpow_nonneg (posPart_nonneg (f (min t T) ω)) _) hg_cont (ε ^ p)
  have hset : {ω | ((ε ^ p : ℝ≥0) : ℝ≥0∞) ≤
      ⨆ t ≤ T, ENNReal.ofReal (((f⁺) (min t T) ω) ^ p)} =
      {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)} := by
    ext ω
    simp only [mem_ofPred_eq, ENNReal.coe_rpow_of_nonneg _ hp0.le]
    have hsup : (⨆ t ≤ T, ENNReal.ofReal (((f⁺) (min t T) ω) ^ p)) =
        (⨆ t ≤ T, ENNReal.ofReal (f t ω)) ^ p := by
      rw [ENNReal.iSup_rpow_of_pos hp0]
      refine iSup_congr fun t ↦ ?_
      by_cases ht : t ≤ T
      · simp only [ht, iSup_pos, min_eq_left ht, Pi.posPart_apply]
        rw [← ENNReal.ofReal_rpow_of_nonneg (posPart_nonneg (f t ω)) hp0.le,
          ENNReal.ofReal_posPart]
      · simp [ht, ENNReal.zero_rpow_of_pos hp0]
    rw [hsup, ENNReal.rpow_le_rpow_iff hp0]
  rw [hset, min_self] at hmax
  simpa only [ENNReal.coe_rpow_of_nonneg _ hp0.le] using hmax

/-- **Closed-level event-refined `Lᵖ` Doob inequality (Bochner form).** Requires nonnegativity and
`MemLp` only at the terminal time `T`. -/
theorem rpow_mul_measure_le_iSup_le_setIntegral
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    (hposT : 0 ≤ᵐ[μ] f T) (ε : ℝ≥0) {p : ℝ} (hp : 1 ≤ p)
    (hT : MemLp (f T) (ENNReal.ofReal p) μ) :
    (ε : ℝ≥0∞) ^ p * μ {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)} ≤
      ENNReal.ofReal (∫ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)},
        f T ω ^ p ∂μ) := by
  have hae : (f⁺) T =ᵐ[μ] f T := hposT.posPart_eq
  have hA : NullMeasurableSet {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)} μ :=
    nullMeasurableSet_le aemeasurable_const (hf.aemeasurable_iSup_ofReal hcont)
  have hcongr : ∫ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)},
      ((f⁺) T ω) ^ p ∂μ =
      ∫ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)}, f T ω ^ p ∂μ :=
    setIntegral_congr_ae₀ hA (hae.mono fun _ hω _ ↦ congrArg (· ^ p) hω)
  rw [← hcongr]
  exact hf.rpow_mul_measure_le_iSup_le_setIntegral_posPart hcont ε hp (hT.ae_eq hae.symm)

/-- **Unconditional closed-level event-refined `Lᵖ` Doob inequality (lower-integral form).** Holds
for every `1 ≤ p < ∞` and `ε : ℝ≥0` with no sign or `MemLp` hypothesis on `f`. -/
theorem rpow_mul_measure_le_iSup_le_setLIntegral
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    (ε : ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
    (ε : ℝ≥0∞) ^ p * μ {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)} ≤
      ∫⁻ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)},
        ENNReal.ofReal (f T ω) ^ p ∂μ := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  set A : Set Ω := {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)}
  have hp_enn : 1 ≤ ENNReal.ofReal p := by
    rwa [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff hp0.le]
  have hp_ne0 : ENNReal.ofReal p ≠ 0 := (zero_lt_one.trans_le hp_enn).ne'
  have hfT_meas : AEStronglyMeasurable ((f⁺) T) μ :=
    ((hf.pos.stronglyAdapted T).mono (ℱ.le T)).aestronglyMeasurable
  by_cases hT : MemLp ((f⁺) T) (ENNReal.ofReal p) μ
  · refine (hf.rpow_mul_measure_le_iSup_le_setIntegral_posPart hcont ε hp hT).trans_eq ?_
    rw [← (hT.restrict A).lintegral_ofReal_rpow_eq_ofReal_integral hp0
      (Eventually.of_forall fun _ ↦ posPart_nonneg _)]
    simp_rw [Pi.posPart_apply, ENNReal.ofReal_posPart]
  · -- If `(f⁺) T ∉ Lᵖ`, the complement `Aᶜ` has bounded `ofReal (f T ω) ≤ ε` on a finite measure
    -- space, forcing the lower integral on `A` to be `∞`.
    have hA : NullMeasurableSet A μ :=
      nullMeasurableSet_le aemeasurable_const (hf.aemeasurable_iSup_ofReal hcont)
    have hfull_top : ∫⁻ ω, ENNReal.ofReal (f T ω) ^ p ∂μ = ∞ := by
      rw [memLp_iff, not_lt, top_le_iff] at hT
      have heq := lintegral_rpow_enorm_eq_eLpNorm_rpow hp_ne0 ENNReal.ofReal_ne_top hfT_meas
      rw [ENNReal.toReal_ofReal hp0.le, hT, ENNReal.top_rpow_of_pos hp0] at heq
      exact (lintegral_congr fun ω ↦ by
        simp only [Pi.posPart_apply]
        rw [Real.eNorm_eq_ofReal (posPart_nonneg (f T ω)), ENNReal.ofReal_posPart]).symm.trans heq
    have hcompl_lt : ∫⁻ ω in Aᶜ, ENNReal.ofReal (f T ω) ^ p ∂μ < ∞ := by
      rw [← lintegral_indicator₀ hA.compl]
      refine lt_of_le_of_lt (lintegral_mono (g := fun _ ↦ (ε : ℝ≥0∞) ^ p) fun ω ↦ ?_) ?_
      · by_cases hω : ω ∈ Aᶜ
        · rw [indicator_of_mem hω]
          simp only [A, mem_compl_iff, mem_ofPred_eq, not_le] at hω
          have hle : ENNReal.ofReal (f T ω) ≤ (ε : ℝ≥0∞) :=
            (le_iSup₂ (f := fun t (_ : t ≤ T) ↦ ENNReal.ofReal (f t ω)) T le_rfl).trans hω.le
          exact ENNReal.rpow_le_rpow hle hp0.le
        · rw [indicator_of_notMem hω]
          exact zero_le
      · rw [lintegral_const]
        exact ENNReal.mul_lt_top
          (ENNReal.rpow_lt_top_of_nonneg hp0.le ENNReal.coe_ne_top) (measure_lt_top _ _)
    have hadd := lintegral_add_compl₀ (fun ω ↦ ENNReal.ofReal (f T ω) ^ p) hA
    rw [hfull_top] at hadd
    have hA_top : ∫⁻ ω in A, ENNReal.ofReal (f T ω) ^ p ∂μ = ∞ := by
      by_contra hne
      exact (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hne, hcompl_lt⟩).ne hadd
    rw [hA_top]
    exact le_top

end ContinuousTimeEventLp

end EventRefinedLp

/-! ### Doob's strong `Lᵖ` maximal inequalities (`1 < p < ∞`) -/

section StrongLp

variable [LinearOrder ι] [IsFiniteMeasure μ] {ℱ : Filtration ι m0} {f : ι → Ω → ℝ}

/-- **Doob's `Lᵖ` maximal inequality on a countable set (positive-part form).** For `1 < p < ∞` in
`ℝ≥0∞`, no sign or `MemLp` assumption on `f` is needed. -/
theorem eLpNorm_biSup_ofReal_le_mul_eLpNorm_posPart
    (hf : Submartingale f ℱ μ) {S : Set ι} (hS : S.Countable) {T : ι} (hST : ∀ t ∈ S, t ≤ T)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (fun ω ↦ ⨆ t ∈ S, ENNReal.ofReal (f t ω)) p μ ≤
      p / (p - 1) * eLpNorm ((f⁺) T) p μ := by
  have := hS.to_subtype
  have hu : AEStronglyMeasurable (fun ω ↦ ⨆ t ∈ S, ENNReal.ofReal (f t ω)) μ := by
    have hmeas : AEMeasurable (fun ω ↦ ⨆ s : S, ENNReal.ofReal (f s ω)) μ :=
      AEMeasurable.iSup fun s : S ↦
        (((hf.stronglyAdapted s).measurable.mono (ℱ.le s) le_rfl).aemeasurable).ennreal_ofReal
    simpa only [iSup_subtype] using hmeas.aestronglyMeasurable
  refine TauCeti.eLpNorm_le_of_mul_meas_ofReal_lt_le_setLIntegral hp hp_top hu
    (fun _ _ ↦ measure_ne_top μ _) fun t ht ↦ ?_
  let ε : ℝ≥0 := Real.toNNReal t
  have hε_coe : (ε : ℝ) = t := Real.coe_toNNReal t ht.le
  have hε_enn : (ε : ℝ≥0∞) = ENNReal.ofReal t := by rw [← ENNReal.ofReal_coe_nnreal, hε_coe]
  have hset : {ω | ENNReal.ofReal t < ‖⨆ s ∈ S, ENNReal.ofReal (f s ω)‖ₑ} =
      {ω | ∃ s ∈ S, (ε : ℝ) < f s ω} := by
    ext ω
    simp only [mem_ofPred_eq, eNorm_eq_self, ← hε_enn, lt_iSup_iff, exists_prop,
      ENNReal.coe_lt_ofReal]
  rw [hset, ← hε_enn]
  refine (hf.mul_measure_exists_mem_lt_le_setIntegral_posPart_of_countable ε hS hST).trans_eq ?_
  rw [ofReal_integral_eq_lintegral_ofReal (hf.pos.integrable T).integrableOn
    (Eventually.of_forall fun _ ↦ posPart_nonneg _)]
  exact lintegral_congr fun ω ↦ (Real.eNorm_eq_ofReal (posPart_nonneg (f T ω))).symm

/-- **Doob's `Lᵖ` maximal inequality on a countable set.** Holds for any real submartingale `f` and
`1 < p < ∞` with no sign or `MemLp` hypothesis, since `‖(f⁺) T ω‖ ≤ ‖f T ω‖` pointwise. -/
theorem eLpNorm_biSup_ofReal_le
    (hf : Submartingale f ℱ μ) {S : Set ι} (hS : S.Countable) {T : ι} (hST : ∀ t ∈ S, t ≤ T)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (fun ω ↦ ⨆ t ∈ S, ENNReal.ofReal (f t ω)) p μ ≤
      p / (p - 1) * eLpNorm (f T) p μ := by
  refine (hf.eLpNorm_biSup_ofReal_le_mul_eLpNorm_posPart hS hST hp hp_top).trans
    (mul_le_mul_of_nonneg_left
      (eLpNorm_mono ((hf.pos.stronglyAdapted T).mono (ℱ.le T)).aestronglyMeasurable fun ω ↦ ?_)
      zero_le)
  simp only [Pi.posPart_apply]
  rw [Real.norm_of_nonneg (posPart_nonneg _), Real.norm_eq_abs, posPart_def]
  exact max_le (le_abs_self _) (abs_nonneg _)

end StrongLp

section DiscreteTimeLp

variable [LinearOrder ι] [LocallyFiniteOrderBot ι] [IsFiniteMeasure μ]
  {ℱ : Filtration ι m0} {f : ι → Ω → ℝ}

/-- **Doob's discrete-time `Lᵖ` maximal inequality (positive-part form).** No `MemLp` assumption is
needed. -/
theorem eLpNorm_partialSups_posPart_le
    (hf : Submartingale f ℱ μ) (n : ι) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (partialSups (f⁺) n) p μ ≤ p / (p - 1) * eLpNorm ((f⁺) n) p μ := by
  have heq (ω : Ω) : ‖partialSups (f⁺) n ω‖ₑ = ⨆ k ∈ Set.Iic n, ENNReal.ofReal (f k ω) := by
    have hnn : 0 ≤ partialSups (f⁺) n ω :=
      (posPart_nonneg (f n ω)).trans (le_partialSups (f⁺) n ω)
    rw [Real.eNorm_eq_ofReal hnn, Pi.partialSups_apply, partialSups_apply]
    refine le_antisymm ?_ ?_
    · obtain ⟨k, hk, hsup⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_Iic (fun j ↦ (f⁺) j ω)
      rw [hsup, Pi.posPart_apply, Pi.posPart_apply, ENNReal.ofReal_posPart]
      exact le_iSup₂_of_le k (Finset.mem_Iic.1 hk) le_rfl
    · refine iSup₂_le fun k hk ↦ ?_
      rw [← ENNReal.ofReal_posPart]
      exact ENNReal.ofReal_le_ofReal
        (Finset.le_sup' (f := fun j ↦ (f⁺) j ω) (Finset.mem_Iic.2 hk))
  have hm_sup : AEStronglyMeasurable (partialSups (f⁺) n) μ := by
    rw [partialSups_apply]
    exact (Finset.sup'_induction _ _ (fun _ h₁ _ h₂ ↦ h₁.sup h₂) fun k _ ↦
      (hf.pos.stronglyAdapted k).mono (ℱ.le k)).aestronglyMeasurable
  calc eLpNorm (partialSups (f⁺) n) p μ
      ≤ eLpNorm (fun ω ↦ ⨆ k ∈ Set.Iic n, ENNReal.ofReal (f k ω)) p μ :=
        eLpNorm_mono_eNorm hm_sup fun ω ↦ by simpa only [eNorm_eq_self] using (heq ω).le
    _ ≤ p / (p - 1) * eLpNorm ((f⁺) n) p μ :=
        hf.eLpNorm_biSup_ofReal_le_mul_eLpNorm_posPart
          (Set.finite_Iic n).countable (fun _ hk ↦ hk) hp hp_top

/-- **Doob's discrete-time `Lᵖ` maximal inequality.** Requires nonnegativity only at the terminal
index `n` (`0 ≤ᵐ[μ] f n`) and no `MemLp` hypothesis. -/
theorem eLpNorm_partialSups_le
    (hf : Submartingale f ℱ μ) {n : ι} (hposn : 0 ≤ᵐ[μ] f n)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (partialSups f n) p μ ≤ p / (p - 1) * eLpNorm (f n) p μ := by
  rw [eLpNorm_congr_ae hposn.partialSups_posPart_eq.symm,
    eLpNorm_congr_ae hposn.posPart_eq.symm]
  exact hf.eLpNorm_partialSups_posPart_le n hp hp_top

/-- **Doob's discrete-time `Lᵖ` maximal inequality (positive-part Bochner moment form).** Requires
`MemLp` of `(f⁺) n` only at the terminal index `n`. -/
theorem integral_rpow_partialSups_posPart_le
    (hf : Submartingale f ℱ μ) (n : ι) {p : ℝ} (hp : 1 < p)
    (hn : MemLp ((f⁺) n) (ENNReal.ofReal p) μ) :
    ∫ ω, (partialSups (f⁺) n ω) ^ p ∂μ ≤ (p / (p - 1)) ^ p * ∫ ω, ((f⁺) n ω) ^ p ∂μ := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hp_enn : 1 < ENNReal.ofReal p := by
    rwa [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff hp0]
  have hbound := hf.eLpNorm_partialSups_posPart_le n hp_enn ENNReal.ofReal_ne_top
  rw [← ENNReal.ofReal_div_sub_one hp] at hbound
  exact integral_rpow_le_mul_integral_rpow_of_eLpNorm_le hp0 (div_pos hp0 (sub_pos.2 hp)).le
    (Eventually.of_forall fun ω ↦ (posPart_nonneg (f n ω)).trans (le_partialSups (f⁺) n ω))
    (Eventually.of_forall fun _ ↦ posPart_nonneg _) hn hbound

/-- **Doob's discrete-time `Lᵖ` maximal inequality (Bochner moment form).** Directly generalizes
`MeasureTheory.Submartingale.integral_sq_partialSups_le` from `p = 2` (constant `4`) to all
`1 < p < ∞` (constant `(p / (p - 1)) ^ p`), requiring nonnegativity and `MemLp` only at the
terminal index `n`. -/
theorem integral_rpow_partialSups_le
    (hf : Submartingale f ℱ μ) {n : ι} (hposn : 0 ≤ᵐ[μ] f n)
    {p : ℝ} (hp : 1 < p) (hn : MemLp (f n) (ENNReal.ofReal p) μ) :
    ∫ ω, (partialSups f n ω) ^ p ∂μ ≤ (p / (p - 1)) ^ p * ∫ ω, (f n ω) ^ p ∂μ := by
  rw [integral_congr_ae (hposn.partialSups_posPart_eq.symm.mono fun _ h ↦ congrArg (· ^ p) h),
    integral_congr_ae (hposn.posPart_eq.symm.mono fun _ h ↦ congrArg (· ^ p) h)]
  exact hf.integral_rpow_partialSups_posPart_le n hp hn.posPart

end DiscreteTimeLp

section ContinuousTimeStrongLp

variable [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
  [IsFiniteMeasure μ] {ℱ : Filtration ι m0} {f : ι → Ω → ℝ}

/-- Because `⨆ t ≤ T, ENNReal.ofReal (f t ω)` is almost surely finite, its `eLpNorm` agrees with
that of its `toReal` projection. -/
private lemma eLpNorm_toReal_iSup_ofReal_eq
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t) (p : ℝ≥0∞) :
    eLpNorm (fun ω ↦ (⨆ t ≤ T, ENNReal.ofReal (f t ω)).toReal) p μ =
      eLpNorm (fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (f t ω)) p μ := by
  have hY := hf.aemeasurable_iSup_ofReal hcont
  refine le_antisymm ?_ ?_
  · exact eLpNorm_mono_eNorm hY.ennreal_toReal.aestronglyMeasurable fun ω ↦ by
      simp [Real.eNorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal_le]
  · refine eLpNorm_mono_eNorm_ae hY.aestronglyMeasurable ?_
    filter_upwards [hf.ae_iSup_ofReal_lt_top hcont] with ω hω
    simp [Real.eNorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hω.ne]

/-- **Doob's continuous-time `Lᵖ` maximal inequality (positive-part `eLpNorm` form).** Holds for
all `1 < p < ∞` in `ℝ≥0∞` with no sign or `MemLp` assumption on `f`. -/
theorem eLpNorm_iSup_ofReal_le_mul_eLpNorm_posPart
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (f t ω)) p μ ≤
      p / (p - 1) * eLpNorm ((f⁺) T) p μ := by
  obtain ⟨S, hSc, hST, hae⟩ := exists_countable_subset_Iic_iSup_ofReal_ae_eq hcont
  rw [eLpNorm_congr_ae hae]
  exact hf.eLpNorm_biSup_ofReal_le_mul_eLpNorm_posPart hSc (fun _ hs ↦ hST hs) hp hp_top

/-- **Doob's continuous-time `Lᵖ` maximal inequality (`eLpNorm` form).** Holds for any real
submartingale `f` and `1 < p < ∞` with no sign or `MemLp` hypothesis, since
`‖(f⁺) T ω‖ ≤ ‖f T ω‖` pointwise. -/
theorem eLpNorm_iSup_ofReal_le
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (f t ω)) p μ ≤
      p / (p - 1) * eLpNorm (f T) p μ := by
  refine (hf.eLpNorm_iSup_ofReal_le_mul_eLpNorm_posPart hcont hp hp_top).trans
    (mul_le_mul_of_nonneg_left
      (eLpNorm_mono ((hf.pos.stronglyAdapted T).mono (ℱ.le T)).aestronglyMeasurable fun ω ↦ ?_)
      zero_le)
  simp only [Pi.posPart_apply]
  rw [Real.norm_of_nonneg (posPart_nonneg _), Real.norm_eq_abs, posPart_def]
  exact max_le (le_abs_self _) (abs_nonneg _)

/-- **Doob's continuous-time `Lᵖ` maximal inequality (lower-integral form).** Holds for all
`1 < p < ∞` with no sign or `MemLp` assumption on `f`. -/
theorem lintegral_iSup_ofReal_rpow_le
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    {p : ℝ} (hp : 1 < p) :
    ∫⁻ ω, (⨆ t ≤ T, ENNReal.ofReal (f t ω)) ^ p ∂μ ≤
      ENNReal.ofReal (p / (p - 1)) ^ p * ∫⁻ ω, ENNReal.ofReal (f T ω) ^ p ∂μ := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hp_enn : 1 < ENNReal.ofReal p := by
    rwa [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff hp0]
  have hp_ne0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  have hY_meas := (hf.aemeasurable_iSup_ofReal hcont).aestronglyMeasurable
  have hfT_meas : AEStronglyMeasurable ((f⁺) T) μ :=
    ((hf.pos.stronglyAdapted T).mono (ℱ.le T)).aestronglyMeasurable
  have hbound := ENNReal.rpow_le_rpow
    (hf.eLpNorm_iSup_ofReal_le_mul_eLpNorm_posPart hcont hp_enn ENNReal.ofReal_ne_top) hp0.le
  have hlhs := lintegral_rpow_enorm_eq_eLpNorm_rpow hp_ne0 ENNReal.ofReal_ne_top hY_meas
  have hrhs := lintegral_rpow_enorm_eq_eLpNorm_rpow hp_ne0 ENNReal.ofReal_ne_top hfT_meas
  rw [ENNReal.toReal_ofReal hp0.le] at hlhs hrhs
  simp only [eNorm_eq_self] at hlhs
  rw [← ENNReal.ofReal_div_sub_one hp, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
    ← hlhs, ← hrhs] at hbound
  refine hbound.trans_eq ?_
  congr 1
  refine lintegral_congr fun ω ↦ ?_
  simp only [Pi.posPart_apply]
  rw [Real.eNorm_eq_ofReal (posPart_nonneg (f T ω)), ENNReal.ofReal_posPart]

/-- **The running supremum of the positive part `(⨆ t ≤ T, ofReal (f t ω)).toReal` belongs to
`Lᵖ`** (`1 < p < ∞`) whenever `(f⁺) T ∈ Lᵖ`. -/
theorem memLp_toReal_iSup_ofReal_posPart
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) (hT : MemLp ((f⁺) T) p μ) :
    MemLp (fun ω ↦ (⨆ t ≤ T, ENNReal.ofReal (f t ω)).toReal) p μ := by
  have := (hf.aemeasurable_iSup_ofReal hcont).ennreal_toReal.aestronglyMeasurable
  rw [memLp_iff, eLpNorm_toReal_iSup_ofReal_eq hf hcont p]
  have hc_lt : p / (p - 1) < ∞ := ENNReal.div_lt_top hp_top (tsub_pos_of_lt hp).ne'
  exact (hf.eLpNorm_iSup_ofReal_le_mul_eLpNorm_posPart hcont hp hp_top).trans_lt
    (ENNReal.mul_lt_top hc_lt hT.eLpNorm_lt_top)

/-- **The running supremum of the positive part `(⨆ t ≤ T, ofReal (f t ω)).toReal` belongs to
`Lᵖ`** (`1 < p < ∞`) whenever `f T ∈ Lᵖ` (with no sign assumption on `f`). -/
theorem memLp_toReal_iSup_ofReal
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) (hT : MemLp (f T) p μ) :
    MemLp (fun ω ↦ (⨆ t ≤ T, ENNReal.ofReal (f t ω)).toReal) p μ :=
  hf.memLp_toReal_iSup_ofReal_posPart hcont hp hp_top hT.posPart

/-- **Doob's continuous-time `Lᵖ` maximal inequality (positive-part Bochner moment form).** For
`1 < p < ∞` and `(f⁺) T ∈ Lᵖ`, the `p`-th moment of `(⨆ t ≤ T, ofReal (f t ω)).toReal` is at most
`(p / (p - 1)) ^ p` times the `p`-th moment of `(f⁺) T`. -/
theorem integral_toReal_iSup_ofReal_rpow_le_mul_integral_posPart_rpow
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    {p : ℝ} (hp : 1 < p) (hT : MemLp ((f⁺) T) (ENNReal.ofReal p) μ) :
    ∫ ω, (⨆ t ≤ T, ENNReal.ofReal (f t ω)).toReal ^ p ∂μ ≤
      (p / (p - 1)) ^ p * ∫ ω, ((f⁺) T ω) ^ p ∂μ := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hp_enn : 1 < ENNReal.ofReal p := by
    rwa [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff hp0]
  have hbound : eLpNorm (fun ω ↦ (⨆ t ≤ T, ENNReal.ofReal (f t ω)).toReal) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (p / (p - 1)) * eLpNorm ((f⁺) T) (ENNReal.ofReal p) μ := by
    rw [eLpNorm_toReal_iSup_ofReal_eq hf hcont, ENNReal.ofReal_div_sub_one hp]
    exact hf.eLpNorm_iSup_ofReal_le_mul_eLpNorm_posPart hcont hp_enn ENNReal.ofReal_ne_top
  exact integral_rpow_le_mul_integral_rpow_of_eLpNorm_le hp0 (div_pos hp0 (sub_pos.2 hp)).le
    (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
    (Eventually.of_forall fun _ ↦ posPart_nonneg _) hT hbound

/-- **Doob's continuous-time `Lᵖ` maximal inequality (Bochner moment form).** Requires
nonnegativity and `MemLp` only at the terminal time `T`. -/
theorem integral_toReal_iSup_ofReal_rpow_le
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    (hposT : 0 ≤ᵐ[μ] f T) {p : ℝ} (hp : 1 < p) (hT : MemLp (f T) (ENNReal.ofReal p) μ) :
    ∫ ω, (⨆ t ≤ T, ENNReal.ofReal (f t ω)).toReal ^ p ∂μ ≤
      (p / (p - 1)) ^ p * ∫ ω, f T ω ^ p ∂μ := by
  rw [integral_congr_ae (hposT.posPart_eq.symm.mono fun _ hω ↦ congrArg (· ^ p) hω)]
  exact hf.integral_toReal_iSup_ofReal_rpow_le_mul_integral_posPart_rpow hcont hp hT.posPart

end ContinuousTimeStrongLp

end MeasureTheory.Submartingale

/-! ### Banach-valued martingales -/

namespace MeasureTheory.Martingale

variable {Ω E ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section DiscreteTime

variable [LinearOrder ι] [LocallyFiniteOrderBot ι] [IsFiniteMeasure μ]
  {ℱ : Filtration ι mΩ} {X : ι → Ω → E}

/-- **Doob's discrete-time `Lᵖ` maximal inequality for Banach-valued martingales (`eLpNorm` form).**
No `MemLp` assumption is needed. -/
theorem eLpNorm_partialSups_norm_le
    (hX : Martingale X ℱ μ) (n : ι) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (partialSups (fun k ω ↦ ‖X k ω‖) n) p μ ≤ p / (p - 1) * eLpNorm (X n) p μ := by
  rw [← eLpNorm_norm (X n) ((hX.stronglyAdapted n).mono (ℱ.le n)).aestronglyMeasurable]
  exact hX.norm.eLpNorm_partialSups_le (Eventually.of_forall fun _ ↦ norm_nonneg _) hp hp_top

/-- **Doob's discrete-time `Lᵖ` maximal inequality for Banach-valued martingales (Bochner moment
form).** Directly generalizes `MeasureTheory.Martingale.integral_sq_partialSups_norm_le` from
`p = 2` to all `1 < p < ∞`, requiring `MemLp` only at the terminal index `n`. -/
theorem integral_rpow_partialSups_norm_le
    (hX : Martingale X ℱ μ) (n : ι) {p : ℝ} (hp : 1 < p)
    (hn : MemLp (X n) (ENNReal.ofReal p) μ) :
    ∫ ω, (partialSups (fun k ω ↦ ‖X k ω‖) n ω) ^ p ∂μ ≤
      (p / (p - 1)) ^ p * ∫ ω, ‖X n ω‖ ^ p ∂μ :=
  hX.norm.integral_rpow_partialSups_le (Eventually.of_forall fun _ ↦ norm_nonneg _) hp hn.norm

end DiscreteTime

section CountableTime

variable [LinearOrder ι] [IsFiniteMeasure μ] {ℱ : Filtration ι mΩ} {M : ι → Ω → E}

/-- **Doob's `Lᵖ` maximal inequality on a countable set for Banach-valued martingales.** -/
theorem eLpNorm_biSup_eNorm_le
    (hM : Martingale M ℱ μ) {S : Set ι} (hS : S.Countable) {T : ι} (hST : ∀ t ∈ S, t ≤ T)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (fun ω ↦ ⨆ t ∈ S, ‖M t ω‖ₑ) p μ ≤ p / (p - 1) * eLpNorm (M T) p μ := by
  simp_rw [← ofReal_norm]
  rw [← eLpNorm_norm (M T) ((hM.stronglyAdapted T).mono (ℱ.le T)).aestronglyMeasurable]
  exact hM.norm.eLpNorm_biSup_ofReal_le hS hST hp hp_top

end CountableTime

section ContinuousTime

variable [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
  [IsFiniteMeasure μ] {ℱ : Filtration ι mΩ} {M : ι → Ω → E}

/-- **Unconditional event-refined `Lᵖ` Doob inequality for Banach-valued martingales
(lower-integral form).** Holds for all `1 ≤ p < ∞` and `ε : ℝ≥0` with no `MemLp` hypothesis. -/
theorem rpow_mul_measure_le_iSup_eNorm_le_setLIntegral
    (hM : Martingale M ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ M u ω) (Ioi t) t)
    (ε : ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
    (ε : ℝ≥0∞) ^ p * μ {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ‖M t ω‖ₑ} ≤
      ∫⁻ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ‖M t ω‖ₑ}, ‖M T ω‖ₑ ^ p ∂μ := by
  simp_rw [← ofReal_norm]
  exact hM.norm.rpow_mul_measure_le_iSup_le_setLIntegral
    (hcont.mono fun _ hω t ht ↦ (hω t ht).norm) ε hp

/-- **Event-refined `Lᵖ` Doob inequality for Banach-valued martingales (Bochner form).** Requires
`MemLp` only at the terminal time `T`. -/
theorem rpow_mul_measure_le_iSup_eNorm_le_setIntegral
    (hM : Martingale M ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ M u ω) (Ioi t) t)
    (ε : ℝ≥0) {p : ℝ} (hp : 1 ≤ p) (hT : MemLp (M T) (ENNReal.ofReal p) μ) :
    (ε : ℝ≥0∞) ^ p * μ {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ‖M t ω‖ₑ} ≤
      ENNReal.ofReal (∫ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ‖M t ω‖ₑ}, ‖M T ω‖ ^ p ∂μ) := by
  simp_rw [← ofReal_norm]
  exact hM.norm.rpow_mul_measure_le_iSup_le_setIntegral
    (hcont.mono fun _ hω t ht ↦ (hω t ht).norm) (Eventually.of_forall fun _ ↦ norm_nonneg _)
    ε hp hT.norm

/-- **Doob's continuous-time `Lᵖ` maximal inequality for Banach-valued martingales (lower-integral
form).** Holds for all `1 < p < ∞` with no `MemLp` hypothesis. -/
theorem lintegral_iSup_eNorm_rpow_le
    (hM : Martingale M ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ M u ω) (Ioi t) t)
    {p : ℝ} (hp : 1 < p) :
    ∫⁻ ω, (⨆ t ≤ T, ‖M t ω‖ₑ) ^ p ∂μ ≤
      ENNReal.ofReal (p / (p - 1)) ^ p * ∫⁻ ω, ‖M T ω‖ₑ ^ p ∂μ := by
  simp_rw [← ofReal_norm]
  exact hM.norm.lintegral_iSup_ofReal_rpow_le (hcont.mono fun _ hω t ht ↦ (hω t ht).norm) hp

/-- **Doob's continuous-time `Lᵖ` maximal inequality for Banach-valued martingales (`eLpNorm`
form).** Holds for all `1 < p < ∞` in `ℝ≥0∞` with no `MemLp` hypothesis. -/
theorem eLpNorm_iSup_eNorm_le
    (hM : Martingale M ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ M u ω) (Ioi t) t)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (fun ω ↦ ⨆ t ≤ T, ‖M t ω‖ₑ) p μ ≤ p / (p - 1) * eLpNorm (M T) p μ := by
  simp_rw [← ofReal_norm]
  rw [← eLpNorm_norm (M T) ((hM.stronglyAdapted T).mono (ℱ.le T)).aestronglyMeasurable]
  exact hM.norm.eLpNorm_iSup_ofReal_le (hcont.mono fun _ hω t ht ↦ (hω t ht).norm) hp hp_top

/-- **The real running norm supremum of a right-continuous martingale belongs to `Lᵖ`**
(`1 < p < ∞`) whenever `M T ∈ Lᵖ`. -/
theorem memLp_toReal_iSup_eNorm
    (hM : Martingale M ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ M u ω) (Ioi t) t)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) (hT : MemLp (M T) p μ) :
    MemLp (fun ω ↦ (⨆ t ≤ T, ‖M t ω‖ₑ).toReal) p μ := by
  simp_rw [← ofReal_norm]
  exact hM.norm.memLp_toReal_iSup_ofReal (hcont.mono fun _ hω t ht ↦ (hω t ht).norm) hp hp_top
    hT.norm

/-- **Doob's continuous-time `Lᵖ` maximal inequality for Banach-valued martingales (Bochner moment
form).** Requires `MemLp` only at the terminal time `T`. -/
theorem integral_toReal_iSup_eNorm_rpow_le
    (hM : Martingale M ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ M u ω) (Ioi t) t)
    {p : ℝ} (hp : 1 < p) (hT : MemLp (M T) (ENNReal.ofReal p) μ) :
    ∫ ω, (⨆ t ≤ T, ‖M t ω‖ₑ).toReal ^ p ∂μ ≤
      (p / (p - 1)) ^ p * ∫ ω, ‖M T ω‖ ^ p ∂μ := by
  simp_rw [← ofReal_norm]
  exact hM.norm.integral_toReal_iSup_ofReal_rpow_le
    (hcont.mono fun _ hω t ht ↦ (hω t ht).norm) (Eventually.of_forall fun _ ↦ norm_nonneg _)
    hp hT.norm

/-- **Uniform `Lᵖ` path convergence from terminal `Lᵖ` convergence (`1 < p < ∞`).** For
right-continuous Banach-valued martingales before `T`, convergence of `M n T → Y T` in `Lᵖ` implies
`Lᵖ` convergence of the uniform running error `⨆ t ≤ T, ‖M n t ω - Y t ω‖ₑ` to `0`. -/
theorem tendsto_eLpNorm_iSup_eNorm_sub {α : Type*} {Y : ι → Ω → E}
    (hY : Martingale Y ℱ μ) {M : α → ι → Ω → E} (hM : ∀ n, Martingale (M n) ℱ μ)
    {T : ι} {l : Filter α}
    (hYcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ Y u ω) (Ioi t) t)
    (hMcont : ∀ n, ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ M n u ω) (Ioi t) t)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞)
    (hlim : Tendsto (fun n ↦ eLpNorm (M n T - Y T) p μ) l (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun ω ↦ ⨆ t ≤ T, ‖M n t ω - Y t ω‖ₑ) p μ) l (𝓝 0) := by
  have hc_ne : p / (p - 1) ≠ ∞ := (ENNReal.div_lt_top hp_top (tsub_pos_of_lt hp).ne').ne
  have hbound (n : α) :
      eLpNorm (fun ω ↦ ⨆ t ≤ T, ‖M n t ω - Y t ω‖ₑ) p μ ≤
        p / (p - 1) * eLpNorm (M n T - Y T) p μ := by
    have hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ (M n - Y) u ω) (Ioi t) t := by
      filter_upwards [hMcont n, hYcont] with ω h₁ h₂ t ht
      exact (h₁ t ht).sub (h₂ t ht)
    simpa only [Pi.sub_apply] using ((hM n).sub hY).eLpNorm_iSup_eNorm_le hcont hp hp_top
  have hmul : Tendsto (fun n ↦ p / (p - 1) * eLpNorm (M n T - Y T) p μ) l (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim (.inr hc_ne)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul
    (fun _ ↦ zero_le) hbound

end ContinuousTime

end MeasureTheory.Martingale

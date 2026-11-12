/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.AccumulatedEnergy
public import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# Bounded-energy truncations of predictable integrands

Truncate a predictable integrand at a deterministic budget for its accumulated square
energy. Each truncated path has total square energy at most that budget, even if the
original path has infinite energy. Under a finite sample measure the truncation therefore
belongs to the expected-square-energy domain. No moment assumption on the original
integrand or usual conditions on the filtration are needed.

On any finite-energy path and horizon, the finite-budget truncations eventually agree
with the original integrand on that horizon. Brownian-specific integrability and almost-everywhere
recovery results are in `TauCeti.Probability.BrownianMotion.Integral.Energy.Truncation`.
These approximations do not themselves construct stochastic integrals or stopping times.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

variable {Ω E : Type*} [NormedAddCommGroup E]

/-- Retain an integrand only while its accumulated square energy is at most the budget `C`.
The closed budget convention includes equality and does not truncate the integrand's size. -/
def energyTruncation (μ : Measure ℝ≥0) (H : ℝ≥0 → Ω → E) (C : ℝ≥0∞)
    (t : ℝ≥0) (ω : Ω) : E :=
  if μ.accumulatedEnergy H t ω ≤ C then H t ω else 0

theorem energyTruncation_def (μ : Measure ℝ≥0) (H : ℝ≥0 → Ω → E) (C : ℝ≥0∞) :
    μ.energyTruncation H C = fun t ω ↦
      if μ.accumulatedEnergy H t ω ≤ C then H t ω else 0 := (rfl)

/-- An infinite budget leaves the integrand unchanged. -/
@[simp]
theorem energyTruncation_top (μ : Measure ℝ≥0) (H : ℝ≥0 → Ω → E) :
    μ.energyTruncation H ∞ = H := by
  ext t ω
  simp [energyTruncation_def]

/-- At an energy within budget, truncation leaves the integrand unchanged. -/
@[simp]
theorem energyTruncation_of_le {μ : Measure ℝ≥0} {H : ℝ≥0 → Ω → E}
    {C : ℝ≥0∞} {t : ℝ≥0} {ω : Ω} (h : μ.accumulatedEnergy H t ω ≤ C) :
    μ.energyTruncation H C t ω = H t ω := by
  simp [energyTruncation_def, h]

/-- After the budget is exceeded the truncated integrand vanishes. -/
@[simp]
theorem energyTruncation_of_lt {μ : Measure ℝ≥0} {H : ℝ≥0 → Ω → E}
    {C : ℝ≥0∞} {t : ℝ≥0} {ω : Ω} (h : C < μ.accumulatedEnergy H t ω) :
    μ.energyTruncation H C t ω = 0 := by
  simp [energyTruncation_def, not_le.mpr h]

/-- A terminal energy within budget leaves the entire path up to that horizon unchanged. -/
theorem energyTruncation_eqOn {μ : Measure ℝ≥0} {H : ℝ≥0 → Ω → E}
    {C : ℝ≥0∞} {T : ℝ≥0} {ω : Ω} (h : μ.accumulatedEnergy H T ω ≤ C) :
    EqOn (fun t ↦ μ.energyTruncation H C t ω) (fun t ↦ H t ω) (Iic T) :=
  fun _ ht ↦ energyTruncation_of_le ((μ.monotone_accumulatedEnergy H ω ht).trans h)

/-- The total square energy of each truncated path is bounded by its budget. No
measurability, integrability or atomlessness assumption is needed for this pathwise bound. -/
theorem lintegral_enorm_sq_energyTruncation_le (μ : Measure ℝ≥0) (H : ℝ≥0 → Ω → E)
    (C : ℝ≥0∞) (ω : Ω) :
    ∫⁻ t, ‖μ.energyTruncation H C t ω‖ₑ ^ 2 ∂μ ≤ C := by
  have heq (t : ℝ≥0) : ‖μ.energyTruncation H C t ω‖ₑ ^ 2 =
      {u | ∫⁻ v in Iic u, ‖H v ω‖ₑ ^ 2 ∂μ ≤ C}.indicator
        (fun u ↦ ‖H u ω‖ₑ ^ 2) t := by
    simp only [energyTruncation_def, accumulatedEnergy_def, Set.indicator_apply,
      Set.mem_ofPred_eq]
    split_ifs <;> simp
  simpa only [heq] using
    μ.lintegral_indicator_setLIntegral_Iic_le (fun t ↦ ‖H t ω‖ₑ ^ 2) C

/-- On a finite-energy horizon, finite budgets eventually recover the whole original path
on that horizon. The required budget may depend on the path and horizon. -/
theorem eventually_energyTruncation_eqOn {μ : Measure ℝ≥0} {H : ℝ≥0 → Ω → E}
    {T : ℝ≥0} {ω : Ω} (h : μ.accumulatedEnergy H T ω < ∞) :
    ∀ᶠ C : ℝ≥0 in atTop, EqOn (fun t ↦ μ.energyTruncation H C t ω)
      (fun t ↦ H t ω) (Iic T) := by
  filter_upwards [eventually_ge_atTop (μ.accumulatedEnergy H T ω).toNNReal] with C hC
  exact energyTruncation_eqOn
    ((ENNReal.coe_toNNReal h.ne).symm.le.trans (ENNReal.coe_le_coe.mpr hC))

end MeasureTheory.Measure

namespace MeasureTheory.AEStronglyMeasurable

/-- Under a finite sample measure, finite-budget truncations of an a.e. strongly measurable
process are square integrable for the entire time-product measure. Neither a filtration nor
atomlessness of the time measure is needed. -/
theorem memLp_energyTruncation {Ω E : Type*} [NormedAddCommGroup E] [MeasurableSpace Ω]
    {μ : Measure ℝ≥0} [SFinite μ] {P : Measure Ω} [IsFiniteMeasure P]
    {H : ℝ≥0 → Ω → E} (hH : AEStronglyMeasurable (Function.uncurry H) (μ.prod P))
    (C : ℝ≥0) : MemLp (Function.uncurry (μ.energyTruncation H C)) 2 (μ.prod P) := by
  classical
  let G := hH.mk (Function.uncurry H)
  have hG : StronglyMeasurable G := hH.stronglyMeasurable_mk
  have hA : Measurable (fun p : ℝ≥0 × Ω ↦ μ.accumulatedEnergy (Function.curry G) p.1 p.2) := by
    have hm : Measurable (fun q : (ℝ≥0 × Ω) × ℝ≥0 ↦
        if q.2 ≤ q.1.1 then ‖G (q.2, q.1.2)‖ₑ ^ 2 else 0) :=
      Measurable.ite (measurableSet_le measurable_snd measurable_fst.fst)
        ((hG.comp_measurable (measurable_snd.prodMk measurable_fst.snd)).eNorm.pow_const 2)
        measurable_const
    simpa only [Measure.accumulatedEnergy_def, ← lintegral_indicator measurableSet_Iic,
      Set.indicator_apply, mem_Iic, Function.curry] using hm.lintegral_prod_right' (ν := μ)
  have hAe : ∀ᵐ ω ∂P, ∀ t, μ.accumulatedEnergy H t ω =
      μ.accumulatedEnergy (Function.curry G) t ω := by
    filter_upwards [Measure.ae_ae_of_ae_prod
      (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hH.ae_eq_mk)] with ω hω t
    simp only [Measure.accumulatedEnergy_def]
    exact lintegral_congr_ae (ae_restrict_of_ae
      (hω.mono fun s hs ↦ congrArg (fun x : E ↦ ‖x‖ₑ ^ 2) hs))
  have hmG : StronglyMeasurable (fun p : ℝ≥0 × Ω ↦
      if μ.accumulatedEnergy (Function.curry G) p.1 p.2 ≤ C then G p else 0) :=
    hG.ite (measurableSet_le hA measurable_const) stronglyMeasurable_zero
  have hm : AEStronglyMeasurable (Function.uncurry (μ.energyTruncation H C)) (μ.prod P) := by
    refine hmG.aestronglyMeasurable.congr ?_
    filter_upwards [hH.ae_eq_mk, Measure.quasiMeasurePreserving_snd.ae hAe] with p hp hAp
    simp only [Function.uncurry] at hp
    simp only [Function.uncurry, Measure.energyTruncation_def, hAp, hp, G]
  rw [hm.memLp_two_iff_lintegral_enorm_sq_lt_top]
  calc
    _ = ∫⁻ ω, ∫⁻ t, ‖μ.energyTruncation H C t ω‖ₑ ^ 2 ∂μ ∂P :=
      lintegral_prod_symm _ (hm.eNorm.pow_const 2)
    _ ≤ ∫⁻ _ : Ω, (C : ℝ≥0∞) ∂P :=
      lintegral_mono (μ.lintegral_enorm_sq_energyTruncation_le H C)
    _ < ∞ := by simp [ENNReal.mul_lt_top, measure_lt_top]

end MeasureTheory.AEStronglyMeasurable

namespace MeasureTheory.IsStronglyPredictable

variable {Ω E : Type*} [NormedAddCommGroup E] {mΩ : MeasurableSpace Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → E}
  (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]

/-- Energy-budget truncation preserves literal predictability on the original filtration. -/
theorem energyTruncation (hH : IsStronglyPredictable ℱ H) (C : ℝ≥0∞) :
    IsStronglyPredictable ℱ (μ.energyTruncation H C) := by
  simp only [Measure.energyTruncation_def]
  exact hH.ite (measurableSet_le
    (hH.isStronglyProgressive.isStronglyPredictable_accumulatedEnergy μ).measurable
      measurable_const) stronglyMeasurable_zero

omit [NullSingletonClass μ] in
/-- Under a finite sample measure, finite-budget truncations are square integrable for the
entire time-product measure, not just separately on each finite horizon. Atomlessness of the
time measure is not required. -/
theorem memLp_energyTruncation {P : Measure Ω} [IsFiniteMeasure P]
    (hH : IsStronglyPredictable ℱ H) (C : ℝ≥0) :
    MemLp (Function.uncurry (μ.energyTruncation H C)) 2 (μ.prod P) :=
  ((hH.mono ℱ.predictable_le_prod).aestronglyMeasurable).memLp_energyTruncation C

end MeasureTheory.IsStronglyPredictable

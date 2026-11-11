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

On any finite-energy path and horizon, the integer-budget truncations eventually agree
with the original integrand on that horizon. Brownian-specific integrability and almost-everywhere
recovery results are in `TauCeti.Probability.BrownianMotion.Integral.EnergyTruncation`.
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
theorem lintegral_sq_energyTruncation_le (μ : Measure ℝ≥0) (H : ℝ≥0 → Ω → E)
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

/-- On a finite-energy horizon, integer budgets eventually recover the whole original path
on that horizon. The required budget may depend on the path and horizon. -/
theorem eventually_energyTruncation_eqOn {μ : Measure ℝ≥0} {H : ℝ≥0 → Ω → E}
    {T : ℝ≥0} {ω : Ω} (h : μ.accumulatedEnergy H T ω < ∞) :
    ∀ᶠ n : ℕ in atTop, EqOn (fun t ↦ μ.energyTruncation H n t ω)
      (fun t ↦ H t ω) (Iic T) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (μ.accumulatedEnergy H T ω).toReal
  have hAn : μ.accumulatedEnergy H T ω ≤ (n : ℝ≥0∞) := by
    apply (ENNReal.toReal_le_toReal h.ne (ENNReal.natCast_ne_top n)).mp
    simpa using hn
  filter_upwards [eventually_ge_atTop n] with m hm
  exact energyTruncation_eqOn (hAn.trans (by exact_mod_cast hm))

end MeasureTheory.Measure

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

/-- Under a finite sample measure, finite-budget truncations are square integrable for the
entire time-product measure, not just separately on each finite horizon. -/
theorem memLp_energyTruncation {P : Measure Ω} [IsFiniteMeasure P]
    (hH : IsStronglyPredictable ℱ H) (C : ℝ≥0) :
    MemLp (Function.uncurry (μ.energyTruncation H C)) 2 (μ.prod P) := by
  have hm := (hH.energyTruncation μ C).mono ℱ.predictable_le_prod
  rw [hm.aestronglyMeasurable.memLp_two_iff_lintegral_enorm_sq_lt_top]
  calc
    _ = ∫⁻ ω, ∫⁻ t, ‖μ.energyTruncation H C t ω‖ₑ ^ 2 ∂μ ∂P :=
      lintegral_prod_symm _ (hm.enorm.pow_const 2).aemeasurable
    _ ≤ ∫⁻ _ : Ω, (C : ℝ≥0∞) ∂P :=
      lintegral_mono (μ.lintegral_sq_energyTruncation_le H C)
    _ < ∞ := by simp [ENNReal.mul_lt_top, measure_lt_top]

end MeasureTheory.IsStronglyPredictable

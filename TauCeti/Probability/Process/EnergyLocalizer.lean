/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.AccumulatedEnergy
public import TauCeti.Probability.Process.HittingTime
public import TauCeti.Probability.Process.StochasticInterval
public import TauCeti.Probability.Process.Stopping

/-!
# Closed-level raw energy localizers

The first closed-level hit of the repaired accumulated square-energy clock is a stopping
time on the original filtration. Up to and including that time the repaired clock is bounded
by the level. For paths with finite energy on every finite horizon these localizers tend to
infinity. Neither right continuity nor completeness of the filtration is required.

The repair removes the integrand where its original accumulated energy is infinite; its
clock is continuous even on paths with immediate right-hand energy explosion. These are
actual closed-level hits, not strict-level infima or augmented-filtration stopping times.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

variable {Ω E : Type*} [NormedAddCommGroup E]

/-- First closed-level hit of the accumulated energy of the finite-energy cutoff.
A positive level gives a strictly positive time for an atomless time measure. -/
def energyLocalizer (μ : Measure ℝ≥0) (H : ℝ≥0 → Ω → E) (C : ℝ≥0) : Ω → WithTop ℝ≥0 :=
  hittingAfter (μ.accumulatedEnergy (μ.finiteEnergyCutoff H)) (Ici (C : ℝ≥0∞)) 0

theorem energyLocalizer_def (μ : Measure ℝ≥0) (H : ℝ≥0 → Ω → E) (C : ℝ≥0) :
    μ.energyLocalizer H C =
      hittingAfter (μ.accumulatedEnergy (μ.finiteEnergyCutoff H)) (Ici (C : ℝ≥0∞)) 0 := (rfl)

/-- The zero energy level is hit immediately, including for an unrepaired divergent input. -/
@[simp]
theorem energyLocalizer_zero_level (μ : Measure ℝ≥0) (H : ℝ≥0 → Ω → E) :
    μ.energyLocalizer H 0 = 0 := by
  ext ω
  apply le_antisymm
  · rw [energyLocalizer_def]
    exact hittingAfter_le_of_mem le_rfl (by simp)
  · exact bot_le

/-- The zero integrand never hits a positive energy level. -/
@[simp]
theorem energyLocalizer_zero (μ : Measure ℝ≥0) {C : ℝ≥0} (hC : 0 < C) :
    μ.energyLocalizer (0 : ℝ≥0 → Ω → E) C = fun _ ↦ ⊤ := by
  ext ω
  rw [energyLocalizer_def, hittingAfter_eq_top_iff]
  intro t _
  simp [accumulatedEnergy_def, finiteEnergyCutoff_def, hC.ne']

variable (μ : Measure ℝ≥0) [NullSingletonClass μ] (H : ℝ≥0 → Ω → E)

/-- A closed-level energy hit occurs by `t` exactly when the repaired clock has reached
that level at `t`. Both endpoints are included. -/
-- Like the native hitting-time equivalence, this is an explicit rewrite rule. Simplification
-- normalizes the time coercion through ENNReal, losing the native WithTop stopping-time form.
theorem energyLocalizer_le_iff (C : ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    μ.energyLocalizer H C ω ≤ t ↔
      (C : ℝ≥0∞) ≤ μ.accumulatedEnergy (μ.finiteEnergyCutoff H) t ω := by
  rw [energyLocalizer_def, isClosed_Ici.hittingAfter_le_iff
    (μ.continuous_accumulatedEnergy_finiteEnergyCutoff H ω)]
  constructor
  · rintro ⟨s, hs, hC⟩
    exact hC.trans (μ.monotone_accumulatedEnergy _ ω hs.2)
  · exact fun hC ↦ ⟨t, ⟨bot_le, le_rfl⟩, hC⟩

/-- Positive energy levels cannot be hit at time zero. -/
theorem energyLocalizer_pos {C : ℝ≥0} (hC : 0 < C) (ω : Ω) :
    0 < μ.energyLocalizer H C ω := by
  rw [← not_le, ← WithTop.coe_zero, energyLocalizer_le_iff]
  simpa using hC.ne'

omit [NullSingletonClass μ] in
/-- Closed energy levels give pointwise increasing hitting times. -/
theorem monotone_energyLocalizer (ω : Ω) : Monotone (fun C ↦ μ.energyLocalizer H C ω) := by
  intro C D hCD
  simp only [energyLocalizer_def]
  exact hittingAfter_apply_anti _ _ _ (Ici_subset_Ici.mpr (ENNReal.coe_le_coe.mpr hCD))

/-- The repaired clock remains at most at its level up to and including the closed hit. -/
theorem stoppedProcess_accumulatedEnergy_energyLocalizer_le (C : ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    stoppedProcess (μ.accumulatedEnergy (μ.finiteEnergyCutoff H))
      (μ.energyLocalizer H C) t ω ≤ C := by
  refine stoppedProcess_mem (s := Iic (C : ℝ≥0∞)) ?_ t
  intro s hs
  exact (μ.continuous_accumulatedEnergy_finiteEnergyCutoff H ω).le_of_le_hittingAfter_Ici
    (a := 0) bot_le (by simp) (by simpa only [energyLocalizer_def] using hs)

/-- Stopping the repaired integrand at its closed-level energy hit bounds its square energy
on every finite horizon. The bound is pathwise and uses no measurability assumptions. -/
theorem setLIntegral_enorm_sq_ite_le_energyLocalizer_le (C : ℝ≥0) (T : ℝ≥0) (ω : Ω) :
    (∫⁻ t in Ioc 0 T, ‖if (t : WithTop ℝ≥0) ≤ μ.energyLocalizer H C ω then
      μ.finiteEnergyCutoff H t ω else 0‖ₑ ^ 2 ∂μ) ≤ C := by
  have hclock : (fun u ω ↦ ∫⁻ s in Ioc 0 u, ‖μ.finiteEnergyCutoff H s ω‖ₑ ^ 2 ∂μ) =
      μ.accumulatedEnergy (μ.finiteEnergyCutoff H) := by
    funext u ω
    exact (μ.accumulatedEnergy_eq_setLIntegral_Ioc _ u ω).symm
  have heq := TauCeti.setLIntegral_ite_le_eq_stoppedProcess
    (fun t ω ↦ ‖μ.finiteEnergyCutoff H t ω‖ₑ ^ 2) (μ.energyLocalizer H C) μ 0 T ω
  rw [hclock] at heq
  calc
    _ = stoppedProcess (μ.accumulatedEnergy (μ.finiteEnergyCutoff H))
        (μ.energyLocalizer H C) T ω := by
      simpa only [apply_ite, eNorm_zero, ite_pow, zero_pow (by norm_num : 2 ≠ 0)] using heq
    _ ≤ C := μ.stoppedProcess_accumulatedEnergy_energyLocalizer_le H C T ω

/-- On a path with finite original energy at every finite horizon, closed-level energy
localizers tend to infinity as the level increases. -/
theorem tendsto_energyLocalizer (ω : Ω)
    (hfinite : ∀ t, μ.accumulatedEnergy H t ω < ∞) :
    Tendsto (fun C ↦ μ.energyLocalizer H C ω) atTop (𝓝 ⊤) := by
  apply (WithTop.tendsto_nhds_top_iff _).mpr
  intro t
  filter_upwards [eventually_gt_atTop (μ.accumulatedEnergy H t ω).toNNReal] with C hC
  rw [← not_le, energyLocalizer_le_iff]
  have hlt : μ.accumulatedEnergy H t ω < (C : ℝ≥0∞) := by
    rw [← ENNReal.coe_toNNReal (hfinite t).ne, ENNReal.coe_lt_coe]
    exact hC
  exact not_le.mpr ((μ.accumulatedEnergy_finiteEnergyCutoff_le H t ω).trans_lt hlt)

end MeasureTheory.Measure

namespace MeasureTheory.IsStronglyPredictable

variable {Ω E : Type*} [NormedAddCommGroup E] {mΩ : MeasurableSpace Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → E}
  (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]

/-- Closed-level hits of the repaired energy are stopping times on the original filtration,
without usual conditions or an almost-sure path-continuity assumption. -/
theorem isStoppingTime_energyLocalizer (hH : IsStronglyPredictable ℱ H) (C : ℝ≥0) :
    IsStoppingTime ℱ (μ.energyLocalizer H C) := by
  intro t
  simp_rw [μ.energyLocalizer_le_iff]
  exact measurableSet_le measurable_const
    (((hH.finiteEnergyCutoff μ).isStronglyProgressive.isStronglyPredictable_accumulatedEnergy
      μ).stronglyAdapted t).measurable

end MeasureTheory.IsStronglyPredictable

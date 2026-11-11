/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.EnergyTruncation
public import TauCeti.Probability.BrownianMotion.Integral.Integrable

/-!
# Energy truncations in Brownian integrand domains

Finite-budget truncations of predictable real processes are Brownian integrable under a finite
sample measure, without moment assumptions on the original process. For a locally
Brownian-integrable process, integer-budget truncations eventually recover the original process
on every finite horizon outside one common sample-null set. These are integrand-domain results;
they do not construct stochastic integrals or stopping times.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ}

/-- Every finite-budget truncation of a predictable real process is Brownian integrable
under a finite sample measure, even when the original process has infinite expected energy. -/
theorem MeasureTheory.IsStronglyPredictable.brownianIntegrable_energyTruncation
    [IsFiniteMeasure P] (hH : IsStronglyPredictable ℱ H) (C : ℝ≥0) :
    TauCeti.BrownianIntegrable ℱ P
      ((volume.comap ((↑) : ℝ≥0 → ℝ)).energyTruncation H C) := by
  let μ := volume.comap ((↑) : ℝ≥0 → ℝ)
  refine ⟨hH.energyTruncation μ C, fun T ↦ ?_⟩
  rw [NNReal.comap_volume_restrict_Ioc]
  exact (hH.memLp_energyTruncation μ C).mono_measure
    (Measure.prod_mono Measure.restrict_le_self le_rfl)

namespace TauCeti

/-- For a locally Brownian-integrable process, on one sample-full event and each finite
horizon, integer-budget truncations eventually agree with the original process everywhere
on that horizon. There is no uniform deterministic budget across samples. -/
theorem LocallyBrownianIntegrable.ae_eventually_energyTruncation_eqOn
    (hH : LocallyBrownianIntegrable ℱ P H) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∀ᶠ n : ℕ in atTop,
      EqOn (fun t ↦ (volume.comap ((↑) : ℝ≥0 → ℝ)).energyTruncation H n t ω)
        (fun t ↦ H t ω) (Iic T) := by
  let μ := volume.comap ((↑) : ℝ≥0 → ℝ)
  filter_upwards [hH.ae_memLp] with ω hω
  intro T
  have heq : Ioc 0 T =ᵐ[μ] Iic T := by
    simpa only [← bot_eq_zero, Icc_bot] using (Ioc_ae_eq_Icc (μ := μ) (a := 0) (b := T))
  have hfinite := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num) (by norm_num) (hω T).aestronglyMeasurable).mp (hω T)
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at hfinite
  rw [NNReal.comap_volume_restrict_Ioc, Measure.restrict_congr_set heq] at hfinite
  exact μ.eventually_energyTruncation_eqOn
    (by simpa only [Measure.accumulatedEnergy_def] using hfinite)

end TauCeti

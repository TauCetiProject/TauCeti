/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.PolynomialGrowth
public import TauCeti.Probability.BrownianMotion.Integral.Integrable

/-!
# Expected square energy of geometric Brownian motion

Geometric Brownian motion driven by a predictable filtered Brownian version is a predictable
Brownian integrand with finite expected square energy on every finite horizon. Almost-sure
right continuity of the driving paths suffices. The initial value and the drift and volatility
are arbitrary deterministic real numbers, including zero.

This connects the geometric Brownian moment bounds to the expected-energy integration domain.
In particular it supplies the stock factor in a delta hedge's Brownian gains coefficient.
Predictability is explicit: almost-sure continuity of an adapted raw version alone does not
make that raw version predictable. The predictable Brownian replacement theorem can supply
this hypothesis without completing or changing the filtration.

The proof uses the existing polynomial-growth time-product estimate, not a new moment or
stochastic-integral construction.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  §3.2 and §5.6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- Geometric Brownian motion with deterministic initial value has finite expected square
energy on each finite horizon. A predictable driving version gives literal predictability of
the integrand on the original filtration. No positivity or nonzero-volatility assumption is
needed. -/
theorem brownianIntegrable_geometricBrownianMotion (hW : IsFilteredPreBrownianReal ℱ W P)
    (hp : IsStronglyPredictable ℱ W) (hc : ∀ᵐ ω ∂P, IsRightContinuous (fun t ↦ W t ω))
    (s μ σ : ℝ) : BrownianIntegrable ℱ P (geometricBrownianMotion s μ σ W) := by
  have hpred (a : ℝ) : IsStronglyPredictable ℱ (geometricBrownianMotion a μ σ W) := by
    have ht := ℱ.measurable_fst_predictable.coe_nnreal_real
    have hw := hp.measurable
    simpa only [IsStronglyPredictable, Function.uncurry_def, geometricBrownianMotion_def,
      Pi.add_apply] using
      (((ht.const_mul (μ - σ ^ 2 / 2)).add (hw.const_mul σ)).exp.const_mul a).stronglyMeasurable
  have hunit : BrownianIntegrable ℱ P (geometricBrownianMotion 1 μ σ W) := by
    refine ⟨hpred 1, fun T ↦ ?_⟩
    have ht : ∀ᵐ t ∂(volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ), t ≤ T := by
      rw [NNReal.comap_volume_restrict_Ioc]
      exact (ae_restrict_mem measurableSet_Ioc).mono fun _ h ↦ h.2
    have hm := hW.memLp_price_geometricBrownianMotion_prod
      (hc.mono fun ω hω t _ ↦ hω t) one_pos μ σ 1
      (C := fun x _ ↦ x) (A := 1)
      (fun x hx t _ ↦ by simp only [abs_of_pos hx, rpow_one, one_mul]; linarith)
      ht ((hpred 1).mono ℱ.predictable_le_prod).aestronglyMeasurable
    exact hm
  -- Scaling the unit-initial process avoids imposing positivity on the initial value.
  convert hunit.const_mul s using 1
  ext t ω
  simp only [geometricBrownianMotion_def, one_mul]

end TauCeti.Probability.IsFilteredPreBrownianReal

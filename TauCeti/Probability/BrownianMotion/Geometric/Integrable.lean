/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Geometric.Basic
public import TauCeti.Probability.BrownianMotion.Integral.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Expected square energy of geometric Brownian motion

Geometric Brownian motion driven by a predictable pre-Brownian process is a predictable
Brownian integrand with finite expected square energy on every finite horizon. Neither path
continuity nor increment independence from the filtration is needed. The initial value and
the drift and volatility are arbitrary deterministic real numbers, including zero.

This connects the geometric Brownian moment bounds to the expected-energy integration domain.
In particular it supplies the stock factor in a delta hedge's Brownian gains coefficient.
Predictability is explicit: almost-sure continuity of an adapted raw version alone does not
make that raw version predictable. The predictable Brownian replacement theorem can supply
this hypothesis without completing or changing the filtration.

The proof uses Tonelli's theorem and the existing explicit second moment, not a path-supremum
estimate or a new stochastic-integral construction.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  §3.2 and §5.6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

open TauCeti TauCeti.Probability

namespace MeasureTheory.IsStronglyPredictable

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- The geometric Brownian formula preserves predictability, without any assumption on
the law of the driving process. -/
theorem geometricBrownianMotion (hp : IsStronglyPredictable ℱ W) (s μ σ : ℝ) :
    IsStronglyPredictable ℱ (TauCeti.Probability.geometricBrownianMotion s μ σ W) := by
  have ht := ℱ.measurable_fst_predictable.coe_nnreal_real
  have hw := hp.measurable
  simpa only [IsStronglyPredictable, Function.uncurry_def, geometricBrownianMotion_def,
    Pi.add_apply] using
    (((ht.const_mul (μ - σ ^ 2 / 2)).add (hw.const_mul σ)).exp.const_mul s).stronglyMeasurable

end MeasureTheory.IsStronglyPredictable

namespace ProbabilityTheory.IsPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- Geometric Brownian motion with deterministic initial value has finite expected square
energy on each finite horizon. A predictable driving version gives literal predictability of
the integrand on the original filtration. No positivity or nonzero-volatility assumption is
needed. -/
theorem brownianIntegrable_geometricBrownianMotion (hW : IsPreBrownianReal W P)
    (hp : IsStronglyPredictable ℱ W)
    (s μ σ : ℝ) : BrownianIntegrable ℱ P (geometricBrownianMotion s μ σ W) := by
  have hpred := hp.geometricBrownianMotion s μ σ
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine ⟨hpred, fun T ↦ ?_⟩
  have hm : AEStronglyMeasurable (Function.uncurry (geometricBrownianMotion s μ σ W))
      (((volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ)).prod P) :=
    (hpred.mono ℱ.predictable_le_prod).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hm).2 ((integrable_prod_iff (hm.pow 2)).2 ⟨?_, ?_⟩)
  · exact Eventually.of_forall fun t ↦
      (hW.memLp_geometricBrownianMotion s μ σ t (by simp)).integrable_sq
  · have hmoment (t : ℝ≥0) :
        ∫ ω, ‖geometricBrownianMotion s μ σ W t ω ^ 2‖ ∂P =
          s ^ 2 * exp ((2 * μ + σ ^ 2) * t) := by
      simp only [Real.norm_eq_abs, abs_pow, sq_abs]
      convert hW.integral_rpow_geometricBrownianMotion s μ σ 2 t using 1 <;>
        norm_num
    simp only [Pi.pow_apply, Function.uncurry_apply_pair, hmoment]
    rw [NNReal.comap_volume_restrict_Ioc]
    have hcont : Continuous (fun t : ℝ≥0 ↦ s ^ 2 * exp ((2 * μ + σ ^ 2) * t)) := by
      fun_prop
    refine hcont.continuousOn.integrableOn_of_subset_isCompact isCompact_Icc
      measurableSet_Ioc Ioc_subset_Icc_self ?_
    rw [← Measure.restrict_apply_univ, ← NNReal.comap_volume_restrict_Ioc,
      NNReal.comap_volume_restrict_Ioc_univ]
    exact ENNReal.coe_ne_top

end ProbabilityTheory.IsPreBrownianReal

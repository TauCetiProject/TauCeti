/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.Local.Dominated
public import TauCeti.MeasureTheory.Constructions.BorelSpace.RightContinuous
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Local martingales with square-integrable running maxima

On a finite measure space, a strongly adapted Banach-valued local martingale with almost
surely right-continuous paths is a true martingale if the squared running maximum of its
norm has finite expectation on every finite horizon. The maximum need only be almost
everywhere measurable: no completion or usual conditions
are imposed on the filtration. This criterion removes localization when maximal moment
estimates are available, for example for polynomial-growth functions of geometric Brownian
motion.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §5.
-/

public section

noncomputable section

open ProbabilityTheory Set
open scoped ENNReal

namespace MeasureTheory

variable {Ω ι E : Type*} [LinearOrder ι] [OrderBot ι]
  [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ι m} {X : ι → Ω → E}

/-- On a finite measure space, a strongly adapted Banach-valued local martingale with
almost surely right-continuous paths and finite expected squared running maxima of its norm
on finite horizons is a true martingale. -/
theorem StronglyAdapted.martingale_of_locally_martingale_of_lintegral_iSup_norm_sq_lt_top
    [IsFiniteMeasure P] (hX : StronglyAdapted ℱ X)
    (hlocal : Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P)
    (hcont : ∀ T, ∀ᵐ ω ∂P, ∀ t < T,
      ContinuousWithinAt (fun u ↦ X u ω) (Ioi t) t)
    (hmax : ∀ T, ∫⁻ ω, ⨆ t ≤ T, ENNReal.ofReal (‖X t ω‖ ^ 2) ∂P < ∞) :
    Martingale X ℱ P := by
  apply hX.martingale_of_locally_martingale_of_dominated hlocal
  intro T
  let G : Ω → ℝ≥0∞ := fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (‖X t ω‖ ^ 2)
  have hG : AEMeasurable G P := aemeasurable_iSup_le_ofReal
    (fun t ↦ (((hX t).mono (ℱ.le t)).norm.measurable.pow_const 2).aemeasurable)
    ((hcont T).mono fun ω hω t ht ↦ (hω t ht).norm.pow 2)
  have hint : Integrable (fun ω ↦ (G ω).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hG (hmax T).ne
  have hb : MemLp (fun ω ↦ Real.sqrt (G ω).toReal) 2 P := by
    apply (memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable
      hint.aestronglyMeasurable)).2
    simpa only [Real.sq_sqrt ENNReal.toReal_nonneg] using hint
  refine ⟨fun ω ↦ Real.sqrt (G ω).toReal, hb.integrable (by norm_num), ?_⟩
  filter_upwards [ae_lt_top' hG (hmax T).ne] with ω hω
  intro t ht
  apply Real.le_sqrt_of_sq_le
  exact (ENNReal.ofReal_le_iff_le_toReal hω.ne).1
    (le_iSup₂ (f := fun t (_ : t ≤ T) ↦ ENNReal.ofReal (‖X t ω‖ ^ 2)) t ht)

end MeasureTheory

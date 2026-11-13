/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.Local.Dominated
public import TauCeti.MeasureTheory.Constructions.BorelSpace.RightContinuous

/-!
# Local martingales with integrable running maxima

A strongly adapted Banach-valued local martingale with almost surely right-continuous
paths is a true martingale if the running maximum of its norm has finite expectation on
every finite horizon, under a sigma-finite filtration. On a finite measure space, a finite
squared maximal moment suffices. The maximum need only be almost everywhere measurable:
no completion or usual conditions are imposed on the filtration. This criterion removes
localization when maximal moment estimates are available, for example for polynomial-growth
functions of geometric Brownian motion.

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

/-- A strongly adapted Banach-valued local martingale with almost surely right-continuous
paths and integrable running maxima is a true martingale under a sigma-finite filtration. -/
theorem StronglyAdapted.martingale_of_locally_martingale_of_lintegral_iSup_norm_lt_top
    [SigmaFiniteFiltration P ℱ] (hX : StronglyAdapted ℱ X)
    (hlocal : Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P)
    (hcont : ∀ T, ∀ᵐ ω ∂P, ∀ t < T,
      ContinuousWithinAt (fun u ↦ X u ω) (Ioi t) t)
    (hmax : ∀ T, ∫⁻ ω, ⨆ t ≤ T, ENNReal.ofReal ‖X t ω‖ ∂P < ∞) :
    Martingale X ℱ P := by
  apply hX.martingale_of_locally_martingale_of_dominated hlocal
  intro T
  let G : Ω → ℝ≥0∞ := fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal ‖X t ω‖
  have hG : AEMeasurable G P := aemeasurable_iSup_le_ofReal
    (fun t ↦ (((hX t).mono (ℱ.le t)).norm.measurable).aemeasurable)
    ((hcont T).mono fun ω hω t ht ↦ (hω t ht).norm)
  refine ⟨fun ω ↦ (G ω).toReal,
    integrable_toReal_of_lintegral_ne_top hG (hmax T).ne, ?_⟩
  filter_upwards [ae_lt_top' hG (hmax T).ne] with ω hω
  intro t ht
  exact (ENNReal.ofReal_le_iff_le_toReal hω.ne).1
    (le_iSup₂ (f := fun t (_ : t ≤ T) ↦ ENNReal.ofReal ‖X t ω‖) t ht)

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
  apply hX.martingale_of_locally_martingale_of_lintegral_iSup_norm_lt_top hlocal hcont
  intro T
  calc
    _ ≤ ∫⁻ ω, 1 + ⨆ t ≤ T, ENNReal.ofReal (‖X t ω‖ ^ 2) ∂P := by
      refine lintegral_mono fun ω ↦ iSup₂_le fun t ht ↦ ?_
      calc
        ENNReal.ofReal ‖X t ω‖ ≤ ENNReal.ofReal (1 + ‖X t ω‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (‖X t ω‖ - 1)])
        _ = 1 + ENNReal.ofReal (‖X t ω‖ ^ 2) := by
          rw [ENNReal.ofReal_add zero_le_one (sq_nonneg _), ENNReal.ofReal_one]
        _ ≤ _ := add_le_add le_rfl (le_iSup₂
          (f := fun t (_ : t ≤ T) ↦ ENNReal.ofReal (‖X t ω‖ ^ 2)) t ht)
    _ = P univ + ∫⁻ ω, ⨆ t ≤ T, ENNReal.ofReal (‖X t ω‖ ^ 2) ∂P := by
      rw [lintegral_add_left measurable_const, lintegral_one]
    _ < ∞ := ENNReal.add_lt_top.2 ⟨measure_lt_top P univ, hmax T⟩

end MeasureTheory

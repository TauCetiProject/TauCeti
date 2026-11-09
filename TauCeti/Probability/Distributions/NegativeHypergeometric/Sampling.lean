/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Finset.SuccessPositions
public import TauCeti.Probability.Distributions.NegativeHypergeometric.Cdf
public import TauCeti.Probability.Distributions.Hypergeometric.Sampling

/-!
# Negative hypergeometric stopping counts from uniform success positions

Choose the `K` success positions uniformly among the `K`-subsets of `Finset.range N`.
The number of failures before the `r`th success has the negative hypergeometric law
with parameters `N`, `K`, and `r`. Waiting for zero successes gives zero, including
an empty population.

The construction combines `Finset.map_card_inter_uniformOn_powersetCard` with the
cumulative identity `negativeHypergeometricMeasure_real_Iic_eq_hypergeometric_tail`:
stopping after at most `k` failures means observing at least `r` successes in the
first `k + r` positions. It provides the stopping-count part of sampling without
replacement, independently of how a uniformly random success-position set is generated.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed.,
  Wiley, 2005, Section 6.2.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

namespace TauCeti.Probability

/-- The failure count before success `r`, when `K` success positions are chosen uniformly
from `N` positions, has the negative hypergeometric law. This includes `r = 0` and `N = 0`. -/
theorem map_failuresBeforeSuccess_uniformOn_powersetCard {N K r : ℕ}
    (hr : r ≤ K) (hK : K ≤ N) :
    (uniformOn ((range N).powersetCard K : Set (Finset ℕ))).map
        (fun s ↦ s.failuresBeforeSuccess r) = negativeHypergeometricMeasure N K r := by
  let μ := uniformOn ((range N).powersetCard K : Set (Finset ℕ))
  have hne : ((range N).powersetCard K).Nonempty :=
    powersetCard_nonempty.mpr (by simpa using hK)
  let _ := isProbabilityMeasure_uniformOn ((range N).powersetCard K).finite_toSet hne
  let _ := isProbabilityMeasure_negativeHypergeometricMeasure hr hK
  apply Measure.ext_of_Iic _ _
  intro k
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [← measureReal_def, ← measureReal_def,
    map_measureReal_apply_of_aemeasurable
      (Finset.aemeasurable_uniformOn_finset _ _) measurableSet_Iic,
    negativeHypergeometricMeasure_real_Iic_eq_hypergeometric_tail hr hK]
  have hcount : μ.map (fun s ↦ #(s ∩ range (k + r))) =
      hypergeometricMeasure N K (min N (k + r)) := by
    rw [hypergeometricMeasure_comm N K]
    simpa only [card_range, range_inter_range] using
      (range N).map_card_inter_uniformOn_powersetCard (range (k + r)) K
  rw [← hcount, map_measureReal_apply_of_aemeasurable
    (Finset.aemeasurable_uniformOn_finset _ _) measurableSet_Ici]
  have hinter : ((range N).powersetCard K : Set (Finset ℕ)) ∩
      (fun s : Finset ℕ ↦ s.failuresBeforeSuccess r) ⁻¹' Set.Iic k =
      ((range N).powersetCard K : Set (Finset ℕ)) ∩
        (fun s : Finset ℕ ↦ #(s ∩ range (k + r))) ⁻¹' Set.Ici r := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ici]
    apply and_congr_right
    intro hs
    have hcard := (mem_powersetCard.mp hs).2
    exact s.failuresBeforeSuccess_le_iff (hcard.symm ▸ hr)
  apply congrArg ENNReal.toReal
  calc
    _ = μ (((range N).powersetCard K : Set (Finset ℕ)) ∩
        (fun s : Finset ℕ ↦ s.failuresBeforeSuccess r) ⁻¹' Set.Iic k) :=
      (uniformOn_inter_self ((range N).powersetCard K).finite_toSet).symm
    _ = μ (((range N).powersetCard K : Set (Finset ℕ)) ∩
        (fun s : Finset ℕ ↦ #(s ∩ range (k + r))) ⁻¹' Set.Ici r) := congrArg μ hinter
    _ = _ := uniformOn_inter_self ((range N).powersetCard K).finite_toSet

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {S : Ω → Finset ℕ} {N K r : ℕ}

/-- Uniform success positions give a negative hypergeometric failure count, on any
underlying probability space. -/
theorem failuresBeforeSuccess_negativeHypergeometricMeasure
    (hS : HasLaw S (uniformOn ((range N).powersetCard K : Set (Finset ℕ))) P)
    (hr : r ≤ K) (hK : K ≤ N) :
    HasLaw (fun ω ↦ (S ω).failuresBeforeSuccess r)
      (TauCeti.Probability.negativeHypergeometricMeasure N K r) P := by
  have hstop : HasLaw (fun s : Finset ℕ ↦ s.failuresBeforeSuccess r)
      (TauCeti.Probability.negativeHypergeometricMeasure N K r)
      (uniformOn ((range N).powersetCard K : Set (Finset ℕ))) :=
    ⟨Finset.aemeasurable_uniformOn_finset _ _,
      TauCeti.Probability.map_failuresBeforeSuccess_uniformOn_powersetCard hr hK⟩
  exact hstop.fun_comp hS

end ProbabilityTheory.HasLaw

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Hypergeometric.Basic
public import TauCeti.Probability.Distributions.Uniform.Finite
public import Mathlib.Probability.HasLaw
import TauCeti.Data.Finset.Powerset

/-!
# Hypergeometric counts in uniform subsets

Choosing uniformly among the `n`-element subsets of a finite population and counting the
marked elements gives the hypergeometric law. The population and marked objects are labelled
by an arbitrary type; only their cardinalities affect the count law. Marks outside the
population have no effect. An oversized sample gives zero on both sides, because there are
no subsets of that size.

`Finset.map_card_inter_uniformOn_powersetCard` is the measure identity, and
`ProbabilityTheory.HasLaw.card_inter_hypergeometricMeasure` is its random-subset form.
The counting step splits a subset into its marked and unmarked parts via
`Finset.card_filter_powersetCard_card_inter`.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Finset

variable {α : Type*} [DecidableEq α]
  [MeasurableSpace (Finset α)] [MeasurableSingletonClass (Finset α)]

/-- Counting marked elements in a uniformly chosen `n`-element subset gives the
hypergeometric law. This includes empty populations and oversized samples. The marks `t`
need not lie in the population `s`. -/
theorem map_card_inter_uniformOn_powersetCard (s t : Finset α) (n : ℕ) :
    (uniformOn (s.powersetCard n : Set (Finset α))).map (fun u ↦ #(u ∩ t)) =
      TauCeti.Probability.hypergeometricMeasure #s #(s ∩ t) n := by
  by_cases hn : n ≤ #s
  swap
  · rw [powersetCard_eq_empty.mpr (Nat.lt_of_not_ge hn)]
    simp [TauCeti.Probability.hypergeometricMeasure_eq_zero_of_invalid, hn]
  have hmarked : #(s ∩ t) ≤ #s := card_le_card inter_subset_left
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_uniformOn_finset _ _)
    (measurableSet_singleton k),
    TauCeti.Probability.hypergeometricMeasure_singleton hmarked hn]
  have hfiber : (s.powersetCard n : Set (Finset α)) ∩
      (fun u ↦ #(u ∩ t)) ⁻¹' {k} =
        (((s.powersetCard n).filter fun u ↦ #(u ∩ t) = k) : Set (Finset α)) := by
    ext u
    simp
  rw [← uniformOn_inter_self (s.powersetCard n).finite_toSet, hfiber,
    uniformOn_apply_finset, inter_eq_right.mpr (filter_subset _ _), card_powersetCard]
  by_cases hk : k ≤ n
  · rw [card_filter_powersetCard_card_inter s t hk,
      TauCeti.Probability.hypergeometricWeight_of_le hk,
      card_sdiff, inter_comm t s]
    norm_cast
  · have hempty : (s.powersetCard n).filter (fun u ↦ #(u ∩ t) = k) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro u hu hcard
      have := card_le_card (inter_subset_left (s₁ := u) (s₂ := t))
      rw [(mem_powersetCard.mp hu).2, hcard] at this
      exact hk this
    simp [hempty, TauCeti.Probability.hypergeometricWeight_of_not_le hk]

end Finset

namespace ProbabilityTheory.HasLaw

open Finset

variable {α Ω : Type*} [DecidableEq α]
  [MeasurableSpace (Finset α)] [MeasurableSingletonClass (Finset α)] [MeasurableSpace Ω]
  {P : Measure Ω} {S : Ω → Finset α} {s t : Finset α} {n : ℕ}

/-- The marked count of a uniform fixed-size random subset has the hypergeometric law. -/
theorem card_inter_hypergeometricMeasure
    (hS : HasLaw S (uniformOn (s.powersetCard n : Set (Finset α))) P) :
    HasLaw (fun ω ↦ #(S ω ∩ t))
      (TauCeti.Probability.hypergeometricMeasure #s #(s ∩ t) n) P := by
  have hcount : HasLaw (fun u : Finset α ↦ #(u ∩ t))
      (TauCeti.Probability.hypergeometricMeasure #s #(s ∩ t) n)
      (uniformOn (s.powersetCard n : Set (Finset α))) :=
    ⟨Finset.aemeasurable_uniformOn_finset _ _,
      Finset.map_card_inter_uniformOn_powersetCard s t n⟩
  exact hcount.fun_comp hS

end ProbabilityTheory.HasLaw

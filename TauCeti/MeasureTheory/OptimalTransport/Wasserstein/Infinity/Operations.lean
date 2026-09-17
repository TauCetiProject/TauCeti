/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Infinity.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward

/-!
# Products and mixtures for the infinite Wasserstein distance

For the usual supremum metric on a product, the `W_∞` distance of product probability laws is
the maximum of the distances of the factors. For mixtures with common weights it is at most
the supremum of the distances of the components with positive weight. Zero weights do not
contribute, even if the corresponding component distance is infinite.

These are extended-valued statements on Polish metric spaces, without moment or bounded-support
assumptions. The mixture theorem allows countably many finite, equal-mass pairs and arbitrary
nonnegative weights; its finite version includes probability mixtures. The estimates use optimal
couplings supplied by `TauCeti.exists_isCoupling_eLpNorm_top_eq_wassersteinEDist`.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer, 2009, Chapters 4 and 6.
* C. R. Givens and R. M. Shortt, *A class of Wasserstein metrics for probability distributions*,
  Michigan Math. J. 31 (1984), 231–240, Proposition 1, for attainment at the infinite exponent.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompleteSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y] [CompleteSpace Y]

/-- For the supremum product metric, `W_∞` of product probability laws is the maximum of the
two factor distances. Infinite distances are allowed. -/
theorem wassersteinEDist_top_prod (μ₁ ν₁ : Measure X) (μ₂ ν₂ : Measure Y)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂] :
    wassersteinEDist ∞ (μ₁.prod μ₂) (ν₁.prod ν₂) =
      max (wassersteinEDist ∞ μ₁ ν₁) (wassersteinEDist ∞ μ₂ ν₂) := by
  apply le_antisymm
  · obtain ⟨π₁, hπ₁, hb₁⟩ := (wassersteinEDist_top_le_iff μ₁ ν₁
      ⟨_, isCoupling_prod μ₁ ν₁⟩).mp le_rfl
    obtain ⟨π₂, hπ₂, hb₂⟩ := (wassersteinEDist_top_le_iff μ₂ ν₂
      ⟨_, isCoupling_prod μ₂ ν₂⟩).mp le_rfl
    have : IsProbabilityMeasure π₁ := hπ₁.isProbabilityMeasure
    have : IsProbabilityMeasure π₂ := hπ₂.isProbabilityMeasure
    apply (wassersteinEDist_top_le_iff _ _
      ⟨_, isCoupling_prod (μ₁.prod μ₂) (ν₁.prod ν₂)⟩).mpr
    refine ⟨_, hπ₁.prodProdProdComm hπ₂, ?_⟩
    rw [ae_map_iff (by fun_prop) (measurableSet_le measurable_edist measurable_const)]
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hb₁,
      measurePreserving_snd.quasiMeasurePreserving.ae hb₂] with z hz₁ hz₂
    simpa only [Prod.edist_eq] using max_le_max hz₁ hz₂
  · apply max_le
    · simpa using wassersteinEDist_map_le_mul (p := ∞) measurable_edist measurable_fst
        LipschitzWith.prod_fst (μ₁.prod μ₂) (ν₁.prod ν₂)
    · simpa using wassersteinEDist_map_le_mul (p := ∞) measurable_edist measurable_snd
        LipschitzWith.prod_snd (μ₁.prod μ₂) (ν₁.prod ν₂)

/-- Mixing countably many finite equal-mass pairs with common weights bounds `W_∞` by the
supremum of the component distances with positive weight. Neither the weights nor the total
mass need be normalized or finite. -/
theorem wassersteinEDist_top_sum_smul_le {ι : Type*} [Countable ι]
    (a : ι → ℝ≥0∞) (μ ν : ι → Measure X) [∀ i, IsFiniteMeasure (μ i)]
    (hmass : ∀ i, μ i Set.univ = ν i Set.univ) :
    wassersteinEDist ∞ (Measure.sum fun i ↦ a i • μ i) (Measure.sum fun i ↦ a i • ν i) ≤
      ⨆ i, ⨆ (_ : 0 < a i), wassersteinEDist ∞ (μ i) (ν i) := by
  choose π hπ hb using fun i ↦ (wassersteinEDist_top_le_iff (μ i) (ν i)
    (exists_isCoupling_iff.mpr (hmass i))).mp le_rfl
  refine (wassersteinEDist_le (IsCoupling.sum fun i ↦ (hπ i).smul (a i)) ∞).trans ?_
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  apply Measure.ae_sum_iff.mpr
  intro i
  by_cases ha : a i = 0
  · simp [ha]
  · apply Measure.ae_smul_measure _ (a i)
    filter_upwards [hb i] with z hz
    exact hz.trans (le_iSup_of_le i (le_iSup_of_le (pos_iff_ne_zero.mpr ha) le_rfl))

/-- The maximum-form bound for finite mixtures. The supremum over an empty set of positive
weights is zero, so this includes the zero mixture. -/
theorem wassersteinEDist_top_finset_sum_smul_le {ι : Type*} (s : Finset ι)
    (a : ι → ℝ≥0∞) (μ ν : ι → Measure X) [∀ i, IsFiniteMeasure (μ i)]
    (hmass : ∀ i ∈ s, μ i Set.univ = ν i Set.univ) :
    wassersteinEDist ∞ (∑ i ∈ s, a i • μ i) (∑ i ∈ s, a i • ν i) ≤
      ⨆ i ∈ s, ⨆ (_ : 0 < a i), wassersteinEDist ∞ (μ i) (ν i) := by
  simpa only [Measure.sum_fintype, Finset.sum_coe_sort s (fun i ↦ a i • μ i),
    Finset.sum_coe_sort s (fun i ↦ a i • ν i), iSup_subtype] using
    wassersteinEDist_top_sum_smul_le (fun i : s ↦ a i) (fun i : s ↦ μ i)
      (fun i : s ↦ ν i) (fun i ↦ hmass i i.property)

end TauCeti

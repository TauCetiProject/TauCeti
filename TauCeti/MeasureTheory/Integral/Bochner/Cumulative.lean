/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Cumulative Bochner integrals on ordered spaces

An integrable function has a bounded-variation cumulative integral. If the measure has no
atoms at singletons, this cumulative integral is continuous. These statements apply in
particular to nonnegative real time, without extending the integrand to negative times.
-/

public section

open Set Filter
open scoped Topology

namespace MeasureTheory

variable {ι E : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [MeasurableSpace ι] [OpensMeasurableSpace ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure ι} {f : ι → E}

/-- The cumulative Bochner integral of an integrable function is continuous for a measure
vanishing on singletons. -/
theorem Integrable.continuous_integral_Iic [FirstCountableTopology ι] [NullSingletonClass μ]
    (hf : Integrable f μ) :
    Continuous (fun t => ∫ s in Iic t, f s ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro t
  simp_rw [← integral_indicator measurableSet_Iic]
  apply continuousAt_of_dominated (bound := fun s => ‖f s‖)
  · exact Eventually.of_forall fun u => hf.aestronglyMeasurable.indicator measurableSet_Iic
  · exact Eventually.of_forall fun u => ae_of_all _ fun s => norm_indicator_le_norm_self _ _
  · exact hf.norm
  · have hne : ∀ᵐ s ∂μ, s ≠ t := by
      simpa only [ae_iff, not_not, ofPred_eq_eq_singleton] using measure_singleton t
    filter_upwards [hne] with s hs
    rcases lt_or_gt_of_ne hs with hst | hts
    · apply (continuousAt_const (y := f s)).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hst] with u hu
      simp [hu.le]
    · apply (continuousAt_const (y := (0 : E))).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hts] with u hu
      simp [not_le.mpr hu]

/-- The total variation of a cumulative Bochner integral is bounded by the integral of the
norm. Atoms are allowed. -/
theorem Integrable.eVariationOn_integral_Iic_le (hf : Integrable f μ) :
    eVariationOn (fun t => ∫ s in Iic t, f s ∂μ) univ ≤
      ENNReal.ofReal (∫ s, ‖f s‖ ∂μ) := by
  simp only [eVariationOn, iSup_le_iff]
  rintro ⟨n, u, hu, -⟩
  have hcell (i : ℕ) :
      edist (∫ s in Iic (u (i + 1)), f s ∂μ) (∫ s in Iic (u i), f s ∂μ) ≤
        ENNReal.ofReal ((∫ s in Iic (u (i + 1)), ‖f s‖ ∂μ) -
          ∫ s in Iic (u i), ‖f s‖ ∂μ) := by
    rw [edist_eq_enorm_sub, ← ofReal_norm, ← setIntegral_sdiff measurableSet_Iic
      hf.integrableOn (Iic_subset_Iic.mpr (hu (Nat.le_succ i))),
      ← setIntegral_sdiff measurableSet_Iic hf.norm.integrableOn
        (Iic_subset_Iic.mpr (hu (Nat.le_succ i)))]
    exact ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm _)
  calc
    _ ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal
        ((∫ s in Iic (u (i + 1)), ‖f s‖ ∂μ) - ∫ s in Iic (u i), ‖f s‖ ∂μ) :=
      Finset.sum_le_sum fun i _ => hcell i
    _ = ENNReal.ofReal ((∫ s in Iic (u n), ‖f s‖ ∂μ) -
        ∫ s in Iic (u 0), ‖f s‖ ∂μ) := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · exact congrArg ENNReal.ofReal (Finset.sum_range_sub
          (fun i => ∫ s in Iic (u i), ‖f s‖ ∂μ) n)
      · intro i _
        exact sub_nonneg.mpr (setIntegral_mono_set hf.norm.integrableOn
          (ae_of_all _ fun s => norm_nonneg _)
          (ae_of_all _ (Iic_subset_Iic.mpr (hu (Nat.le_succ i)))))
    _ ≤ ENNReal.ofReal (∫ s, ‖f s‖ ∂μ) := by
      apply ENNReal.ofReal_le_ofReal
      exact (sub_le_self _ (integral_nonneg fun s => norm_nonneg _)).trans
        (integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun s => norm_nonneg _)
          hf.norm)

/-- A path integrable on a finite horizon has a continuous accumulated integral throughout
that horizon for a measure vanishing on singletons. -/
theorem IntegrableOn.continuousOn_integral_Ioc [FirstCountableTopology ι]
    [NullSingletonClass μ] {a b : ι} (hf : IntegrableOn f (Ioc a b) μ) :
    ContinuousOn (fun t => ∫ s in Ioc a t, f s ∂μ) (Iic b) := by
  refine hf.continuous_integral_Iic.continuousOn.congr ?_
  intro t ht
  simp only [Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioc_of_le ht]

/-- The variation of an accumulated integral on a finite horizon is bounded by its pathwise
integral norm. No atomlessness or integrability outside the horizon is required. -/
theorem IntegrableOn.eVariationOn_integral_Ioc_le {a b : ι}
    (hf : IntegrableOn f (Ioc a b) μ) :
    eVariationOn (fun t => ∫ s in Ioc a t, f s ∂μ) (Iic b) ≤
      ENNReal.ofReal (∫ s in Ioc a b, ‖f s‖ ∂μ) := by
  have heq : EqOn (fun t => ∫ s in Iic t, f s ∂μ.restrict (Ioc a b))
      (fun t => ∫ s in Ioc a t, f s ∂μ) (Iic b) := by
    intro t ht
    simp only [Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioc_of_le ht]
  rw [← eVariationOn.congr heq]
  exact (eVariationOn.mono _ (subset_univ _)).trans hf.eVariationOn_integral_Iic_le

end MeasureTheory

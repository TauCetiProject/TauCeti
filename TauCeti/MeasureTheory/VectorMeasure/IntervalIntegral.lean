/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

/-!
# Continuity of indefinite vector-measure integrals

An integrable function has a continuous cumulative integral at every point which is not an
atom of the variation measure. In particular, for an atomless vector measure, integration over
`(a,t]` gives a continuous path on a finite horizon, even for merely L¹ integrands.

The endpoint condition concerns the variation, not just the value of the vector measure on a
large set: cancellation does not control the integral. These results apply to signed Stieltjes
measures and to continuous bilinear pairings with vector-valued integrators.

The proof adapts the dominated-convergence argument of Mathlib's
`intervalIntegral.continuousWithinAt_primitive` in
`Mathlib.MeasureTheory.Integral.DominatedConvergence` to vector measures on ordered spaces.
The finite-horizon result is the vector-measure counterpart of
`intervalIntegral.continuousOn_primitive` and `intervalIntegral.continuousOn_primitive_Icc`.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace MeasureTheory.VectorMeasure

variable {α E F G : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [FirstCountableTopology α] [MeasurableSpace α] [BorelSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ : VectorMeasure α F} {f : α → E} {B : E →L[ℝ] F →L[ℝ] G}

/-- The cumulative integral of an L¹ function is continuous at any point with zero variation
mass. No continuity of the integrand is required. -/
theorem Integrable.continuousAt_setIntegral_Iic (hf : μ.Integrable f) {t : α}
    (ht : μ.variation {t} = 0) :
    ContinuousAt (fun u ↦ ∫ᵛ x in Iic u, f x ∂[B; μ]) t := by
  simp_rw [← integral_indicator measurableSet_Iic]
  refine continuousAt_of_dominated
    (Eventually.of_forall fun u ↦ hf.aestronglyMeasurable.indicator measurableSet_Iic)
    (Eventually.of_forall fun u ↦ Eventually.of_forall fun x ↦ norm_indicator_le_norm_self _ _)
    hf.norm ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 ht] with x hx
  simp only [mem_singleton_iff] at hx
  rcases lt_or_gt_of_ne hx with hxt | htx
  · exact (continuousAt_const (y := f x)).congr_of_eventuallyEq
      ((eventually_gt_nhds hxt).mono fun u hu ↦ by simp [hu.le])
  · exact (continuousAt_const (y := (0 : E))).congr_of_eventuallyEq
      ((eventually_lt_nhds htx).mono fun u hu ↦ by simp [hu.not_ge])

/-- An L¹ function has a continuous cumulative integral against an atomless vector measure. -/
theorem Integrable.continuous_setIntegral_Iic (hf : μ.Integrable f)
    [NullSingletonClass μ.variation] :
    Continuous (fun t ↦ ∫ᵛ x in Iic t, f x ∂[B; μ]) :=
  continuous_iff_continuousAt.2 fun _ ↦ hf.continuousAt_setIntegral_Iic (measure_singleton _)

/-- The indefinite integral of a function integrable only on `(a,b]` is continuous throughout
`[a,b]` when the variation measure has no atoms in `(a,b]`. Atoms outside the integration
horizon, including at `a`, are allowed. This includes an empty or zero-length horizon. -/
theorem IntegrableOn.continuousOn_setIntegral_Ioc {a b : α}
    (hf : μ.IntegrableOn f (Ioc a b)) (hμ : ∀ t ∈ Ioc a b, μ.variation {t} = 0) :
    ContinuousOn (fun t ↦ ∫ᵛ x in Ioc a t, f x ∂[B; μ]) (Icc a b) := by
  have : NullSingletonClass (μ.restrict (Ioc a b)).variation := by
    rw [variation_restrict measurableSet_Ioc]
    constructor
    intro t
    by_cases ht : t ∈ Ioc a b
    · simpa [Measure.restrict_apply, ht] using hμ t ht
    · simp [Measure.restrict_apply, ht]
  have hc := hf.continuous_setIntegral_Iic (B := B)
  refine hc.continuousOn.congr fun t ht ↦ ?_
  dsimp only
  rw [restrict_restrict _ measurableSet_Iic measurableSet_Ioc]
  congr 2
  ext x
  simp only [mem_inter_iff, mem_Iic, mem_Ioc]
  grind

end MeasureTheory.VectorMeasure

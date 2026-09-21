/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Martingale.Convergence
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.ConditionalExpectation
public import TauCeti.Probability.Process.PartitionFiltration

/-!
# Approximation by block-average step graphons

On a countably generated probability space, the block averages of a graphon along the canonical
refining finite partitions converge to the graphon in `L¹`. The finite partitions generate the
ambient σ-algebra, so this is Lévy's upward theorem after identifying each block average with the
corresponding conditional expectation.

This gives a strict, finite-step approximation while stating convergence in the almost-everywhere
language used by analytic limit arguments.

## Main result

* `TauCeti.DenseGraphLimits.countableStepGraphonAvg` is the canonical sequence of block-average
  step graphons, characterized by `TauCeti.DenseGraphLimits.countableStepGraphonAvg_def`.
* `TauCeti.DenseGraphLimits.tendsto_eLpNorm_stepGraphonAvg_countablePartition` gives `L¹`
  convergence of canonical block averages.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §9.2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory

open scoped ENNReal Topology

namespace TauCeti.DenseGraphLimits

variable {Ω : Type*} [m : MeasurableSpace Ω] [MeasurableSpace.CountablyGenerated Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The block-average step graphon on the level-`n` canonical finite partition of a countably
generated measurable space. -/
noncomputable def countableStepGraphonAvg (W : Graphon Ω μ) (n : ℕ) : Graphon Ω μ :=
  stepGraphonAvg (Finpartition.countablePartition Ω n)
    (fun _ hp => Finpartition.measurableSet_of_mem_countablePartition Ω n hp) W

/-- The canonical block-average step graphon is the block average on the canonical finite
partition.

`countableStepGraphonAvg` is a definition whose body is not exposed outside this module, so this is
the only way a downstream file can rewrite it into the bundled `stepGraphonAvg` API. -/
theorem countableStepGraphonAvg_def (W : Graphon Ω μ) (n : ℕ) :
    countableStepGraphonAvg W n =
      stepGraphonAvg (Finpartition.countablePartition Ω n)
        (fun _ hp => Finpartition.measurableSet_of_mem_countablePartition Ω n hp) W := by
  rw [countableStepGraphonAvg]

/-- The canonical block-average step graphon takes the same values as the block average on the
canonical finite partition. -/
@[simp]
theorem countableStepGraphonAvg_apply (W : Graphon Ω μ) (n : ℕ) (x y : Ω) :
    countableStepGraphonAvg W n x y =
      stepGraphonAvg (Finpartition.countablePartition Ω n)
        (fun _ hp => Finpartition.measurableSet_of_mem_countablePartition Ω n hp) W x y := by
  rw [countableStepGraphonAvg_def]

/-- The block-average step graphons along the canonical refining finite partitions converge to the
original graphon in `L¹` on the product space. -/
theorem tendsto_eLpNorm_stepGraphonAvg_countablePartition (W : Graphon Ω μ) :
    Tendsto
      (fun n => eLpNorm
        ((fun z : Ω × Ω => countableStepGraphonAvg W n z.1 z.2) -
          fun z : Ω × Ω => W z.1 z.2) 1 (μ.prod μ))
      atTop (𝓝 0) := by
  let ℱ := TauCeti.MeasureTheory.countableSquareFiltration Ω
  let f : Ω × Ω → ℝ := fun z => W z.1 z.2
  have hfint : Integrable f (μ.prod μ) := W.toSymmKernel.integrable_uncurry μ
  have hfmeas : StronglyMeasurable[⨆ n, ℱ n] f :=
    W.measurable.stronglyMeasurable.mono
      TauCeti.MeasureTheory.iSup_countableSquareFiltration.ge
  have hcond : Tendsto (fun n => eLpNorm ((μ.prod μ)[f | ℱ n] - f) 1 (μ.prod μ))
      atTop (𝓝 0) := hfint.tendsto_eLpNorm_condExp hfmeas
  refine hcond.congr' (Eventually.of_forall fun n => ?_)
  apply eLpNorm_congr_ae
  refine Filter.EventuallyEq.sub ?_ Filter.EventuallyEq.rfl
  simpa only [ℱ, f,
    TauCeti.MeasureTheory.countableSquareFiltration_eq_comap,
    countableStepGraphonAvg_apply] using
    (stepGraphonAvg_ae_eq_condExp (Finpartition.countablePartition Ω n)
      (fun _ hp => Finpartition.measurableSet_of_mem_countablePartition Ω n hp) W).symm

end TauCeti.DenseGraphLimits

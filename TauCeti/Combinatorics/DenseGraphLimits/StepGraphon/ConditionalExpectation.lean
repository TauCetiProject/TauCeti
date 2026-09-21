/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.Average
public import TauCeti.MeasureTheory.Function.ConditionalExpectation

/-!
# Block averages as conditional expectations

The block-average step graphon of a measurable finite partition agrees almost everywhere with
conditional expectation onto the σ-algebra recording the partition part of each coordinate.
This identifies the strict block-average construction with the analytic conditional-expectation
API, so approximation along refining partitions can use martingale convergence.

The identification includes partitions with null parts: the strict representative uses zero on
null rectangles, while conditional expectation determines values only almost everywhere.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §9.2.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Block averaging is conditional expectation given the two partition indices. The equality is
almost everywhere, so it is independent of values on null rectangles. -/
theorem stepGraphonAvg_ae_eq_condExp (P : Finpartition (Set.univ : Set Ω))
    (hP : ∀ p ∈ P.parts, MeasurableSet p) (W : Graphon Ω μ) :
    (fun z : Ω × Ω => stepGraphonAvg P hP W z.1 z.2) =ᵐ[μ.prod μ]
      (μ.prod μ)[(fun z : Ω × Ω => W z.1 z.2) |
        MeasurableSpace.comap (Prod.map P.indexedPartition.index P.indexedPartition.index) ⊤] := by
  let : MeasurableSpace (P.parts × P.parts) := ⊤
  let X : Ω × Ω → P.parts × P.parts :=
    Prod.map P.indexedPartition.index P.indexedPartition.index
  have hfiber (pq : P.parts × P.parts) :
      X ⁻¹' {pq} = (pq.1 : Set Ω) ×ˢ (pq.2 : Set Ω) := by
    ext ⟨x, y⟩
    rcases pq with ⟨p, q⟩
    simp only [mem_preimage, mem_singleton_iff, X, Prod.map_apply, Prod.mk.injEq,
      mem_prod, P.indexedPartition.mem_iff_index_eq]
  have hX : Measurable X := by
    refine measurable_to_countable' fun pq => ?_
    rw [hfiber]
    exact (hP _ pq.1.property).prod (hP _ pq.2.property)
  have hvalue : (fun z : Ω × Ω => stepGraphonAvg P hP W z.1 z.2) =
      (fun pq : P.parts × P.parts => (blockAverage P W pq.1 pq.2 : ℝ)) ∘ X := by
    funext z
    exact (stepGraphonAvg_apply P hP W (P.indexedPartition.mem_index z.1)
      (P.indexedPartition.mem_index z.2)).trans (coe_blockAverage P W _ _).symm
  have hmeas : StronglyMeasurable[MeasurableSpace.comap X ⊤]
      (fun z : Ω × Ω => stepGraphonAvg P hP W z.1 z.2) := by
    rw [hvalue]
    exact (measurable_of_countable _).stronglyMeasurable.comp_measurable
      (comap_measurable X)
  refine MeasureTheory.ae_eq_condExp_of_forall_setIntegral_fiber_eq hX
    W.toSymmKernel.integrable_uncurry
    (stepGraphonAvg P hP W).toSymmKernel.integrable_uncurry
    hmeas.aestronglyMeasurable ?_
  intro pq
  rw [hfiber]
  simpa only [SymmKernel.rectIntegral_def, Graphon.coe_toSymmKernel] using
    stepGraphonAvg_rectIntegral P hP W pq.1 pq.2

end TauCeti.DenseGraphLimits

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.Basic
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.Density

/-!
# Step graphons are dense in graphon space

`exists_stepGraphon_cutDist_le` approximates a graphon by a step graphon in cut distance.  This
file transports that approximation to the metric space `GraphonSpace Ω μ`, where cut distance is a
genuine metric on the separation quotient: the classes of step graphons on measurable finite
partitions form a dense subset.

Density is stated for an arbitrary carrier, since nothing here inspects it: the approximation is
the one supplied by Frieze--Kannan weak regularity, and the passage to the quotient only uses that
the distance of two classes is the cut distance of any two representatives.

## Main results

* `TauCeti.DenseGraphLimits.dense_stepGraphon` -- step graphons are dense in graphon space.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §9.2.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Step graphons are dense in graphon space.** -/
theorem dense_stepGraphon :
    Dense {x : GraphonSpace Ω μ | ∃ (P : Finpartition (Set.univ : Set Ω))
      (hP : ∀ p ∈ P.parts, MeasurableSet p) (val : P.parts → P.parts → Set.Icc (0 : ℝ) 1)
      (hsymm : ∀ p q, val p q = val q p),
      x = SeparationQuotient.mk (stepGraphon (μ := μ) P hP val hsymm)} := by
  rw [Metric.dense_iff]
  rintro x r hr
  obtain ⟨W, rfl⟩ := SeparationQuotient.surjective_mk x
  obtain ⟨P, hP, val, hsymm, _, hle⟩ := exists_stepGraphon_cutDist_le W (half_pos hr)
  refine ⟨SeparationQuotient.mk (stepGraphon (μ := μ) P hP val hsymm), ?_,
    ⟨P, hP, val, hsymm, rfl⟩⟩
  rw [Metric.mem_ball, dist_comm, dist_graphonSpace_mk_mk]
  exact hle.trans_lt (half_lt_self hr)

end DenseGraphLimits

end TauCeti

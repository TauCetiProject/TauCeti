/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.Basic
public import TauCeti.NumberTheory.Padics.Measure.Topology.Basic

/-!
# Weakly closed ranges of coefficient extensions

`AbstractMeasure.isClosed_range_extendCoefficients_weak` proves that extension along a bounded
coefficient embedding with closed image has weakly closed range. The range is the intersection
of the closed conditions obtained by evaluating on transported tests.
-/

public section

open AbstractMeasure ContinuousMap
open scoped AbstractMeasure

variable {X O K : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X] [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  [NormedCommRing K] [IsUltrametricDist K] [CompleteSpace K] {B : ℝ}

/-- On a profinite space, extension along a bounded coefficient embedding with closed image has
weakly closed range. -/
theorem AbstractMeasure.isClosed_range_extendCoefficients_weak (j : O →+* K)
    (hj : ∀ a, ‖j a‖ ≤ B) (hje : Topology.IsEmbedding j) (hjr : IsClosed (Set.range j)) :
    @IsClosed D(X, K) WeakTopology (extendCoefficients (X := X) j hj).range := by
  have hrange : ((extendCoefficients (X := X) j hj).range : Set D(X, K)) =
      ⋂ f : C(X, O), {ν | ν ((⟨j, hje.continuous⟩ : C(O, K)).comp f) ∈ Set.range j} := by
    ext ν
    simpa only [SetLike.mem_coe, Set.mem_iInter, Set.mem_ofPred_eq] using
      mem_range_extendCoefficients_iff_apply_comp_mem_range j hj hje (ν := ν)
  rw [hrange]
  let : TopologicalSpace D(X, K) := WeakTopology
  exact isClosed_iInter fun f ↦ hjr.preimage
    (continuous_apply_weak ((⟨j, hje.continuous⟩ : C(O, K)).comp f))

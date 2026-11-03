/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.OpenMapping
public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Completion

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.FirstCountable
import TauCeti.Topology.Algebra.GroupCompletion
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Spanning evaluations out of `A⟨X⟩_T` are open

Let `A` be a Tate ring and `B` a complete Hausdorff Huber `A`-algebra with continuous structure
map. Evaluation `A⟨X₁, …, Xₙ⟩_T → B` at a weight-bounded family `b₁, …, bₙ`, extended to the
completion (`weightedEvalHomCompletion`), is an open quotient map as soon as the `bᵢ` span `B` as
an `A`-module. It is surjective because already the linear polynomials `∑ aᵢ Xᵢ` hit every element
of `B`, and open by the open mapping theorem over a Tate ring
(`LinearMap.isOpenMap_of_isTateRing`), applied to the evaluation as an `A`-linear
map between complete metrizable modules.

## Main results

* `TauCeti.Huber.isOpenQuotientMap_weightedEvalHomCompletion`: evaluation at a weight-bounded
  family spanning `B` over `A` is an open quotient map.
-/

public section

open Topology UniformSpace Uniformity

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [IsHuberRing B] [CompleteSpace B] [T0Space B] [Algebra A B]

/-- Evaluation `A⟨X₁, …, Xₙ⟩ → B` at a weight-bounded family spanning `B` over `A` is an open
quotient map: it is surjective because the family spans, and open by the open mapping theorem
over the Tate ring `A`. -/
theorem isOpenQuotientMap_weightedEvalHomCompletion (hcont : Continuous (algebraMap A B))
    {n : ℕ} {T : Fin n → Set A} (hT : IsWeightFamily T)
    {b : Fin n → B} (hb : IsWeightBounded (algebraMap A B) T b)
    (hspan : Submodule.span A (Set.range b) = ⊤) :
    IsOpenQuotientMap (weightedEvalHomCompletion hT hcont.continuousAt hb) := by
  set ψ := weightedEvalHomCompletion hT hcont.continuousAt hb
  have hψc : Continuous ψ := continuous_weightedEvalHomCompletion ..
  have hψC (a : A) : ψ ((weightedC T hT a : weightedRestrictedSubring T hT) :
      Completion (weightedRestrictedSubring T hT)) = algebraMap A B a := by
    rw [weightedEvalHomCompletion_coe, weightedEvalHom_weightedC]
  have hψX (j : Fin n) : ψ ((weightedX T hT j : weightedRestrictedSubring T hT) :
      Completion (weightedRestrictedSubring T hT)) = b j := by
    rw [weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp
      (hspan ▸ Submodule.mem_top : y ∈ Submodule.span A (Set.range b))
    refine ⟨∑ j, ((weightedC T hT (a j) * weightedX T hT j : weightedRestrictedSubring T hT) :
      Completion (weightedRestrictedSubring T hT)), ?_⟩
    simp only [map_sum, Completion.coe_mul, map_mul, hψC, hψX, Algebra.smul_def]
  let π : Completion (weightedRestrictedSubring T hT) →ₐ[A] B :=
    { ψ with
      commutes' := fun a ↦ by
        have := hψC a
        rwa [← algebraMap_completion_weightedRestrictedSubring_apply] at this }
  have : ContinuousSMul A B := continuousSMul_of_algebraMap A B hcont
  have : (𝓤 (Completion (weightedRestrictedSubring T hT))).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  have : (𝓤 B).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact ⟨hsurj, hψc, π.toLinearMap.isOpenMap_of_isTateRing hsurj hψc.continuousAt⟩

end TauCeti.Huber

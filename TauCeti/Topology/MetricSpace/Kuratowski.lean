/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.MetricSpace.Kuratowski
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# The Fréchet–Kuratowski embedding of a pseudometric space

Every pseudometric space `X` embeds isometrically into the bounded continuous real functions on
`X`, by the Fréchet–Kuratowski embedding `x ↦ (y ↦ dist x y - dist x₀ y)` based at a point `x₀`.
Unlike Mathlib's `KuratowskiEmbedding.embeddingOfSubset`, which lands in `ℓ^∞(ℕ)` and needs a
separable space, this embedding exists for every pseudometric space. It transfers metric
statements proved for normed targets to arbitrary pseudometric targets.

A separable pseudometric space moreover maps isometrically into a *separable* Banach space: the
closed linear span of the image of Mathlib's Kuratowski embedding of its metric quotient into
`ℓ^∞(ℕ)`. This transfers statements proved for separable Banach spaces, such as those resting on
Polish path spaces, to separable pseudometric spaces.

## Main definitions

* `TauCeti.kuratowskiEmbedding x₀`: the Fréchet–Kuratowski embedding `X → X →ᵇ ℝ` based at `x₀`.

## Main results

* `TauCeti.isometry_kuratowskiEmbedding`: the Fréchet–Kuratowski embedding is an isometry.
* `TauCeti.exists_isometry_separableSpace_completeSpace`: a separable pseudometric space maps
  isometrically into a separable Banach space.
-/

public section

open Set TopologicalSpace
open scoped BoundedContinuousFunction ENNReal lp

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X]

/-- The Fréchet–Kuratowski embedding of a pseudometric space into the bounded continuous real
functions on it, based at `x₀`: it sends `x` to `y ↦ dist x y - dist x₀ y`. -/
noncomputable def kuratowskiEmbedding (x₀ x : X) : X →ᵇ ℝ :=
  .ofNormedAddCommGroup (fun y ↦ dist x y - dist x₀ y) (by fun_prop) (dist x x₀)
    fun y ↦ abs_dist_sub_le x x₀ y

/-- The Fréchet–Kuratowski embedding of `x` evaluated at `y`. -/
@[simp]
theorem kuratowskiEmbedding_apply (x₀ x y : X) :
    kuratowskiEmbedding x₀ x y = dist x y - dist x₀ y := by
  simp [kuratowskiEmbedding]

/-- The Fréchet–Kuratowski embedding is an isometry. -/
theorem isometry_kuratowskiEmbedding (x₀ : X) : Isometry (kuratowskiEmbedding x₀) := by
  refine Isometry.of_dist_eq fun x x' ↦ le_antisymm
    ((BoundedContinuousFunction.dist_le dist_nonneg).2 fun y ↦ ?_) ?_
  · simpa [Real.dist_eq] using abs_dist_sub_le x x' y
  · simpa [Real.dist_eq, abs_sub_comm, dist_comm x] using
      BoundedContinuousFunction.dist_coe_le_dist (f := kuratowskiEmbedding x₀ x)
        (g := kuratowskiEmbedding x₀ x') x

/-- A separable pseudometric space maps isometrically into a separable real Banach space. -/
theorem exists_isometry_separableSpace_completeSpace (Y : Type*) [PseudoMetricSpace Y]
    [SeparableSpace Y] :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℝ E), CompleteSpace E ∧
      SeparableSpace E ∧ ∃ f : Y → E, Isometry f := by
  -- Kuratowski-embed the metric quotient of `Y` into `ℓ^∞(ℕ, ℝ)` and take the closed linear span.
  have : SeparableSpace (SeparationQuotient Y) := SeparationQuotient.isQuotientMap_mk.separableSpace
  have hι : Isometry (_root_.kuratowskiEmbedding (SeparationQuotient Y) ∘ SeparationQuotient.mk) :=
    (kuratowskiEmbedding.isometry _).comp (.of_dist_eq SeparationQuotient.dist_mk)
  set K : Submodule ℝ ℓ^∞(ℕ, ℝ) := (Submodule.span ℝ (range _)).topologicalClosure
  have hK : IsSeparable (K : Set ℓ^∞(ℕ, ℝ)) := (isSeparable_range hι.continuous).span.closure
  exact ⟨K, inferInstance, inferInstance, inferInstance, hK.separableSpace,
    fun y ↦ ⟨_, Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨y, rfl⟩)⟩,
    Isometry.of_dist_eq hι.dist_eq⟩

end TauCeti

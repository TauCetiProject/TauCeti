/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.MetricSpace.Kuratowski
import Mathlib.Topology.Algebra.Module.Basic

/-!
# The Fréchet–Kuratowski embedding of a pseudometric space

Every pseudometric space `X` embeds isometrically into the bounded continuous real functions on
`X`, by the Fréchet–Kuratowski embedding `x ↦ (y ↦ dist x y - dist x₀ y)` based at a point `x₀`.
Unlike Mathlib's `KuratowskiEmbedding.embeddingOfSubset`, which lands in `ℓ^∞(ℕ)` and needs a
separable space, this embedding exists for every pseudometric space. It transfers metric
statements proved for normed targets to arbitrary pseudometric targets.

A separable metric space moreover embeds isometrically into a *separable* Banach space: the closed
linear span of the image of Mathlib's Kuratowski embedding into `ℓ^∞(ℕ)`. This transfers
statements proved for separable Banach spaces, such as those resting on Polish path spaces, to
separable metric spaces.

## Main definitions

* `TauCeti.kuratowskiEmbedding x₀`: the Fréchet–Kuratowski embedding `X → X →ᵇ ℝ` based at `x₀`.

## Main results

* `TauCeti.isometry_kuratowskiEmbedding`: the Fréchet–Kuratowski embedding is an isometry.
* `TauCeti.exists_isometry_separableSpace_completeSpace`: a separable metric space embeds
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
  .mkOfBound ⟨fun y ↦ dist x y - dist x₀ y, by fun_prop⟩ (2 * dist x x₀) fun y z ↦ by
    have hy := abs_le.1 (abs_dist_sub_le x x₀ y)
    have hz := abs_le.1 (abs_dist_sub_le x x₀ z)
    rw [ContinuousMap.coe_mk, Real.dist_eq, abs_le]
    constructor <;> linarith [hy.1, hy.2, hz.1, hz.2]

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

/-- A separable metric space embeds isometrically into a separable real Banach space, namely the
closed linear span of its image under Mathlib's Kuratowski embedding into `ℓ^∞(ℕ, ℝ)`. -/
theorem exists_isometry_separableSpace_completeSpace (Y : Type*) [MetricSpace Y]
    [SeparableSpace Y] :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℝ E), CompleteSpace E ∧
      SeparableSpace E ∧ ∃ f : Y → E, Isometry f := by
  set K : Submodule ℝ ℓ^∞(ℕ, ℝ) :=
    (Submodule.span ℝ (range (_root_.kuratowskiEmbedding Y))).topologicalClosure
  have hK : IsSeparable (K : Set ℓ^∞(ℕ, ℝ)) :=
    (isSeparable_range (kuratowskiEmbedding.isometry Y).continuous).span.closure
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK.separableSpace,
    fun y ↦ ⟨_root_.kuratowskiEmbedding Y y,
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨y, rfl⟩)⟩,
    Isometry.of_dist_eq fun y y' ↦ (kuratowskiEmbedding.isometry Y).dist_eq y y'⟩

end TauCeti

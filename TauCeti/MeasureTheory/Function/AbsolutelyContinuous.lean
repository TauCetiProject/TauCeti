/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Absolutely continuous curves in pseudometric spaces

Mathlib defines `AbsolutelyContinuousOnInterval f a b` for maps `f : ℝ → X` into an arbitrary
pseudometric space, but states continuity (`AbsolutelyContinuousOnInterval.continuousOn`) and
bounded variation (`AbsolutelyContinuousOnInterval.boundedVariationOn`) only for maps into a
seminormed additive group. This file supplies both for an arbitrary pseudometric target, as needed
for curves in metric spaces which are not normed, such as spaces of probability measures with a
Wasserstein distance.

Both are transferred from the normed case along the Fréchet–Kuratowski embedding
`x ↦ (y ↦ dist x y - dist x₀ y)` of a pseudometric space into the bounded continuous real functions
on it. This embedding is an isometry, so it preserves absolute continuity, continuity and
variation.

## Main results

* `AbsolutelyContinuousOnInterval.continuousOn'`: an absolutely continuous curve in a pseudometric
  space is continuous on its interval.
* `AbsolutelyContinuousOnInterval.boundedVariationOn'`: an absolutely continuous curve in a
  pseudometric space has bounded variation on its interval.
-/

public section

open Set

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X]

/-- The Fréchet–Kuratowski embedding of a pseudometric space into the bounded continuous real
functions on it, based at `x₀`: it sends `x` to `y ↦ dist x y - dist x₀ y`. -/
private noncomputable def distEmbedding (x₀ x : X) : BoundedContinuousFunction X ℝ :=
  .mkOfBound ⟨fun y ↦ dist x y - dist x₀ y, by fun_prop⟩ (2 * dist x x₀) fun y z ↦ by
    have hy := abs_le.1 (abs_dist_sub_le x x₀ y)
    have hz := abs_le.1 (abs_dist_sub_le x x₀ z)
    rw [ContinuousMap.coe_mk, Real.dist_eq, abs_le]
    constructor <;> linarith [hy.1, hy.2, hz.1, hz.2]

private lemma isometry_distEmbedding (x₀ : X) : Isometry (distEmbedding x₀) := by
  refine Isometry.of_dist_eq fun x x' ↦ le_antisymm
    ((BoundedContinuousFunction.dist_le dist_nonneg).2 fun y ↦ ?_) ?_
  · simpa [distEmbedding, Real.dist_eq] using abs_dist_sub_le x x' y
  · simpa [distEmbedding, Real.dist_eq, abs_sub_comm, dist_comm x] using
      BoundedContinuousFunction.dist_coe_le_dist (f := distEmbedding x₀ x)
        (g := distEmbedding x₀ x') x

end TauCeti

namespace AbsolutelyContinuousOnInterval

variable {X : Type*} [PseudoMetricSpace X] {γ : ℝ → X} {a b : ℝ}

/-- An absolutely continuous curve in a pseudometric space is continuous on its interval. This
generalizes `AbsolutelyContinuousOnInterval.continuousOn` from seminormed groups to pseudometric
spaces. -/
theorem continuousOn' (hγ : AbsolutelyContinuousOnInterval γ a b) : ContinuousOn γ (uIcc a b) :=
  have he := TauCeti.isometry_distEmbedding (γ a)
  he.isUniformInducing.isInducing.continuousOn_iff.2
    (he.lipschitzWith.comp_absolutelyContinuousOnInterval hγ).continuousOn

/-- An absolutely continuous curve in a pseudometric space has bounded variation on its interval.
This generalizes `AbsolutelyContinuousOnInterval.boundedVariationOn` from seminormed groups to
pseudometric spaces. -/
theorem boundedVariationOn' (hγ : AbsolutelyContinuousOnInterval γ a b) :
    BoundedVariationOn γ (uIcc a b) := by
  have he := TauCeti.isometry_distEmbedding (γ a)
  have hvar : eVariationOn (TauCeti.distEmbedding (γ a) ∘ γ) (uIcc a b) =
      eVariationOn γ (uIcc a b) := by
    simp only [eVariationOn, Function.comp_apply, he.edist_eq]
  rw [BoundedVariationOn, ← hvar]
  exact (he.lipschitzWith.comp_absolutelyContinuousOnInterval hγ).boundedVariationOn

end AbsolutelyContinuousOnInterval

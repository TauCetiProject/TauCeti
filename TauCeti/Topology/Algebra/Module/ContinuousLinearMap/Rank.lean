/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Rank bounds for continuous linear maps

The rank of a continuous linear map `R` is the rank of its underlying linear map, the dimension of
its range. This file records facts used to work with maps of bounded rank, for instance in the
infimum defining approximation numbers.

* `ContinuousLinearMap.instNonemptyRankLE`: for every cardinal `c`, some continuous linear map has
  rank at most `c`, namely the zero map.
* `ContinuousLinearMap.rank_comp_le_of_rank_le`: postcomposition preserves a rank bound by a
  natural number. The bound is a natural number so that the three spaces may lie in different
  universes.
* `ContinuousLinearMap.range_toLinearMap_eq_bot`: only the zero map has trivial range.
* `ContinuousLinearMap.rank_eq_zero_iff`: over a domain, with torsion-free target, only the zero
  map has rank `0`.
* `ContinuousLinearMap.rank_add_le_of_le`: rank bounds add along a sum of maps.
-/

public section

universe v

namespace ContinuousLinearMap

variable {K E F G : Type*} [Semiring K]
  [TopologicalSpace E] [AddCommMonoid E] [Module K E]
  [TopologicalSpace F] [AddCommMonoid F] [Module K F]
  [TopologicalSpace G] [AddCommMonoid G] [Module K G]

/-- The continuous linear maps of rank at most `c` form a nonempty type: the zero map has
rank `0`. -/
instance instNonemptyRankLE [Nontrivial K] (c : Cardinal) :
    Nonempty {R : E →L[K] F // R.rank ≤ c} :=
  ⟨⟨0, by simp⟩⟩

/-- **Postcomposition preserves a finite rank bound.** If `R` has rank at most `n`, so does
`A ∘ R`, whatever the universes of the three spaces. -/
theorem rank_comp_le_of_rank_le (A : F →L[K] G) {R : E →L[K] F} {n : ℕ} (hR : R.rank ≤ n) :
    (A.comp R).rank ≤ n := by
  rw [toLinearMap_comp]
  exact Cardinal.lift_le_nat_iff.mp <|
    (LinearMap.lift_rank_comp_le_right _ _).trans (by simpa using hR)

/-- A continuous linear map has trivial range exactly when it is the zero map. This is the
`simp` normal form that `R.rank = 0` reaches through `Submodule.rank_eq_zero`. -/
@[simp]
theorem range_toLinearMap_eq_bot {R : E →L[K] F} : (R : E →ₗ[K] F).range = ⊥ ↔ R = 0 := by
  rw [LinearMap.range_eq_bot, ← toLinearMap_zero, coe_inj]

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {K E F : Type*} [Ring K]
  [TopologicalSpace E] [AddCommMonoid E] [Module K E]
  [TopologicalSpace F] [AddCommGroup F] [Module K F]

/-- Over a domain, a continuous linear map into a torsion-free module has rank `0` exactly when it
is the zero map.

This is not a `simp` lemma: `simp` already rewrites `R.rank = 0` to `range R = ⊥` through
`Submodule.rank_eq_zero`, and then to `R = 0` through `range_toLinearMap_eq_bot`. -/
theorem rank_eq_zero_iff [IsDomain K] [Module.IsTorsionFree K F] {R : E →L[K] F} :
    R.rank = 0 ↔ R = 0 := by
  rw [LinearMap.rank, Submodule.rank_eq_zero, range_toLinearMap_eq_bot]

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {K E : Type*} {F : Type v} [Ring K] [HasRankNullity.{v} K]
  [TopologicalSpace E] [AddCommGroup E] [Module K E]
  [TopologicalSpace F] [AddCommGroup F] [Module K F] [ContinuousAdd F]

/-- **Subadditivity of rank bounds.** If `R₁` has rank at most `a` and `R₂` rank at most `b`, then
`R₁ + R₂` has rank at most `a + b`. -/
theorem rank_add_le_of_le {R₁ R₂ : E →L[K] F} {a b : Cardinal} (h₁ : R₁.rank ≤ a)
    (h₂ : R₂.rank ≤ b) : (R₁ + R₂).rank ≤ a + b := by
  rw [toLinearMap_add]
  exact (LinearMap.rank_add_le _ _).trans (add_le_add h₁ h₂)

end ContinuousLinearMap

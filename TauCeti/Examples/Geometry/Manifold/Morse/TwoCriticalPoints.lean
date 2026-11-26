/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Geometry.Manifold.Morse.TwoCriticalPoints

/-!
# Examples: Reeb's theorem for degenerate critical points in dimension zero

Reeb's sphere theorem for functions with two possibly degenerate critical points
(`TauCeti.nonempty_homeomorph_sphere_of_two_criticalPoints`), and the cover by two Euclidean open
sets behind it (`TauCeti.exists_twoEuclideanOpenCover_of_two_criticalPoints`), assume neither
positive dimension nor connectedness. These examples check the dimension-zero case. On a manifold
modelled on a zero-dimensional space every point is a critical point of every function
(`TauCeti.criticalPoints_eq_univ_of_subsingleton`), so the hypothesis that a function has exactly
two critical points says that the manifold has exactly two points.

* On a two-point zero-dimensional manifold every function has both points critical and `2`
  critical points, and the theorem identifies the manifold with `S⁰`.
* The two Euclidean open sets of the cover are the two points: each singleton is open, the two
  cover the manifold, and each is homeomorphic to `ℝ⁰`.
* On a one-point zero-dimensional manifold every function has `1` critical point, so the
  hypothesis fails.
-/

open Module Set
open scoped ContDiff Manifold

namespace TauCeti.Examples.MorseTwoCriticalPoints

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Subsingleton E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- On a two-point manifold modelled on a zero-dimensional space, every function has both points
critical, so it has `2` critical points, and Reeb's theorem identifies the manifold with `S⁰`. -/
example [I.Boundaryless] [IsManifold I ∞ M] (hM : Nat.card M = 2) (f : M → ℝ) :
    criticalPoints I f = univ ∧ totalCriticalCount I f = 2 ∧
      Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) := by
  have : Finite M := Nat.finite_of_card_ne_zero (by omega)
  have : Subsingleton H := I.injective.subsingleton
  have : DiscreteTopology M := ChartedSpace.discreteTopology H M
  have h2 : totalCriticalCount I f = 2 := by
    simp [totalCriticalCount_of_subsingleton, ENat.card_eq_coe_natCard, hM]
  refine ⟨criticalPoints_eq_univ_of_subsingleton, h2, ?_⟩
  have h := nonempty_homeomorph_sphere_of_two_criticalPoints contMDiff_of_discreteTopology h2
  rwa [finrank_zero_of_subsingleton] at h

/-- On a manifold `M = {x, y}` modelled on a zero-dimensional space, the singletons `{x}` and
`{y}` are open sets covering `M`, each homeomorphic to `ℝ⁰`. -/
example {x y : M} (hM : (univ : Set M) = {x, y}) :
    IsOpen {x} ∧ IsOpen {y} ∧ {x} ∪ {y} = (univ : Set M) ∧
      Nonempty (({x} : Set M) ≃ₜ EuclideanSpace ℝ (Fin 0)) ∧
      Nonempty (({y} : Set M) ≃ₜ EuclideanSpace ℝ (Fin 0)) := by
  have : Subsingleton H := I.injective.subsingleton
  have : DiscreteTopology M := ChartedSpace.discreteTopology H M
  exact ⟨isOpen_discrete _, isOpen_discrete _, by rw [hM, insert_eq],
    ⟨Homeomorph.homeomorphOfUnique _ _⟩, ⟨Homeomorph.homeomorphOfUnique _ _⟩⟩

/-- On a one-point manifold modelled on a zero-dimensional space, every function has `1` critical
point, so the hypothesis of Reeb's theorem fails. -/
example [Unique M] (f : M → ℝ) : totalCriticalCount I f = 1 := by
  rw [totalCriticalCount_of_subsingleton, ENat.card_eq_one_iff_unique]
  exact ⟨inferInstance⟩

end TauCeti.Examples.MorseTwoCriticalPoints

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Sphere
public import Mathlib.Topology.Homotopy.Equiv

/-!
# The Smale conjecture for the three-sphere

The reference homomorphism from the orthogonal group of `ℝ⁴` to the smooth
self-diffeomorphisms of the round three-sphere is already continuous for the weak Whitney
topology.  This file records the sharp Smale conjecture: that this particular inclusion, rather
than merely some homotopy equivalence between the two spaces, is itself a homotopy equivalence.

The proposition is the formal shape of Hatcher's theorem.  It records the canonical map whose
homotopy inverse compares the homotopy type of `Diff (S³)` with that of `O(4)`.  Continuity of the
displayed map is supplied by `TauCeti.continuous_orthogonalToDiffSphere`.

## Main definitions

* `TauCeti.SmaleConjecture`: the inclusion `O(4) → Diff(S³)` is a homotopy equivalence.

## References

* A. Hatcher, *A proof of the Smale conjecture, Diff(S³) ≃ O(4)*, Ann. of Math. 117 (1983),
  553–607.
* R. Kirby, *Problems in Low-Dimensional Topology*, Problem 4.34.
-/

public section

open Metric
open scoped Manifold ContDiff

namespace TauCeti

open scoped EuclideanSpace TauCeti.DiffeomorphWeakWhitney

/-- **Smale's conjecture for the three-sphere:** the canonical continuous inclusion of the
orthogonal group `O(4)` into the weak-Whitney space of smooth self-diffeomorphisms of the round
three-sphere is a homotopy equivalence. -/
def SmaleConjecture : Prop :=
  ∃ e : ContinuousMap.HomotopyEquiv (Matrix.orthogonalGroup (Fin 4) ℝ)
      (Diff (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞),
    e.toFun = continuousOrthogonalToDiffSphere 3 ∞

/-- Characterize Smale's conjecture by a continuous inverse for the canonical inclusion and the two
homotopies witnessing its inverse laws. -/
theorem smaleConjecture_iff_exists_homotopyInverse :
    SmaleConjecture ↔
      ∃ g : ContinuousMap
          (Diff (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞)
          (Matrix.orthogonalGroup (Fin 4) ℝ),
        (g.comp (continuousOrthogonalToDiffSphere 3 ∞)).Homotopic (ContinuousMap.id _) ∧
          ((continuousOrthogonalToDiffSphere 3 ∞).comp g).Homotopic (ContinuousMap.id _) := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e.invFun, ?_, ?_⟩
    · rw [← he]
      exact e.left_inv
    · rw [← he]
      exact e.right_inv
  · rintro ⟨g, hleft, hright⟩
    exact ⟨{
      toFun := continuousOrthogonalToDiffSphere 3 ∞
      invFun := g
      left_inv := hleft
      right_inv := hright
    }, rfl⟩

end TauCeti

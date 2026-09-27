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

The proposition is intentionally stated without a proof.  It is the formal shape of Hatcher's
theorem and is the endpoint that the geometric-topology roadmap needs in order to compare the
homotopy type of `Diff (S³)` with that of `O(4)`.  Continuity of the displayed map is supplied by
`TauCeti.continuous_orthogonalToDiffSphere`; the remaining content is the existence of a homotopy
inverse.

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
    (e.toFun : Matrix.orthogonalGroup (Fin 4) ℝ →
      Diff (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞) =
      fun A ↦ orthogonalToDiffSphere 3 ∞ A

/-- Smale's conjecture is stable under taking the product of two copies of the spaces. -/
theorem smaleConjecture_prod (h : SmaleConjecture) :
    ∃ e : ContinuousMap.HomotopyEquiv
        (Matrix.orthogonalGroup (Fin 4) ℝ × Matrix.orthogonalGroup (Fin 4) ℝ)
        (Diff (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞ ×
          Diff (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞),
      (e.toFun : Matrix.orthogonalGroup (Fin 4) ℝ × Matrix.orthogonalGroup (Fin 4) ℝ →
        Diff (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞ ×
          Diff (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞) =
        fun p ↦ (orthogonalToDiffSphere 3 ∞ p.1, orthogonalToDiffSphere 3 ∞ p.2) := by
  rcases h with ⟨e, he⟩
  refine ⟨e.prodCongr e, ?_⟩
  funext p
  simp only [ContinuousMap.HomotopyEquiv.prodCongr, ContinuousMap.prodMap_apply, he]
  rfl

end TauCeti

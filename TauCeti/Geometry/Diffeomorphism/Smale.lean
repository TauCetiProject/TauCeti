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
    (e.toFun : Matrix.orthogonalGroup (Fin 4) ℝ →
      Diff (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞) =
      fun A ↦ orthogonalToDiffSphere 3 ∞ A

/-- The canonical inclusion, packaged as a continuous map for homotopy constructions. -/
noncomputable def continuousOrthogonalToDiffSphere :
    ContinuousMap (Matrix.orthogonalGroup (Fin 4) ℝ)
      (Diff (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞) :=
  ⟨orthogonalToDiffSphere 3 ∞, continuous_orthogonalToDiffSphere 3 ∞⟩

/-- Characterize `SmaleConjecture` using the bundled canonical continuous map. -/
theorem smaleConjecture_iff :
    SmaleConjecture ↔
      ∃ e : ContinuousMap.HomotopyEquiv (Matrix.orthogonalGroup (Fin 4) ℝ)
          (Diff (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞),
        e.toFun = continuousOrthogonalToDiffSphere := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    apply ContinuousMap.ext
    intro A
    exact congrFun he A
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    funext A
    exact ContinuousMap.congr_fun he A

/-- Smale's conjecture supplies a continuous homotopy inverse for the canonical inclusion. -/
theorem smaleConjecture_homotopyInverse (h : SmaleConjecture) :
    ∃ g : ContinuousMap
        (Diff (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞)
        (Matrix.orthogonalGroup (Fin 4) ℝ),
      (g.comp continuousOrthogonalToDiffSphere).Homotopic (ContinuousMap.id _) ∧
        (continuousOrthogonalToDiffSphere.comp g).Homotopic (ContinuousMap.id _) := by
  rcases smaleConjecture_iff.mp h with ⟨e, he⟩
  refine ⟨e.invFun, ?_, ?_⟩
  · rw [← he]
    exact e.left_inv
  · rw [← he]
    exact e.right_inv

end TauCeti

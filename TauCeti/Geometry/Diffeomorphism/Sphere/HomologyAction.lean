/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
public import TauCeti.Geometry.Diffeomorphism.HomologyAction

/-!
# The factor swap of `S² × S²` on integral homology

For the product of two area forms of equal area on `S² × S²`, the homologically trivial
stabilizer `TauCeti.SmoothForm.homologicallyTrivialStabilizer σ (ModuleCat.of ℤ (ULift ℤ)) 2`, for
`H₂(·; ℤ)`, is the group `G₀` in Gromov's description of the symplectomorphism group of
`S² × S²`. The factor swap is never in it: it exchanges the classes `A = [S² × pt]` and
`B = [pt × S²]` of the two rulings in `H₂(S² × S²; ℤ)`.

## Main results

* `TauCeti.SmoothForm.prodComm_sphere_notMem_homologicallyTrivialStabilizer`: the factor swap of
  `S² × S²` acts nontrivially on `H₂(S² × S²; ℤ)`.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. **82** (1985),
  307–347, §2.4 (the symplectomorphism group of `S² × S²`).
-/

public section

open scoped Manifold ContDiff


namespace TauCeti.SmoothForm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {j : ℕ}

/-- **The swap of `S² × S²` is not homologically trivial.** For every smooth form `σ` on
`S² × S²`, such as the product of two area forms of equal area, the factor swap does not lie in
the homologically trivial stabilizer of `σ` for `H₂(S² × S²; ℤ)`: it exchanges the classes
`A = [S² × pt]` and `B = [pt × S²]` of the two rulings. -/
theorem prodComm_sphere_notMem_homologicallyTrivialStabilizer
    (σ : SmoothForm ((𝓡 2).prod (𝓡 2))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ×
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) F j) :
    Diffeomorph.prodComm (𝓡 2) (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞ ∉
      σ.homologicallyTrivialStabilizer (ModuleCat.of ℤ (ULift.{0} ℤ)) 2 := by
  have := simplyConnectedSpace_sphere_euclideanSpace (n := 2) le_rfl
  obtain ⟨o⟩ := HomologicalOrientation.nonempty_of_simplyConnectedSpace
    (M := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (finrank_euclideanSpace_fin (n := 2))
  exact o.prodComm_notMem_homologicallyTrivialStabilizer finrank_euclideanSpace_fin two_ne_zero σ

end TauCeti.SmoothForm

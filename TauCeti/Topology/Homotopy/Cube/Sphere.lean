/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Compactification.OnePoint.Sphere
public import TauCeti.Topology.Homotopy.Cube.OnePoint

/-!
# Collapsing the boundary of the cube onto a sphere

For `k ≥ 1`, the unit sphere `S^k ⊆ ℝ^(k+1)` is the quotient of the cube `I^k` by its boundary:
the cube with its boundary collapsed is `OnePoint (Fin k → ℝ)` (`TauCeti.cubeToOnePoint`), which is
homeomorphic to `S^k`, with `∞` at any prescribed basepoint
(`TauCeti.onePointHomeomorphSphere`).

## Main declarations

* `TauCeti.sphereCollapse`: the continuous map `I^k → S^k` collapsing the cube boundary to a given
  basepoint of the sphere, a quotient map for `k ≥ 1` (`TauCeti.sphereCollapse_surjective`).
-/

public section

noncomputable section

open Metric OnePoint
open scoped unitInterval

namespace TauCeti

variable (k : ℕ)

/-- The map `I^k → S^k` collapsing the boundary of the cube to the basepoint `s₀`. It is a
quotient map for `k ≥ 1`, when it is surjective. -/
def sphereCollapse (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    C((Fin k → I), sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :=
  (ContinuousMap.mk (onePointHomeomorphSphere k s₀)
    (onePointHomeomorphSphere k s₀).continuous).comp (cubeToOnePoint (Fin k))

/-- The collapse onto the sphere is the collapse of the cube onto `OnePoint (Fin k → ℝ)` followed by
the homeomorphism with the sphere. -/
theorem sphereCollapse_apply (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)
    (z : Fin k → I) :
    sphereCollapse k s₀ z = onePointHomeomorphSphere k s₀ (cubeToOnePoint (Fin k) z) := by
  rw [sphereCollapse]
  rfl

/-- The collapse sends a point of the cube to the basepoint exactly when it is on the boundary. -/
@[simp]
theorem sphereCollapse_eq_basepoint_iff (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)
    (z : Fin k → I) : sphereCollapse k s₀ z = s₀ ↔ z ∈ Cube.boundary (Fin k) := by
  have h := onePointHomeomorphSphere_infty k s₀
  rw [← cubeToOnePoint_eq_infty_iff, sphereCollapse_apply]
  exact ⟨fun hz => (onePointHomeomorphSphere k s₀).injective (hz.trans h.symm),
    fun hz => by rw [hz, h]⟩

/-- Two cube points with the same image under the collapse are equal, or both on the boundary. -/
theorem eq_or_mem_boundary_of_sphereCollapse_eq
    (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) {z z' : Fin k → I}
    (h : sphereCollapse k s₀ z = sphereCollapse k s₀ z') :
    z = z' ∨ (z ∈ Cube.boundary (Fin k) ∧ z' ∈ Cube.boundary (Fin k)) :=
  eq_or_mem_boundary_of_cubeToOnePoint_eq ((onePointHomeomorphSphere k s₀).injective h)

variable [NeZero k] (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)

/-- The collapse map is surjective for `k ≥ 1`. -/
theorem sphereCollapse_surjective : Function.Surjective (sphereCollapse k s₀) := by
  have : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_neZero k⟩⟩
  exact (onePointHomeomorphSphere k s₀).surjective.comp cubeToOnePoint_surjective

end TauCeti

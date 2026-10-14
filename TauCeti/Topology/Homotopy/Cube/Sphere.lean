/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Sphere.LinearIsometry
public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import TauCeti.Topology.Homotopy.Cube.OnePoint

/-!
# Collapsing the boundary of the cube onto a sphere

For `k ≥ 1`, the unit sphere `S^k ⊆ ℝ^(k+1)` is the quotient of the cube `I^k` by its boundary:
the cube with its boundary collapsed is `OnePoint (Fin k → ℝ)` (`TauCeti.cubeToOnePoint`), which is
homeomorphic to `S^k`, with `∞` at any prescribed basepoint.

## Main declarations

* `TauCeti.onePointHomeomorphSphere`: `OnePoint (Fin k → ℝ) ≃ₜ S^k` sending `∞` to a basepoint.
* `TauCeti.sphereCollapse`: the continuous map `I^k → S^k` collapsing the cube boundary to a given
  basepoint of the sphere, a quotient map for `k ≥ 1` (`TauCeti.sphereCollapse_surjective`).
-/

public section

noncomputable section

open Metric OnePoint
open scoped unitInterval

namespace TauCeti

variable (k : ℕ)

/-- Mathlib's homeomorphism of the one-point compactification of `ℝ^k` with the unit sphere
`S^k ⊆ ℝ^(k+1)`. -/
private def onePointHomeomorphSphereAux :
    OnePoint (Fin k → ℝ) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 :=
  onePointEquivSphereOfFinrankEq (V := Fin k → ℝ) (ι := Fin (k + 1)) (by simp)

/-- The unit sphere `S^k ⊆ ℝ^(k+1)` is the one-point compactification of `ℝ^k` with `∞` at any
prescribed basepoint `s₀`: Mathlib's homeomorphism `onePointEquivSphereOfFinrankEq`, followed by a
linear isometry of `ℝ^(k+1)` moving the image of `∞` to `s₀`. -/
def onePointHomeomorphSphere (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    OnePoint (Fin k → ℝ) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 :=
  (onePointHomeomorphSphereAux k).trans
    (LinearIsometryEquiv.unitSphereIsometryEquiv
      (MulAction.exists_smul_eq (EuclideanSpace ℝ (Fin (k + 1)) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin (k + 1))) (onePointHomeomorphSphereAux k ∞) s₀).choose).toHomeomorph

private theorem toHomeomorph_unitSphereIsometryEquiv_apply
    (g : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k + 1)))
    (x : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    (LinearIsometryEquiv.unitSphereIsometryEquiv g).toHomeomorph x = g • x :=
  Subtype.ext ((LinearIsometryEquiv.coe_unitSphereIsometryEquiv_apply g x).trans
    (LinearIsometryEquiv.coe_smul_unitSphere g x).symm)

@[simp]
theorem onePointHomeomorphSphere_infty (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    onePointHomeomorphSphere k s₀ ∞ = s₀ := by
  rw [onePointHomeomorphSphere, Homeomorph.trans_apply]
  exact (toHomeomorph_unitSphereIsometryEquiv_apply k _ _).trans
    (MulAction.exists_smul_eq (EuclideanSpace ℝ (Fin (k + 1)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (k + 1))) (onePointHomeomorphSphereAux k ∞) s₀).choose_spec

/-- The map `I^k → S^k` collapsing the boundary of the cube to the basepoint `s₀`. It is a
quotient map for `k ≥ 1`, when it is surjective. -/
def sphereCollapse (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    C((Fin k → I), sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :=
  (ContinuousMap.mk (onePointHomeomorphSphere k s₀)
    (onePointHomeomorphSphere k s₀).continuous).comp (cubeToOnePoint (Fin k))

theorem sphereCollapse_apply (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)
    (z : Fin k → I) :
    sphereCollapse k s₀ z = onePointHomeomorphSphere k s₀ (cubeToOnePoint (Fin k) z) := by
  rw [sphereCollapse]
  rfl

@[simp]
theorem sphereCollapse_eq_basepoint_iff (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)
    (z : Fin k → I) : sphereCollapse k s₀ z = s₀ ↔ z ∈ Cube.boundary (Fin k) := by
  have h := onePointHomeomorphSphere_infty k s₀
  rw [← cubeToOnePoint_eq_infty_iff, sphereCollapse_apply]
  exact ⟨fun hz => (onePointHomeomorphSphere k s₀).injective (hz.trans h.symm),
    fun hz => by rw [hz, h]⟩

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

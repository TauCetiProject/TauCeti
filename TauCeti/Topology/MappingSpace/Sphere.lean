/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import TauCeti.Topology.Homotopy.Cube.OnePoint
public import TauCeti.Topology.Homotopy.HomotopyGroup.IteratedLoopSpace.Homeomorph
public import TauCeti.Topology.MappingSpace.Based

/-!
# Based mapping spaces out of spheres

For `k ≥ 1`, the space `Map_*(S^k, X)` of continuous maps from the unit sphere
`S^k ⊆ ℝ^(k+1)` to a space `X`, sending a basepoint of the sphere to a point `x` of `X`, with the
compact-open topology, is homeomorphic to the space `Ω^ (Fin k) X x` of generalized loops
`I^k → X` sending the cube boundary to `x`, and to the `k`-fold iterated loop space `Ω^[k] X`.
The homeomorphism is precomposition with a quotient map `I^k → S^k` that collapses the boundary
of the cube to the basepoint: the cube is the closed unit ball of the sup norm on `ℝ^k`, which with
its boundary collapsed is the one-point compactification of `ℝ^k`, which is homeomorphic to `S^k`.
It is natural in `X` by postcomposition.

## Main declarations

* `TauCeti.sphereHomeomorphOfBasepoints`: a homeomorphism of the sphere carrying a given point to
  another given point, a reflection.
* `TauCeti.sphereCollapse`: the quotient map `I^k → S^k` collapsing the cube boundary to a given
  basepoint of the sphere.
* `TauCeti.basedMapSphereHomeomorph`: `Map_*(S^k, X) ≃ₜ Ω^ (Fin k) X x`.
* `TauCeti.BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace`:
  `Map_*(S^k, X) ≃ₜ Ω^[k] X`, natural in `X` by
  `TauCeti.BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace_map`.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I.
-/

public section

noncomputable section

open Metric Module OnePoint Submodule Set Topology.Homotopy
open scoped unitInterval

namespace TauCeti

section Reflection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Any point of the unit sphere is carried to any other by a homeomorphism of the sphere: the
reflection in the hyperplane orthogonal to the difference. -/
def sphereHomeomorphOfBasepoints (v w : sphere (0 : E) 1) : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1 :=
  (reflection (ℝ ∙ ((v : E) - w))ᗮ).toHomeomorph.subtype fun x => by
    simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph,
      LinearIsometryEquiv.norm_map]

omit [FiniteDimensional ℝ E] in
theorem sphereHomeomorphOfBasepoints_apply_self (v w : sphere (0 : E) 1) :
    sphereHomeomorphOfBasepoints v w v = w :=
  Subtype.ext (reflection_sub (by simp [mem_sphere_zero_iff_norm.1 v.2,
    mem_sphere_zero_iff_norm.1 w.2]))

end Reflection

section Sphere

variable (k : ℕ)

/-- The unit sphere `S^k ⊆ ℝ^(k+1)` is the one-point compactification of `ℝ^k` with `∞` at any
prescribed basepoint `s₀`: Mathlib's homeomorphism
`onePointEquivSphereOfFinrankEq`, followed by a reflection moving the image of `∞` to `s₀`. -/
def onePointHomeomorphSphere (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    OnePoint (Fin k → ℝ) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 :=
  (onePointEquivSphereOfFinrankEq (V := Fin k → ℝ) (ι := Fin (k + 1)) (by simp)).trans
    (sphereHomeomorphOfBasepoints
      (onePointEquivSphereOfFinrankEq (V := Fin k → ℝ) (ι := Fin (k + 1)) (by simp) ∞) s₀)

@[simp]
theorem onePointHomeomorphSphere_infty (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    onePointHomeomorphSphere k s₀ ∞ = s₀ :=
  sphereHomeomorphOfBasepoints_apply_self _ _

/-- The quotient map `I^k → S^k` collapsing the boundary of the cube to the basepoint `s₀`. -/
def sphereCollapse (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    C((Fin k → I), sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :=
  (ContinuousMap.mk (onePointHomeomorphSphere k s₀)
    (onePointHomeomorphSphere k s₀).continuous).comp (cubeToOnePoint (Fin k))

@[simp]
theorem sphereCollapse_apply (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)
    (z : Fin k → I) :
    sphereCollapse k s₀ z = onePointHomeomorphSphere k s₀ (cubeToOnePoint (Fin k) z) := by
  rw [sphereCollapse]
  rfl

theorem sphereCollapse_eq_iff (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)
    (z : Fin k → I) : sphereCollapse k s₀ z = s₀ ↔ z ∈ Cube.boundary (Fin k) := by
  have h := onePointHomeomorphSphere_infty k s₀
  rw [← cubeToOnePoint_eq_infty_iff, sphereCollapse_apply]
  exact ⟨fun hz => (onePointHomeomorphSphere k s₀).injective (hz.trans h.symm),
    fun hz => by rw [hz, h]⟩

theorem eq_or_mem_boundary_of_sphereCollapse_eq (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)
    {z z' : Fin k → I}
    (h : sphereCollapse k s₀ z = sphereCollapse k s₀ z') :
    z = z' ∨ (z ∈ Cube.boundary (Fin k) ∧ z' ∈ Cube.boundary (Fin k)) :=
  eq_or_mem_boundary_of_cubeToOnePoint_eq ((onePointHomeomorphSphere k s₀).injective h)

end Sphere

section Maps

variable (k : ℕ) [NeZero k] {X : Type*} [TopologicalSpace X] (x : X)
  (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)

theorem sphereCollapse_surjective : Function.Surjective (sphereCollapse k s₀) := by
  have : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_neZero k⟩⟩
  exact (onePointHomeomorphSphere k s₀).surjective.comp cubeToOnePoint_surjective

/-- **Based maps out of the sphere are generalized loops.** For `k ≥ 1`, the space
`Map_*(S^k, X)` of continuous maps from the unit sphere in `ℝ^(k+1)` to `X` sending the basepoint
`s₀` to `x` is homeomorphic to the space `Ω^ (Fin k) X x` of maps `I^k → X` sending the cube
boundary to `x`, by precomposition with the quotient map `sphereCollapse`. -/
def basedMapSphereHomeomorph :
    BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X s₀ x ≃ₜ Ω^ (Fin k) X x :=
  BasedMap.homeomorphGenLoop (sphereCollapse k s₀) s₀ (sphereCollapse_eq_iff k s₀)
    (sphereCollapse_surjective k s₀) fun _ _ h => eq_or_mem_boundary_of_sphereCollapse_eq k s₀ h

@[simp]
theorem basedMapSphereHomeomorph_apply
    (f : BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X s₀ x) (z : Fin k → I) :
    basedMapSphereHomeomorph k x s₀ f z = f.1 (sphereCollapse k s₀ z) :=
  BasedMap.homeomorphGenLoop_apply _ _ _ _ _ _ _

/-- The homeomorphism `basedMapSphereHomeomorph` is natural in `X`: it commutes with
postcomposition by a based map `g : X → Y`. -/
theorem basedMapSphereHomeomorph_map {Y : Type*} [TopologicalSpace Y] {y : Y} (g : C(X, Y))
    (hg : g x = y)
    (f : BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X s₀ x) :
    basedMapSphereHomeomorph k y s₀ (BasedMap.map g hg f) =
      GenLoop.map g hg (basedMapSphereHomeomorph k x s₀ f) :=
  BasedMap.homeomorphGenLoop_map _ _ _ _ _ _ _ _

end Maps

namespace BasedTopologicalSpace

universe u

/-- **Based maps out of the sphere are iterated loops.** For `k ≥ 1` and a based space `X`, the
space `Map_*(S^k, X)` of maps from the unit sphere in `ℝ^(k+1)`, based at `s₀`, to `X` is
homeomorphic to the `k`-fold iterated loop space `Ω^[k] X`. -/
def basedMapSphereHomeomorphIteratedLoopSpace (k : ℕ) [NeZero k] (X : BasedTopologicalSpace.{u})
    (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X.carrier s₀ X.basepoint ≃ₜ
      (X.iteratedLoopSpace k).carrier :=
  (basedMapSphereHomeomorph k X.basepoint s₀).trans (iteratedLoopSpaceHomeomorph k X).symm

/-- The homeomorphism `basedMapSphereHomeomorphIteratedLoopSpace` is natural in `X`: it commutes
with postcomposition by a based map and the induced map `Ω^[k] f` of iterated loop spaces. -/
theorem basedMapSphereHomeomorphIteratedLoopSpace_map (k : ℕ) [NeZero k]
    {X Y : BasedTopologicalSpace.{u}} (f : Hom X Y)
    (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)
    (φ : BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X.carrier s₀ X.basepoint) :
    basedMapSphereHomeomorphIteratedLoopSpace k Y s₀
        (BasedMap.map f.toContinuousMap f.map_basepoint φ) =
      f.iteratedLoopSpace k (basedMapSphereHomeomorphIteratedLoopSpace k X s₀ φ) := by
  apply (iteratedLoopSpaceHomeomorph k Y).injective
  rw [iteratedLoopSpaceHomeomorph_map]
  simp [basedMapSphereHomeomorphIteratedLoopSpace, basedMapSphereHomeomorph_map]

end BasedTopologicalSpace

end TauCeti

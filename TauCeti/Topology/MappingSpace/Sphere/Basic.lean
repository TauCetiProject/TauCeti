/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Cube.Sphere
public import TauCeti.Topology.Homotopy.IteratedLoopSpace.Homeomorph
public import TauCeti.Topology.MappingSpace.Based

/-!
# Based mapping spaces out of spheres

For `k ≥ 1`, the space `Map_*(S^k, X)` of continuous maps from the unit sphere
`S^k ⊆ ℝ^(k+1)` to a space `X`, sending a basepoint of the sphere to a point `x` of `X`, with the
compact-open topology, is homeomorphic to the space `Ω^ (Fin k) X x` of generalized loops
`I^k → X` sending the cube boundary to `x`, and to the `k`-fold iterated loop space `Ω^[k] X`.
The homeomorphism is precomposition with the map `I^k → S^k` that collapses the boundary of the
cube to the basepoint, which for `k ≥ 1` is a quotient map: the cube is the closed unit ball of the
sup norm on `ℝ^k`, which with its boundary collapsed is the one-point compactification of `ℝ^k`
(for `k ≥ 1`), which is homeomorphic to `S^k`.
It is natural in `X` by postcomposition.

## Main declarations

The collapse map `TauCeti.sphereCollapse` is in `TauCeti.Topology.Homotopy.Cube.Sphere`.

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


section Maps

variable (k : ℕ) [NeZero k] {X : Type*} [TopologicalSpace X] (x : X)
  (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)

/-- **Based maps out of the sphere are generalized loops.** For `k ≥ 1`, the space
`Map_*(S^k, X)` of continuous maps from the unit sphere in `ℝ^(k+1)` to `X` sending the basepoint
`s₀` to `x` is homeomorphic to the space `Ω^ (Fin k) X x` of maps `I^k → X` sending the cube
boundary to `x`, by precomposition with the quotient map `sphereCollapse` (a quotient map as
`k ≥ 1`). -/
def basedMapSphereHomeomorph :
    BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X s₀ x ≃ₜ Ω^ (Fin k) X x :=
  BasedMap.homeomorphGenLoop (sphereCollapse k s₀) s₀ (sphereCollapse_eq_basepoint_iff k s₀)
    (sphereCollapse_surjective k s₀) fun _ _ h => eq_or_mem_boundary_of_sphereCollapse_eq k s₀ h

/-- The homeomorphism `basedMapSphereHomeomorph` takes a based map `f` to the generalized loop
`z ↦ f (sphereCollapse z)`. -/
@[simp]
theorem basedMapSphereHomeomorph_apply
    (f : BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X s₀ x) (z : Fin k → I) :
    basedMapSphereHomeomorph k x s₀ f z = f.1 (sphereCollapse k s₀ z) :=
  BasedMap.homeomorphGenLoop_apply _ _ _ _ _ _ _

/-- The inverse of `basedMapSphereHomeomorph` evaluates at `sphereCollapse z` to the value of the
generalized loop at `z`. -/
@[simp]
theorem basedMapSphereHomeomorph_symm_apply (p : Ω^ (Fin k) X x) (z : Fin k → I) :
    ((basedMapSphereHomeomorph k x s₀).symm p).1 (sphereCollapse k s₀ z) = p z :=
  BasedMap.homeomorphGenLoop_symm_apply_comp _ _ _ _ _ _ _

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

/-- The cube-loop homeomorphism of the iterated loop space takes a based sphere map to the
generalized loop of `basedMapSphereHomeomorph`. -/
@[simp]
theorem iteratedLoopSpaceHomeomorph_basedMapSphereHomeomorphIteratedLoopSpace (k : ℕ) [NeZero k]
    (X : BasedTopologicalSpace.{u}) (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)
    (φ : BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) X.carrier s₀ X.basepoint) :
    iteratedLoopSpaceHomeomorph k X (basedMapSphereHomeomorphIteratedLoopSpace k X s₀ φ) =
      basedMapSphereHomeomorph k X.basepoint s₀ φ :=
  (iteratedLoopSpaceHomeomorph k X).apply_symm_apply _

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
  rw [iteratedLoopSpaceHomeomorph_basedMapSphereHomeomorphIteratedLoopSpace,
    basedMapSphereHomeomorph_map,
    iteratedLoopSpaceHomeomorph_basedMapSphereHomeomorphIteratedLoopSpace]

end BasedTopologicalSpace

end TauCeti

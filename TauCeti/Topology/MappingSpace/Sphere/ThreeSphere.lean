/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Quaternion
public import TauCeti.Topology.MappingSpace.FreeLoop
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph

/-!
# The free loop space of the three-sphere

Let `S³` be the unit sphere of a real normed space of dimension `4`. It is homeomorphic to the unit
quaternions (`TauCeti.threeSphereHomeomorphUnitQuaternion`), a topological group, and transporting
their multiplication makes `S³` a topological group (`TauCeti.threeSphereGroup`,
`TauCeti.isTopologicalGroup_threeSphere`). The free loop space of a topological group `G` is the
product `G × ΩG` (`TauCeti.circleMapGroupHomeomorphLoopSpace`), so the free loop space of `S³` is
the product of the sphere and its loop space, `𝓛S³ ≃ₜ S³ × ΩS³`
(`TauCeti.circleMapThreeSphereHomeomorphProd`), with loops based at the point
`TauCeti.threeSphereOne` corresponding to the unit quaternion `1`.

## Main declarations

* `TauCeti.threeSphereHomeomorphUnitQuaternion`: `S³` is homeomorphic to the unit quaternions.
* `TauCeti.threeSphereGroup`, `TauCeti.isTopologicalGroup_threeSphere`: the topological group
  structure on `S³` transported from the unit quaternions, with identity `TauCeti.threeSphereOne`.
* `TauCeti.circleMapThreeSphereHomeomorphProd`: `C(S¹, S³) ≃ₜ S³ × ΩS³`, whose first coordinate is
  the value at `1 ∈ S¹` (`_apply_fst`).

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.
-/

public section

noncomputable section

universe u

open Metric Module
open scoped Quaternion

namespace TauCeti

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : finrank ℝ E = 3 + 1)

include hE in
/-- The unit sphere of a four-dimensional real normed space is homeomorphic to the unit
quaternions. -/
def threeSphereHomeomorphUnitQuaternion : sphere (0 : E) 1 ≃ₜ sphere (0 : ℍ[ℝ]) 1 :=
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  sphereHomeomorphOfFinrankEq (by rw [hE, Quaternion.finrank_eq_four])

/-- The group structure on the three-sphere transported from the unit quaternions. -/
abbrev threeSphereGroup : Group (sphere (0 : E) 1) :=
  (threeSphereHomeomorphUnitQuaternion hE).toEquiv.group

/-- With the multiplication transported from the unit quaternions, the three-sphere is a
topological group: the homeomorphism with the unit quaternions is then a group isomorphism. -/
theorem isTopologicalGroup_threeSphere :
    @IsTopologicalGroup (sphere (0 : E) 1) _ (threeSphereGroup hE) :=
  letI := threeSphereGroup hE
  (threeSphereHomeomorphUnitQuaternion hE).isInducing.isTopologicalGroup
    (threeSphereHomeomorphUnitQuaternion hE).toEquiv.mulEquiv

/-- The base point of the three-sphere at which the free loop space splits off the loop space: the
point corresponding to the unit quaternion `1`, the identity of `TauCeti.threeSphereGroup`. -/
def threeSphereOne : sphere (0 : E) 1 :=
  (threeSphereHomeomorphUnitQuaternion hE).symm 1

/-- **The free loop space of the three-sphere is the product of the sphere and its loop space**,
`C(S¹, S³) ≃ₜ S³ × ΩS³`, through the group structure transported from the unit quaternions. -/
def circleMapThreeSphereHomeomorphProd :
    C(Circle, sphere (0 : E) 1) ≃ₜ
      sphere (0 : E) 1 × Path (threeSphereOne hE) (threeSphereOne hE) :=
  letI := threeSphereGroup hE
  letI := isTopologicalGroup_threeSphere hE
  (circleMapGroupHomeomorphLoopSpace (sphere (0 : E) 1)).symm

/-- The sphere coordinate of a free loop in `S³` is its value at `1 ∈ S¹`. -/
@[simp]
theorem circleMapThreeSphereHomeomorphProd_apply_fst (f : C(Circle, sphere (0 : E) 1)) :
    (circleMapThreeSphereHomeomorphProd hE f).1 = f 1 :=
  letI := threeSphereGroup hE
  letI := isTopologicalGroup_threeSphere hE
  circleMapGroupHomeomorphLoopSpace_symm_fst f

end TauCeti

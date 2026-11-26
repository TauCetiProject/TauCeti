/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Quaternion.Unitary.Sphere
public import TauCeti.Topology.MappingSpace.FreeLoop

/-!
# The free loop space of the three-sphere

Let `S³` be the unit sphere of a real normed space of dimension `4`, made a topological group by
transporting the multiplication of the unit quaternions (`TauCeti.threeSphereGroup`,
`TauCeti.isTopologicalGroup_threeSphere`). The free loop space of a topological group `G` is the
product `G × ΩG` (`TauCeti.circleMapGroupHomeomorphLoopSpace`), so the free loop space of `S³` is
the product of the sphere and its loop space, `𝓛S³ ≃ₜ S³ × ΩS³`
(`TauCeti.circleMapThreeSphereHomeomorphProd`), with loops based at the point
`TauCeti.threeSphereOne` corresponding to the unit quaternion `1`.

## Main declarations

* `TauCeti.circleMapThreeSphereHomeomorphProd`: `C(S¹, S³) ≃ₜ S³ × ΩS³`, whose first coordinate is
  the value at `1 ∈ S¹` (`_apply_fst`), whose loop coordinate and inverse are given by quaternion
  products through `TauCeti.threeSphereHomeomorphUnitQuaternion` (`_apply_snd_apply`,
  `_symm_apply_unitToCircle`).

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.
-/

public section

noncomputable section

universe u

open Metric Module

namespace TauCeti

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : finrank ℝ E = 3 + 1)

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

/-- The loop coordinate of a free loop `f` in `S³` is the loop `t ↦ f(1)⁻¹ f(t)`, computed in the
unit quaternions. -/
@[simp]
theorem circleMapThreeSphereHomeomorphProd_apply_snd_apply (f : C(Circle, sphere (0 : E) 1))
    (t : unitInterval) :
    (circleMapThreeSphereHomeomorphProd hE f).2 t =
      (threeSphereHomeomorphUnitQuaternion hE).symm
        ((threeSphereHomeomorphUnitQuaternion hE (f 1))⁻¹ *
          threeSphereHomeomorphUnitQuaternion hE (f (unitToCircle t))) :=
  letI := threeSphereGroup hE
  letI := isTopologicalGroup_threeSphere hE
  (threeSphereHomeomorphUnitQuaternion hE).eq_symm_apply.2 <|
    (congrArg _ (circleMapGroupHomeomorphLoopSpace_symm_snd_apply f t)).trans <| by
      rw [threeSphereHomeomorphUnitQuaternion_mul, threeSphereHomeomorphUnitQuaternion_inv]

/-- The free loop in `S³` with sphere coordinate `g` and loop coordinate `γ` sends the image
`unitToCircle t` of a time `t` to the point corresponding to the quaternion product `g γ(t)`. -/
@[simp]
theorem circleMapThreeSphereHomeomorphProd_symm_apply_unitToCircle (g : sphere (0 : E) 1)
    (γ : Path (threeSphereOne hE) (threeSphereOne hE)) (t : unitInterval) :
    (circleMapThreeSphereHomeomorphProd hE).symm (g, γ) (unitToCircle t) =
      (threeSphereHomeomorphUnitQuaternion hE).symm
        (threeSphereHomeomorphUnitQuaternion hE g *
          threeSphereHomeomorphUnitQuaternion hE (γ t)) :=
  letI := threeSphereGroup hE
  letI := isTopologicalGroup_threeSphere hE
  (threeSphereHomeomorphUnitQuaternion hE).eq_symm_apply.2 <|
    (congrArg _ (circleMapGroupHomeomorphLoopSpace_apply_unitToCircle g γ t)).trans
      (threeSphereHomeomorphUnitQuaternion_mul hE g (γ t))

end TauCeti

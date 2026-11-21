/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Stiefel.UnitTangent
public import TauCeti.Topology.Algebra.Quaternion.SpecialOrthogonal

/-!
# The unit tangent bundle of the round two-sphere is `ℝP³`

A unit tangent vector `w` at a point `x` of the round sphere `S²` of `ℝ³` determines the rotation
with columns `x`, `dι w` and `x ⨯₃ dι w`, where `ι` is the inclusion of the sphere
(`TauCeti.sphereUnitTangentHomeomorphSpecialOrthogonalGroup`), and every rotation is conjugation
`v ↦ q * v * star q` by a unit quaternion `q`, determined up to sign
(`TauCeti.RealProjectiveSpace.homeomorphSpecialOrthogonalGroup`). Composing the two gives the
homeomorphism `UT(S²) ≃ₜ ℝP³` (`TauCeti.sphereUnitTangentHomeomorphRealProjectiveSpace`).

On representatives: the class of a unit vector `(a, b, c, d)` of `ℝ⁴`, the quaternion
`q = a + b i + c j + d k` up to sign, corresponds to the unit tangent vector at the point
`q * i * star q` of `S²` whose image under `dι` is `q * j * star q`, reading pure quaternions as
vectors of `ℝ³`. These are the first two columns of the rotation matrix
`Quaternion.rotationMatrix q`, and they do not change when `q` is replaced by `-q`. The class of
`(1, 0, 0, 0)` corresponds to the unit tangent vector at `(1, 0, 0)` pointing along `(0, 1, 0)`.

## Main definitions

* `TauCeti.sphereUnitTangentHomeomorphRealProjectiveSpace`: the homeomorphism `UT(S²) ≃ₜ ℝP³`.

## Main results

* `TauCeti.homeomorphSpecialOrthogonalGroup_sphereUnitTangentHomeomorphRealProjectiveSpace`: the
  rotation attached to the image of a unit tangent vector.
* `TauCeti.proj_sphereUnitTangentHomeomorphRealProjectiveSpace_symm_mk` and
  `TauCeti.mfderiv_sphereUnitTangentHomeomorphRealProjectiveSpace_symm_mk`: the unit tangent
  vector attached to the class of a unit vector of `ℝ⁴`.

## References

* J. Stillwell, *Naive Lie Theory*, Undergraduate Texts in Mathematics, Springer, 2008, §2.3.
-/

public section

open Bundle Matrix Metric WithLp Quaternion
open scoped Manifold

noncomputable section

namespace TauCeti

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

/-- **The unit tangent bundle of the round two-sphere is `ℝP³`.** A unit tangent vector `w` at a
point `x` of the round sphere `S²` of `ℝ³` goes to the class of the unit quaternions `±q` whose
conjugation is the rotation with columns `x`, `dι w` and `x ⨯₃ dι w`, where `ι` is the inclusion of
the sphere into `ℝ³`. -/
def sphereUnitTangentHomeomorphRealProjectiveSpace :
    {p : TangentBundle (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) | ‖p.2‖ = 1} ≃ₜ
      RealProjectiveSpace 3 :=
  sphereUnitTangentHomeomorphSpecialOrthogonalGroup.trans
    RealProjectiveSpace.homeomorphSpecialOrthogonalGroup.symm

/-- The point of `ℝP³` attached to a unit tangent vector `w` at `x` corresponds to the rotation with
columns `x`, `dι w` and `x ⨯₃ dι w`. -/
@[simp]
theorem homeomorphSpecialOrthogonalGroup_sphereUnitTangentHomeomorphRealProjectiveSpace
    (p : {p : TangentBundle (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) | ‖p.2‖ = 1}) :
    RealProjectiveSpace.homeomorphSpecialOrthogonalGroup
        (sphereUnitTangentHomeomorphRealProjectiveSpace p) =
      sphereUnitTangentHomeomorphSpecialOrthogonalGroup p := by
  rw [sphereUnitTangentHomeomorphRealProjectiveSpace, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply]

/-- The unit tangent vector attached to the class of a unit vector `x` of `ℝ⁴` lies over the
point `q * i * star q` of `S²`, the first column of the rotation by the quaternion `q` with
coordinates `x`. -/
@[simp]
theorem proj_sphereUnitTangentHomeomorphRealProjectiveSpace_symm_mk
    (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    ((sphereUnitTangentHomeomorphRealProjectiveSpace.symm (RealProjectiveSpace.mk 3 x)).1.proj :
        EuclideanSpace ℝ (Fin 3)) =
      toLp 2 ((rotationMatrix (linearIsometryEquivTuple.symm x)).col 0) := by
  rw [sphereUnitTangentHomeomorphRealProjectiveSpace, Homeomorph.symm_trans_apply,
    Homeomorph.symm_symm, RealProjectiveSpace.homeomorphSpecialOrthogonalGroup_mk,
    proj_sphereUnitTangentHomeomorphSpecialOrthogonalGroup_symm_apply,
    coe_unitaryToSpecialOrthogonalGroup_apply, coe_unitaryHomeomorphEuclideanSphere_symm_apply]

/-- The unit tangent vector attached to the class of a unit vector `x` of `ℝ⁴` is sent by the
differential of the inclusion to `q * j * star q`, the second column of the rotation by the
quaternion `q` with coordinates `x`. -/
@[simp]
theorem mfderiv_sphereUnitTangentHomeomorphRealProjectiveSpace_symm_mk
    (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    mfderiv (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        ((↑) : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
        (sphereUnitTangentHomeomorphRealProjectiveSpace.symm (RealProjectiveSpace.mk 3 x)).1.proj
        (sphereUnitTangentHomeomorphRealProjectiveSpace.symm (RealProjectiveSpace.mk 3 x)).1.2 =
      toLp 2 ((rotationMatrix (linearIsometryEquivTuple.symm x)).col 1) := by
  rw [sphereUnitTangentHomeomorphRealProjectiveSpace, Homeomorph.symm_trans_apply,
    Homeomorph.symm_symm, RealProjectiveSpace.homeomorphSpecialOrthogonalGroup_mk,
    mfderiv_sphereUnitTangentHomeomorphSpecialOrthogonalGroup_symm_apply,
    coe_unitaryToSpecialOrthogonalGroup_apply, coe_unitaryHomeomorphEuclideanSphere_symm_apply]

end TauCeti

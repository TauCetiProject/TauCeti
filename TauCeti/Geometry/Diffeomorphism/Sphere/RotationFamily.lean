/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PlaneRotation
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Degree.SphereRotation

/-!
# The rotation family of a sphere as a family of diffeomorphisms

Let `E` be a real inner product space with unit sphere `Sⁿ`, and fix `p ∈ Sⁿ`. A unit tangent
vector `v` of the sphere at `p`, that is a unit vector of `p^⊥ = (ℝ ∙ p)ᗮ`, spans with `p` an
oriented plane of `E`, the image of the linear isometry `w ↦ Re w • p + Im w • v` from `ℂ`
(`TauCeti.sphereRotationPlane`). A point `z` of the unit circle rotates this plane by the angle of
`z`, fixing its orthogonal complement (`LinearIsometry.planeRotation`). This gives a family of
rotations of `E`, parametrized by `Sⁿ⁻¹ × S¹` (`TauCeti.sphereRotationIsometry`),

`R (v, z) p = Re z • p + Im z • v`, `R (v, z) v = -Im z • p + Re z • v`,

and `R (v, z)` fixes every vector orthogonal to `p` and `v`. The rotations depend continuously on
`(v, z)` in the operator norm, so their restrictions to the sphere form a continuous family of
diffeomorphisms of `Sⁿ` for the weak Whitney topology (`TauCeti.sphereRotationDiff`). Evaluated at
`p`, this family is the rotation family `TauCeti.sphereRotationFamily p` of the sphere
(`TauCeti.evalAt_comp_sphereRotationDiff`).

The rotation family has degree `2` on odd-dimensional spheres
(`Orientation.degreeAtRegularValue_sphereRotationFamily_of_even`). Since it is the evaluation of a
family of diffeomorphisms, the image of the fundamental class of `Sⁿ⁻¹ × S¹` under that family is
a class of `H_n(Diff(Sⁿ); ℤ)` whose evaluation is the image of the fundamental class under the
rotation family. Once that image is identified with the degree times `[Sⁿ]`,
`TauCeti.HomologicalOrientation.IsCoveredByDiffeomorphisms.of_mapFundamentalClass` shows that odd
spheres are `2`-covered by diffeomorphisms. This is the direct proof of Barraud, Damian, Humilière
and Oancea, which needs no computation of homotopy groups of `SO(n)`.

## Main definitions

* `TauCeti.sphereRotationPlane p v`: the linear isometry `w ↦ Re w • p + Im w • v` from `ℂ` onto
  the plane spanned by `p` and `v`.
* `TauCeti.sphereRotationIsometry p (v, z)`: the rotation of `E` by the angle of `z` in that plane.
* `TauCeti.sphereRotationDiff p k`: the rotations as a continuous family of `C^k` diffeomorphisms
  of the sphere.

## Main results

* `TauCeti.sphereRotationIsometry_apply_self`, `TauCeti.sphereRotationIsometry_apply_tangent`,
  `TauCeti.sphereRotationIsometry_apply_of_inner_eq_zero`: the rotation on `p`, on `v`, and on
  vectors orthogonal to both.
* `TauCeti.continuous_sphereRotationIsometry`: the rotation depends continuously on `(v, z)`.
* `TauCeti.evalAt_comp_sphereRotationDiff`: evaluating the family of diffeomorphisms at `p` gives
  the rotation family of the sphere.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.3 (second proof of
  Proposition 6.34).
-/

public section

noncomputable section

open Metric Module
open scoped RealInnerProductSpace Manifold ContDiff TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **plane spanned by a point `p` of the sphere and a unit tangent vector `v` at `p`**, as the
linear isometry `w ↦ Re w • p + Im w • v` from `ℂ`. It sends `1` to `p` and `i` to `v`. -/
def sphereRotationPlane (p : sphere (0 : E) 1) (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    ℂ →ₗᵢ[ℝ] E where
  toLinearMap := (Complex.reCLM.smulRight (p : E) +
    Complex.imCLM.smulRight ((v : (ℝ ∙ (p : E))ᗮ) : E)).toLinearMap
  norm_map' w := by
    -- `p` and `v` are orthonormal, and `Re w ^ 2 + Im w ^ 2 = ‖w‖ ^ 2`.
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    have hv : ‖((v : (ℝ ∙ (p : E))ᗮ) : E)‖ = 1 := norm_eq_of_mem_sphere v
    have hpv : ⟪(p : E), ((v : (ℝ ∙ (p : E))ᗮ) : E)⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 (v : (ℝ ∙ (p : E))ᗮ).2
    simp [norm_add_sq_real, norm_smul, real_inner_smul_left, real_inner_smul_right, hpv, hv,
      Complex.sq_norm, Complex.normSq_apply]
    ring

@[simp]
theorem sphereRotationPlane_apply (p : sphere (0 : E) 1) (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)
    (w : ℂ) : sphereRotationPlane p v w = w.re • (p : E) + w.im • ((v : (ℝ ∙ (p : E))ᗮ) : E) :=
  (rfl)

/-- The plane spanned by `p` and `v` depends continuously on `v`, in the operator norm. -/
theorem continuous_sphereRotationPlane (p : sphere (0 : E) 1) :
    Continuous fun v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 ↦
      (sphereRotationPlane p v).toContinuousLinearMap := by
  have hv : Continuous fun v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 ↦ ((v : (ℝ ∙ (p : E))ᗮ) : E) :=
    continuous_subtype_val.comp continuous_subtype_val
  refine ((continuous_const (y := Complex.reCLM.smulRight (p : E))).add
    ((ContinuousLinearMap.smulRightL ℝ ℂ E Complex.imCLM).continuous.comp hv)).congr fun v ↦ ?_
  ext w
  simp

/-- The **rotation of `E` by the angle of `z` in the plane spanned by `p` and `v`**, for a point
`p` of the unit sphere, a unit tangent vector `v` at `p` and a point `z` of the unit circle of `ℂ`.
It sends `p` to `Re z • p + Im z • v` and `v` to `-Im z • p + Re z • v`, and fixes the vectors
orthogonal to `p` and `v`. -/
def sphereRotationIsometry (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) : E ≃ₗᵢ[ℝ] E :=
  (sphereRotationPlane p x.1).planeRotation ⟨x.2, x.2.2⟩

/-- **The rotation moves `p` along the great circle in the direction `v`**: it sends `p` to
`Re z • p + Im z • v`, the value of the rotation family of the sphere at `(v, z)`. -/
@[simp]
theorem sphereRotationIsometry_apply_self (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    sphereRotationIsometry p x p = sphereRotationFamily p x := by
  simpa [sphereRotationIsometry] using
    (sphereRotationPlane p x.1).planeRotation_apply_map ⟨x.2, x.2.2⟩ 1

/-- The rotation sends the tangent vector `v` to `-Im z • p + Re z • v`. -/
@[simp]
theorem sphereRotationIsometry_apply_tangent (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    sphereRotationIsometry p x ((x.1 : (ℝ ∙ (p : E))ᗮ) : E) =
      -(x.2 : ℂ).im • (p : E) + (x.2 : ℂ).re • ((x.1 : (ℝ ∙ (p : E))ᗮ) : E) := by
  simpa [sphereRotationIsometry] using
    (sphereRotationPlane p x.1).planeRotation_apply_map ⟨x.2, x.2.2⟩ Complex.I

/-- The rotation fixes the vectors orthogonal to `p` and to `v`. -/
theorem sphereRotationIsometry_apply_of_inner_eq_zero (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) {y : E} (hp : ⟪(p : E), y⟫ = 0)
    (hv : ⟪((x.1 : (ℝ ∙ (p : E))ᗮ) : E), y⟫ = 0) : sphereRotationIsometry p x y = y := by
  refine LinearIsometry.planeRotation_apply_of_mem_orthogonal _ _ ?_
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨w, rfl⟩
  simp [inner_add_left, real_inner_smul_left, hp, hv]

/-- **The rotations depend continuously on the tangent vector and the angle**, in the operator
norm. -/
theorem continuous_sphereRotationIsometry (p : sphere (0 : E) 1) :
    Continuous fun x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦
      ((sphereRotationIsometry p x).toContinuousLinearEquiv : E →L[ℝ] E) :=
  ((continuous_sphereRotationPlane p).comp continuous_fst).planeRotation
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

variable [FiniteDimensional ℝ E] {m : ℕ} [Fact (finrank ℝ E = m + 1 + 1)]

/-- **The rotation family of the sphere as a family of diffeomorphisms**: the restrictions to the
unit sphere `Sᵐ⁺¹` of the rotations `TauCeti.sphereRotationIsometry p (v, z)`, as a continuous map
from `Sᵐ × S¹` to the group of `C^k` diffeomorphisms of `Sᵐ⁺¹` with the weak Whitney topology. Its
evaluation at `p` is the rotation family `TauCeti.sphereRotationFamily p`
(`TauCeti.evalAt_comp_sphereRotationDiff`). -/
def sphereRotationDiff (p : sphere (0 : E) 1) (k : ℕ∞ω) :
    C(sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1, Diff (𝓡 (m + 1)) (sphere (0 : E) 1) k) where
  toFun x := LinearIsometryEquiv.unitSphereDiffHom k (sphereRotationIsometry p x)
  continuous_toFun := by
    refine Diffeomorph.continuous_weakWhitney_iff.mpr ?_
    simpa only [LinearIsometryEquiv.unitSphereDiffHom_apply] using
      (continuous_sphereRotationIsometry p).toContMDiffMap_unitSphereDiffeomorph

@[simp]
theorem coe_sphereRotationDiff_apply (p : sphere (0 : E) 1) (k : ℕ∞ω)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) (y : sphere (0 : E) 1) :
    (sphereRotationDiff (m := m) p k x y : E) = sphereRotationIsometry p x y := by
  simp [sphereRotationDiff]

/-- **Evaluating the rotations at `p` gives the rotation family of the sphere.** -/
theorem evalAt_comp_sphereRotationDiff (p : sphere (0 : E) 1) (k : ℕ∞ω) :
    (Diffeomorph.evalAt p).comp (sphereRotationDiff (m := m) p k) =
      ⟨sphereRotationFamily p, (contMDiff_sphereRotationFamily (m := m) p).continuous⟩ := by
  ext x : 2
  simp

end TauCeti

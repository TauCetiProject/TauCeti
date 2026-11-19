/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PlaneRotation
public import TauCeti.Geometry.Diffeomorphism.Covered
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Degree.Homological
public import TauCeti.Geometry.Manifold.Degree.SphereRotation
public import TauCeti.Geometry.Manifold.IsManifold.Prod
public import TauCeti.Topology.Grassmannian.SphereBundle.Action
import TauCeti.Geometry.Sphere.Connected
import TauCeti.Geometry.Sphere.Equator
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic

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
rotation family, and that image is the degree times `[Sⁿ]`
(`TauCeti.Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul`). So odd spheres
are `2`-covered by diffeomorphisms, at every base point and for every orientation
(`TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_two_of_even`). This is the direct
proof of Barraud, Damian, Humilière and Oancea, which needs no computation of homotopy groups of
`SO(n)`.

For `E = ℝᴺ` the rotations are special orthogonal matrices. They form a continuous family
`Sᴺ⁻² × S¹ → SO(N)` (`TauCeti.sphereRotationMatrix`) whose orbit map at `p` is the rotation family
(`TauCeti.sphereRotationMatrix_smul_self`), so the rotation family factors through the orbit map
`SO(N) → Sᴺ⁻¹` of `p`.

More generally the rotation family has degree `1 + (-1) ^ (n - 1)` on `Sⁿ`, so the fundamental
class of `Sⁿ⁻¹ × S¹` is sent to `(1 + (-1) ^ (n - 1)) • [Sⁿ]`
(`Orientation.mapFundamentalClass_sphereRotationFamily`) and `Sⁿ` is `(1 + (-1) ^ (n - 1))`-covered
(`TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_one_add_neg_one_pow`). The
comparison of the smooth and homological degrees is applied directly with the product model of
`Sⁿ⁻¹ × S¹` on `ℝⁿ⁻¹ × ℝ`, which differs from the model `ℝⁿ` of `Sⁿ`.

## Main definitions

* `TauCeti.sphereRotationPlane p v`: the linear isometry `w ↦ Re w • p + Im w • v` from `ℂ` onto
  the plane spanned by `p` and `v`.
* `TauCeti.sphereRotationIsometry p (v, z)`: the rotation of `E` by the angle of `z` in that plane.
* `TauCeti.sphereRotationDiff p k`: the rotations as a continuous family of `C^k` diffeomorphisms
  of the sphere.
* `TauCeti.sphereRotationMatrix p`: for `E = ℝᴺ`, the rotations as a continuous family of
  special orthogonal matrices.

## Main results

* `TauCeti.sphereRotationIsometry_apply_self`, `TauCeti.sphereRotationIsometry_apply_tangent`,
  `TauCeti.sphereRotationIsometry_apply_of_inner_eq_zero`: the rotation on `p`, on `v`, and on
  vectors orthogonal to both.
* `TauCeti.continuous_sphereRotationIsometry`: the rotation depends continuously on `(v, z)`.
* `TauCeti.evalAt_comp_sphereRotationDiff`: evaluating the family of diffeomorphisms at `p` gives
  the rotation family of the sphere.
* `TauCeti.sphereRotationMatrix_smul_self`: the matrices act on `p` by the rotation family.
* `Orientation.mapFundamentalClass_sphereRotationFamily`: the rotation family sends `[Sᵐ × S¹]` to
  `(1 + (-1) ^ m) • [Sᵐ⁺¹]`.
* `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_one_add_neg_one_pow`: `Sᵐ⁺¹`
  is `(1 + (-1) ^ m)`-covered by diffeomorphisms.
* `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_two_of_even`,
  `TauCeti.HomologicalOrientation.exists_isCoveredByDiffeomorphisms_sphere_of_even`: odd spheres
  are `2`-covered by diffeomorphisms (the second proof of Proposition 6.34 of
  Barraud–Damian–Humilière–Oancea).

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

theorem sphereRotationIsometry_def (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    sphereRotationIsometry p x = (sphereRotationPlane p x.1).planeRotation ⟨x.2, x.2.2⟩ :=
  (rfl)

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

variable [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- **The rotation family of the sphere as a family of diffeomorphisms**: the restrictions to the
unit sphere `Sⁿ` of the rotations `TauCeti.sphereRotationIsometry p (v, z)`, as a continuous map
from `Sⁿ⁻¹ × S¹` to the group of `C^k` diffeomorphisms of `Sⁿ` with the weak Whitney topology. Its
evaluation at `p` is the rotation family `TauCeti.sphereRotationFamily p`
(`TauCeti.evalAt_comp_sphereRotationDiff`). -/
def sphereRotationDiff (p : sphere (0 : E) 1) (k : ℕ∞ω) :
    C(sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1, Diff (𝓡 n) (sphere (0 : E) 1) k) where
  toFun x := LinearIsometryEquiv.unitSphereDiffHom k (sphereRotationIsometry p x)
  continuous_toFun := by
    refine Diffeomorph.continuous_weakWhitney_iff.mpr ?_
    simpa only [LinearIsometryEquiv.unitSphereDiffHom_apply] using
      (continuous_sphereRotationIsometry p).toContMDiffMap_unitSphereDiffeomorph

theorem sphereRotationDiff_apply (p : sphere (0 : E) 1) (k : ℕ∞ω)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    sphereRotationDiff (n := n) p k x =
      LinearIsometryEquiv.unitSphereDiffHom k (sphereRotationIsometry p x) :=
  (rfl)

@[simp]
theorem coe_sphereRotationDiff_apply (p : sphere (0 : E) 1) (k : ℕ∞ω)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) (y : sphere (0 : E) 1) :
    (sphereRotationDiff (n := n) p k x y : E) = sphereRotationIsometry p x y := by
  simp [sphereRotationDiff]

/-- The rotations send `p` to the value of the rotation family of the sphere. -/
@[simp]
theorem sphereRotationDiff_apply_self (p : sphere (0 : E) 1) (k : ℕ∞ω)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    sphereRotationDiff (n := n) p k x p = sphereRotationFamily p x :=
  Subtype.ext (by simp)

/-- **Evaluating the rotations at `p` gives the rotation family of the sphere.** -/
theorem evalAt_comp_sphereRotationDiff (p : sphere (0 : E) 1) (k : ℕ∞ω) :
    (Diffeomorph.evalAt p).comp (sphereRotationDiff (n := n) p k) =
      ⟨sphereRotationFamily p, continuous_sphereRotationFamily p⟩ := by
  ext x : 2
  simp

/-! ### The rotations as special orthogonal matrices -/

section Matrix

open _root_.Matrix

variable {N : ℕ}

/-- The matrix of the rotation `TauCeti.sphereRotationIsometry p x` of `ℝᴺ`, an orthogonal
matrix. -/
private def sphereRotationOrthogonal (p : sphere (0 : EuclideanSpace ℝ (Fin N)) 1)
    (x : sphere (0 : (ℝ ∙ (p : EuclideanSpace ℝ (Fin N)))ᗮ) 1 × sphere (0 : ℂ) 1) :
    unitaryGroup (Fin N) ℝ :=
  ⟨LinearMap.toMatrix (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (sphereRotationIsometry p x).toLinearEquiv,
    (sphereRotationIsometry p x).toMatrix_mem_unitaryGroup _ _⟩

private theorem toLinearIsometryEquiv_sphereRotationOrthogonal
    (p : sphere (0 : EuclideanSpace ℝ (Fin N)) 1)
    (x : sphere (0 : (ℝ ∙ (p : EuclideanSpace ℝ (Fin N)))ᗮ) 1 × sphere (0 : ℂ) 1) :
    UnitaryGroup.toLinearIsometryEquiv (sphereRotationOrthogonal p x) =
      sphereRotationIsometry p x := by
  ext y i
  have h := congrFun (LinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
    ((sphereRotationIsometry p x).toLinearEquiv : _ →ₗ[ℝ] _) y) i
  have hrepr : ⇑((EuclideanSpace.basisFun (Fin N) ℝ).toBasis.repr y) = y.ofLp := by
    ext j
    simp
  rw [hrepr] at h
  simpa [sphereRotationOrthogonal] using h

private theorem continuous_sphereRotationOrthogonal
    (p : sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    Continuous (sphereRotationOrthogonal p) := by
  refine Continuous.subtype_mk (continuous_matrix fun i j ↦ ?_) _
  have h := (PiLp.continuous_apply 2 (fun _ : Fin N ↦ ℝ) i).comp
    ((continuous_sphereRotationIsometry p).clm_apply
      (continuous_const (y := EuclideanSpace.single j (1 : ℝ))))
  simpa [sphereRotationOrthogonal, LinearMap.toMatrix_apply, Function.comp_def] using h

/-- The rotations have determinant one: along the circle of angles the determinant is continuous
with values `±1`, and at the angle `0` the rotation is the identity. -/
private theorem det_sphereRotationOrthogonal (p : sphere (0 : EuclideanSpace ℝ (Fin N)) 1)
    (x : sphere (0 : (ℝ ∙ (p : EuclideanSpace ℝ (Fin N)))ᗮ) 1 × sphere (0 : ℂ) 1) :
    (sphereRotationOrthogonal p x : Matrix (Fin N) (Fin N) ℝ).det = 1 := by
  let f : sphere (0 : ℂ) 1 → ℝ := fun z ↦ (sphereRotationOrthogonal p (x.1, z) :
    Matrix (Fin N) (Fin N) ℝ).det
  have hf : Continuous f :=
    (continuous_subtype_val.comp ((continuous_sphereRotationOrthogonal p).comp
      (continuous_const.prodMk continuous_id))).matrix_det
  have hpm (z : sphere (0 : ℂ) 1) : f z = 1 ∨ f z = -1 :=
    det_eq_one_or_neg_one_of_mem_orthogonalGroup (sphereRotationOrthogonal p (x.1, z)).2
  have h1 : f 1 = 1 := by
    have : sphereRotationOrthogonal p (x.1, 1) = 1 := UnitaryGroup.toLinearIsometryEquiv_injective
      (by
        rw [toLinearIsometryEquiv_sphereRotationOrthogonal, map_one, sphereRotationIsometry_def]
        -- The angle `1` of the unit circle is the unit of `Circle`.
        exact map_one _)
    simp [f, this]
  have := connectedSpace_sphere (E := ℂ) 1
  refine (hpm x.2).resolve_right fun hx ↦ ?_
  -- Otherwise the determinant would vanish at some angle.
  obtain ⟨z, -, hz⟩ := isPreconnected_univ.intermediate_value (Set.mem_univ x.2) (Set.mem_univ 1)
    hf.continuousOn (show (0 : ℝ) ∈ Set.Icc (f x.2) (f 1) by rw [hx, h1]; norm_num)
  rcases hpm z with h | h <;> rw [hz] at h <;> norm_num at h

/-- **The rotations of `ℝᴺ` in the planes through `p` as special orthogonal matrices**: the matrix
of the rotation `TauCeti.sphereRotationIsometry p (v, z)` by the angle of `z` in the plane spanned
by `p` and `v`, as a continuous map `Sᴺ⁻² × S¹ → SO(N)`. It acts on `p` by the rotation family of
the sphere (`TauCeti.sphereRotationMatrix_smul_self`). -/
def sphereRotationMatrix (p : sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    C(sphere (0 : (ℝ ∙ (p : EuclideanSpace ℝ (Fin N)))ᗮ) 1 × sphere (0 : ℂ) 1,
      specialOrthogonalGroup (Fin N) ℝ) where
  toFun x := ⟨sphereRotationOrthogonal p x,
    mem_specialOrthogonalGroup_iff.2 ⟨(sphereRotationOrthogonal p x).2,
      det_sphereRotationOrthogonal p x⟩⟩
  continuous_toFun :=
    (continuous_subtype_val.comp (continuous_sphereRotationOrthogonal p)).subtype_mk _

private theorem coe_sphereRotationMatrix_apply (p : sphere (0 : EuclideanSpace ℝ (Fin N)) 1)
    (x : sphere (0 : (ℝ ∙ (p : EuclideanSpace ℝ (Fin N)))ᗮ) 1 × sphere (0 : ℂ) 1) :
    (sphereRotationMatrix p x : Matrix (Fin N) (Fin N) ℝ) = sphereRotationOrthogonal p x :=
  (rfl)

/-- The matrix `TauCeti.sphereRotationMatrix p x` acts on the unit sphere as the rotation
`TauCeti.sphereRotationIsometry p x`. -/
theorem sphereRotationMatrix_smul (p : sphere (0 : EuclideanSpace ℝ (Fin N)) 1)
    (x : sphere (0 : (ℝ ∙ (p : EuclideanSpace ℝ (Fin N)))ᗮ) 1 × sphere (0 : ℂ) 1)
    (y : sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    sphereRotationMatrix p x • y = sphereRotationIsometry p x • y :=
  Subtype.ext <| by
    rw [SpecialOrthogonalGroup.coe_smul_sphere, LinearIsometryEquiv.coe_smul_unitSphere,
      ← toLinearIsometryEquiv_sphereRotationOrthogonal, UnitaryGroup.toLinearIsometryEquiv_apply,
      coe_sphereRotationMatrix_apply]

/-- **The matrices act on `p` by the rotation family of the sphere.** -/
@[simp]
theorem sphereRotationMatrix_smul_self (p : sphere (0 : EuclideanSpace ℝ (Fin N)) 1)
    (x : sphere (0 : (ℝ ∙ (p : EuclideanSpace ℝ (Fin N)))ᗮ) 1 × sphere (0 : ℂ) 1) :
    sphereRotationMatrix p x • p = sphereRotationFamily p x :=
  Subtype.ext <| by
    rw [sphereRotationMatrix_smul, LinearIsometryEquiv.coe_smul_unitSphere,
      sphereRotationIsometry_apply_self]

end Matrix

/-! ### Odd spheres are covered by rotations -/

section Covering

attribute [local instance low] chartedSpaceProd

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {m : ℕ}
  [Fact (finrank ℝ F = m + 1 + 1)]

/-- Pushing forward the product fundamental class of `Sᵐ × S¹` along `sphereRotationFamily p`
yields `(1 + (-1) ^ m)` times the fundamental class of `Sᵐ⁺¹`. -/
theorem _root_.Orientation.mapFundamentalClass_sphereRotationFamily
    (oF : Orientation ℝ F (Fin (m + 1 + 1))) (p : sphere (0 : F) 1)
    (hdim : finrank ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 1)) = m + 1 := by
      rw [finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]) :
    (((oF.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere p)).sphereOrientation.prod
        Complex.orientation.sphereOrientation).toHomologicalOrientation
        hdim).mapFundamentalClass hdim
      ⟨sphereRotationFamily p, continuous_sphereRotationFamily p⟩ =
    (1 + (-1) ^ m) •
      (oF.sphereOrientation.toHomologicalOrientation finrank_euclideanSpace_fin).fundamentalClass
        finrank_euclideanSpace_fin := by
  have := connectedSpace_sphere (E := F) (m + 1)
  obtain ⟨q, hqp, hqp'⟩ := exists_ne_and_ne_neg_sphere
    (by rw [Fact.out (p := finrank ℝ F = m + 1 + 1)]; omega) p
  refine (Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul hdim
    finrank_euclideanSpace_fin _ oF.sphereOrientation
    (isRegularValue_sphereRotationFamily p hqp hqp')).trans ?_
  rw [ContinuousMap.coe_mk, oF.degreeAtRegularValue_sphereRotationFamily p hqp hqp']
  -- `mapFundamentalClass` and `fundamentalClass` have definitionally equal carrier types
  -- (`singularHomologyFunctor` vs `SSet.homology`).
  rfl

namespace HomologicalOrientation

/-- **Spheres covered by rotations.** The unit sphere `Sᵐ⁺¹` of an `(m + 2)`-dimensional real inner
product space is `(1 + (-1) ^ m)`-covered by `C^k` diffeomorphisms at every base point, for every
orientation and every smoothness exponent `k`: the rotations of `Sᵐ⁺¹` parametrized by `Sᵐ × S¹`
push the fundamental class of `Sᵐ × S¹` to a class of `H_{m + 1}(Diff(Sᵐ⁺¹); ℤ)` evaluating to
`(1 + (-1) ^ m) • [Sᵐ⁺¹]`, since their evaluation at the base point is the rotation family. -/
theorem isCoveredByDiffeomorphisms_sphere_one_add_neg_one_pow
    (o : HomologicalOrientation (sphere (0 : F) 1) (EuclideanSpace ℝ (Fin (m + 1))) (m + 1))
    (k : ℕ∞ω) (x₀ : sphere (0 : F) 1) :
    o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ (1 + (-1) ^ m) := by
  have := connectedSpace_sphere (E := F) (m + 1)
  -- Every orientation is the outward-normal orientation up to sign.
  let oF : Orientation ℝ F (Fin (m + 1 + 1)) :=
    (finBasisOfFinrankEq ℝ F (Fact.out : finrank ℝ F = m + 1 + 1)).orientation
  let o₀ := oF.sphereOrientation.toHomologicalOrientation finrank_euclideanSpace_fin
  refine (isCoveredByDiffeomorphisms_iff_of_preconnectedSpace o₀ o).1 ?_
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 1)) = m + 1 := by
    rw [finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
  refine .of_mapFundamentalClass
    (((oF.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere x₀)).sphereOrientation.prod
      Complex.orientation.sphereOrientation).toHomologicalOrientation hdim)
    hdim (sphereRotationDiff (n := m + 1) x₀ k) ?_
  rw [evalAt_comp_sphereRotationDiff, o₀.mapFundamentalClass_id]
  exact oF.mapFundamentalClass_sphereRotationFamily x₀ hdim

/-- **Odd spheres are `2`-covered by diffeomorphisms** (the second proof of Proposition 6.34 of
Barraud–Damian–Humilière–Oancea). For even `m`, the odd-dimensional sphere `Sᵐ⁺¹` is `2`-covered by
diffeomorphisms, at every base point, for every orientation and every smoothness exponent. -/
theorem isCoveredByDiffeomorphisms_sphere_two_of_even
    (o : HomologicalOrientation (sphere (0 : F) 1) (EuclideanSpace ℝ (Fin (m + 1))) (m + 1))
    (hm : Even m) (k : ℕ∞ω) (x₀ : sphere (0 : F) 1) :
    o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ 2 := by
  have h := o.isCoveredByDiffeomorphisms_sphere_one_add_neg_one_pow k x₀
  rwa [hm.neg_one_pow, one_add_one_eq_two] at h

/-- **Odd spheres are `ℓ`-covered by diffeomorphisms for some `ℓ > 0`**, without any torsion
hypothesis on homotopy groups of orthogonal groups. -/
theorem exists_isCoveredByDiffeomorphisms_sphere_of_even
    (o : HomologicalOrientation (sphere (0 : F) 1) (EuclideanSpace ℝ (Fin (m + 1))) (m + 1))
    (hm : Even m) (k : ℕ∞ω) (x₀ : sphere (0 : F) 1) :
    ∃ ℓ : ℤ, 0 < ℓ ∧ o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ ℓ :=
  ⟨2, two_pos, o.isCoveredByDiffeomorphisms_sphere_two_of_even hm k x₀⟩

end HomologicalOrientation

end Covering

end TauCeti

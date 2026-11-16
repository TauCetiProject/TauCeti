/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PlaneRotation
public import TauCeti.Geometry.Diffeomorphism.Covered
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Degree.SphereRotation
import TauCeti.Geometry.Manifold.Degree.Homological
import TauCeti.Geometry.Manifold.ModelTransport.Boundaryless
import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.LinearEquiv
import TauCeti.Geometry.Manifold.Orientation.Pullback
import TauCeti.Geometry.Sphere.Connected
import TauCeti.Geometry.Sphere.Equator

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

The comparison of the smooth and homological degrees is stated for manifolds charted in one inner
product space, while `Sⁿ⁻¹ × S¹` carries the product model on `ℝⁿ⁻¹ × ℝ`. The proof therefore
reads `Sⁿ⁻¹ × S¹` through a copy charted in `ℝⁿ` (`TauCeti.BoundarylessModel`), after a linear
identification `ℝⁿ⁻¹ × ℝ ≃ ℝⁿ`, with the orientation pulled back along the identity, which does not
change the degree (`TauCeti.degreeAtRegularValue_comp_of_bijective`).

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
* `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_two_of_even`: odd spheres are
  `2`-covered by diffeomorphisms (the second proof of Proposition 6.34 of
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

/-! ### Odd spheres are covered by rotations -/

namespace HomologicalOrientation

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {m : ℕ}
  [Fact (finrank ℝ F = m + 1 + 1)]

/-- The statement of `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_two_of_even`
for the outward-normal orientation of the sphere, based at the point `p` of the rotation family. -/
private theorem isCoveredByDiffeomorphisms_sphereOrientation_two
    (o : Orientation ℝ F (Fin (m + 1 + 1))) (hm : Even m) (k : ℕ∞ω) (p : sphere (0 : F) 1) :
    (o.sphereOrientation.toHomologicalOrientation
      finrank_euclideanSpace_fin).IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k p 2 := by
  have := connectedSpace_sphere (E := F) (m + 1)
  -- A copy `P'` of `P = Sᵐ × S¹` charted in `ℝᵐ⁺¹`, and the identity `ι : P' → P`.
  let L : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (m + 1)) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  let J := ((𝓡 m).prod (𝓡 1)).transContinuousLinearEquiv L
  let P := sphere (0 : (ℝ ∙ (p : F))ᗮ) 1 × sphere (0 : ℂ) 1
  let _ : CompactSpace (BoundarylessModel J P) := (BoundarylessModel.homeomorph J P).compactSpace
  let _ : T2Space (BoundarylessModel J P) := (BoundarylessModel.homeomorph J P).t2Space
  let ι : BoundarylessModel J P ≃ₘ^∞⟮𝓡 (m + 1), (𝓡 m).prod (𝓡 1)⟯ P :=
    ((ContinuousLinearEquiv.toTransContinuousLinearEquiv ((𝓡 m).prod (𝓡 1)) P L).trans
      (BoundarylessModel.diffeomorph J ∞)).symm
  have hι (x) : (mfderiv (𝓡 (m + 1)) ((𝓡 m).prod (𝓡 1)) ι x).IsInvertible :=
    ι.isInvertible_mfderiv (by simp)
  -- The product orientation of `P`, pulled back to `P'`.
  let oP := (o.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere p)).sphereOrientation.prod
    Complex.orientation.sphereOrientation
  let oP' := oP.pullback (ι.contMDiff.of_le (by simp)) hι (by simp)
  -- Read on `P'`, the rotation family still has degree `2` at a point `q ≠ ±p`, a regular value.
  let f : P → sphere (0 : F) 1 := sphereRotationFamily p
  have hf : ContMDiff ((𝓡 m).prod (𝓡 1)) (𝓡 (m + 1)) ∞ f := contMDiff_sphereRotationFamily p
  obtain ⟨q, hqp, hqp'⟩ := exists_ne_and_ne_neg_sphere
    (by rw [Fact.out (p := finrank ℝ F = m + 1 + 1)]; omega) p
  have hreg : IsRegularValue (𝓡 (m + 1)) (𝓡 (m + 1)) (f ∘ ι) q :=
    isRegularValue_iff.2 fun x hx ↦
      ((isRegularValue_sphereRotationFamily p hqp hqp').isRegularPoint hx).comp
        (isRegularPoint_iff.2 (hι x).surjective)
  -- Stated for the composite of continuous maps that the rotations evaluate to below.
  have key := Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul
    finrank_euclideanSpace_fin oP' o.sphereOrientation
    (f := (⟨sphereRotationFamily p, continuous_sphereRotationFamily p⟩ :
      C(P, sphere (0 : F) 1)).comp ⟨ι, ι.continuous⟩)
    (by rwa [ContinuousMap.coe_comp, ContinuousMap.coe_mk, ContinuousMap.coe_mk])
  rw [ContinuousMap.coe_comp, ContinuousMap.coe_mk, ContinuousMap.coe_mk,
    degreeAtRegularValue_comp_of_bijective (e := ι)
    ι.toHomeomorph.bijective (oP.isOrientationPreservingAt_pullback _ hι _)
    (hf.mdifferentiable (by simp)), o.degreeAtRegularValue_sphereRotationFamily_of_even p hm hqp
    hqp'] at key
  -- The rotations, composed with `ι`, are a family of diffeomorphisms evaluating to `f ∘ ι`.
  refine .of_mapFundamentalClass (oP'.toHomologicalOrientation finrank_euclideanSpace_fin)
    finrank_euclideanSpace_fin ((sphereRotationDiff p k).comp ⟨ι, ι.continuous⟩) ?_
  rw [← ContinuousMap.comp_assoc, evalAt_comp_sphereRotationDiff, mapFundamentalClass_id]
  exact key

/-- **Odd spheres are `2`-covered by diffeomorphisms** (the second proof of Proposition 6.34 of
Barraud–Damian–Humilière–Oancea). For even `m`, the odd-dimensional sphere `Sᵐ⁺¹` is `2`-covered by
diffeomorphisms, at every base point, for every orientation and every smoothness exponent: the
rotations of `Sᵐ⁺¹` parametrized by `Sᵐ × S¹` push the fundamental class of `Sᵐ × S¹` to a class of
`H_{m + 1}(Diff(Sᵐ⁺¹); ℤ)` evaluating to `2 • [Sᵐ⁺¹]`, since their evaluation at the base point is
the rotation family, of degree `2`. -/
theorem isCoveredByDiffeomorphisms_sphere_two_of_even
    (o : HomologicalOrientation (sphere (0 : F) 1) (EuclideanSpace ℝ (Fin (m + 1))) (m + 1))
    (hm : Even m) (k : ℕ∞ω) (x₀ : sphere (0 : F) 1) :
    o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ 2 := by
  have := connectedSpace_sphere (E := F) (m + 1)
  -- Every orientation is the outward-normal orientation up to sign.
  let o₀ : Orientation ℝ F (Fin (m + 1 + 1)) :=
    (finBasisOfFinrankEq ℝ F (Fact.out : finrank ℝ F = m + 1 + 1)).orientation
  rcases eq_or_eq_neg finrank_euclideanSpace_fin
    (o₀.sphereOrientation.toHomologicalOrientation finrank_euclideanSpace_fin) o with rfl | rfl
  · exact isCoveredByDiffeomorphisms_sphereOrientation_two o₀ hm k x₀
  · exact isCoveredByDiffeomorphisms_neg.2
      (isCoveredByDiffeomorphisms_sphereOrientation_two o₀ hm k x₀)

end HomologicalOrientation

end TauCeti

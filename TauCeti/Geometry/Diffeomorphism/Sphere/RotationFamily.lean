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
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import TauCeti.Analysis.Complex.Circle
import TauCeti.Geometry.Diffeomorphism.Degree
import TauCeti.Geometry.Sphere.Connected

/-!
# The rotation family of a sphere as a family of diffeomorphisms, and `2`-covering of odd spheres

Let `E` be a real inner product space with unit sphere `Sⁿ`, and fix `p ∈ Sⁿ`. A unit tangent
vector `v` of the sphere at `p`, that is a unit vector of `p^⊥ = (ℝ ∙ p)ᗮ`, spans with `p` an
oriented plane of `E`, the image of the linear isometry `w ↦ Re w • p + Im w • v` from `ℂ`
(`TauCeti.sphereRotationPlane`). A point `z` of the unit circle rotates this plane by the angle of
`z`, fixing its orthogonal complement (`LinearIsometry.planeRotation`). This gives a family of
rotations of `E`, parametrized by `Sⁿ⁻¹ × S¹` (`TauCeti.sphereRotationIsometry`),

`R (v, z) p = Re z • p + Im z • v`, `R (v, z) v = -Im z • p + Re z • v`,

and `R (v, z)` fixes every vector orthogonal to `p` and `v`. The rotations depend continuously on
`(v, z)` in the operator norm, so their restrictions to the sphere form a continuous family of
diffeomorphisms of `Sⁿ` for the weak Whitney topology (`TauCeti.sphereRotationDiff`), landing in the
identity path component of `Diff^k(Sⁿ)` (`TauCeti.joined_one_sphereRotationDiff`). Evaluated at `p`,
this family is the rotation family `TauCeti.sphereRotationFamily p` of the sphere
(`TauCeti.sphereRotationDiff_apply_self`, `TauCeti.evalAt_comp_sphereRotationDiff`).

Combining this lift with
`TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_degreeAtRegularValue` and the degree
computation `Orientation.degreeAtRegularValue_sphereRotationFamily` (`1 + (-1)ⁿ⁻¹`, equal to `2`
when `n` is odd) formalizes the covering step in the second, homotopy-group-free proof of
Proposition 6.34 of Barraud–Damian–Humilière–Oancea (whose conclusion is abundance with `2`-spheres
for odd `n ≥ 3` via Proposition 6.33): every odd-dimensional sphere `Sⁿ` (including `S¹`, `S³`,
`S⁵`, …) is `2`-covered by `C^k` diffeomorphisms at every base point, for every homological
orientation and every smoothness `k : ℕ∞ω`
(`TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_of_odd`,
`TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_euclideanSphere_of_odd`), without
assuming that `π_{n-1}(SO(n))` is torsion.

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
* `TauCeti.sphereRotationDiff_apply_self`, `TauCeti.evalAt_comp_sphereRotationDiff`: evaluating the
  family of diffeomorphisms at `p` (pointwise or via `Diffeomorph.evalAt p`) gives the rotation
  family of the sphere.
* `TauCeti.joined_one_sphereRotationDiff`: every diffeomorphism in the family lies in the identity
  path component of `Diff^k(Sⁿ)`.
* `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_one_add_neg_one_pow`: `Sᵐ⁺¹` is
  `(1 + (-1) ^ m)`-covered by `C^k` diffeomorphisms.
* `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_of_odd`,
  `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_euclideanSphere_of_odd`: every
  odd-dimensional sphere `Sⁿ` is `2`-covered by `C^k` diffeomorphisms.
* `TauCeti.HomologicalOrientation.exists_isCoveredByDiffeomorphisms_sphere_of_odd`,
  `TauCeti.HomologicalOrientation.exists_isCoveredByDiffeomorphisms_euclideanSphere_of_odd`: every
  odd-dimensional sphere `Sⁿ` is `ℓ`-covered by `C^k` diffeomorphisms for some `ℓ > 0` (the
  covering input to Proposition 6.33 in the second proof of Proposition 6.34 of
  Barraud–Damian–Humilière–Oancea).

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.3 (second proof of
  Proposition 6.34).
-/

public section

noncomputable section

open Metric Module
open scoped RealInnerProductSpace Manifold ContDiff EuclideanSpace TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

section RotationFamily

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

/-- At angle `1 ∈ S¹`, `sphereRotationIsometry p` is the identity isometry. -/
theorem sphereRotationIsometry_of_coe_eq_one (p : sphere (0 : E) 1)
    (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) {z : sphere (0 : ℂ) 1} (hz : (z : ℂ) = 1) :
    sphereRotationIsometry p (v, z) = 1 :=
  (congrArg (sphereRotationPlane p v).planeRotation (Circle.ext hz : (⟨z, z.2⟩ : Circle) = 1)).trans
    (sphereRotationPlane p v).planeRotation.map_one

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

/-- At angle `1 ∈ S¹`, `sphereRotationDiff p k` is the identity diffeomorphism. -/
theorem sphereRotationDiff_of_coe_eq_one (p : sphere (0 : E) 1) (k : ℕ∞ω)
    (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) {z : sphere (0 : ℂ) 1} (hz : (z : ℂ) = 1) :
    sphereRotationDiff (n := n) p k (v, z) = 1 := by
  rw [sphereRotationDiff_apply, sphereRotationIsometry_of_coe_eq_one p v hz, map_one]

/-- Every diffeomorphism in `sphereRotationDiff p k` lies in the identity path component of
`Diff^k(Sⁿ)`. -/
theorem joined_one_sphereRotationDiff (p : sphere (0 : E) 1) (k : ℕ∞ω)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    Joined 1 (sphereRotationDiff (n := n) p k x) := by
  have hj : Joined (x.1, Circle.homeomorphSphere 1) x := by
    simpa only [Circle.homeomorphSphere.apply_symm_apply] using
      (PathConnectedSpace.joined (1 : Circle) (Circle.homeomorphSphere.symm x.2)).map
        (continuous_const.prodMk Circle.homeomorphSphere.continuous)
  have hz1 : (Circle.homeomorphSphere 1 : ℂ) = 1 :=
    (Circle.coe_homeomorphSphere_apply 1).trans Circle.coe_one
  simpa only [sphereRotationDiff_of_coe_eq_one p k x.1 hz1] using
    hj.map (sphereRotationDiff (n := n) p k).continuous

end RotationFamily

/-! ### Unconditional covering of odd-dimensional spheres by diffeomorphisms -/

section Covered

namespace HomologicalOrientation

/-- **Covering of unit spheres by plane rotations.** For any `(m + 2)`-dimensional real inner
product space `E`, every unit sphere `Sᵐ⁺¹` is `(1 + (-1) ^ m)`-covered by `C^k` diffeomorphisms at
every base point `x₀`, for every homological orientation `o` and every smoothness exponent
`k : ℕ∞ω`. -/
theorem isCoveredByDiffeomorphisms_sphere_one_add_neg_one_pow
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {m : ℕ} [Fact (finrank ℝ E = m + 1 + 1)]
    (o : HomologicalOrientation (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin (m + 1))) (m + 1))
    (k : ℕ∞ω) (x₀ : sphere (0 : E) 1) :
    o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ (1 + (-1) ^ m) := by
  have : ConnectedSpace (sphere (0 : E) 1) := connectedSpace_sphere (m + 1)
  let oE : Orientation ℝ E (Fin (m + 1 + 1)) :=
    (finBasisOfFinrankEq ℝ E (Fact.out : finrank ℝ E = m + 1 + 1)).orientation
  obtain ⟨q, hqp, hqp'⟩ := exists_sphere_ne_and_ne_neg (m + 1) x₀
  have hy : IsRegularValue ((𝓡 m).prod (𝓡 1)) (𝓡 (m + 1))
      (fun x ↦ sphereRotationDiff (n := m + 1) x₀ k x x₀) q := by
    simpa only [sphereRotationDiff_apply_self] using
      isRegularValue_sphereRotationFamily x₀ hqp hqp'
  have hcov := o.isCoveredByDiffeomorphisms_degreeAtRegularValue finrank_euclideanSpace_fin k
    ((oE.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere x₀)).sphereOrientation.prod
      Complex.orientation.sphereOrientation)
    oE.sphereOrientation (sphereRotationDiff (n := m + 1) x₀ k) hy x₀
  simpa only [sphereRotationDiff_apply_self,
    oE.degreeAtRegularValue_sphereRotationFamily x₀ hqp hqp'] using hcov

/-- **Odd-dimensional spheres are `2`-covered by diffeomorphisms** (the covering step in the second
proof of Proposition 6.34 of Barraud–Damian–Humilière–Oancea). Whenever `n` is odd, the
`n`-dimensional unit sphere `Sⁿ` of `E` is `2`-covered by `C^k` diffeomorphisms at every base point
`x₀`, for every homological orientation `o` and every smoothness exponent `k : ℕ∞ω`, with no
homotopy-group torsion hypothesis. -/
theorem isCoveredByDiffeomorphisms_sphere_of_odd
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} [Fact (finrank ℝ E = n + 1)] (hn : Odd n)
    (o : HomologicalOrientation (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n)) n)
    (k : ℕ∞ω) (x₀ : sphere (0 : E) 1) :
    o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ 2 := by
  obtain ⟨j, rfl⟩ := hn
  have h := o.isCoveredByDiffeomorphisms_sphere_one_add_neg_one_pow k x₀
  rw [(even_two_mul j).neg_one_pow] at h
  norm_num at h
  exact h

/-- **Odd-dimensional spheres are `ℓ`-covered by diffeomorphisms for some `ℓ > 0`** (via `ℓ = 2`,
the covering input to Proposition 6.33 in the second proof of Proposition 6.34 of
Barraud–Damian–Humilière–Oancea). -/
theorem exists_isCoveredByDiffeomorphisms_sphere_of_odd
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} [Fact (finrank ℝ E = n + 1)] (hn : Odd n)
    (o : HomologicalOrientation (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n)) n)
    (k : ℕ∞ω) (x₀ : sphere (0 : E) 1) :
    ∃ ℓ : ℤ, 0 < ℓ ∧ o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ ℓ :=
  ⟨2, by norm_num, o.isCoveredByDiffeomorphisms_sphere_of_odd hn k x₀⟩

/-- **Every odd-dimensional Euclidean sphere `Sⁿ` is `2`-covered by `C^k` diffeomorphisms** (the
covering step in the second proof of Proposition 6.34 of Barraud–Damian–Humilière–Oancea). -/
theorem isCoveredByDiffeomorphisms_euclideanSphere_of_odd {n : ℕ} (hn : Odd n)
    (o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
      (EuclideanSpace ℝ (Fin n)) n)
    (k : ℕ∞ω) (x₀ : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ 2 :=
  letI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  o.isCoveredByDiffeomorphisms_sphere_of_odd hn k x₀

/-- **Every odd-dimensional Euclidean sphere `Sⁿ` is `ℓ`-covered by `C^k` diffeomorphisms for some
`ℓ > 0`** (namely `ℓ = 2`). -/
theorem exists_isCoveredByDiffeomorphisms_euclideanSphere_of_odd {n : ℕ} (hn : Odd n)
    (o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
      (EuclideanSpace ℝ (Fin n)) n)
    (k : ℕ∞ω) (x₀ : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    ∃ ℓ : ℤ, 0 < ℓ ∧ o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ ℓ :=
  ⟨2, by norm_num, o.isCoveredByDiffeomorphisms_euclideanSphere_of_odd hn k x₀⟩

end HomologicalOrientation

end Covered

end TauCeti

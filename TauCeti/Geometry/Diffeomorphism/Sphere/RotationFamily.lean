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
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.Degree.Homological
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
diffeomorphisms of `Sⁿ` for the weak Whitney topology (`TauCeti.sphereRotationDiff`), and the
evaluation `((v, z), q) ↦ sphereRotationDiff p k (v, z) q` is jointly `C^k`
(`TauCeti.contMDiff_sphereRotationDiff_uncurry`). Evaluated at `p`, this family is the rotation
family `TauCeti.sphereRotationFamily p` of the sphere (`TauCeti.evalAt_comp_sphereRotationDiff`).

The rotation family has degree `1 + (-1)ᵐ` on `Sᵐ⁺¹`
(`Orientation.degreeAtRegularValue_sphereRotationFamily`), and in particular degree `2` on
odd-dimensional spheres (`Orientation.degreeAtRegularValue_sphereRotationFamily_of_even`).
Comparing the smooth degree with the homological pushforward of the fundamental class across the
product model `(𝓡 m).prod (𝓡 1)` and the target model `𝓡 (m + 1)`
(`TauCeti.Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul`) pushes `[Sᵐ × S¹]`
along `sphereRotationDiff` to a class of `H_{m + 1}(Diff(Sᵐ⁺¹); ℤ)` whose evaluation at `p` is
`(1 + (-1)ᵐ) • [Sᵐ⁺¹]`. Thus `Sᵐ⁺¹` is `(1 + (-1)ᵐ)`-covered by diffeomorphisms
(`TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_one_add_neg_one_pow`), and odd
spheres are `2`-covered by diffeomorphisms, at every base point and for every orientation
(`TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_two_of_even`). This is the direct
proof of Barraud, Damian, Humilière and Oancea, which needs no computation of homotopy groups of
`SO(n)`.

## Main definitions

* `TauCeti.sphereRotationPlane p v`: the linear isometry `w ↦ Re w • p + Im w • v` from `ℂ` onto
  the plane spanned by `p` and `v`.
* `TauCeti.sphereRotationIsometry p (v, z)`: the rotation of `E` by the angle of `z` in that plane.
* `TauCeti.sphereRotationDiff p k`: the rotations as a continuous family of `C^k` diffeomorphisms
  of the sphere.

## Main results

* `TauCeti.sphereRotationIsometry_apply`: explicit coordinate formula for the rotation.
* `TauCeti.sphereRotationIsometry_apply_self`, `TauCeti.sphereRotationIsometry_apply_tangent`,
  `TauCeti.sphereRotationIsometry_apply_of_inner_eq_zero`: the rotation on `p`, on `v`, and on
  vectors orthogonal to both.
* `TauCeti.continuous_sphereRotationIsometry`: the rotation depends continuously on `(v, z)`.
* `TauCeti.contMDiff_sphereRotationDiff_uncurry`: the rotation diffeomorphism family is jointly
  `C^k` in the parameters `(v, z)` and the sphere point `q`.
* `TauCeti.evalAt_comp_sphereRotationDiff`: evaluating the family of diffeomorphisms at `p` gives
  the rotation family of the sphere.
* `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_one_add_neg_one_pow`: `Sᵐ⁺¹` is
  `(1 + (-1)ᵐ)`-covered by `C^k` diffeomorphisms.
* `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_two_of_even`: odd spheres are
  `2`-covered by diffeomorphisms (the second proof of Proposition 6.34 of
  Barraud–Damian–Humilière–Oancea).
* `TauCeti.HomologicalOrientation.exists_isCoveredByDiffeomorphisms_sphere_of_even`: odd spheres are
  `ℓ`-covered by diffeomorphisms for some `ℓ > 0`.

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

/-- Explicit coordinate formula for `sphereRotationIsometry`: it adds `(z - 1)` times the complex
coordinate of the orthogonal projection onto the plane spanned by `p` and `v`. -/
theorem sphereRotationIsometry_apply (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) (u : E) :
    sphereRotationIsometry p x u =
      u + sphereRotationPlane p x.1 (((x.2 : ℂ) - 1) *
        ((⟪(p : E), u⟫ : ℂ) + (⟪((x.1 : (ℝ ∙ (p : E))ᗮ) : E), u⟫ : ℂ) * Complex.I)) := by
  simpa [sphereRotationIsometry_def] using
    (sphereRotationPlane p x.1).planeRotation_apply ⟨x.2, x.2.2⟩ u

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

section DiffFamily

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

end DiffFamily

/-- The rotation diffeomorphism family is jointly `C^k` in the parameters `(v, z)` and the sphere
point `q`. -/
theorem contMDiff_sphereRotationDiff_uncurry [FiniteDimensional ℝ E] {m : ℕ}
    [Fact (finrank ℝ E = m + 1 + 1)] (p : sphere (0 : E) 1) (k : ℕ∞ω) :
    ContMDiff (((𝓡 m).prod (𝓡 1)).prod (𝓡 (m + 1))) (𝓡 (m + 1)) k
      fun z : (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) × sphere (0 : E) 1 ↦
        sphereRotationDiff (n := m + 1) p k z.1 z.2 := by
  let I₀ := ((𝓡 m).prod (𝓡 1)).prod (𝓡 (m + 1))
  let P := (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) × sphere (0 : E) 1
  have hp : ContMDiff I₀ 𝓘(ℝ, E) k fun _ : P ↦ (p : E) := contMDiff_const
  have hv : ContMDiff I₀ 𝓘(ℝ, E) k fun z : P ↦ ((z.1.1 : (ℝ ∙ (p : E))ᗮ) : E) :=
    ((ℝ ∙ (p : E))ᗮ.subtypeL.contDiff.contMDiff.comp contMDiff_coe_sphere).comp
      (contMDiff_fst.comp contMDiff_fst)
  have hc : ContMDiff I₀ 𝓘(ℝ, ℂ) k fun z : P ↦ (z.1.2 : ℂ) :=
    contMDiff_coe_sphere.comp (contMDiff_snd.comp contMDiff_fst)
  have hu : ContMDiff I₀ 𝓘(ℝ, E) k fun z : P ↦ (z.2 : E) :=
    contMDiff_coe_sphere.comp contMDiff_snd
  have hpi : ContMDiff I₀ 𝓘(ℝ, ℝ) k fun z : P ↦ ⟪(p : E), (z.2 : E)⟫ :=
    (contDiff_inner (𝕜 := ℝ)).contMDiff.comp (hp.prodMk_space hu)
  have hvi : ContMDiff I₀ 𝓘(ℝ, ℝ) k fun z : P ↦ ⟪((z.1.1 : (ℝ ∙ (p : E))ᗮ) : E), (z.2 : E)⟫ :=
    (contDiff_inner (𝕜 := ℝ)).contMDiff.comp (hv.prodMk_space hu)
  have hw : ContMDiff I₀ 𝓘(ℝ, ℂ) k fun z : P ↦
      (⟪(p : E), (z.2 : E)⟫ : ℂ) +
        (⟪((z.1.1 : (ℝ ∙ (p : E))ᗮ) : E), (z.2 : E)⟫ : ℂ) * Complex.I :=
    (Complex.ofRealCLM.contDiff.contMDiff.comp hpi).add
      (contDiff_mul.contMDiff.comp
        ((Complex.ofRealCLM.contDiff.contMDiff.comp hvi).prodMk_space contMDiff_const))
  have hmul : ContMDiff I₀ 𝓘(ℝ, ℂ) k fun z : P ↦
      ((z.1.2 : ℂ) - 1) *
        ((⟪(p : E), (z.2 : E)⟫ : ℂ) +
          (⟪((z.1.1 : (ℝ ∙ (p : E))ᗮ) : E), (z.2 : E)⟫ : ℂ) * Complex.I) :=
    contDiff_mul.contMDiff.comp ((hc.sub contMDiff_const).prodMk_space hw)
  have hval : ContMDiff I₀ 𝓘(ℝ, E) k fun z : P ↦
      (sphereRotationDiff (n := m + 1) p k z.1 z.2 : E) := by
    simp only [coe_sphereRotationDiff_apply, sphereRotationIsometry_apply,
      sphereRotationPlane_apply]
    exact hu.add (((Complex.reCLM.contDiff.contMDiff.comp hmul).smul hp).add
      ((Complex.imCLM.contDiff.contMDiff.comp hmul).smul hv))
  exact hval.codRestrict_sphere (n := m + 1) fun z ↦
    (sphereRotationDiff (n := m + 1) p k z.1 z.2).2

/-! ### Odd spheres are covered by rotations -/

namespace HomologicalOrientation

section GeneralSphere

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {m : ℕ}
  [Fact (finrank ℝ F = m + 1 + 1)]

/-- **Spheres are `(1 + (-1)ᵐ)`-covered by plane rotations** (second proof of Proposition 6.34 of
Barraud–Damian–Humilière–Oancea). For every homological orientation `o` of the unit sphere `Sᵐ⁺¹`
in an `(m + 2)`-dimensional real inner product space `F`, every smoothness exponent `k : ℕ∞ω`, and
every base point `x₀`, `Sᵐ⁺¹` is `(1 + (-1) ^ m)`-covered by `C^k` diffeomorphisms at `x₀`. -/
theorem isCoveredByDiffeomorphisms_sphere_one_add_neg_one_pow
    (o : HomologicalOrientation (sphere (0 : F) 1) (EuclideanSpace ℝ (Fin (m + 1))) (m + 1))
    (k : ℕ∞ω) (x₀ : sphere (0 : F) 1) :
    o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ (1 + (-1) ^ m) := by
  have := connectedSpace_sphere (E := F) (m + 1)
  let oF : _root_.Orientation ℝ F (Fin (m + 1 + 1)) :=
    (finBasisOfFinrankEq ℝ F (Fact.out : finrank ℝ F = m + 1 + 1)).orientation
  let o₀ := oF.sphereOrientation.toHomologicalOrientation finrank_euclideanSpace_fin
  suffices h₀ : o₀.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ (1 + (-1) ^ m) by
    rcases o₀.eq_or_eq_neg finrank_euclideanSpace_fin o with rfl | rfl
    · exact h₀
    · rwa [isCoveredByDiffeomorphisms_neg]
  obtain ⟨q, hqx₀, hqneg⟩ := exists_ne_and_ne_neg_sphere
    (by rw [Fact.out (p := finrank ℝ F = m + 1 + 1)]; omega) x₀
  let oDom := (oF.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere x₀)).sphereOrientation.prod
    Complex.orientation.sphereOrientation
  refine .of_homologyMap (sphereRotationDiff x₀ k) oDom.fundamentalClass ?_
  rw [← oDom.mapFundamentalClass_def, evalAt_comp_sphereRotationDiff,
    oDom.mapFundamentalClass_eq_degreeAtRegularValue_smul oF.sphereOrientation
      (isRegularValue_sphereRotationFamily x₀ hqx₀ hqneg),
    ContinuousMap.coe_mk, oF.degreeAtRegularValue_sphereRotationFamily x₀ hqx₀ hqneg,
    oF.sphereOrientation.fundamentalClass_euclideanSpace, o₀.mapFundamentalClass_id]

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
  have h := o.isCoveredByDiffeomorphisms_sphere_one_add_neg_one_pow k x₀
  rw [hm.neg_one_pow] at h
  norm_num at h
  exact h

/-- When `m` is even, `Sᵐ⁺¹` is `ℓ`-covered by `C^k` diffeomorphisms for some positive integer `ℓ`
(namely `ℓ = 2`). -/
theorem exists_isCoveredByDiffeomorphisms_sphere_of_even
    (o : HomologicalOrientation (sphere (0 : F) 1) (EuclideanSpace ℝ (Fin (m + 1))) (m + 1))
    (hm : Even m) (k : ℕ∞ω) (x₀ : sphere (0 : F) 1) :
    ∃ ℓ : ℤ, 0 < ℓ ∧ o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ ℓ :=
  ⟨2, two_pos, o.isCoveredByDiffeomorphisms_sphere_two_of_even hm k x₀⟩

end GeneralSphere

section EuclideanSphere

/-- Euclidean-sphere specialization of `isCoveredByDiffeomorphisms_sphere_one_add_neg_one_pow`:
`Sᵐ⁺¹ ⊆ ℝᵐ⁺²` is `(1 + (-1) ^ m)`-covered by `C^k` diffeomorphisms. -/
theorem isCoveredByDiffeomorphisms_euclideanSphere_one_add_neg_one_pow {m : ℕ}
    (o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1)
      (EuclideanSpace ℝ (Fin (m + 1))) (m + 1))
    (k : ℕ∞ω) (x₀ : sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1) :
    o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ (1 + (-1) ^ m) := by
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 1 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  exact o.isCoveredByDiffeomorphisms_sphere_one_add_neg_one_pow k x₀

/-- Euclidean-sphere specialization of `isCoveredByDiffeomorphisms_sphere_two_of_even`: for even
`m`, `Sᵐ⁺¹ ⊆ ℝᵐ⁺²` is `2`-covered by `C^k` diffeomorphisms. -/
theorem isCoveredByDiffeomorphisms_euclideanSphere_two_of_even {m : ℕ}
    (o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1)
      (EuclideanSpace ℝ (Fin (m + 1))) (m + 1))
    (hm : Even m) (k : ℕ∞ω) (x₀ : sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1) :
    o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ 2 := by
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 1 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  exact o.isCoveredByDiffeomorphisms_sphere_two_of_even hm k x₀

/-- Direct degree proof of Proposition 6.34 for all odd Euclidean spheres `Sᵐ⁺¹ ⊆ ℝᵐ⁺²` (`Even m`):
`Sᵐ⁺¹` is `ℓ`-covered by `C^k` diffeomorphisms for some `ℓ > 0` (witnessed by `ℓ = 2`). -/
theorem exists_isCoveredByDiffeomorphisms_euclideanSphere_of_even {m : ℕ}
    (o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1)
      (EuclideanSpace ℝ (Fin (m + 1))) (m + 1))
    (hm : Even m) (k : ℕ∞ω) (x₀ : sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1) :
    ∃ ℓ : ℤ, 0 < ℓ ∧ o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ ℓ :=
  ⟨2, two_pos, o.isCoveredByDiffeomorphisms_euclideanSphere_two_of_even hm k x₀⟩

end EuclideanSphere

end HomologicalOrientation

end TauCeti

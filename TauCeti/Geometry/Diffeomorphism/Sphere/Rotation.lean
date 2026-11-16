/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Circle
public import TauCeti.Analysis.InnerProductSpace.PlaneRotation
public import TauCeti.Geometry.Diffeomorphism.Covered
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Degree.Homological
public import TauCeti.Geometry.Manifold.Degree.SphereRotation
public import TauCeti.Geometry.Sphere.Connected
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# Odd spheres are `2`-covered by plane rotations

Let `E` be a real inner product space of dimension `m + 2`, with unit sphere `Sᵐ⁺¹`, and fix a
base point `p ∈ Sᵐ⁺¹`. Each unit vector `v ∈ Sᵐ ⊆ (ℝ ∙ p)ᗮ` spans with `p` an oriented plane
isometric to `ℂ` via `w ↦ Re w • p + Im w • v` (`TauCeti.spherePlaneIsometry`). Rotating `E` in
that plane by a unit complex number `z ∈ S¹` (`TauCeti.spherePlaneRotation`) restricts to a
self-diffeomorphism of `Sᵐ⁺¹`. Because the underlying map is jointly smooth in `((v, z), u)`,
these restrictions form a continuous family

`Sᵐ × S¹ → Diff^k(Sᵐ⁺¹)` (`TauCeti.sphereRotationDiffFamily`)

for the weak Whitney `C^k` topology (`k : ℕ∞ω`). Evaluating this family at `p` recovers the
great-circle rotation family `(v, z) ↦ Re z • p + Im z • v` (`TauCeti.sphereRotationFamily`),
whose smooth degree at every point `q ≠ ±p` is `1 + (-1)ᵐ`
(`Orientation.degreeAtRegularValue_sphereRotationFamily`).

Comparing the smooth degree with the homological pushforward of the fundamental class across the
product model `(𝓡 m).prod (𝓡 1)` and the target model `𝓡 (m + 1)`
(`TauCeti.Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul`)
gives the second, direct proof of Proposition 6.34 of Barraud–Damian–Humilière–Oancea:

* `Sᵐ⁺¹` is `(1 + (-1)ᵐ)`-covered by `C^k` diffeomorphisms for every `m`, every homological
  orientation, every base point, and every smoothness exponent `k`
  (`TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_one_add_neg_one_pow`).
* In particular, when `m` is even, every odd-dimensional sphere `Sᵐ⁺¹` (including `S¹`) is
  explicitly `2`-covered by diffeomorphisms
  (`TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_two_of_even`), without
  appealing to homotopy groups of orthogonal groups.

## Main definitions

* `TauCeti.spherePlaneIsometry`: the isometric plane embedding `ℂ →ₗᵢ[ℝ] E`,
  `w ↦ Re w • p + Im w • v`, for `p ∈ S(E)` and `v ∈ S((ℝ ∙ p)ᗮ)`.
* `TauCeti.spherePlaneRotation`: the linear isometry equivalence of `E` rotating the plane of `p`
  and `v` by `z ∈ S¹`.
* `TauCeti.sphereRotationDiffFamily`: the continuous family
  `C(S((ℝ ∙ p)ᗮ) × S¹, Diff (𝓡 (m + 1)) (sphere (0 : E) 1) k)` of sphere diffeomorphisms.

## Main results

* `TauCeti.evalAt_comp_sphereRotationDiffFamily`: evaluating `sphereRotationDiffFamily p k` at `p`
  recovers `sphereRotationFamily p`.
* `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_one_add_neg_one_pow`: `Sᵐ⁺¹` is
  `(1 + (-1)ᵐ)`-covered by `C^k` diffeomorphisms.
* `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_two_of_even`: when `m` is even,
  `Sᵐ⁺¹` is `2`-covered by `C^k` diffeomorphisms.
* `TauCeti.HomologicalOrientation.exists_isCoveredByDiffeomorphisms_sphere_of_even`: when `m` is
  even, `Sᵐ⁺¹` is `ℓ`-covered by `C^k` diffeomorphisms for some `ℓ > 0`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.3, second proof of Proposition 6.34.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
-/

public section

noncomputable section

open Metric Module Set TauCeti.Manifold.Orientation
open scoped ContDiff EuclideanSpace Manifold RealInnerProductSpace TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

/-! ### Plane rotations determined by a base point and a unit tangent vector -/

section Plane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The linear isometry `ℂ →ₗᵢ[ℝ] E` sending `1` to `p ∈ S(E)` and `i` to a unit vector
`v ∈ S((ℝ ∙ p)ᗮ)` orthogonal to `p`. -/
def spherePlaneIsometry (p : sphere (0 : E) 1) (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    ℂ →ₗᵢ[ℝ] E where
  toLinearMap := Complex.reCLM.toLinearMap.smulRight (p : E) +
    Complex.imCLM.toLinearMap.smulRight ((v : (ℝ ∙ (p : E))ᗮ) : E)
  norm_map' w := by
    have hv : ‖((v : (ℝ ∙ (p : E))ᗮ) : E)‖ = 1 := norm_eq_of_mem_sphere v
    have horth : ⟪(p : E), ((v : (ℝ ∙ (p : E))ᗮ) : E)⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 (v : (ℝ ∙ (p : E))ᗮ).2
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.normSq_apply]
    simp only [LinearMap.add_apply, LinearMap.smulRight_apply, ContinuousLinearMap.coe_coe,
      Complex.reCLM_apply, Complex.imCLM_apply, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
      real_inner_smul_left, real_inner_smul_right, horth, norm_eq_of_mem_sphere p, hv,
      mul_zero, mul_one, sq_abs]
    ring

/-- `spherePlaneIsometry p v` sends `w` to `Re w • p + Im w • v`. -/
@[simp]
theorem spherePlaneIsometry_apply (p : sphere (0 : E) 1) (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)
    (w : ℂ) :
    spherePlaneIsometry p v w = w.re • (p : E) + w.im • ((v : (ℝ ∙ (p : E))ᗮ) : E) :=
  (rfl)

/-- `spherePlaneIsometry p v` sends `1` to `p`. -/
theorem spherePlaneIsometry_one (p : sphere (0 : E) 1) (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    spherePlaneIsometry p v 1 = (p : E) := by
  simp

/-- `spherePlaneIsometry p v` sends `Complex.I` to `v`. -/
theorem spherePlaneIsometry_I (p : sphere (0 : E) 1) (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    spherePlaneIsometry p v Complex.I = ((v : (ℝ ∙ (p : E))ᗮ) : E) := by
  simp

/-- The linear isometry equivalence of `E` rotating the plane spanned by `p` and `x.1` by the unit
complex number `x.2`, and fixing the orthogonal complement `(ℝ ∙ p ⊔ ℝ ∙ x.1)ᗮ` pointwise. -/
def spherePlaneRotation (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) : E ≃ₗᵢ[ℝ] E :=
  (spherePlaneIsometry p x.1).planeRotation (Circle.homeomorphSphere.symm x.2)

/-- Unfolding equation relating `spherePlaneRotation` to `LinearIsometry.planeRotation`. -/
theorem spherePlaneRotation_def (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    spherePlaneRotation p x =
      (spherePlaneIsometry p x.1).planeRotation (Circle.homeomorphSphere.symm x.2) :=
  (rfl)

/-- Explicit coordinate formula for `spherePlaneRotation`: it adds `(z - 1)` times the complex
coordinate of the orthogonal projection onto the plane spanned by `p` and `v`. -/
theorem spherePlaneRotation_apply (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) (u : E) :
    spherePlaneRotation p x u =
      u + spherePlaneIsometry p x.1 (((x.2 : ℂ) - 1) *
        ((⟪(p : E), u⟫ : ℂ) + (⟪((x.1 : (ℝ ∙ (p : E))ᗮ) : E), u⟫ : ℂ) * Complex.I)) := by
  rw [spherePlaneRotation_def, LinearIsometry.planeRotation_apply,
    Circle.coe_homeomorphSphere_symm_apply, spherePlaneIsometry_one, spherePlaneIsometry_I]

/-- Evaluating `spherePlaneRotation p (v, z)` at `p` gives `Re z • p + Im z • v`. -/
@[simp]
theorem spherePlaneRotation_apply_coe_self (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    spherePlaneRotation p x (p : E) =
      (x.2 : ℂ).re • (p : E) + (x.2 : ℂ).im • ((x.1 : (ℝ ∙ (p : E))ᗮ) : E) := by
  calc
    spherePlaneRotation p x (p : E) =
        (spherePlaneIsometry p x.1).planeRotation (Circle.homeomorphSphere.symm x.2)
          (spherePlaneIsometry p x.1 1) := by
      rw [spherePlaneRotation_def, spherePlaneIsometry_one]
    _ = (x.2 : ℂ).re • (p : E) + (x.2 : ℂ).im • ((x.1 : (ℝ ∙ (p : E))ᗮ) : E) := by
      rw [LinearIsometry.planeRotation_apply_map, Circle.coe_homeomorphSphere_symm_apply, mul_one,
        spherePlaneIsometry_apply]

end Plane

/-! ### The continuous family of sphere diffeomorphisms -/

section DiffFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {m : ℕ} [Fact (finrank ℝ E = m + 1 + 1)]

/-- The plane rotations of the unit sphere depend jointly smoothly on the parameters `(v, z)` and
the sphere point `q`. -/
private theorem contMDiff_unitSphereDiffHom_spherePlaneRotation (p : sphere (0 : E) 1)
    (k : ℕ∞ω) :
    ContMDiff (((𝓡 m).prod (𝓡 1)).prod (𝓡 (m + 1))) (𝓡 (m + 1)) k
      fun z : (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) × sphere (0 : E) 1 ↦
        LinearIsometryEquiv.unitSphereDiffHom (n := m + 1) k (spherePlaneRotation p z.1) z.2 := by
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
      ((LinearIsometryEquiv.unitSphereDiffHom (n := m + 1) k (spherePlaneRotation p z.1) z.2 :
        sphere (0 : E) 1) : E) := by
    simp only [LinearIsometryEquiv.unitSphereDiffHom_apply,
      LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply, spherePlaneRotation_apply,
      spherePlaneIsometry_apply]
    exact hu.add (((Complex.reCLM.contDiff.contMDiff.comp hmul).smul hp).add
      ((Complex.imCLM.contDiff.contMDiff.comp hmul).smul hv))
  exact hval.codRestrict_sphere (n := m + 1) fun z ↦
    (LinearIsometryEquiv.unitSphereDiffHom (n := m + 1) k (spherePlaneRotation p z.1) z.2).2

variable [FiniteDimensional ℝ E]

/-- **The plane-rotation family in `Diff^k(Sᵐ⁺¹)`**: the continuous map
`S((ℝ ∙ p)ᗮ) × S¹ → Diff (𝓡 (m + 1)) (sphere (0 : E) 1) k` sending `(v, z)` to the restriction of
`spherePlaneRotation p (v, z)` to the unit sphere. -/
def sphereRotationDiffFamily (p : sphere (0 : E) 1) (k : ℕ∞ω) :
    C(sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1,
      Diff (𝓡 (m + 1)) (sphere (0 : E) 1) k) :=
  Diffeomorph.ofSmoothFamily
    (fun x ↦ LinearIsometryEquiv.unitSphereDiffHom (n := m + 1) k (spherePlaneRotation p x))
    (contMDiff_unitSphereDiffHom_spherePlaneRotation p k)

/-- `sphereRotationDiffFamily p k` restricts `spherePlaneRotation p x` to the unit sphere. -/
@[simp]
theorem sphereRotationDiffFamily_apply (p : sphere (0 : E) 1) (k : ℕ∞ω)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    sphereRotationDiffFamily (m := m) p k x =
      LinearIsometryEquiv.unitSphereDiffHom (n := m + 1) k (spherePlaneRotation p x) := by
  rw [sphereRotationDiffFamily, Diffeomorph.ofSmoothFamily_apply]

/-- The plane-rotation diffeomorphism family is jointly `C^k` in the parameters `(v, z)` and the
sphere point `q`. -/
theorem contMDiff_sphereRotationDiffFamily_uncurry (p : sphere (0 : E) 1) (k : ℕ∞ω) :
    ContMDiff (((𝓡 m).prod (𝓡 1)).prod (𝓡 (m + 1))) (𝓡 (m + 1)) k
      fun z : (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) × sphere (0 : E) 1 ↦
        sphereRotationDiffFamily (m := m) p k z.1 z.2 := by
  simpa only [sphereRotationDiffFamily_apply] using
    contMDiff_unitSphereDiffHom_spherePlaneRotation (m := m) p k

/-- Evaluating the diffeomorphism `sphereRotationDiffFamily p k x` at `p` gives
`sphereRotationFamily p x`. -/
theorem sphereRotationDiffFamily_apply_self (p : sphere (0 : E) 1) (k : ℕ∞ω)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    sphereRotationDiffFamily (m := m) p k x p = sphereRotationFamily p x := by
  apply Subtype.ext
  rw [sphereRotationDiffFamily_apply, LinearIsometryEquiv.unitSphereDiffHom_apply,
    LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply, spherePlaneRotation_apply_coe_self,
    coe_sphereRotationFamily]

/-- Composing `sphereRotationDiffFamily p k` with evaluation at `p` recovers
`sphereRotationFamily p` as a continuous map. -/
@[simp]
theorem evalAt_comp_sphereRotationDiffFamily (p : sphere (0 : E) 1) (k : ℕ∞ω) :
    (Diffeomorph.evalAt p).comp (sphereRotationDiffFamily (m := m) p k) =
      ⟨sphereRotationFamily p, (contMDiff_sphereRotationFamily (m := m) p).continuous⟩ :=
  DFunLike.ext _ _ fun x ↦ by
    rw [ContinuousMap.comp_apply, Diffeomorph.evalAt_apply, sphereRotationDiffFamily_apply_self,
      ContinuousMap.coe_mk]

end DiffFamily

/-! ### Covering odd spheres by plane rotations -/

namespace HomologicalOrientation

section GeneralSphere

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {m : ℕ} [Fact (finrank ℝ E = m + 1 + 1)]

/-- **Spheres are `(1 + (-1)ᵐ)`-covered by plane rotations** (second proof of Proposition 6.34 of
Barraud–Damian–Humilière–Oancea). For every homological orientation `o` of the unit sphere `Sᵐ⁺¹`
in an `(m + 2)`-dimensional real inner product space `E`, every smoothness exponent `k : ℕ∞ω`, and
every base point `x₀`, `Sᵐ⁺¹` is `(1 + (-1) ^ m)`-covered by `C^k` diffeomorphisms at `x₀`. -/
theorem isCoveredByDiffeomorphisms_sphere_one_add_neg_one_pow
    (o : HomologicalOrientation (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin (m + 1))) (m + 1))
    (k : ℕ∞ω) (x₀ : sphere (0 : E) 1) :
    o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ (1 + (-1) ^ m) := by
  have : ConnectedSpace (sphere (0 : E) 1) := connectedSpace_sphere (m + 1)
  let oE : _root_.Orientation ℝ E (Fin (m + 1 + 1)) :=
    (finBasisOfFinrankEq ℝ E Fact.out).orientation
  let o₀ := oE.sphereOrientation.toHomologicalOrientation finrank_euclideanSpace_fin
  suffices h₀ : o₀.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ (1 + (-1) ^ m) by
    rcases o₀.eq_or_eq_neg finrank_euclideanSpace_fin o with rfl | rfl
    · exact h₀
    · rwa [isCoveredByDiffeomorphisms_neg]
  obtain ⟨qE, hqnorm, hqorth⟩ :=
    exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank (𝕜 := ℝ) {(x₀ : E)}
      (by rw [Finset.card_singleton, Fact.out (p := finrank ℝ E = m + 1 + 1)]; omega)
  have hinner : ⟪qE, (x₀ : E)⟫ = 0 := by
    rw [real_inner_comm]
    exact hqorth (x₀ : E) (Finset.mem_singleton_self _)
  let q : sphere (0 : E) 1 := ⟨qE, mem_sphere_zero_iff_norm.2 hqnorm⟩
  have hqx₀ : q ≠ x₀ := fun h ↦ by
    have h' : qE = (x₀ : E) := congrArg Subtype.val h
    rw [h', inner_self_eq_zero] at hinner
    exact ne_zero_of_mem_unit_sphere x₀ hinner
  have hqneg : q ≠ -x₀ := fun h ↦
    ne_neg_of_inner_eq_zero (𝕜 := ℝ) (ne_zero_of_mem_unit_sphere x₀) hinner (congrArg Subtype.val h)
  let oDom := (oE.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere x₀)).sphereOrientation.prod
    Complex.orientation.sphereOrientation
  refine .of_homologyMap (sphereRotationDiffFamily x₀ k) oDom.fundamentalClass ?_
  rw [← oDom.mapFundamentalClass_def, evalAt_comp_sphereRotationDiffFamily,
    oDom.mapFundamentalClass_eq_degreeAtRegularValue_smul oE.sphereOrientation
      (isRegularValue_sphereRotationFamily x₀ hqx₀ hqneg),
    ContinuousMap.coe_mk, oE.degreeAtRegularValue_sphereRotationFamily x₀ hqx₀ hqneg,
    oE.sphereOrientation.fundamentalClass_euclideanSpace, o₀.mapFundamentalClass_id]

/-- **Odd-dimensional spheres are `2`-covered by diffeomorphisms** (Proposition 6.34 of
Barraud–Damian–Humilière–Oancea). When `m` is even, the unit sphere `Sᵐ⁺¹` of an
`(m + 2)`-dimensional real inner product space is `2`-covered by `C^k` diffeomorphisms at every
base point and for every orientation. -/
theorem isCoveredByDiffeomorphisms_sphere_two_of_even
    (o : HomologicalOrientation (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin (m + 1))) (m + 1))
    (hm : Even m) (k : ℕ∞ω) (x₀ : sphere (0 : E) 1) :
    o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ 2 := by
  have h := o.isCoveredByDiffeomorphisms_sphere_one_add_neg_one_pow k x₀
  rw [hm.neg_one_pow] at h
  norm_num at h
  exact h

/-- When `m` is even, `Sᵐ⁺¹` is `ℓ`-covered by `C^k` diffeomorphisms for some positive integer `ℓ`
(namely `ℓ = 2`). -/
theorem exists_isCoveredByDiffeomorphisms_sphere_of_even
    (o : HomologicalOrientation (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin (m + 1))) (m + 1))
    (hm : Even m) (k : ℕ∞ω) (x₀ : sphere (0 : E) 1) :
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

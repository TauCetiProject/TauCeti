/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Circle
public import TauCeti.Analysis.InnerProductSpace.PlaneRotation
public import TauCeti.Geometry.Diffeomorphism.Degree
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Degree.SphereRotation
import TauCeti.Geometry.Sphere.Connected

/-!
# Lifting the sphere rotation family to diffeomorphisms, and `2`-covering of odd spheres

For a point `p` of the unit sphere `Sⁿ` of an `(n + 1)`-dimensional real inner product space `E`
(`n = m + 1`), the rotation family `TauCeti.sphereRotationFamily p : Sⁿ⁻¹ × S¹ → Sⁿ` sends a unit
tangent vector `v ∈ S(p^⊥)` and an angle `z ∈ S¹` to `Re z • p + Im z • v`, and has smooth degree
`1 + (-1)ⁿ⁻¹` (`Orientation.degreeAtRegularValue_sphereRotationFamily`).

This file lifts `sphereRotationFamily p` through evaluation at `p` to a continuous family of
self-diffeomorphisms of `Sⁿ` (`TauCeti.sphereRotationDiffFamily`):

1. Each orthonormal pair `(p, v)` defines a real-linear isometric embedding
   `TauCeti.spherePlaneIsometry p v : ℂ →ₗᵢ[ℝ] E` with `1 ↦ p` and `i ↦ v`.
2. Rotating in that plane by `z ∈ S¹` while fixing `(span {p, v})ᗮ` pointwise gives a continuous
   family of ambient linear isometries `TauCeti.spherePlaneRotation p : Sⁿ⁻¹ × S¹ → (E ≃ₗᵢ[ℝ] E)`
   of determinant `1` whose evaluation at `p` is `sphereRotationFamily p`.
3. Restricting to the unit sphere via `LinearIsometryEquiv.unitSphereDiffHom` produces a continuous
   map `TauCeti.sphereRotationDiffFamily p k : C(Sⁿ⁻¹ × S¹, Diff^k(Sⁿ))` for the weak Whitney
   `C^k` topology, at every smoothness exponent `k : ℕ∞ω`, landing in the identity component of
   `Diff^k(Sⁿ)` (`TauCeti.joined_one_sphereRotationDiffFamily`) and lifting `sphereRotationFamily p`
   along `Diffeomorph.evalAt p` (`TauCeti.evalAt_comp_sphereRotationDiffFamily`).

Combining this lift with
`TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_of_degreeAtRegularValue` and the degree
computation `Orientation.degreeAtRegularValue_sphereRotationFamily` gives the second,
homotopy-group-free proof of Proposition 6.34 of Barraud–Damian–Humilière–Oancea: every
odd-dimensional sphere (`n = m + 1` with `Even m`, including `S¹`, `S³`, `S⁵`, …) is `2`-covered
by `C^k` diffeomorphisms at every base point, for every orientation and every smoothness `k : ℕ∞ω`
(`TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_of_even`,
`TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_euclideanSphere_odd`), without assuming
that `π_{n-1}(SO(n))` is torsion.

## Main definitions

* `TauCeti.spherePlaneIsometry p v`: the plane embedding `ℂ →ₗᵢ[ℝ] E` sending `1 ↦ p` and `i ↦ v`.
* `TauCeti.spherePlaneRotation p`: the ambient plane rotation family
  `S(p^⊥) × S¹ → (E ≃ₗᵢ[ℝ] E)`.
* `TauCeti.sphereRotationDiffFamily p k`: the continuous family `C(S(p^⊥) × S¹, Diff^k(Sⁿ))` of
  `C^k` diffeomorphisms of the unit sphere lifting `sphereRotationFamily p`.

## Main results

* `TauCeti.evalAt_comp_sphereRotationDiffFamily`: composing `sphereRotationDiffFamily p k` with
  `Diffeomorph.evalAt p` recovers `sphereRotationFamily p`.
* `TauCeti.joined_one_sphereRotationDiffFamily`: every diffeomorphism in the family is isotopic to
  the identity in `Diff^k(Sⁿ)`.
* `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_one_add_neg_one_pow`: `Sᵐ⁺¹` is
  `(1 + (-1) ^ m)`-covered by `C^k` diffeomorphisms.
* `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_of_even`,
  `TauCeti.HomologicalOrientation.exists_isCoveredByDiffeomorphisms_sphere_of_even`,
  `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_euclideanSphere_odd`: odd-dimensional
  spheres are `2`-covered by `C^k` diffeomorphisms (Barraud–Damian–Humilière–Oancea,
  Proposition 6.34, second proof).

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.3, Proposition 6.34 (second proof).
-/

public section

noncomputable section

open Metric Module
open scoped Manifold ContDiff EuclideanSpace RealInnerProductSpace TauCeti.DiffeomorphWeakWhitney
  unitInterval

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

/-! ### Ambient plane rotations over unit tangent vectors -/

section PlaneRotation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The plane embedding of a point `p ∈ S(E)` and a unit tangent vector `v ∈ S(p^⊥)`**: the
real-linear isometry `ℂ →ₗᵢ[ℝ] E` sending `w` to `Re w • p + Im w • v`, so `1 ↦ p` and `i ↦ v`. -/
def spherePlaneIsometry (p : sphere (0 : E) 1) (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    ℂ →ₗᵢ[ℝ] E :=
  LinearIsometry.ofOrthonormalPair (norm_eq_of_mem_sphere p)
    ((Submodule.norm_coe (v : (ℝ ∙ (p : E))ᗮ)).trans (norm_eq_of_mem_sphere v))
    (Submodule.mem_orthogonal_singleton_iff_inner_right.1 (v : (ℝ ∙ (p : E))ᗮ).2)

@[simp]
theorem spherePlaneIsometry_apply (p : sphere (0 : E) 1) (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)
    (w : ℂ) :
    spherePlaneIsometry p v w = w.re • (p : E) + w.im • ((v : (ℝ ∙ (p : E))ᗮ) : E) :=
  LinearIsometry.ofOrthonormalPair_apply _ _ _ w

/-- `spherePlaneIsometry p v` sends `1 ∈ ℂ` to `p`. -/
theorem spherePlaneIsometry_one (p : sphere (0 : E) 1) (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    spherePlaneIsometry p v 1 = (p : E) := by
  simp

/-- `spherePlaneIsometry p v` sends `i ∈ ℂ` to `v`. -/
theorem spherePlaneIsometry_I (p : sphere (0 : E) 1) (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    spherePlaneIsometry p v Complex.I = ((v : (ℝ ∙ (p : E))ᗮ) : E) := by
  simp

/-- **The ambient plane rotation** determined by a point `p` of the unit sphere, a unit vector
`v` orthogonal to `p`, and an angle `z` on the unit circle of `ℂ`: rotate the oriented plane
`span {p, v}` by `z` and fix `(span {p, v})ᗮ` pointwise. -/
def spherePlaneRotation (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) : E ≃ₗᵢ[ℝ] E :=
  (spherePlaneIsometry p x.1).planeRotation (Circle.homeomorphSphere.symm x.2)

/-- Evaluating `spherePlaneRotation p (v, z)` at `p` rotates `p` to `Re z • p + Im z • v`. -/
@[simp]
theorem spherePlaneRotation_apply_basepoint (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    spherePlaneRotation p x (p : E) =
      (x.2 : ℂ).re • (p : E) + (x.2 : ℂ).im • ((x.1 : (ℝ ∙ (p : E))ᗮ) : E) := by
  simpa [spherePlaneRotation] using
    (spherePlaneIsometry p x.1).planeRotation_apply_map (Circle.homeomorphSphere.symm x.2) 1

/-- Evaluating `spherePlaneRotation p (v, z)` at `v` rotates `v` to `-Im z • p + Re z • v`. -/
@[simp]
theorem spherePlaneRotation_apply_tangent (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    spherePlaneRotation p x ((x.1 : (ℝ ∙ (p : E))ᗮ) : E) =
      -((x.2 : ℂ).im • (p : E)) + (x.2 : ℂ).re • ((x.1 : (ℝ ∙ (p : E))ᗮ) : E) := by
  simpa [spherePlaneRotation] using
    (spherePlaneIsometry p x.1).planeRotation_apply_map (Circle.homeomorphSphere.symm x.2)
      Complex.I

/-- Vectors orthogonal to both `p` and `v` are fixed by `spherePlaneRotation p (v, z)`. -/
theorem spherePlaneRotation_apply_of_orthogonal (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) {w : E}
    (hwp : ⟪(p : E), w⟫ = 0) (hwv : ⟪((x.1 : (ℝ ∙ (p : E))ᗮ) : E), w⟫ = 0) :
    spherePlaneRotation p x w = w :=
  LinearIsometry.planeRotation_apply_of_mem_orthogonal _ _
    ((LinearIsometry.mem_orthogonal_range_ofOrthonormalPair_iff _ _ _).2 ⟨hwp, hwv⟩)

@[simp]
theorem spherePlaneRotation_one (p : sphere (0 : E) 1) (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    spherePlaneRotation p (v, Circle.homeomorphSphere 1) = 1 := by
  simp [spherePlaneRotation]

@[simp]
theorem spherePlaneRotation_mul (p : sphere (0 : E) 1) (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)
    (c₁ c₂ : Circle) :
    spherePlaneRotation p (v, Circle.homeomorphSphere (c₁ * c₂)) =
      spherePlaneRotation p (v, Circle.homeomorphSphere c₁) *
        spherePlaneRotation p (v, Circle.homeomorphSphere c₂) := by
  simp [spherePlaneRotation, map_mul]

@[simp]
theorem spherePlaneRotation_inv (p : sphere (0 : E) 1) (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)
    (c : Circle) :
    spherePlaneRotation p (v, Circle.homeomorphSphere c⁻¹) =
      (spherePlaneRotation p (v, Circle.homeomorphSphere c))⁻¹ := by
  simp [spherePlaneRotation, map_inv]

/-- Every ambient plane rotation in `spherePlaneRotation p` has determinant `1` as a continuous
linear map. -/
@[simp]
theorem det_toContinuousLinearMap_spherePlaneRotation (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    ((spherePlaneRotation p x).toContinuousLinearEquiv : E →L[ℝ] E).det = 1 :=
  LinearIsometry.det_toContinuousLinearMap_planeRotation _ _

/-- Every ambient plane rotation in `spherePlaneRotation p` has determinant `1`. -/
@[simp]
theorem det_spherePlaneRotation (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    LinearMap.det ((spherePlaneRotation p x).toLinearEquiv : E →ₗ[ℝ] E) = 1 :=
  LinearIsometry.det_planeRotation _ _

/-- The ambient plane rotations `spherePlaneRotation p` depend continuously on `(v, z)` in the
operator-norm topology. -/
theorem continuous_spherePlaneRotation_toContinuousLinearMap (p : sphere (0 : E) 1) :
    Continuous fun x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦
      ((spherePlaneRotation p x).toContinuousLinearEquiv : E →L[ℝ] E) := by
  refine Continuous.planeRotation_toContinuousLinearMap
    (ι := fun x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦ spherePlaneIsometry p x.1)
    ?_ ?_ (Circle.homeomorphSphere.symm.continuous.comp continuous_snd)
  · simp only [spherePlaneIsometry_one]
    exact continuous_const
  · simp only [spherePlaneIsometry_I]
    exact continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)

/-- Restricting `spherePlaneRotation p x` to the unit sphere and evaluating at `p` recovers
`sphereRotationFamily p x`. -/
@[simp]
theorem unitSphereEquiv_spherePlaneRotation_self (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    LinearIsometryEquiv.unitSphereEquiv (spherePlaneRotation p x) p = sphereRotationFamily p x :=
  Subtype.ext (by simp)

end PlaneRotation

/-! ### The continuous family of sphere diffeomorphisms -/

section DiffFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}
  [Fact (finrank ℝ E = m + 1 + 1)]

@[simp]
theorem unitSphereDiffeomorph_spherePlaneRotation_self (p : sphere (0 : E) 1) (k : ℕ∞ω)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    LinearIsometryEquiv.unitSphereDiffeomorph (n := m + 1) (k := m + 1)
        (spherePlaneRotation p x) k p =
      sphereRotationFamily p x :=
  Subtype.ext (by simp)

variable [FiniteDimensional ℝ E]

/-- **The rotation family of `C^k` sphere diffeomorphisms** at `p ∈ Sᵐ⁺¹`, continuous for the weak
Whitney `C^k` topology: each `(v, z) ∈ S(p^⊥) × S¹` acts on `Sᵐ⁺¹` by restricting the plane
rotation `spherePlaneRotation p (v, z)` to the unit sphere. -/
def sphereRotationDiffFamily (p : sphere (0 : E) 1) (k : ℕ∞ω) :
    C(sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1, Diff (𝓡 (m + 1)) (sphere (0 : E) 1) k) where
  toFun x := LinearIsometryEquiv.unitSphereDiffHom k (spherePlaneRotation p x)
  continuous_toFun := by
    refine Diffeomorph.continuous_weakWhitney_iff.mpr ?_
    simpa only [LinearIsometryEquiv.unitSphereDiffHom_apply] using
      (continuous_spherePlaneRotation_toContinuousLinearMap p).toContMDiffMap_unitSphereDiffeomorph

@[simp]
theorem sphereRotationDiffFamily_apply (p : sphere (0 : E) 1) (k : ℕ∞ω)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    sphereRotationDiffFamily (m := m) p k x =
      LinearIsometryEquiv.unitSphereDiffeomorph (n := m + 1) (k := m + 1)
        (spherePlaneRotation p x) k := by
  change LinearIsometryEquiv.unitSphereDiffHom k (spherePlaneRotation p x) = _
  exact LinearIsometryEquiv.unitSphereDiffHom_apply _

/-- Read in the ambient space `E`, `sphereRotationDiffFamily p k x` acts as
`spherePlaneRotation p x`. -/
theorem coe_sphereRotationDiffFamily_apply (p : sphere (0 : E) 1) (k : ℕ∞ω)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) (q : sphere (0 : E) 1) :
    ((sphereRotationDiffFamily (m := m) p k x q : sphere (0 : E) 1) : E) =
      spherePlaneRotation p x q := by
  simp

/-- Evaluating `sphereRotationDiffFamily p k x` at `p` yields `sphereRotationFamily p x`. -/
theorem sphereRotationDiffFamily_apply_self (p : sphere (0 : E) 1) (k : ℕ∞ω)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    sphereRotationDiffFamily (m := m) p k x p = sphereRotationFamily p x := by
  simp

/-- Composing `sphereRotationDiffFamily p k` with evaluation at `p` recovers the smooth rotation
family `sphereRotationFamily p`. -/
@[simp]
theorem evalAt_comp_sphereRotationDiffFamily (p : sphere (0 : E) 1) (k : ℕ∞ω) :
    (Diffeomorph.evalAt p).comp (sphereRotationDiffFamily (m := m) p k) =
      ⟨sphereRotationFamily p, (contMDiff_sphereRotationFamily (m := m) p).continuous⟩ := by
  ext x : 1
  simp

/-- At the identity angle `1 ∈ S¹`, `sphereRotationDiffFamily p k` is the identity
diffeomorphism. -/
theorem sphereRotationDiffFamily_one (p : sphere (0 : E) 1) (k : ℕ∞ω)
    (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    sphereRotationDiffFamily (m := m) p k (v, Circle.homeomorphSphere 1) = 1 := by
  ext q
  simp

/-- Every diffeomorphism in `sphereRotationDiffFamily p k` lies in the identity path component of
`Diff^k(Sᵐ⁺¹)`. -/
theorem joined_one_sphereRotationDiffFamily (p : sphere (0 : E) 1) (k : ℕ∞ω)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    Joined 1 (sphereRotationDiffFamily (m := m) p k x) := by
  set c : Circle := Circle.homeomorphSphere.symm x.2
  let γ : Path (x.1, Circle.homeomorphSphere 1) x :=
    { toFun := fun t : I ↦ (x.1, Circle.homeomorphSphere (Circle.exp ((t : ℝ) * Complex.arg c)))
      continuous_toFun := continuous_const.prodMk (Circle.homeomorphSphere.continuous.comp
        (Circle.exp.continuous.comp (continuous_subtype_val.mul continuous_const)))
      source' := by simp
      target' := by
        rw [Set.Icc.coe_one, one_mul, Circle.exp_arg]
        exact Prod.ext rfl (Circle.homeomorphSphere.apply_symm_apply x.2) }
  simpa only [sphereRotationDiffFamily_one] using
    Joined.map ⟨γ⟩ (sphereRotationDiffFamily (m := m) p k).continuous

end DiffFamily

/-! ### Unconditional covering of odd-dimensional spheres by diffeomorphisms -/

section Covered

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every unit sphere of dimension `m + 1 ≥ 1` contains a point distinct from both `p` and `-p`,
namely any unit vector orthogonal to `p`. -/
private theorem exists_mem_sphere_ne_and_ne_neg (m : ℕ) [Fact (finrank ℝ E = m + 1 + 1)]
    (p : sphere (0 : E) 1) :
    ∃ q : sphere (0 : E) 1, q ≠ p ∧ q ≠ -p := by
  let b := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (m + 1)
    (ne_zero_of_mem_unit_sphere p)
  have hb_norm : ‖((b 0 : (ℝ ∙ (p : E))ᗮ) : E)‖ = 1 :=
    ((Submodule.norm_coe (b 0)).trans (b.norm_eq_one 0))
  have hb_orth : ⟪(p : E), ((b 0 : (ℝ ∙ (p : E))ᗮ) : E)⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.1 (b 0).2
  refine ⟨⟨((b 0 : (ℝ ∙ (p : E))ᗮ) : E), mem_sphere_zero_iff_norm.2 hb_norm⟩, ?_, ?_⟩
  · intro h
    have h' := congrArg (fun w : sphere (0 : E) 1 ↦ ⟪(p : E), (w : E)⟫) h
    simp only [hb_orth, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p, one_pow] at h'
    exact zero_ne_one h'
  · intro h
    have h' := congrArg (fun w : sphere (0 : E) 1 ↦ ⟪(p : E), (w : E)⟫) h
    simp only [hb_orth, coe_neg_sphere, inner_neg_right, real_inner_self_eq_norm_sq,
      norm_eq_of_mem_sphere p, one_pow] at h'
    linarith

variable [FiniteDimensional ℝ E] {m : ℕ} [Fact (finrank ℝ E = m + 1 + 1)]

namespace HomologicalOrientation

/-- **Covering of unit spheres by plane rotations.** For any `(m + 2)`-dimensional real inner
product space `E`, every unit sphere `Sᵐ⁺¹` is `(1 + (-1) ^ m)`-covered by `C^k` diffeomorphisms at
every base point `x₀`, for every homological orientation `o` and every smoothness exponent
`k : ℕ∞ω`. -/
theorem isCoveredByDiffeomorphisms_sphere_one_add_neg_one_pow
    (o : HomologicalOrientation (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin (m + 1))) (m + 1))
    (k : ℕ∞ω) (x₀ : sphere (0 : E) 1) :
    o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ (1 + (-1) ^ m) := by
  have : ConnectedSpace (sphere (0 : E) 1) := connectedSpace_sphere (m + 1)
  let oE : Orientation ℝ E (Fin (m + 1 + 1)) :=
    (finBasisOfFinrankEq ℝ E (Fact.out : finrank ℝ E = m + 1 + 1)).orientation
  obtain ⟨q, hqp, hqp'⟩ := exists_mem_sphere_ne_and_ne_neg m x₀
  have hy : IsRegularValue ((𝓡 m).prod (𝓡 1)) (𝓡 (m + 1))
      (fun x ↦ sphereRotationDiffFamily (m := m) x₀ k x x₀) q := by
    simpa only [sphereRotationDiffFamily_apply, unitSphereDiffeomorph_spherePlaneRotation_self]
      using isRegularValue_sphereRotationFamily x₀ hqp hqp'
  have hcov := o.isCoveredByDiffeomorphisms_of_degreeAtRegularValue finrank_euclideanSpace_fin k
    ((oE.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere x₀)).sphereOrientation.prod
      Complex.orientation.sphereOrientation)
    oE.sphereOrientation (sphereRotationDiffFamily (m := m) x₀ k) hy x₀
  simpa only [sphereRotationDiffFamily_apply, unitSphereDiffeomorph_spherePlaneRotation_self,
    oE.degreeAtRegularValue_sphereRotationFamily x₀ hqp hqp'] using hcov

/-- **Odd-dimensional spheres are `2`-covered by diffeomorphisms** (the second proof of
Proposition 6.34 of Barraud–Damian–Humilière–Oancea). Whenever `m` is even, the odd-dimensional
unit sphere `Sᵐ⁺¹` of `E` is `2`-covered by `C^k` diffeomorphisms at every base point `x₀`, for
every homological orientation `o` and every smoothness exponent `k : ℕ∞ω`, with no homotopy-group
torsion hypothesis. -/
theorem isCoveredByDiffeomorphisms_sphere_of_even
    (o : HomologicalOrientation (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin (m + 1))) (m + 1))
    (hm : Even m) (k : ℕ∞ω) (x₀ : sphere (0 : E) 1) :
    o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ 2 := by
  have h := o.isCoveredByDiffeomorphisms_sphere_one_add_neg_one_pow k x₀
  rw [hm.neg_one_pow] at h
  norm_num at h
  exact h

/-- **Odd-dimensional spheres are `ℓ`-covered by diffeomorphisms for some `ℓ > 0`**
(Barraud–Damian–Humilière–Oancea, Proposition 6.34), unconditionally via `ℓ = 2`. -/
theorem exists_isCoveredByDiffeomorphisms_sphere_of_even
    (o : HomologicalOrientation (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin (m + 1))) (m + 1))
    (hm : Even m) (k : ℕ∞ω) (x₀ : sphere (0 : E) 1) :
    ∃ ℓ : ℤ, 0 < ℓ ∧ o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ ℓ :=
  ⟨2, by norm_num, o.isCoveredByDiffeomorphisms_sphere_of_even hm k x₀⟩

/-- **Every odd-dimensional Euclidean sphere `S^{2j+1}` is `2`-covered by `C^k` diffeomorphisms**
(Barraud–Damian–Humilière–Oancea, Proposition 6.34, second proof). -/
theorem isCoveredByDiffeomorphisms_euclideanSphere_odd {j : ℕ}
    (o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin (2 * j + 2))) 1)
      (EuclideanSpace ℝ (Fin (2 * j + 1))) (2 * j + 1))
    (k : ℕ∞ω) (x₀ : sphere (0 : EuclideanSpace ℝ (Fin (2 * j + 2))) 1) :
    o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ 2 :=
  letI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (2 * j + 2))) = 2 * j + 1 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  o.isCoveredByDiffeomorphisms_sphere_of_even (even_two_mul j) k x₀

/-- **Every odd-dimensional Euclidean sphere `S^{2j+1}` is `ℓ`-covered by `C^k` diffeomorphisms for
some `ℓ > 0`** (namely `ℓ = 2`). -/
theorem exists_isCoveredByDiffeomorphisms_euclideanSphere_odd {j : ℕ}
    (o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin (2 * j + 2))) 1)
      (EuclideanSpace ℝ (Fin (2 * j + 1))) (2 * j + 1))
    (k : ℕ∞ω) (x₀ : sphere (0 : EuclideanSpace ℝ (Fin (2 * j + 2))) 1) :
    ∃ ℓ : ℤ, 0 < ℓ ∧ o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ ℓ :=
  ⟨2, by norm_num, o.isCoveredByDiffeomorphisms_euclideanSphere_odd k x₀⟩

end HomologicalOrientation

end Covered

end TauCeti

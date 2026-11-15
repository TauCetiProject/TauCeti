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
2. Rotating in that plane by `z ∈ S¹` via `LinearIsometry.planeRotation` while fixing
   `(span {p, v})ᗮ` pointwise gives an operator-norm continuous family of ambient linear isometries
   `Sⁿ⁻¹ × S¹ → (E ≃ₗᵢ[ℝ] E)` of determinant `1` whose evaluation at `p` is
   `sphereRotationFamily p`.
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

/-! ### Plane embeddings over unit tangent vectors -/

section PlaneIsometry

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

end PlaneIsometry

/-! ### The continuous family of sphere diffeomorphisms -/

section DiffFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {m : ℕ} [Fact (finrank ℝ E = m + 1 + 1)]

/-- **The rotation family of `C^k` sphere diffeomorphisms** at `p ∈ Sᵐ⁺¹`, continuous for the weak
Whitney `C^k` topology: each `(v, z) ∈ S(p^⊥) × S¹` acts on `Sᵐ⁺¹` by restricting the plane
rotation `(spherePlaneIsometry p v).planeRotation (Circle.homeomorphSphere.symm z)` to the unit
sphere. -/
def sphereRotationDiffFamily (p : sphere (0 : E) 1) (k : ℕ∞ω) :
    C(sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1, Diff (𝓡 (m + 1)) (sphere (0 : E) 1) k) where
  toFun x := LinearIsometryEquiv.unitSphereDiffHom k
    ((spherePlaneIsometry p x.1).planeRotation (Circle.homeomorphSphere.symm x.2))
  continuous_toFun := by
    have hcont : Continuous fun x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦
        ((((spherePlaneIsometry p x.1).planeRotation
          (Circle.homeomorphSphere.symm x.2)).toContinuousLinearEquiv : E →L[ℝ] E)) := by
      refine Continuous.planeRotation_toContinuousLinearMap
        (ι := fun x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦ spherePlaneIsometry p x.1)
        ?_ ?_ (Circle.homeomorphSphere.symm.continuous.comp continuous_snd)
      · simp only [spherePlaneIsometry_one]
        exact continuous_const
      · simp only [spherePlaneIsometry_I]
        exact continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
    refine Diffeomorph.continuous_weakWhitney_iff.mpr ?_
    simpa only [LinearIsometryEquiv.unitSphereDiffHom_apply] using
      hcont.toContMDiffMap_unitSphereDiffeomorph

@[simp]
theorem sphereRotationDiffFamily_apply (p : sphere (0 : E) 1) (k : ℕ∞ω)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    sphereRotationDiffFamily (m := m) p k x =
      LinearIsometryEquiv.unitSphereDiffeomorph (n := m + 1) (k := m + 1)
        ((spherePlaneIsometry p x.1).planeRotation (Circle.homeomorphSphere.symm x.2)) k := by
  rw [sphereRotationDiffFamily, ContinuousMap.coe_mk, LinearIsometryEquiv.unitSphereDiffHom_apply]

/-- Composing `sphereRotationDiffFamily p k` with evaluation at `p` recovers the smooth rotation
family `sphereRotationFamily p`. -/
@[simp]
theorem evalAt_comp_sphereRotationDiffFamily (p : sphere (0 : E) 1) (k : ℕ∞ω) :
    (Diffeomorph.evalAt p).comp (sphereRotationDiffFamily (m := m) p k) =
      ⟨sphereRotationFamily p, (contMDiff_sphereRotationFamily (m := m) p).continuous⟩ := by
  ext x : 2
  simp only [ContinuousMap.comp_apply, Diffeomorph.evalAt_apply, sphereRotationDiffFamily_apply,
    LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply, ContinuousMap.coe_mk,
    coe_sphereRotationFamily]
  simpa using
    (spherePlaneIsometry p x.1).planeRotation_apply_map (Circle.homeomorphSphere.symm x.2) 1

/-- At the identity angle `1 ∈ S¹`, `sphereRotationDiffFamily p k` is the identity
diffeomorphism. -/
theorem sphereRotationDiffFamily_one (p : sphere (0 : E) 1) (k : ℕ∞ω)
    (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    sphereRotationDiffFamily (m := m) p k (v, Circle.homeomorphSphere 1) = 1 := by
  rw [sphereRotationDiffFamily_apply, ← LinearIsometryEquiv.unitSphereDiffHom_apply,
    Homeomorph.symm_apply_apply, map_one, map_one]

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

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {m : ℕ} [Fact (finrank ℝ E = m + 1 + 1)]

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
  obtain ⟨q, hqp, hqp'⟩ := exists_sphere_ne_and_ne_neg (m + 1) x₀
  have heval :
      (fun x ↦ sphereRotationDiffFamily (m := m) x₀ k x x₀) = sphereRotationFamily x₀ := by
    funext x
    simpa only [ContinuousMap.comp_apply, Diffeomorph.evalAt_apply, ContinuousMap.coe_mk] using
      DFunLike.congr_fun (evalAt_comp_sphereRotationDiffFamily (m := m) x₀ k) x
  have hy : IsRegularValue ((𝓡 m).prod (𝓡 1)) (𝓡 (m + 1))
      (fun x ↦ sphereRotationDiffFamily (m := m) x₀ k x x₀) q := by
    rw [heval]
    exact isRegularValue_sphereRotationFamily x₀ hqp hqp'
  have hcov := o.isCoveredByDiffeomorphisms_of_degreeAtRegularValue finrank_euclideanSpace_fin k
    ((oE.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere x₀)).sphereOrientation.prod
      Complex.orientation.sphereOrientation)
    oE.sphereOrientation (sphereRotationDiffFamily (m := m) x₀ k) hy x₀
  rwa [heval, oE.degreeAtRegularValue_sphereRotationFamily x₀ hqp hqp'] at hcov

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

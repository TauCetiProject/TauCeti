/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Covered
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Degree.SphereReflection
import TauCeti.Analysis.InnerProductSpace.Reflection
import TauCeti.Geometry.Manifold.Degree.Homological
import TauCeti.Geometry.Sphere.Connected

/-!
# Odd-dimensional spheres are covered by rotations

A compact oriented `d`-manifold `M` is `ℓ`-covered by diffeomorphisms at `x₀` when some class of
`H_d(Diff(M); ℤ)` is sent to `ℓ • [M]` by evaluation at `x₀`
(`TauCeti.HomologicalOrientation.IsCoveredByDiffeomorphisms`). This file proves that every
odd-dimensional sphere `Sⁿ` is `2`-covered, by an explicit family of rotations parametrized by the
sphere itself. This is Proposition 6.34 of Barraud–Damian–Humilière–Oancea, with `ℓ = 2`, for every
odd `n`.

For `p, x ∈ Sⁿ ⊆ E`, let `r_x` be the reflection of `E` in the hyperplane orthogonal to `x`. The
composite `r_x ∘ r_p` (`TauCeti.sphereReflectionRotation`) is a rotation of `E` in the plane of `p`
and `x`, and depends continuously on `x`. Acting on the sphere, it gives a continuous family of
diffeomorphisms `Φ : Sⁿ → Diff(Sⁿ)` (`TauCeti.sphereReflectionDiff`). Since `r_p` sends `p` to `-p`,
evaluating at `p` gives `r_x (-p) = 2 ⟪p, x⟫ • x - p`, the reflection map
`TauCeti.sphereReflectionMap` (`TauCeti.evalAt_comp_sphereReflectionDiff`). For odd `n` this map has
degree `2` at its regular value `p`
(`TauCeti.Manifold.Orientation.degreeAtRegularValue_sphereReflectionMap_self_of_odd`), so it sends
the fundamental class of `Sⁿ` to `2 • [Sⁿ]`
(`TauCeti.Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul`), and `Φ_*[Sⁿ]` is
the required class of `H_n(Diff(Sⁿ); ℤ)`.

Unlike the first proof of Proposition 6.34
(`TauCeti.HomologicalOrientation.exists_isCoveredByDiffeomorphisms_sphere_of_isMulTorsion`), this
argument needs no information on the homotopy groups of `SO(n)`: it is a direct degree
computation, like the paper's second proof through the rotation family `Sⁿ⁻¹ × S¹ → Sⁿ`.

## Main declarations

* `TauCeti.sphereReflectionRotation`: the rotation `r_x ∘ r_p`.
* `TauCeti.sphereReflectionDiff`: the family `x ↦ r_x ∘ r_p` of diffeomorphisms of the sphere.
* `TauCeti.evalAt_comp_sphereReflectionDiff`: its evaluation at `p` is the reflection map.
* `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_two_of_odd`: odd-dimensional
  spheres are `2`-covered by diffeomorphisms, for every orientation, base point and smoothness
  exponent.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.3, Proposition 6.34.
-/

public section

noncomputable section

open CategoryTheory Metric Module Submodule
open scoped Manifold ContDiff RealInnerProductSpace TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The composite `r_x ∘ r_p` of the reflections of `E` in the hyperplanes orthogonal to two
points `p` and `x` of the unit sphere. As a composite of two reflections it is a rotation, of the
plane of `p` and `x` by twice the angle between them. -/
def sphereReflectionRotation (p x : sphere (0 : E) 1) : E ≃ₗᵢ[ℝ] E :=
  (ℝ ∙ (p : E))ᗮ.reflection.trans (ℝ ∙ (x : E))ᗮ.reflection

omit [FiniteDimensional ℝ E] in
theorem sphereReflectionRotation_apply (p x : sphere (0 : E) 1) (y : E) :
    sphereReflectionRotation p x y = (ℝ ∙ (x : E))ᗮ.reflection ((ℝ ∙ (p : E))ᗮ.reflection y) :=
  (rfl)

omit [FiniteDimensional ℝ E] in
/-- The rotation `r_x ∘ r_p` sends `p` to `2 ⟪p, x⟫ • x - p`, the value of the reflection map. -/
@[simp]
theorem sphereReflectionRotation_apply_self (p x : sphere (0 : E) 1) :
    sphereReflectionRotation p x p = sphereReflectionMap p x := by
  rw [sphereReflectionRotation_apply, reflection_orthogonalComplement_singleton_eq_neg,
    reflection_orthogonal_singleton_apply (norm_eq_of_mem_sphere x), coe_sphereReflectionMap,
    inner_neg_right, real_inner_comm]
  module

/-- The rotation `r_x ∘ r_p` depends continuously on `x`, in the operator norm. -/
theorem continuous_sphereReflectionRotation (p : sphere (0 : E) 1) :
    Continuous fun x ↦
      ((sphereReflectionRotation p x).toContinuousLinearEquiv : E →L[ℝ] E) := by
  refine continuous_clm_apply.2 fun y ↦ ?_
  set z := (ℝ ∙ (p : E))ᗮ.reflection y
  have h (x : sphere (0 : E) 1) : sphereReflectionRotation p x y = z - (2 * ⟪(x : E), z⟫) • x :=
    reflection_orthogonal_singleton_apply (mem_sphere_zero_iff_norm.1 x.2) z
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv, h]
  fun_prop

/-- The family of diffeomorphisms `x ↦ r_x ∘ r_p` of the unit sphere, a continuous map from the
sphere to its group of `C^k` diffeomorphisms with the weak Whitney topology. -/
def sphereReflectionDiff (p : sphere (0 : E) 1) (k : ℕ∞ω) :
    C(sphere (0 : E) 1, Diff (𝓡 n) (sphere (0 : E) 1) k) where
  toFun x := LinearIsometryEquiv.unitSphereDiffHom k (sphereReflectionRotation p x)
  continuous_toFun := by
    refine Diffeomorph.continuous_weakWhitney_iff.mpr ?_
    simpa only [LinearIsometryEquiv.unitSphereDiffHom_apply] using
      (continuous_sphereReflectionRotation p).toContMDiffMap_unitSphereDiffeomorph

@[simp]
theorem sphereReflectionDiff_apply (p : sphere (0 : E) 1) (k : ℕ∞ω) (x y : sphere (0 : E) 1) :
    (sphereReflectionDiff (n := n) p k x y : E) = sphereReflectionRotation p x y := by
  simp [sphereReflectionDiff]

/-- Evaluating the family `x ↦ r_x ∘ r_p` at `p` gives the reflection map
`x ↦ 2 ⟪p, x⟫ • x - p`. -/
theorem evalAt_comp_sphereReflectionDiff (p : sphere (0 : E) 1) (k : ℕ∞ω) :
    (Diffeomorph.evalAt p).comp (sphereReflectionDiff (n := n) p k) =
      ⟨sphereReflectionMap p, continuous_sphereReflectionMap p⟩ := by
  ext x : 2
  simp

namespace HomologicalOrientation

variable {m : ℕ}

/-- The statement of `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_two_of_odd`
for the homological orientation of an outward-normal orientation. -/
private theorem isCoveredByDiffeomorphisms_sphere_two_of_sphereOrientation
    [Fact (finrank ℝ E = m + 1 + 1)] (hm : Odd (m + 1)) (oE : Orientation ℝ E (Fin (m + 1 + 1)))
    (k : ℕ∞ω) (x₀ : sphere (0 : E) 1) :
    IsCoveredByDiffeomorphisms
      (oE.sphereOrientation.toHomologicalOrientation finrank_euclideanSpace_fin)
      finrank_euclideanSpace_fin k x₀ 2 := by
  refine .of_mapFundamentalClass
    (oE.sphereOrientation.toHomologicalOrientation finrank_euclideanSpace_fin)
    finrank_euclideanSpace_fin (sphereReflectionDiff x₀ k) ?_
  have := connectedSpace_sphere (E := E) (m + 1)
  -- The evaluation is the reflection map, of degree `2` at its regular value `x₀`.
  have hdeg := Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul
    finrank_euclideanSpace_fin oE.sphereOrientation oE.sphereOrientation
    (f := ⟨sphereReflectionMap x₀, continuous_sphereReflectionMap x₀⟩)
    (isRegularValue_sphereReflectionMap_self x₀)
  rw [ContinuousMap.coe_mk,
    Manifold.Orientation.degreeAtRegularValue_sphereReflectionMap_self_of_odd hm] at hdeg
  rw [evalAt_comp_sphereReflectionDiff, mapFundamentalClass_id]
  exact hdeg

/-- **Odd-dimensional spheres are covered by rotations** (Proposition 6.34 of
Barraud–Damian–Humilière–Oancea). For odd `m + 1`, the unit sphere `Sᵐ⁺¹` of a real inner product
space of dimension `m + 2` is `2`-covered by diffeomorphisms, for every orientation, every base
point `x₀` and every smoothness exponent: the family of rotations `x ↦ r_x ∘ r_{x₀}` sends the
fundamental class to a class of `Hₘ₊₁(Diff(Sᵐ⁺¹); ℤ)` that evaluates at `x₀` to `2 • [Sᵐ⁺¹]`. -/
theorem isCoveredByDiffeomorphisms_sphere_two_of_odd [Fact (finrank ℝ E = m + 1 + 1)]
    (hm : Odd (m + 1))
    (o : HomologicalOrientation (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin (m + 1))) (m + 1))
    (k : ℕ∞ω) (x₀ : sphere (0 : E) 1) :
    o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ 2 := by
  have hE : finrank ℝ E = m + 1 + 1 := Fact.out
  have := connectedSpace_sphere (E := E) (m + 1)
  let oE := (finBasisOfFinrankEq ℝ E hE).orientation
  have h := isCoveredByDiffeomorphisms_sphere_two_of_sphereOrientation hm oE k x₀
  rcases (oE.sphereOrientation.toHomologicalOrientation finrank_euclideanSpace_fin).eq_or_eq_neg
    finrank_euclideanSpace_fin o with rfl | rfl
  · exact h
  · exact isCoveredByDiffeomorphisms_neg.2 h

end HomologicalOrientation

end TauCeti

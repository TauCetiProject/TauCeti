/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Covered
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Degree.SphereDoubleAngle
import TauCeti.Analysis.InnerProductSpace.Reflection

/-!
# Odd-dimensional spheres are `2`-covered by rotations

A compact oriented `d`-manifold `M` is `ℓ`-covered by diffeomorphisms at `x₀` when some class of
`H_d(Diff(M); ℤ)` evaluates at `x₀` to `ℓ • [M]`
(`TauCeti.HomologicalOrientation.IsCoveredByDiffeomorphisms`). This file proves that every
odd-dimensional sphere `Sⁿ⁺¹ ⊆ ℝⁿ⁺²`, `n` even, is `2`-covered by diffeomorphisms, at every base
point, for every orientation and every smoothness exponent
(`TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_two`). This is Proposition 6.34
of Barraud–Damian–Humilière–Oancea, with `ℓ = 2`, by their direct degree argument, with no input
from the homotopy groups of the orthogonal groups.

The covering family consists of rotations. For a base point `p` and a point `x` of the sphere, the
composite `r_x ∘ r_p` of the reflections in the hyperplanes `p^⊥` and `x^⊥`
(`TauCeti.sphereDoubleReflection`) is the rotation in the plane of `p` and `x` by twice the angle
from `p` to `x`, and the identity on the orthogonal complement of that plane. It depends
continuously on `x`, so restricting it to the sphere gives a continuous family of diffeomorphisms
`Sⁿ⁺¹ → Diff(Sⁿ⁺¹)` (`TauCeti.sphereDoubleReflectionDiffeomorph`). Its evaluation at `p` is the
angle-doubling map `x ↦ 2⟪p, x⟫ • x - p` (`TauCeti.sphereDoubleAngle`), which sends the
fundamental class to `(1 + (-1)ⁿ) • [Sⁿ⁺¹] = 2 • [Sⁿ⁺¹]`. The class `A ∈ H_{n+1}(Diff(Sⁿ⁺¹); ℤ)` is
the image of the fundamental class under the family.

These are the rotations of the source's rotation family `T¹_pSⁿ⁺¹ × S¹ → Diff(Sⁿ⁺¹)`, whose
evaluation `TauCeti.sphereRotationFamily` also has degree `2`, parametrized instead by the point
`x` at half the angle of rotation. With this parametrization the parameter space is the sphere
itself, and the degree computation is the comparison of the smooth and the homological degree of a
self-map of the sphere.

## Main definitions

* `TauCeti.sphereDoubleReflection p x`: the linear isometry `r_x ∘ r_p`.
* `TauCeti.sphereDoubleReflectionDiffeomorph p m`: the continuous family `x ↦ r_x ∘ r_p` of
  diffeomorphisms of the unit sphere.

## Main results

* `TauCeti.sphereDoubleReflection_apply_self`: `r_x (r_p p)` is the angle-doubling map at `p`.
* `TauCeti.evalAt_comp_sphereDoubleReflectionDiffeomorph`: the evaluation of the family at `p` is
  the angle-doubling map.
* `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_two`: odd-dimensional spheres
  are `2`-covered by diffeomorphisms.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.3, Proposition 6.34.
-/

public section

noncomputable section

open Metric Module
open scoped Manifold ContDiff RealInnerProductSpace TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The double reflection -/

/-- The **double reflection** `r_x ∘ r_p` at points `p` and `x` of the unit sphere: the reflection
in the hyperplane `p^⊥` followed by the reflection in `x^⊥`. It is the rotation in the plane of `p`
and `x` by twice the angle from `p` to `x`, and it sends `p` to the image of `x` under the
angle-doubling map at `p` (`TauCeti.sphereDoubleReflection_apply_self`). -/
def sphereDoubleReflection (p x : sphere (0 : E) 1) : E ≃ₗᵢ[ℝ] E :=
  (ℝ ∙ (p : E))ᗮ.reflection.trans (ℝ ∙ (x : E))ᗮ.reflection

theorem sphereDoubleReflection_apply (p x : sphere (0 : E) 1) (y : E) :
    sphereDoubleReflection p x y = (ℝ ∙ (x : E))ᗮ.reflection ((ℝ ∙ (p : E))ᗮ.reflection y) :=
  (rfl)

/-- The double reflection at `p` and `x` sends `p` to `2⟪p, x⟫ • x - p`, the image of `x` under the
angle-doubling map at `p`. -/
theorem sphereDoubleReflection_apply_self (p x : sphere (0 : E) 1) :
    sphereDoubleReflection p x p = sphereDoubleAngle p x := by
  rw [sphereDoubleReflection_apply, Submodule.reflection_orthogonalComplement_singleton_eq_neg,
    reflection_orthogonal_singleton_apply (norm_eq_of_mem_sphere x), coe_sphereDoubleAngle,
    inner_neg_right, real_inner_comm]
  module

/-- The double reflection depends continuously on the second point, for the operator norm. -/
theorem continuous_sphereDoubleReflection [FiniteDimensional ℝ E] (p : sphere (0 : E) 1) :
    Continuous fun x ↦ ((sphereDoubleReflection p x).toContinuousLinearEquiv : E →L[ℝ] E) := by
  refine continuous_clm_apply.2 fun y ↦ ?_
  -- Reflecting in `x^⊥` is `z ↦ z - 2⟪x, z⟫ • x` for a unit vector `x`.
  have h (x : sphere (0 : E) 1) :
      ((sphereDoubleReflection p x).toContinuousLinearEquiv : E →L[ℝ] E) y =
        (ℝ ∙ (p : E))ᗮ.reflection y - (2 * ⟪(x : E), (ℝ ∙ (p : E))ᗮ.reflection y⟫) • (x : E) := by
    rw [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      sphereDoubleReflection_apply,
      reflection_orthogonal_singleton_apply (by simp : ‖(x : E)‖ = 1)]
  simp only [h]
  fun_prop

/-! ### The family of diffeomorphisms -/

variable [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E = n + 1 + 1)]

/-- The family `x ↦ r_x ∘ r_p` of diffeomorphisms of the unit sphere, continuous for the weak
Whitney `C^m` topology. -/
def sphereDoubleReflectionDiffeomorph (p : sphere (0 : E) 1) (m : ℕ∞ω) :
    C(sphere (0 : E) 1, sphere (0 : E) 1 ≃ₘ^m⟮𝓡 (n + 1), 𝓡 (n + 1)⟯ sphere (0 : E) 1) where
  toFun x := LinearIsometryEquiv.unitSphereDiffeomorph (sphereDoubleReflection p x) m
  continuous_toFun :=
    Diffeomorph.continuous_weakWhitney_iff.2
      (continuous_sphereDoubleReflection p).toContMDiffMap_unitSphereDiffeomorph

@[simp]
theorem coe_sphereDoubleReflectionDiffeomorph_apply (p : sphere (0 : E) 1) (m : ℕ∞ω)
    (x y : sphere (0 : E) 1) :
    ((sphereDoubleReflectionDiffeomorph (n := n) p m x y : sphere (0 : E) 1) : E) =
      sphereDoubleReflection p x y :=
  LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply _ y

/-- **The evaluation of the family at `p`** is the angle-doubling map at `p`. -/
theorem evalAt_comp_sphereDoubleReflectionDiffeomorph (p : sphere (0 : E) 1) (m : ℕ∞ω) :
    (Diffeomorph.evalAt p).comp (sphereDoubleReflectionDiffeomorph (n := n) p m) =
      ⟨sphereDoubleAngle p, continuous_sphereDoubleAngle p⟩ := by
  refine ContinuousMap.ext fun x ↦ Subtype.ext ?_
  simp [Diffeomorph.evalAt_apply, sphereDoubleReflection_apply_self]

/-! ### Covering odd-dimensional spheres -/

namespace HomologicalOrientation

/-- **Odd-dimensional spheres are `2`-covered by diffeomorphisms** (Proposition 6.34 of
Barraud–Damian–Humilière–Oancea, with `ℓ = 2`). For even `n`, the sphere `Sⁿ⁺¹ ⊆ ℝⁿ⁺²` is
`2`-covered by diffeomorphisms at every base point `x₀`, for every orientation and every
smoothness exponent: the family of rotations `x ↦ r_x ∘ r_{x₀}` sends the fundamental class to a
class of `H_{n+1}(Diff(Sⁿ⁺¹); ℤ)` evaluating at `x₀` to `2 • [Sⁿ⁺¹]`. -/
theorem isCoveredByDiffeomorphisms_sphere_two (hn : Even n)
    (o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
      (EuclideanSpace ℝ (Fin (n + 1))) (n + 1))
    (m : ℕ∞ω) (x₀ : sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :
    o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin m x₀ 2 := by
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 2))) = n + 1 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  refine .of_mapFundamentalClass o finrank_euclideanSpace_fin
    (sphereDoubleReflectionDiffeomorph x₀ m) ?_
  rw [evalAt_comp_sphereDoubleReflectionDiffeomorph, mapFundamentalClass_sphereDoubleAngle,
    mapFundamentalClass_id, hn.neg_one_pow]
  -- `mapFundamentalClass_id` changes the presentation of `H_{n+1}(Sⁿ⁺¹; ℤ)`, and with it the
  -- instance through which `ℤ` acts on it; the two actions of `1 + 1` agree definitionally.
  rfl

end HomologicalOrientation

end TauCeti

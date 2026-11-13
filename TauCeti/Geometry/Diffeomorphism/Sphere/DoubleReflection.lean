/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Covered
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Degree.Sphere.DoubleAngle
import TauCeti.Analysis.InnerProductSpace.Reflection

/-!
# Odd-dimensional spheres are `2`-covered by rotations

A compact oriented `d`-manifold `M` is `ℓ`-covered by diffeomorphisms at `x₀` when some class of
`H_d(Diff(M); ℤ)` evaluates at `x₀` to `ℓ • [M]`
(`TauCeti.HomologicalOrientation.IsCoveredByDiffeomorphisms`). This file proves that every
odd-dimensional sphere `Sⁿ`, the unit sphere of a real inner product space of dimension `n + 1`
with `n` odd, is `2`-covered by diffeomorphisms, at every base point, for every orientation and
every smoothness exponent
(`TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_two_of_odd`). This is
Proposition 6.34 of Barraud–Damian–Humilière–Oancea, with `ℓ = 2`, by their direct degree argument,
with no input from the homotopy groups of the orthogonal groups.

The covering family consists of rotations. For a base point `p` and a point `x` of the sphere, the
composite `r_x ∘ r_p` of the reflections in the hyperplanes `p^⊥` and `x^⊥`
(`TauCeti.sphereDoubleReflection`) is the rotation in the plane of `p` and `x` by twice the angle
from `p` to `x`, and the identity on the orthogonal complement of that plane. It depends
continuously on `x`, so restricting it to the sphere gives a continuous family of diffeomorphisms
`Sⁿ → Diff(Sⁿ)` (`TauCeti.sphereDoubleReflectionDiffeomorph`). Its evaluation at `p` is the
angle-doubling map `x ↦ 2⟪p, x⟫ • x - p` (`TauCeti.sphereDoubleAngle`), which sends the
fundamental class to `(1 + (-1)ⁿ⁺¹) • [Sⁿ] = 2 • [Sⁿ]`. The class `A ∈ H_n(Diff(Sⁿ); ℤ)` is the
image of the fundamental class under the family.

These are the rotations of the source's rotation family `T¹_pSⁿ × S¹ → Diff(Sⁿ)`, whose
evaluation `TauCeti.sphereRotationFamily` also has degree `2`, parametrized instead by the point
`x` at half the angle of rotation. With this parametrization the parameter space is the sphere
itself, and the degree computation is the comparison of the smooth and the homological degree of a
self-map of the sphere.

## Main definitions

* `TauCeti.sphereDoubleReflection p x`: the linear isometry `r_x ∘ r_p`.
* `TauCeti.sphereDoubleReflectionDiffeomorph p m`: the continuous family `x ↦ r_x ∘ r_p` of
  diffeomorphisms of the unit sphere.

## Main results

* `TauCeti.sphereDoubleReflection_apply_left`: `r_x (r_p p)` is the angle-doubling map at `p`.
* `TauCeti.linearEquiv_det_sphereDoubleReflection`: `r_x ∘ r_p` has determinant `1`.
* `TauCeti.evalAt_comp_sphereDoubleReflectionDiffeomorph`: the evaluation of the family at `p` is
  the angle-doubling map.
* `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_two_of_odd`: odd-dimensional
  spheres are `2`-covered by diffeomorphisms.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.3, Proposition 6.34.
-/

public section

noncomputable section

open Metric Module
open scoped Manifold ContDiff RealInnerProductSpace TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

section Ambient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The double reflection -/

/-- The **double reflection** `r_x ∘ r_p` at points `p` and `x` of the unit sphere: the reflection
in the hyperplane `p^⊥` followed by the reflection in `x^⊥`. It is the rotation in the plane of `p`
and `x` by twice the angle from `p` to `x`, and it sends `p` to the image of `x` under the
angle-doubling map at `p` (`TauCeti.sphereDoubleReflection_apply_left`). -/
def sphereDoubleReflection (p x : sphere (0 : E) 1) : E ≃ₗᵢ[ℝ] E :=
  (ℝ ∙ (p : E))ᗮ.reflection.trans (ℝ ∙ (x : E))ᗮ.reflection

theorem sphereDoubleReflection_def (p x : sphere (0 : E) 1) :
    sphereDoubleReflection p x = (ℝ ∙ (p : E))ᗮ.reflection.trans (ℝ ∙ (x : E))ᗮ.reflection :=
  (rfl)

theorem sphereDoubleReflection_apply (p x : sphere (0 : E) 1) (y : E) :
    sphereDoubleReflection p x y = (ℝ ∙ (x : E))ᗮ.reflection ((ℝ ∙ (p : E))ᗮ.reflection y) :=
  (rfl)

/-- The double reflection at `p` and `p` is the identity. -/
@[simp]
theorem sphereDoubleReflection_self (p : sphere (0 : E) 1) :
    sphereDoubleReflection p p = LinearIsometryEquiv.refl ℝ E :=
  Submodule.reflection_trans_reflection _

/-- The inverse of the double reflection `r_x ∘ r_p` is `r_p ∘ r_x`. -/
@[simp]
theorem sphereDoubleReflection_symm (p x : sphere (0 : E) 1) :
    (sphereDoubleReflection p x).symm = sphereDoubleReflection x p := by
  rw [sphereDoubleReflection_def, sphereDoubleReflection_def, LinearIsometryEquiv.symm_trans,
    Submodule.reflection_symm, Submodule.reflection_symm]

/-- The double reflection only depends on the first point up to sign. -/
@[simp]
theorem sphereDoubleReflection_neg_left (p x : sphere (0 : E) 1) :
    sphereDoubleReflection (-p) x = sphereDoubleReflection p x := by
  have h : (ℝ ∙ -(p : E)) = ℝ ∙ (p : E) := by rw [← Set.neg_singleton, Submodule.span_neg]
  simp only [sphereDoubleReflection_def, coe_neg_sphere, h]

/-- The double reflection only depends on the second point up to sign. -/
@[simp]
theorem sphereDoubleReflection_neg_right (p x : sphere (0 : E) 1) :
    sphereDoubleReflection p (-x) = sphereDoubleReflection p x := by
  have h : (ℝ ∙ -(x : E)) = ℝ ∙ (x : E) := by rw [← Set.neg_singleton, Submodule.span_neg]
  simp only [sphereDoubleReflection_def, coe_neg_sphere, h]

/-- The double reflection is a rotation: it has determinant `1`. -/
theorem linearEquiv_det_sphereDoubleReflection [FiniteDimensional ℝ E] (p x : sphere (0 : E) 1) :
    (LinearEquiv.det (sphereDoubleReflection p x).toLinearEquiv : ℝ) = 1 := by
  have hp : (p : E) ≠ 0 := ne_zero_of_mem_unit_sphere p
  have hx : (x : E) ≠ 0 := ne_zero_of_mem_unit_sphere x
  rw [sphereDoubleReflection_def, LinearIsometryEquiv.toLinearEquiv_trans,
    LinearEquiv.det_trans, Units.val_mul,
    linearEquiv_det_reflection_orthogonal_singleton hx,
    linearEquiv_det_reflection_orthogonal_singleton hp]
  norm_num

/-- The double reflection at `p` and `x` sends `p` to `2⟪p, x⟫ • x - p`, the image of `x` under the
angle-doubling map at `p`. -/
theorem sphereDoubleReflection_apply_left (p x : sphere (0 : E) 1) :
    sphereDoubleReflection p x p = sphereDoubleAngle p x := by
  rw [sphereDoubleReflection_apply, Submodule.reflection_orthogonalComplement_singleton_eq_neg,
    reflection_orthogonal_singleton_apply (norm_eq_of_mem_sphere x), coe_sphereDoubleAngle,
    inner_neg_right, real_inner_comm]
  module

/-- The double reflection depends continuously on the second point, for the operator norm. -/
theorem continuous_sphereDoubleReflection (p : sphere (0 : E) 1) :
    Continuous fun x ↦ ((sphereDoubleReflection p x).toContinuousLinearEquiv : E →L[ℝ] E) := by
  -- Reflecting in `x^⊥` is `z ↦ z - 2⟪x, z⟫ • x` for a unit vector `x`.
  have h (x : sphere (0 : E) 1) :
      ((sphereDoubleReflection p x).toContinuousLinearEquiv : E →L[ℝ] E) =
        (ContinuousLinearMap.id ℝ E - (2 : ℝ) • (innerSL ℝ (x : E)).smulRight (x : E)).comp
          ((ℝ ∙ (p : E))ᗮ.reflection.toContinuousLinearEquiv : E →L[ℝ] E) := by
    ext y
    rw [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      sphereDoubleReflection_apply, reflection_orthogonal_singleton_apply (norm_eq_of_mem_sphere x)]
    simp [mul_smul]
  simp only [h]
  fun_prop

/-! ### The family of diffeomorphisms -/

-- The finite dimension makes the sphere compact, which the weak Whitney topology on its
-- diffeomorphisms requires.
variable [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- The family `x ↦ r_x ∘ r_p` of diffeomorphisms of the unit sphere, continuous for the weak
Whitney `C^m` topology. -/
def sphereDoubleReflectionDiffeomorph (p : sphere (0 : E) 1) (m : ℕ∞ω) :
    C(sphere (0 : E) 1, sphere (0 : E) 1 ≃ₘ^m⟮𝓡 n, 𝓡 n⟯ sphere (0 : E) 1) where
  toFun x := LinearIsometryEquiv.unitSphereDiffeomorph (sphereDoubleReflection p x) m
  continuous_toFun :=
    Diffeomorph.continuous_weakWhitney_iff.2
      (continuous_sphereDoubleReflection p).toContMDiffMap_unitSphereDiffeomorph

@[simp]
theorem sphereDoubleReflectionDiffeomorph_apply (p : sphere (0 : E) 1) (m : ℕ∞ω)
    (x : sphere (0 : E) 1) :
    sphereDoubleReflectionDiffeomorph (n := n) p m x =
      LinearIsometryEquiv.unitSphereDiffeomorph (sphereDoubleReflection p x) m :=
  (rfl)

theorem coe_sphereDoubleReflectionDiffeomorph_apply (p : sphere (0 : E) 1) (m : ℕ∞ω)
    (x y : sphere (0 : E) 1) :
    ((sphereDoubleReflectionDiffeomorph (n := n) p m x y : sphere (0 : E) 1) : E) =
      sphereDoubleReflection p x y :=
  LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply _ y

/-- **The evaluation of the family at `p`** is the angle-doubling map at `p`. -/
@[simp]
theorem evalAt_comp_sphereDoubleReflectionDiffeomorph (p : sphere (0 : E) 1) (m : ℕ∞ω) :
    (Diffeomorph.evalAt p).comp (sphereDoubleReflectionDiffeomorph (n := n) p m) =
      ⟨sphereDoubleAngle p, continuous_sphereDoubleAngle p⟩ := by
  refine ContinuousMap.ext fun x ↦ Subtype.ext ?_
  simp [Diffeomorph.evalAt_apply, sphereDoubleReflection_apply_left]

end Ambient

/-! ### Covering odd-dimensional spheres -/

namespace HomologicalOrientation

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- **Odd-dimensional spheres are `2`-covered by diffeomorphisms** (Proposition 6.34 of
Barraud–Damian–Humilière–Oancea, with `ℓ = 2`). For odd `n`, the unit sphere `Sⁿ` of a real inner
product space of dimension `n + 1` is `2`-covered by diffeomorphisms at every base point `x₀`, for
every orientation and every smoothness exponent: the family of rotations `x ↦ r_x ∘ r_{x₀}` sends
the fundamental class to a class of `H_n(Diff(Sⁿ); ℤ)` evaluating at `x₀` to `2 • [Sⁿ]`. -/
theorem isCoveredByDiffeomorphisms_sphere_two_of_odd (hn : Odd n)
    (o : HomologicalOrientation (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n)) n)
    (m : ℕ∞ω) (x₀ : sphere (0 : E) 1) :
    o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin m x₀ 2 := by
  have : NeZero n := ⟨hn.pos.ne'⟩
  refine .of_mapFundamentalClass o finrank_euclideanSpace_fin
    (sphereDoubleReflectionDiffeomorph x₀ m) ?_
  rw [evalAt_comp_sphereDoubleReflectionDiffeomorph, mapFundamentalClass_sphereDoubleAngle,
    mapFundamentalClass_id, hn.add_one.neg_one_pow]
  -- `mapFundamentalClass_id` changes the presentation of `H_n(Sⁿ; ℤ)`, and with it the
  -- instance through which `ℤ` acts on it; the two actions of `1 + 1` agree definitionally.
  rfl

end HomologicalOrientation

end TauCeti

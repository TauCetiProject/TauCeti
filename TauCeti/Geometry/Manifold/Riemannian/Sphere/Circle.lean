/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Gradient
public import TauCeti.Geometry.Manifold.VectorField.Derivation
import TauCeti.Analysis.Complex.Inner
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Laplacian
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Parallelizable

/-!
# The rotation field of the round circle

The unit circle `S¹` is the unit sphere of `ℂ`, with its round metric. Its **rotation field**
`∂ₓ` (`TauCeti.circleRotationField`) is the vector field `z ↦ i z`, the skew field
(`ContinuousLinearMap.sphereSkewField`) of multiplication by `i`, and the derivative `d/dx` in the
angle `z = e^(ix)`. It has unit length (`TauCeti.norm_circleRotationField`) and spans every
tangent line (`TauCeti.eq_inner_circleRotationField_smul`), so the gradient of a function is
`grad f = (∂ₓ f) ∂ₓ` (`TauCeti.mgradient_eq_smul_circleRotationField`). It differentiates the height
functions `⟪a, ·⟫` into height functions, `∂ₓ ⟪a, ·⟫ = ⟪-i a, ·⟫`; at `z = e^(ix)` the imaginary and
real parts are `sin x` and `cos x`, and this is `∂ₓ sin = cos` and `∂ₓ cos = -sin`
(`TauCeti.mvfderiv_im_circleRotationField`, `TauCeti.mvfderiv_re_circleRotationField`).

Since `grad g = (∂ₓ g) ∂ₓ`, the Laplace–Beltrami operator is
`Δ g = ∂ₓ (∂ₓ g) + (∂ₓ g) div ∂ₓ`
(`TauCeti.laplaceBeltrami_eq_mvfderiv_circleRotationField_add`). Comparing this for
`g = ⟪a, ·⟫` with `Δ ⟪a, ·⟫ = -⟪a, ·⟫` (`TauCeti.laplaceBeltrami_inner_coe_sphere`) shows that
`∂ₓ` is divergence free (`TauCeti.divergence_circleRotationField`), and then the Laplace–Beltrami
operator of the circle is `Δ = ∂ₓ²`
(`TauCeti.laplaceBeltrami_eq_vectorFieldDerivation_circleRotationField`).

## Main definitions

* `TauCeti.circleRotationField`: the rotation field `z ↦ i z` of the unit circle.

## Main results

* `TauCeti.eq_inner_circleRotationField_smul`, `TauCeti.mgradient_eq_smul_circleRotationField`:
  tangent vectors and gradients are multiples of the rotation field; for instance `grad Im = Re ∂ₓ`
  (`TauCeti.mgradient_im_eq_re_smul_circleRotationField`).
* `TauCeti.mvfderiv_inner_coe_circleRotationField`: `∂ₓ ⟪a, ·⟫ = ⟪-i a, ·⟫`, and in particular
  `∂ₓ Im = Re` and `∂ₓ Re = -Im` (`TauCeti.mvfderiv_im_circleRotationField`,
  `TauCeti.mvfderiv_re_circleRotationField`).
* `TauCeti.laplaceBeltrami_eq_mvfderiv_circleRotationField_add`:
  `Δ g = ∂ₓ (∂ₓ g) + (∂ₓ g) div ∂ₓ`.
* `TauCeti.divergence_circleRotationField`: the rotation field is divergence free.
* `TauCeti.laplaceBeltrami_eq_vectorFieldDerivation_circleRotationField`: `Δ = ∂ₓ²` on the
  circle.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (the round metric, gradient and divergence).
-/

public section

noncomputable section

open Bundle Metric Module TauCeti.Manifold
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

/-- The **rotation field** `∂ₓ` of the unit circle `S¹ ⊂ ℂ`, the unit vector field `z ↦ i z`
generating the rotations `z ↦ e^(it) z`, that is the skew field of multiplication by `i`. In the
angle `z = e^(ix)` it is the derivative `d/dx`. -/
def circleRotationField :
    Cₛ^∞⟮𝓡 1; EuclideanSpace ℝ (Fin 1), (TangentSpace (𝓡 1) : sphere (0 : ℂ) 1 → Type _)⟯ :=
  -- Multiplication by `i` is skew-symmetric for the real inner product of `ℂ`.
  ⟨(ContinuousLinearMap.mul ℝ ℂ Complex.I).sphereSkewField fun w z ↦ by
      simp only [ContinuousLinearMap.mul_apply', Complex.inner, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
      ring,
    ContinuousLinearMap.contMDiff_sphereSkewField _ _⟩

/-- Read in `ℂ`, the rotation field at `z` is `i z`. -/
@[simp]
theorem mfderiv_coe_circleRotationField (z : sphere (0 : ℂ) 1) :
    mfderiv (𝓡 1) 𝓘(ℝ, ℂ) ((↑) : sphere (0 : ℂ) 1 → ℂ) z (circleRotationField z) =
      Complex.I * (z : ℂ) :=
  ContinuousLinearMap.mfderiv_coe_sphereSkewField _ _ z

/-- Read in `ℂ` through `mvfderiv`, the rotation field at `z` is `i z`. -/
theorem mvfderiv_coe_circleRotationField (z : sphere (0 : ℂ) 1) :
    mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z (circleRotationField z) = Complex.I * z :=
  ContinuousLinearMap.mvfderiv_coe_sphereSkewField _ _ z

/-- The rotation field has unit length. -/
theorem norm_circleRotationField (z : sphere (0 : ℂ) 1) : ‖circleRotationField z‖ = 1 := by
  rw [norm_tangentSpace_sphere, mvfderiv_coe_circleRotationField, norm_mul, Complex.norm_I,
    norm_eq_of_mem_sphere z, one_mul]

/-- The derivative of the height function `⟪a, ·⟫` along the rotation field is the height function
`⟪-i a, ·⟫`. -/
theorem mvfderiv_inner_coe_circleRotationField (a : ℂ) (z : sphere (0 : ℂ) 1) :
    mvfderiv (𝓡 1) (fun q : sphere (0 : ℂ) 1 ↦ ⟪a, (q : ℂ)⟫) z (circleRotationField z) =
      ⟪-Complex.I * a, (z : ℂ)⟫ := by
  rw [mvfderiv_inner_coe_sphere, mvfderiv_coe_circleRotationField, Complex.inner, Complex.inner]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re,
    Complex.conj_im, Complex.neg_re, Complex.neg_im]
  ring

/-- The derivative of the imaginary part along the rotation field is the real part:
`∂ₓ sin x = cos x` in the angle `z = e^(ix)`. -/
theorem mvfderiv_im_circleRotationField (z : sphere (0 : ℂ) 1) :
    mvfderiv (𝓡 1) (fun q : sphere (0 : ℂ) 1 ↦ (q : ℂ).im) z (circleRotationField z) =
      (z : ℂ).re := by
  have h := mvfderiv_inner_coe_circleRotationField Complex.I z
  rw [neg_mul, Complex.I_mul_I, neg_neg, Complex.real_inner_one_left] at h
  simpa only [Complex.real_inner_I_left] using h

/-- The derivative of the real part along the rotation field is minus the imaginary part:
`∂ₓ cos x = -sin x` in the angle `z = e^(ix)`. -/
theorem mvfderiv_re_circleRotationField (z : sphere (0 : ℂ) 1) :
    mvfderiv (𝓡 1) (fun q : sphere (0 : ℂ) 1 ↦ (q : ℂ).re) z (circleRotationField z) =
      -(z : ℂ).im := by
  have h := mvfderiv_inner_coe_circleRotationField 1 z
  rw [mul_one, inner_neg_left, Complex.real_inner_I_left] at h
  simpa only [Complex.real_inner_one_left] using h

/-- The tangent spaces of the circle are lines spanned by the rotation field:
`v = ⟪∂ₓ, v⟫ ∂ₓ`. -/
theorem eq_inner_circleRotationField_smul (z : sphere (0 : ℂ) 1) (v : TangentSpace (𝓡 1) z) :
    v = ⟪circleRotationField z, v⟫ • circleRotationField z := by
  have h : finrank ℝ (TangentSpace (𝓡 1) z) = 1 :=
    (finrank_tangentSpace z).trans finrank_euclideanSpace_fin
  simpa using ((FiniteDimensional.orthonormalBasisSingleton Unit ℝ h (circleRotationField z)
    (norm_circleRotationField z)).sum_repr' v).symm

/-- On the circle the gradient of a function is its derivative along the rotation field times the
rotation field: `grad f = (∂ₓ f) ∂ₓ`. -/
theorem mgradient_eq_smul_circleRotationField (f : sphere (0 : ℂ) 1 → ℝ) (z : sphere (0 : ℂ) 1) :
    mgradient (𝓡 1) f z = mvfderiv (𝓡 1) f z (circleRotationField z) • circleRotationField z := by
  refine (eq_mgradient_iff.2 fun v ↦ ?_).symm
  conv_rhs => rw [eq_inner_circleRotationField_smul z v]
  rw [real_inner_smul_left, map_smul, smul_eq_mul, mul_comm]

/-- The gradient of the imaginary part is the real part times the rotation field:
`grad sin x = cos x ∂ₓ` in the angle `z = e^(ix)`. -/
theorem mgradient_im_eq_re_smul_circleRotationField (z : sphere (0 : ℂ) 1) :
    mgradient (𝓡 1) (fun q : sphere (0 : ℂ) 1 ↦ (q : ℂ).im) z =
      (z : ℂ).re • circleRotationField z := by
  rw [mgradient_eq_smul_circleRotationField, mvfderiv_im_circleRotationField]

/-- On the circle the Laplace–Beltrami operator is computed from the rotation field:
`Δ g = ∂ₓ (∂ₓ g) + (∂ₓ g) div ∂ₓ` wherever `∂ₓ g` is differentiable. -/
theorem laplaceBeltrami_eq_mvfderiv_circleRotationField_add (g : sphere (0 : ℂ) 1 → ℝ)
    (z : sphere (0 : ℂ) 1)
    (hg : MDifferentiableAt (𝓡 1) 𝓘(ℝ)
      (fun y ↦ mvfderiv (𝓡 1) g y (circleRotationField y)) z) :
    laplaceBeltrami (𝓡 1) g z =
      mvfderiv (𝓡 1) (fun y ↦ mvfderiv (𝓡 1) g y (circleRotationField y)) z
          (circleRotationField z) +
        mvfderiv (𝓡 1) g z (circleRotationField z) *
          divergence (𝓡 1) (circleRotationField : Π y : sphere (0 : ℂ) 1, TangentSpace (𝓡 1) y)
            z := by
  have hX : MDifferentiableAt (𝓡 1) (𝓡 1).tangent
      (fun y ↦ (⟨y, circleRotationField y⟩ : TangentBundle (𝓡 1) (sphere (0 : ℂ) 1))) z :=
    circleRotationField.contMDiff.mdifferentiableAt (by simp)
  have hgrad : mgradient (𝓡 1) g = (fun y ↦ mvfderiv (𝓡 1) g y (circleRotationField y)) •
      (circleRotationField : Π y : sphere (0 : ℂ) 1, TangentSpace (𝓡 1) y) :=
    funext fun y ↦ by rw [mgradient_eq_smul_circleRotationField, Pi.smul_apply']
  rw [laplaceBeltrami_def, hgrad, divergence_smul_function (𝓡 1) _ _ z hg hX, add_comm]

/-- The rotation field of the circle is divergence free. -/
@[simp]
theorem divergence_circleRotationField (z : sphere (0 : ℂ) 1) :
    divergence (𝓡 1) (circleRotationField : Π y : sphere (0 : ℂ) 1, TangentSpace (𝓡 1) y) z =
      0 := by
  -- Compare `Δ⟪a, ·⟫ = -⟪a, ·⟫` with `∂ₓ (∂ₓ ⟪a, ·⟫) + (∂ₓ ⟪a, ·⟫) div ∂ₓ` for `a = i z`.
  have ha : -Complex.I * (Complex.I * z) = z := by
    rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
  have h0 : ⟪Complex.I * (z : ℂ), (z : ℂ)⟫ = 0 := by
    rw [real_inner_comm, ← mvfderiv_coe_circleRotationField]
    exact inner_coe_mvfderiv_subtypeVal_sphere z _
  have hd : (fun y ↦ mvfderiv (𝓡 1) (fun q : sphere (0 : ℂ) 1 ↦ ⟪Complex.I * z, (q : ℂ)⟫) y
      (circleRotationField y)) = fun q : sphere (0 : ℂ) 1 ↦ ⟪(z : ℂ), (q : ℂ)⟫ :=
    funext fun y ↦ by rw [mvfderiv_inner_coe_circleRotationField, ha]
  have hg : MDifferentiableAt (𝓡 1) 𝓘(ℝ) (fun q : sphere (0 : ℂ) 1 ↦ ⟪(z : ℂ), (q : ℂ)⟫) z :=
    ((innerSL ℝ (z : ℂ)).contMDiff.comp contMDiff_coe_sphere).mdifferentiableAt one_ne_zero
  have h := laplaceBeltrami_eq_mvfderiv_circleRotationField_add
    (fun q : sphere (0 : ℂ) 1 ↦ ⟪Complex.I * z, (q : ℂ)⟫) z (hd ▸ hg)
  rw [hd, laplaceBeltrami_inner_coe_sphere, mvfderiv_inner_coe_circleRotationField,
    mvfderiv_inner_coe_circleRotationField, ha, real_inner_self_eq_norm_sq,
    norm_eq_of_mem_sphere z, neg_mul Complex.I, inner_neg_left, h0] at h
  linear_combination -h

/-- On the circle the Laplace–Beltrami operator is the square of the rotation field:
`Δ f = ∂ₓ² f`. -/
theorem laplaceBeltrami_eq_vectorFieldDerivation_circleRotationField
    (f : C^∞⟮𝓡 1, sphere (0 : ℂ) 1; ℝ⟯) (z : sphere (0 : ℂ) 1) :
    laplaceBeltrami (𝓡 1) f z =
      vectorFieldDerivation circleRotationField
        (vectorFieldDerivation circleRotationField f) z := by
  have hd : ⇑(vectorFieldDerivation circleRotationField f) =
      fun y ↦ mvfderiv (𝓡 1) f y (circleRotationField y) :=
    funext (ContMDiffSection.vectorFieldDerivation_apply_apply circleRotationField f)
  rw [laplaceBeltrami_eq_mvfderiv_circleRotationField_add f z
      (hd ▸ (vectorFieldDerivation circleRotationField f).contMDiff.mdifferentiableAt (by simp)),
    divergence_circleRotationField, mul_zero, add_zero,
    ContMDiffSection.vectorFieldDerivation_apply_apply, hd]

end TauCeti

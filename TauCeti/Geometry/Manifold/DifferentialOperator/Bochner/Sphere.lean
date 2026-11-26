/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.Bochner.Weighted
public import TauCeti.Geometry.Manifold.DifferentialOperator.FormalAdjoint.Connection
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Circle
import TauCeti.Analysis.Complex.Inner
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Laplacian

/-!
# The weighted Laplacian on the round sphere and the weighted circle

On the unit sphere `Sⁿ` of an `(n + 1)`-dimensional real inner product space take as weight a
height function `φ = ⟪a, ·⟫`. The weighted Laplacian `Δ_φ = Δ + ⟪grad φ, grad ·⟫`
(`TauCeti.smoothWeightedLaplacian`) is formally self-adjoint for the density `e^φ dV`
(`TauCeti.isFormalTranspose_smoothWeightedLaplacian`), and `-Δ_φ` is of Laplace type. Since
`Δφ = -n φ` and `‖grad φ‖² = ‖a‖² - φ²`, its Bochner decomposition is

`-Δ_φ f = ∇*∇ f + (¼ (‖a‖² - φ²) - ½ n φ) f`,  `∇ = d + ½ ⟪grad φ, ·⟫`

(`TauCeti.neg_smoothWeightedLaplacian_apply_eq_of_coe_eq_inner`). In positive dimension `dφ`
vanishes identically only for `a = 0`, so this Bochner connection is compatible with the standard
fibre metric exactly when `a = 0`
(`TauCeti.isMetricCompatible_trivialAddInner_iff_eq_zero_of_coe_eq_inner`).

On the unit circle `S¹ ⊂ ℂ`, with angle `z = e^(ix)` and rotation field `∂ₓ`
(`TauCeti.circleRotationField`), the weight `sin x` is the imaginary part. This gives a formally
self-adjoint operator of Laplace type on a closed manifold whose Bochner connection is not metric,
because the density is not the Riemannian volume:

* the formal transpose of `∂ₓ` for the density `e^(sin x) dx` is `-∂ₓ - cos x`
  (`TauCeti.isFormalTranspose_vectorFieldDerivation_circleRotationField_withDensity_exp`);
* their product is `-Δ_φ = (-∂ₓ - cos x) ∘ ∂ₓ = -∂ₓ² - cos x ∂ₓ`
  (`TauCeti.neg_smoothWeightedLaplacian_eq_comp_vectorFieldDerivation_circleRotationField`),
  formally self-adjoint for the density `e^(sin x) dx`;
* `grad sin = cos ∂ₓ` (`TauCeti.mgradient_im_eq_re_smul_circleRotationField`), so its Bochner
  connection is `d + ½ cos x dx`, with potential `¼ cos² x - ½ sin x`, and it is not metric
  (`TauCeti.not_isMetricCompatible_trivialAddInner_of_coe_eq_im`).

The operator `∂ₓ` here is of Dirac type: on the sections of the trivial line bundle with its
standard fibre metric, `∂ₓ` is of Dirac type
(`TauCeti.isDiracType_alongVectorField_circleRotationField`), and its formal adjoint for the
density `e^(sin x) dx` is `-∂ₓ - cos x`
(`TauCeti.isFormalAdjoint_alongVectorField_circleRotationField_withDensity_exp`). So the product
`(-∂ₓ - cos x) ∘ ∂ₓ = -Δ_φ` is of the form `D* D` for an operator `D` of Dirac type, to which
`TauCeti.IsDiracType.isSectionLaplaceType_comp` applies, although the density defining `D*` is not
the Riemannian volume and the Bochner connection of `D* D` is not metric.

## Main results

* `TauCeti.neg_smoothWeightedLaplacian_apply_eq_of_coe_eq_inner`: the Bochner decomposition of
  `-Δ_φ` for a height weight on the sphere.
* `TauCeti.isMetricCompatible_trivialAddInner_iff_eq_zero_of_coe_eq_inner`: its Bochner connection
  is metric only for `a = 0`.
* `TauCeti.isFormalTranspose_vectorFieldDerivation_circleRotationField_withDensity_exp`,
  `TauCeti.neg_smoothWeightedLaplacian_eq_comp_vectorFieldDerivation_circleRotationField`,
  `TauCeti.not_isMetricCompatible_trivialAddInner_of_coe_eq_im`: the weighted circle.
* `TauCeti.isDiracType_alongVectorField_circleRotationField`,
  `TauCeti.isFormalAdjoint_alongVectorField_circleRotationField_withDensity_exp`: `∂ₓ` on the
  trivial line bundle is of Dirac type, with formal adjoint `-∂ₓ - cos x` for `e^(sin x) dx`.

## References

* P. B. Gilkey, *The spectral geometry of operators of Dirac and Laplace type*, in Handbook of
  Global Analysis, Elsevier, 2008, §2, Lemma 2.1 and the paragraph following it.
-/

public section

noncomputable section

open Bundle Metric Module MeasureTheory TauCeti.Manifold CovariantDerivative
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- **The Bochner decomposition of a weighted Laplacian on the round sphere.** For the weight
`φ = ⟪a, ·⟫`, `-Δ_φ f = ∇*∇ f + (¼ (‖a‖² - φ²) - ½ n φ) f` with `∇ = d + ½ ⟪grad φ, ·⟫`. -/
theorem neg_smoothWeightedLaplacian_apply_eq_of_coe_eq_inner (a : E)
    {φ : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯} (hφ : ⇑φ = fun q : sphere (0 : E) 1 ↦ ⟪a, (q : E)⟫)
    (f : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯) (x : sphere (0 : E) 1) :
    -smoothWeightedLaplacian φ f x =
      (trivialAddInner ⇑((2⁻¹ : ℝ) • smoothGradient (𝓡 n) (sphere (0 : E) 1) φ)).roughLaplacian
          (leviCivitaConnection (𝓡 n) (sphere (0 : E) 1)) f x +
        (4⁻¹ * (‖a‖ ^ 2 - ⟪a, (x : E)⟫ ^ 2) - 2⁻¹ * n * ⟪a, (x : E)⟫) * f x := by
  rw [neg_smoothWeightedLaplacian_apply_eq, hφ, real_inner_self_eq_norm_sq,
    laplaceBeltrami_inner_coe_sphere, norm_mgradient_inner_coe_sphere_sq]
  ring

/-- **The Bochner connection of a weighted Laplacian on the round sphere.** On the unit sphere of
positive dimension, with the weight `φ = ⟪a, ·⟫`, let `∇ = d + ⟪Y, ·⟫` be a connection on the
trivial line bundle and `V` a function such that `-Δ_φ f = ∇*∇ f + V f` for every smooth `f`. Then
`∇` is compatible with the standard fibre metric exactly when `a = 0`. -/
theorem isMetricCompatible_trivialAddInner_iff_eq_zero_of_coe_eq_inner (hn : n ≠ 0) (a : E)
    {φ : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯} (hφ : ⇑φ = fun q : sphere (0 : E) 1 ↦ ⟪a, (q : E)⟫)
    (Y : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯) (V : sphere (0 : E) 1 → ℝ)
    (h : ∀ (f : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯) (x : sphere (0 : E) 1),
      -smoothWeightedLaplacian φ f x =
        (trivialAddInner (Y : Π x : sphere (0 : E) 1, TangentSpace (𝓡 n) x)).roughLaplacian
          (leviCivitaConnection (𝓡 n) (sphere (0 : E) 1)) f x + V x * f x) :
    (trivialAddInner (Y : Π x : sphere (0 : E) 1, TangentSpace (𝓡 n) x)).IsMetricCompatible ↔
      a = 0 := by
  rw [isMetricCompatible_trivialAddInner_iff_of_neg_smoothWeightedLaplacian_eq φ Y V h, hφ,
    forall_mvfderiv_inner_coe_sphere_eq_zero_iff hn]

/-! ### The weighted circle -/

section Circle

attribute [local instance] finrank_real_complex_fact'

/-- **The weighted Laplacian of the circle.** For the weight `φ = sin x`, the imaginary part, the
weighted Laplacian is `Δ_φ = ∂ₓ² + cos x ∂ₓ`, where `ψ = cos x` is the real part. So
`-Δ_φ = (-∂ₓ - cos x) ∘ ∂ₓ` is the product of `∂ₓ` with its formal transpose for the density
`e^(sin x) dx`
(`TauCeti.isFormalTranspose_vectorFieldDerivation_circleRotationField_withDensity_exp`). -/
theorem neg_smoothWeightedLaplacian_eq_comp_vectorFieldDerivation_circleRotationField
    {φ ψ : C^∞⟮𝓡 1, sphere (0 : ℂ) 1; ℝ⟯}
    (hφ : ⇑φ = fun z : sphere (0 : ℂ) 1 ↦ (z : ℂ).im)
    (hψ : ⇑ψ = fun z : sphere (0 : ℂ) 1 ↦ (z : ℂ).re) :
    -smoothWeightedLaplacian φ =
      (-(vectorFieldDerivation circleRotationField :
          C^∞⟮𝓡 1, sphere (0 : ℂ) 1; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓡 1, sphere (0 : ℂ) 1; ℝ⟯) -
        LinearMap.mulLeft ℝ ψ) ∘ₗ
        (vectorFieldDerivation circleRotationField :
          C^∞⟮𝓡 1, sphere (0 : ℂ) 1; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓡 1, sphere (0 : ℂ) 1; ℝ⟯) := by
  ext f z
  simp only [LinearMap.neg_apply, ContMDiffMap.coe_neg, Pi.neg_apply, smoothWeightedLaplacian_apply,
    LinearMap.comp_apply, LinearMap.sub_apply, ContMDiffMap.coe_sub, Pi.sub_apply,
    LinearMap.mulLeft_apply, ContMDiffMap.coe_mul, Pi.mul_apply, Derivation.coeFn_coe]
  rw [laplaceBeltrami_eq_vectorFieldDerivation_circleRotationField, hφ,
    mgradient_im_eq_re_smul_circleRotationField, map_smul, smul_eq_mul, hψ,
    ← ContMDiffSection.vectorFieldDerivation_apply_apply circleRotationField f]
  ring

/-- **The formal transpose of `∂ₓ` for the density `e^(sin x) dx`** is `-∂ₓ - cos x`: with `φ` the
imaginary part and `ψ` the real part of a point of the circle, the transpose of differentiation
along the rotation field for the density `e^φ dV` is `-∂ₓ - ψ`. -/
theorem isFormalTranspose_vectorFieldDerivation_circleRotationField_withDensity_exp
    {φ ψ : C^∞⟮𝓡 1, sphere (0 : ℂ) 1; ℝ⟯}
    (hφ : ⇑φ = fun z : sphere (0 : ℂ) 1 ↦ (z : ℂ).im)
    (hψ : ⇑ψ = fun z : sphere (0 : ℂ) 1 ↦ (z : ℂ).re) :
    (vectorFieldDerivation circleRotationField :
        C^∞⟮𝓡 1, sphere (0 : ℂ) 1; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓡 1, sphere (0 : ℂ) 1; ℝ⟯).IsFormalTranspose
      (-(vectorFieldDerivation circleRotationField :
          C^∞⟮𝓡 1, sphere (0 : ℂ) 1; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓡 1, sphere (0 : ℂ) 1; ℝ⟯) -
        LinearMap.mulLeft ℝ ψ)
      ((riemannianVolume (𝓡 1) (sphere (0 : ℂ) 1)).withDensity
        fun z ↦ ENNReal.ofReal (Real.exp (φ z))) := by
  have h := LinearMap.isFormalTranspose_vectorFieldDerivation_withDensity_exp circleRotationField φ
  -- The rotation field is divergence free and `∂ₓ φ = ψ`.
  have hdiv : smoothDivergence (𝓡 1) (sphere (0 : ℂ) 1) circleRotationField +
      vectorFieldDerivation circleRotationField φ = ψ := by
    ext z
    rw [ContMDiffMap.coe_add, Pi.add_apply, smoothDivergence_apply, divergence_circleRotationField,
      zero_add, ContMDiffSection.vectorFieldDerivation_apply_apply, hφ, hψ,
      mvfderiv_im_circleRotationField]
  rwa [hdiv] at h

/-- **A formally self-adjoint operator of Laplace type on the circle whose Bochner connection is
not metric.** On the unit circle, with the weight `φ = sin x` given by the imaginary part, the
operator `-Δ_φ = -∂ₓ² - cos x ∂ₓ`
(`TauCeti.neg_smoothWeightedLaplacian_eq_comp_vectorFieldDerivation_circleRotationField`) is
formally self-adjoint for the density `e^(sin x) dx`
(`TauCeti.isFormalTranspose_smoothWeightedLaplacian`), but no connection `d + ⟪Y, ·⟫` with
`-Δ_φ = ∇*∇ + V` is compatible with the standard fibre metric. Its Bochner connection is
`d + ½ cos x dx` (`TauCeti.mgradient_im_eq_re_smul_circleRotationField`). -/
theorem not_isMetricCompatible_trivialAddInner_of_coe_eq_im
    {φ : C^∞⟮𝓡 1, sphere (0 : ℂ) 1; ℝ⟯}
    (hφ : ⇑φ = fun z : sphere (0 : ℂ) 1 ↦ (z : ℂ).im)
    (Y : Cₛ^∞⟮𝓡 1; EuclideanSpace ℝ (Fin 1),
      (TangentSpace (𝓡 1) : sphere (0 : ℂ) 1 → Type _)⟯) (V : sphere (0 : ℂ) 1 → ℝ)
    (h : ∀ (f : C^∞⟮𝓡 1, sphere (0 : ℂ) 1; ℝ⟯) (z : sphere (0 : ℂ) 1),
      -smoothWeightedLaplacian φ f z =
        (trivialAddInner (Y : Π z : sphere (0 : ℂ) 1, TangentSpace (𝓡 1) z)).roughLaplacian
          (leviCivitaConnection (𝓡 1) (sphere (0 : ℂ) 1)) f z + V z * f z) :
    ¬(trivialAddInner (Y : Π z : sphere (0 : ℂ) 1, TangentSpace (𝓡 1) z)).IsMetricCompatible :=
  (isMetricCompatible_trivialAddInner_iff_eq_zero_of_coe_eq_inner one_ne_zero Complex.I
    (hφ.trans (funext fun _ ↦ (Complex.real_inner_I_left _).symm)) Y V h).not.2
    Complex.I_ne_zero

/-! ### `∂ₓ` as an operator of Dirac type on the trivial line bundle -/

/-- **`∂ₓ` is of Dirac type.** On the sections of the trivial line bundle of the circle, with its
standard fibre metric, differentiation along the rotation field, `∂ₓ = d_{∂ₓ}`, is of Dirac type:
its principal symbol `ξ(∂ₓ)` satisfies `ξ(∂ₓ)² = ‖ξ‖²`. -/
theorem isDiracType_alongVectorField_circleRotationField :
    IsDiracType ⟨(trivial ℝ).alongVectorField circleRotationField,
      (trivial ℝ).alongVectorField_mem_differentialOperators_one circleRotationField⟩ :=
  (trivial ℝ).isDiracType_alongVectorField circleRotationField
    fun z _ v ↦ eq_inner_circleRotationField_smul z v

/-- **The formal adjoint of `∂ₓ` for the density `e^(sin x) dx`**, on the sections of the trivial
line bundle of the circle: with `φ` the imaginary part and `ψ` the real part of a point of the
circle, the formal adjoint of `∂ₓ` for the density `e^φ dV` is `-∂ₓ - ψ`, that is `-∂ₓ - cos x`. -/
theorem isFormalAdjoint_alongVectorField_circleRotationField_withDensity_exp
    {φ ψ : C^∞⟮𝓡 1, sphere (0 : ℂ) 1; ℝ⟯}
    (hφ : ⇑φ = fun z : sphere (0 : ℂ) 1 ↦ (z : ℂ).im)
    (hψ : ⇑ψ = fun z : sphere (0 : ℂ) 1 ↦ (z : ℂ).re) :
    ((trivial ℝ).alongVectorField circleRotationField).IsFormalAdjoint
      (-(trivial ℝ).alongVectorField circleRotationField -
        Algebra.lsmul ℝ ℝ Cₛ^∞⟮𝓡 1; ℝ, Bundle.Trivial (sphere (0 : ℂ) 1) ℝ⟯ ψ)
      ((riemannianVolume (𝓡 1) (sphere (0 : ℂ) 1)).withDensity
        fun z ↦ ENNReal.ofReal (Real.exp (φ z))) := by
  have hcov : (trivial (I := 𝓡 1) (M := sphere (0 : ℂ) 1) ℝ).IsMetricCompatible := by
    rw [← trivialAddInner_zero, isMetricCompatible_trivialAddInner_iff]
  -- The rotation field is divergence free and `∂ₓ φ = ψ`.
  refine hcov.isFormalAdjoint_alongVectorField_withDensity_exp _ φ fun τ z ↦ ?_
  rw [hφ, mvfderiv_im_circleRotationField, divergence_circleRotationField, zero_add]
  simp [hψ]

end Circle

end TauCeti

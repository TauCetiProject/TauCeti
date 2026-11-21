/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import TauCeti.Geometry.Manifold.DifferentialOperator.FormalAdjoint.Basic
public import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.DifferentialOperator
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support

/-!
# The formal adjoint of a covariant derivative along a vector field

Let `∇` be a smooth connection on a vector bundle `V` over a smooth manifold `M`, and let `X` be a
smooth vector field. The covariant derivative along `X`, `∇_X σ = ∇σ(X)`
(`CovariantDerivative.alongVectorField`), is a first-order differential operator on the smooth
sections of `V` (`CovariantDerivative.alongVectorField_mem_differentialOperators_one`).

If `M` is a Riemannian manifold without boundary, `V` carries a smooth fibre metric and `∇` is
compatible with it, then with respect to the Riemannian volume `dV` the formal adjoint of `∇_X` is

`(∇_X)* = -∇_X - div X`

(`CovariantDerivative.IsMetricCompatible.isFormalAdjoint_alongVectorField`). Indeed metric
compatibility gives `X ⟪σ, τ⟫ = ⟪∇_X σ, τ⟫ + ⟪σ, ∇_X τ⟫`, and integrating by parts against the
divergence, `∫ X(f) dV = -∫ f div X dV` for compactly supported `f`
(`TauCeti.Manifold.integral_mul_divergence`), moves `∇_X` to the other side. For the trivial line
bundle with the flat connection this is the formula `-X - div X` for the formal transpose of a
vector field acting on functions. Merely negating `∇_X` is wrong unless `X` is divergence-free.

## Main results

* `CovariantDerivative.IsMetricCompatible.isFormalAdjoint_alongVectorField`,
  `CovariantDerivative.IsMetricCompatible.formalAdjoint_alongVectorField_apply`: the formal
  adjoint of `∇_X` for the Riemannian volume is `-∇_X - div X`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989),
  Chapter II, §8 (formal adjoints of connections and the connection Laplacian).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2 (the divergence theorem).
-/

public section

noncomputable section

open MeasureTheory Bundle TauCeti TauCeti.Manifold
open scoped ContDiff Manifold RealInnerProductSpace

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)

/-! ### The formal adjoint for the Riemannian volume -/

section Adjoint

variable [FiniteDimensional ℝ E] [T2Space M] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]
  {cov : CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]

local instance : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

/-- **The formal adjoint of a covariant derivative along a vector field.** For a metric connection
`∇` on a Riemannian vector bundle over a Riemannian manifold without boundary, and a smooth vector
field `X`, an operator `Q` acting by `Q τ = -∇_X τ - (div X) τ` is the formal adjoint of `∇_X` with
respect to the Riemannian volume: `∫ ⟪∇_X σ, τ⟫ dV = ∫ ⟪σ, Q τ⟫ dV` whenever `σ` or `τ` has compact
support. -/
theorem IsMetricCompatible.isFormalAdjoint_alongVectorField (hcov : cov.IsMetricCompatible)
    {Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯}
    (hQ : ∀ τ x, Q τ x = -cov τ x (X x) - divergence I (fun y ↦ X y) x • τ x) :
    (cov.alongVectorField X).IsFormalAdjoint Q (riemannianVolume I M) := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F)
    (V := V)
  refine LinearMap.isFormalAdjoint_iff.2 fun σ τ hστ ↦ ?_
  set μ := riemannianVolume I M
  set f : M → ℝ := fun x ↦ ⟪σ x, τ x⟫
  have hfc : HasCompactSupport f := ContMDiffSection.hasCompactSupport_inner hστ
  have hdiv := X.contMDiff_divergence
  have h₁ : Integrable (fun x ↦ ⟪cov.alongVectorField X σ x, τ x⟫) μ :=
    LinearMap.integrable_inner_apply_left (cov.tsupport_alongVectorField_apply_subset X) hστ
  have h₂ : Integrable (fun x ↦ ⟪σ x, cov.alongVectorField X τ x⟫) μ :=
    LinearMap.integrable_inner_apply_right (cov.tsupport_alongVectorField_apply_subset X) hστ
  have h₃ : Integrable (fun x ↦ f x * divergence I (fun y ↦ X y) x) μ :=
    ((ContMDiffSection.continuous_inner σ τ).mul hdiv.continuous).integrable_of_hasCompactSupport
      hfc.mul_right
  -- Metric compatibility and integration by parts against the divergence:
  -- `∫ ⟪∇_X σ, τ⟫ + ⟪σ, ∇_X τ⟫ = ∫ X ⟪σ, τ⟫ = -∫ ⟪σ, τ⟫ div X`.
  have hparts : ∫ x, ⟪cov.alongVectorField X σ x, τ x⟫ ∂μ +
      ∫ x, ⟪σ x, cov.alongVectorField X τ x⟫ ∂μ = -∫ x, f x * divergence I (fun y ↦ X y) x ∂μ := by
    rw [← integral_add h₁ h₂, integral_mul_divergence
      ((σ.contMDiff.inner_bundle τ.contMDiff).of_le (by simp)) hfc
      ((by simpa using X.contMDiff : ContMDiff I I.tangent ∞ (T% fun x ↦ X x)).of_le (by simp)),
      neg_neg]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp only [alongVectorField_apply]
    exact (hcov.mvfderiv_inner_eq (fun y ↦ X y) σ.mdifferentiableAt τ.mdifferentiableAt).symm
  calc ∫ x, ⟪cov.alongVectorField X σ x, τ x⟫ ∂μ =
        -∫ x, ⟪σ x, cov.alongVectorField X τ x⟫ ∂μ -
          ∫ x, f x * divergence I (fun y ↦ X y) x ∂μ := by
        linarith
    _ = ∫ x, (-⟪σ x, cov.alongVectorField X τ x⟫ - f x * divergence I (fun y ↦ X y) x) ∂μ := by
        have h := integral_sub h₂.neg h₃
        simp only [Pi.neg_apply, integral_neg] at h
        linarith
    _ = ∫ x, ⟪σ x, Q τ x⟫ ∂μ := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        simp only [hQ, alongVectorField_apply, inner_sub_right, inner_neg_right,
          real_inner_smul_right, f]
        ring

/-- **The formal adjoint of a covariant derivative along a vector field.** For a metric connection
on a Riemannian vector bundle over a Riemannian manifold without boundary, the formal adjoint of
`∇_X` with respect to the Riemannian volume is `-∇_X - div X`. -/
theorem IsMetricCompatible.formalAdjoint_alongVectorField_apply (hcov : cov.IsMetricCompatible)
    (τ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    (cov.alongVectorField X).formalAdjoint (riemannianVolume I M) τ x =
      -cov τ x (X x) - divergence I (fun y ↦ X y) x • τ x := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F)
    (V := V)
  let d : C^∞⟮I, M; ℝ⟯ := ⟨divergence I fun y ↦ X y, X.contMDiff_divergence⟩
  have hd : ⇑d = divergence I fun y ↦ X y := ContMDiffMap.coeFn_mk _ _
  have h := hcov.isFormalAdjoint_alongVectorField X
    (Q := -cov.alongVectorField X - Algebra.lsmul ℝ ℝ Cₛ^∞⟮I; F, V⟯ d) fun τ x ↦ by simp [hd]
  rw [h.formalAdjoint_eq]
  simp [hd]

end Adjoint

end CovariantDerivative

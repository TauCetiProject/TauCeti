/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearTensor.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearTensor.SMul

/-!
# The divergence of a field of bilinear forms

Let `∇` be a connection on the tangent bundle of a Riemannian manifold and let `b` be a field of
bilinear forms on the tangent spaces. The divergence of `b` is the field of covectors

`(div b)(w) = ∑ᵢ (∇_{eᵢ} b)(eᵢ, w)`,

the contraction of the differentiation slot of `∇b` (`CovariantDerivative.derivBilinearTensor`)
against its first argument, for any orthonormal basis `eᵢ` of the tangent space. In index notation
`(div b)_j = ∇^i b_ij`. For a symmetric field `b` the choice of the contracted argument does not
matter. Divergences of symmetric two-tensors appear in the contracted second Bianchi identity
`2 div Ric = d Scal` and, applied twice, in the first variation of scalar curvature.

## Main definitions and results

* `CovariantDerivative.divBilinearTensor`: the divergence of a field of bilinear forms.
* `CovariantDerivative.divBilinearTensor_apply_eq_sum`: its values in an orthonormal basis.
* `CovariantDerivative.divBilinearTensor_congr`: the divergence depends only on the connection on
  differentiable vector fields.
* `CovariantDerivative.divBilinearTensor_const_smul`: homogeneity.
* `CovariantDerivative.divBilinearTensor_eq_zero_of_derivBilinearTensor_eq_zero`: the divergence
  vanishes where the field is parallel.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Ch. 5 and 7.
* P. Topping, *Lectures on the Ricci Flow*, LMS Lecture Note Series 325, CUP (2006), Section 2.1.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  (b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) {x : M}

/-- The **divergence of a field of bilinear forms** `b` at `x`: the covector
`w ↦ tr_g ((u, v) ↦ (∇_v b)(u, w))`, contracting the direction of differentiation against the first
argument of `b`. Its value in an orthonormal basis is
`CovariantDerivative.divBilinearTensor_apply_eq_sum`. -/
def divBilinearTensor (x : M) : TangentSpace I x →L[ℝ] ℝ :=
  LinearMap.BilinMap.metricTrace <| ContinuousLinearMap.toLinearMap₁₂ <|
    (ContinuousLinearMap.flipₗᵢ ℝ (TangentSpace I x) (TangentSpace I x)
      ℝ).toContinuousLinearEquiv.toContinuousLinearMap ∘L cov.derivBilinearTensor b x

/-- In an orthonormal basis `eᵢ`, the divergence of `b` is `(div b)(w) = ∑ᵢ (∇_{eᵢ} b)(eᵢ, w)`. -/
theorem divBilinearTensor_apply_eq_sum {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ (TangentSpace I x)) (w : TangentSpace I x) :
    cov.divBilinearTensor b x w = ∑ i, cov.derivBilinearTensor b x (e i) w (e i) := by
  rw [divBilinearTensor, LinearMap.BilinMap.metricTrace_eq_sum _ e, sum_apply]
  simp [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]

/-- The divergence at `x` depends only on the values at `x` of the connection on vector fields
differentiable there. In particular all Levi-Civita connections of a metric compute the same
divergence. -/
theorem divBilinearTensor_congr {cov' : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (h : ∀ ⦃Y : Π y : M, TangentSpace I y⦄, MDiffAt (T% Y) x → cov Y x = cov' Y x) :
    cov.divBilinearTensor b x = cov'.divBilinearTensor b x := by
  rw [divBilinearTensor, divBilinearTensor, cov.derivBilinearTensor_congr h]

/-- The divergence of `b` vanishes at a point where `b` is parallel. -/
theorem divBilinearTensor_eq_zero_of_derivBilinearTensor_eq_zero
    (h : cov.derivBilinearTensor b x = 0) : cov.divBilinearTensor b x = 0 := by
  ext w
  simp [cov.divBilinearTensor_apply_eq_sum b (stdOrthonormalBasis ℝ (TangentSpace I x)), h]

/-- The zero field of bilinear forms has zero divergence. -/
@[simp]
theorem divBilinearTensor_zero :
    cov.divBilinearTensor (0 : (y : M) → TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x = 0 :=
  cov.divBilinearTensor_eq_zero_of_derivBilinearTensor_eq_zero 0 cov.derivBilinearTensor_zero

/-- The divergence of a field of bilinear forms commutes with constant real scaling. -/
@[simp]
theorem divBilinearTensor_const_smul (c : ℝ) :
    cov.divBilinearTensor (c • b) x = c • cov.divBilinearTensor b x := by
  ext w
  simp [divBilinearTensor_apply_eq_sum _ _ (stdOrthonormalBasis ℝ (TangentSpace I x)),
    Finset.mul_sum]

end CovariantDerivative

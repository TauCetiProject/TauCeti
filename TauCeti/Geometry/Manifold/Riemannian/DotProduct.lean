/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.Quotient
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Descent
import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# The dot-product metric on `ι → ℝ` and its quotients by discrete subgroups

The space `ι → ℝ` of real functions on a finite type carries the sup norm, which is not an inner
product norm, so no Riemannian metric is installed on it by instance. This file defines its
Euclidean metric `⟪v, w⟫ = v ⬝ᵥ w = Σ_i v_i w_i` (`TauCeti.dotProductMetric`), the same at every
point, as the pullback of the metric of `EuclideanSpace ℝ ι` along the identification
`(ι → ℝ) ≃ EuclideanSpace ℝ ι`.

Translations preserve this metric, so it descends to the quotient `(ι → ℝ) ⧸ N` by any discrete
subgroup `N` (`AddSubgroup.quotientDotProductMetric`), with its manifold structure of a quotient by
a discrete subgroup. The tangent spaces of the quotient are read in its charts, which are local
inverses of the projection, so the differential of the projection is the identity of `ι → ℝ`
(`AddSubgroup.mfderiv_quotientMk`) and the descended metric is again the dot product
(`AddSubgroup.quotientDotProductMetric_inner`). With these metrics the projection is a local
Riemannian isometry (`AddSubgroup.isLocalRiemannianIsometry_quotientMk`).

For any manifold modelled on `ι → ℝ` whose metric is the dot product in its charts, such as
`ι → ℝ` itself and its quotients by discrete subgroups, the gradient of a function is the vector of
its partial derivatives, `grad f x = (df_x(e_i))_i` for the standard basis vectors `e_i`
(`TauCeti.Manifold.mgradient_eq_of_inner_eq_dotProduct`).

Examples of such quotients are the flat tori `ℝⁿ / ℤⁿ` and the flat cylinders, such as the
quotient of `ℝⁿ` by the diagonal integers `ℤ (1, …, 1)`, a circle times `ℝⁿ⁻¹`.

## Main definitions

* `TauCeti.dotProductMetric ι`: the Euclidean metric `⟪v, w⟫ = v ⬝ᵥ w` on `ι → ℝ`.
* `AddSubgroup.quotientDotProductMetric N`: the metric descended to `(ι → ℝ) ⧸ N`.

## Main results

* `TauCeti.dotProductMetric_inner`, `AddSubgroup.quotientDotProductMetric_inner`: both metrics
  are the dot product.
* `AddSubgroup.isLocalRiemannianIsometry_quotientMk`: the projection is a local Riemannian
  isometry.
* `TauCeti.Manifold.mgradient_eq_of_inner_eq_dotProduct`: for the dot-product metric, the gradient
  is the vector of partial derivatives.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2 (Riemannian coverings and flat quotients of Euclidean space).
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable (ι : Type*) [Fintype ι]

/-- The **dot-product metric** `⟪v, w⟫ = v ⬝ᵥ w = Σ_i v_i w_i` on `ι → ℝ`, the same at every point:
the pullback of the Euclidean metric of `EuclideanSpace ℝ ι` along the identification
`(ι → ℝ) ≃ EuclideanSpace ℝ ι`. -/
def dotProductMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, ι → ℝ) ∞ (ι → ℝ)
      (fun x : ι → ℝ ↦ TangentSpace 𝓘(ℝ, ι → ℝ) x) :=
  (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := 𝓘(ℝ, EuclideanSpace ℝ ι))
    (n := ∞) (F := EuclideanSpace ℝ ι)
    (V := fun x : EuclideanSpace ℝ ι ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ ι) x)).pullback
    (EuclideanSpace.equiv ι ℝ).symm (EuclideanSpace.equiv ι ℝ).symm.contDiff.contMDiff
    fun x ↦ by
      rw [ContinuousLinearEquiv.mfderiv_eq]
      exact (EuclideanSpace.equiv ι ℝ).symm.injective

/-- The dot-product metric is the dot product of the tangent vectors, read in `ι → ℝ`. -/
@[simp]
theorem dotProductMetric_inner (x : ι → ℝ) (v w : TangentSpace 𝓘(ℝ, ι → ℝ) x) :
    (dotProductMetric ι).inner x v w = dotProduct (v : ι → ℝ) w := by
  rw [dotProductMetric, ContMDiffRiemannianMetric.pullback_ofIsContMDiffRiemannianBundle_inner,
    ContinuousLinearEquiv.mfderiv_eq]
  -- the tangent vectors are vectors of `ι → ℝ`, and their images are the same vectors of
  -- `EuclideanSpace ℝ ι`
  have h (v w : ι → ℝ) :
      inner ℝ (((EuclideanSpace.equiv ι ℝ).symm : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι) v)
        (((EuclideanSpace.equiv ι ℝ).symm : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι) w) =
        dotProduct v w := by
    simp [PiLp.inner_apply, dotProduct, mul_comm]
  exact h v w

end TauCeti

namespace AddSubgroup

variable {ι : Type*} [Fintype ι] (N : AddSubgroup (ι → ℝ)) [DiscreteTopology N]

/-- The dot-product metric is compatible with the projection onto `(ι → ℝ) ⧸ N`: the differential
of the projection is the identity at every point. -/
private theorem dotProductMetric_inner_eq_of_mk_eq (x x' : ι → ℝ)
    (v w : TangentSpace 𝓘(ℝ, ι → ℝ) x) (v' w' : TangentSpace 𝓘(ℝ, ι → ℝ) x')
    (_ : (x : (ι → ℝ) ⧸ N) = x')
    (hv : mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (QuotientAddGroup.mk : (ι → ℝ) → (ι → ℝ) ⧸ N) x v =
      mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (QuotientAddGroup.mk : (ι → ℝ) → (ι → ℝ) ⧸ N) x' v')
    (hw : mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (QuotientAddGroup.mk : (ι → ℝ) → (ι → ℝ) ⧸ N) x w =
      mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (QuotientAddGroup.mk : (ι → ℝ) → (ι → ℝ) ⧸ N) x' w') :
    (TauCeti.dotProductMetric ι).inner x v w = (TauCeti.dotProductMetric ι).inner x' v' w' := by
  simp only [mfderiv_quotientMk] at hv hw
  rw [TauCeti.dotProductMetric_inner, TauCeti.dotProductMetric_inner]
  -- `hv` and `hw` state `v = v'` and `w = w'`, through the identity map of `ι → ℝ`
  exact congrArg₂ (fun a b : ι → ℝ ↦ dotProduct a b) hv hw

/-- The **dot-product metric of a quotient** of `ι → ℝ` by a discrete subgroup `N`: the
dot-product metric of `ι → ℝ`, descended along the projection `ι → ℝ → (ι → ℝ) ⧸ N`. -/
def quotientDotProductMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, ι → ℝ) ∞ (ι → ℝ)
      (fun y : (ι → ℝ) ⧸ N ↦ TangentSpace 𝓘(ℝ, ι → ℝ) y) :=
  (TauCeti.dotProductMetric ι).descend N.isLocalDiffeomorph_quotientMk
    QuotientAddGroup.mk_surjective (dotProductMetric_inner_eq_of_mk_eq N)

/-- The metric of `(ι → ℝ) ⧸ N` is the dot product of the tangent vectors, read in the charts of
the quotient. -/
@[simp]
theorem quotientDotProductMetric_inner (y : (ι → ℝ) ⧸ N) (v w : TangentSpace 𝓘(ℝ, ι → ℝ) y) :
    N.quotientDotProductMetric.inner y v w = dotProduct (v : ι → ℝ) w := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  have h := (TauCeti.dotProductMetric ι).descend_inner_mfderiv N.isLocalDiffeomorph_quotientMk
    QuotientAddGroup.mk_surjective (dotProductMetric_inner_eq_of_mk_eq N) x v w
  rw [mfderiv_quotientMk] at h
  exact h.trans (TauCeti.dotProductMetric_inner ι x v w)

/-- **The projection onto `(ι → ℝ) ⧸ N` is a local Riemannian isometry** for the dot-product
metrics. -/
theorem isLocalRiemannianIsometry_quotientMk :
    letI : RiemannianBundle (fun x : ι → ℝ ↦ TangentSpace 𝓘(ℝ, ι → ℝ) x) :=
      ⟨(TauCeti.dotProductMetric ι).toRiemannianMetric⟩
    letI : RiemannianBundle (fun y : (ι → ℝ) ⧸ N ↦ TangentSpace 𝓘(ℝ, ι → ℝ) y) :=
      ⟨N.quotientDotProductMetric.toRiemannianMetric⟩
    TauCeti.IsLocalRiemannianIsometry 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ)
      (QuotientAddGroup.mk : (ι → ℝ) → (ι → ℝ) ⧸ N) :=
  (TauCeti.dotProductMetric ι).isLocalRiemannianIsometry_descend N.isLocalDiffeomorph_quotientMk
    QuotientAddGroup.mk_surjective (dotProductMetric_inner_eq_of_mk_eq N)

end AddSubgroup

namespace TauCeti.Manifold

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ι → ℝ) M] [IsManifold 𝓘(ℝ, ι → ℝ) 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, ι → ℝ) x)]

/-- **The gradient for the dot-product metric.** If the metric of a manifold modelled on `ι → ℝ`
is the dot product at `x`, the gradient of a function at `x` is the vector of its partial
derivatives `df_x(e_i)` along the standard basis vectors `e_i`. -/
theorem mgradient_eq_of_inner_eq_dotProduct {x : M}
    (hx : ∀ v w : TangentSpace 𝓘(ℝ, ι → ℝ) x, inner ℝ v w = dotProduct (v : ι → ℝ) w)
    (f : M → ℝ) :
    mgradient 𝓘(ℝ, ι → ℝ) f x = fun i ↦ mvfderiv 𝓘(ℝ, ι → ℝ) f x (Pi.single i 1) := by
  refine (eq_mgradient_iff.2 fun v ↦ (hx _ v).trans ?_).symm
  -- the values on the standard basis represent the derivative under the dot product
  have h (L : (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) : dotProduct (fun i ↦ L (Pi.single i 1)) v = L v := by
    have hL : (fun i ↦ L (Pi.single i 1)) = (dotProductEquiv ℝ ι).symm L.toLinearMap := by
      funext i
      simp only [dotProductEquiv_symm_apply, LinearMap.single_apply, ContinuousLinearMap.coe_coe]
    rw [hL, ← dotProductEquiv_apply_apply, LinearEquiv.apply_symm_apply,
      ContinuousLinearMap.coe_coe]
  exact h (mvfderiv 𝓘(ℝ, ι → ℝ) f x) v

end TauCeti.Manifold

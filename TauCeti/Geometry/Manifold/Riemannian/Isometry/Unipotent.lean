/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Unipotent differentials of Riemannian isometries at fixed points

Let `x` be a fixed point of a map `f : M → M` whose differential `df_x` preserves the inner product
of `T_x M`, for instance a fixed point of a Riemannian isometry. Read as an endomorphism of `T_x M`
(`TauCeti.fixedPointDerivative`), `df_x` is an isometry of the inner product
(`TauCeti.isIsometry_fixedPointDerivative`,
`TauCeti.RiemannianIsometry.isIsometry_fixedPointDerivative`). An inner product is anisotropic,
so if `df_x - 1` is nilpotent, then `df_x = 1`
(`TauCeti.fixedPointDerivative_eq_one_of_isNilpotent_sub_one`,
`TauCeti.RiemannianIsometry.fixedPointDerivative_eq_one_of_isNilpotent_sub_one`).

This is a pointwise obstruction to invariant metrics. A diffeomorphism with a fixed point at which
its differential is unipotent and not the identity, such as the shear `(q, p) ↦ (q + p, p)` of
`ℝ²`, is an isometry of no Riemannian metric whatsoever: neither smoothness of the metric nor
completeness or compactness enters.
-/

public section

open Bundle
open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- At a fixed point `x` of `f` at which `df_x` preserves the inner product, the fixed-point
derivative preserves the inner product of `T_x M`. -/
theorem isIsometry_fixedPointDerivative {f : M → M} (x : {x // f x = x})
    (hf : ∀ v w : TangentSpace I x.1,
      inner ℝ (mfderiv I I f x.1 v) (mfderiv I I f x.1 w) = inner ℝ v w) :
    BilinForm.IsIsometry (innerₗ (TangentSpace I x.1)) (fixedPointDerivative I f x) :=
  BilinForm.isIsometry_iff.mpr fun v w ↦ by
    rw [innerₗ_apply_apply, innerₗ_apply_apply, fixedPointDerivative_apply,
      fixedPointDerivative_apply, ← hf v w]
    exact inner_tangentSpace_congr x.2.symm rfl rfl

/-- At a fixed point `x` of `f` at which `df_x` preserves the inner product, a unipotent
fixed-point derivative is the identity. -/
theorem fixedPointDerivative_eq_one_of_isNilpotent_sub_one {f : M → M} (x : {x // f x = x})
    (hf : ∀ v w : TangentSpace I x.1,
      inner ℝ (mfderiv I I f x.1 v) (mfderiv I I f x.1 w) = inner ℝ v w)
    (h : IsNilpotent (fixedPointDerivative I f x - 1)) :
    fixedPointDerivative I f x = 1 :=
  (isIsometry_fixedPointDerivative x hf).eq_one_of_isNilpotent_sub_one
    (fun v hv ↦ inner_self_eq_zero.mp (by
      rwa [LinearMap.BilinMap.toQuadraticMap_apply, innerₗ_apply_apply] at hv)) h

namespace RiemannianIsometry

/-- At a fixed point of a Riemannian isometry, the differential preserves the inner product of the
tangent space. -/
theorem isIsometry_fixedPointDerivative (Φ : RiemannianIsometry I I M M) (x : {x // Φ x = x}) :
    BilinForm.IsIsometry (innerₗ (TangentSpace I x.1)) (fixedPointDerivative I Φ x) :=
  TauCeti.isIsometry_fixedPointDerivative x (Φ.inner_mfderiv x.1)

/-- At a fixed point of a Riemannian isometry, a unipotent differential is the identity. -/
theorem fixedPointDerivative_eq_one_of_isNilpotent_sub_one (Φ : RiemannianIsometry I I M M)
    (x : {x // Φ x = x}) (h : IsNilpotent (fixedPointDerivative I Φ x - 1)) :
    fixedPointDerivative I Φ x = 1 :=
  TauCeti.fixedPointDerivative_eq_one_of_isNilpotent_sub_one x (Φ.inner_mfderiv x.1) h

end RiemannianIsometry

end TauCeti

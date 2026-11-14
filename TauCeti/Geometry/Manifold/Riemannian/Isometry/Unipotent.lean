/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import TauCeti.LinearAlgebra.BilinearForm.Isometry.Unipotent

/-!
# Unipotent differentials of Riemannian isometries at fixed points

At a fixed point `x` of a Riemannian isometry `Φ` of `M`, the differential `dΦ_x`, read as an
endomorphism of `T_x M` (`TauCeti.fixedPointDerivative`), preserves the inner product of `T_x M`
(`TauCeti.RiemannianIsometry.isIsometry_fixedPointDerivative`). An inner product is anisotropic,
so if `dΦ_x - 1` is nilpotent, then `dΦ_x = 1`
(`TauCeti.RiemannianIsometry.fixedPointDerivative_eq_one_of_isNilpotent`).

This is a pointwise obstruction to invariant metrics. A diffeomorphism with a fixed point at which
its differential is unipotent and not the identity, such as the shear `(q, p) ↦ (q + p, p)` of
`ℝ²`, is an isometry of no Riemannian metric whatsoever: neither smoothness of the metric nor
completeness or compactness enters.
-/

public section

open Bundle
open scoped Manifold

namespace TauCeti.RiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- At a fixed point of a Riemannian isometry, the differential preserves the inner product of the
tangent space. -/
theorem isIsometry_fixedPointDerivative (Φ : RiemannianIsometry I I M M) (x : {x // Φ x = x}) :
    BilinForm.IsIsometry (innerₗ (TangentSpace I x.1)) (fixedPointDerivative I Φ x) :=
  BilinForm.isIsometry_iff.mpr fun v w ↦ by
    -- The inner products of the fibres over `Φ x` and over `x` agree, as these points are equal.
    have key : ∀ {y : M}, y = x.1 → ∀ a b : E,
        innerₗ (TangentSpace I y) a b = innerₗ (TangentSpace I x.1) a b := by
      rintro y rfl a b
      rfl
    rw [fixedPointDerivative_apply, fixedPointDerivative_apply]
    exact (key x.2 _ _).symm.trans (Φ.inner_mfderiv x.1 v w)

/-- At a fixed point of a Riemannian isometry, a unipotent differential is the identity. -/
theorem fixedPointDerivative_eq_one_of_isNilpotent (Φ : RiemannianIsometry I I M M)
    (x : {x // Φ x = x}) (h : IsNilpotent (fixedPointDerivative I Φ x - 1)) :
    fixedPointDerivative I Φ x = 1 :=
  (Φ.isIsometry_fixedPointDerivative x).eq_one_of_isNilpotent_sub_one
    (fun v hv ↦ inner_self_eq_zero.mp (by
      rwa [LinearMap.BilinMap.toQuadraticMap_apply, innerₗ_apply_apply] at hv)) h

end TauCeti.RiemannianIsometry

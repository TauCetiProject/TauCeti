/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Complexification
import TauCeti.Analysis.InnerProductSpace.Orthonormal.SesquilinearForm
import TauCeti.LinearAlgebra.ExteriorAlgebra.Subspace

/-!
# The Euclidean exterior Gram metric and its complexification

Let `V` be a real inner product space (not necessarily finite-dimensional). The Euclidean inner
product `innerₗ V` induces the orthogonal direct-sum Gram form `(innerₗ V).sesqExteriorAlgebra` on
`ExteriorAlgebra ℝ V`, which is symmetric and strictly positive definite without any
finite-dimensionality assumption on `V` and agrees with the wedge-basis form of any finite
orthonormal basis `b` of `V`.

Identifying the basis-free complexified Euclidean exterior Gram metric
`LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra` on
`ℂ ⊗[ℝ] ExteriorAlgebra ℝ V` with the orthonormal wedge-basis Hermitian form on
`ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)` turns coordinate Clifford/Hilbert–Schmidt trace identities into
basis-free metric comparisons for spinor endomorphisms (`AlgEquiv.cliffordFormsEquivEnd`) and
spinor tensors (`AlgEquiv.cliffordFormsEquivTensor`):

* `(innerₗ V).sesqExteriorAlgebra` is symmetric and strictly positive definite on
  `ExteriorAlgebra ℝ V`, and agrees with the wedge-basis form of any finite orthonormal basis;
* `LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra` is Hermitian and
  strictly positive definite on `ℂ ⊗[ℝ] ExteriorAlgebra ℝ V` without finite-dimensionality on `V`;
* under `ExteriorAlgebra.baseChangeEquiv ℝ V ℂ`, the Hermitian form making
  `(b.toBasis.baseChange ℂ).ExteriorAlgebra` orthonormal pulls back to
  `LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra`, independent of `b`;
* when `V` is finite-dimensional, its restriction in homogeneous degree `k` along
  `(⋀[ℝ]^k V).subtype.baseChange ℂ` is
  `LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V))` (while orthogonality of distinct
  complexified exterior powers is
  `LinearMap.BilinForm.sesqComplexification_sesqExteriorAlgebra_eq_zero_of_mem_baseChange_of_ne`
  in `TauCeti.LinearAlgebra.ExteriorAlgebra.Complexification`).

## Main results

* `OrthonormalBasis.toLinearMap₂_toBasis_exteriorAlgebra_one`: the wedge-basis real bilinear form
  of a finite orthonormal basis `b` is `(innerₗ V).sesqExteriorAlgebra`.
* `ExteriorAlgebra.isSymm_sesqExteriorAlgebra_innerₗ` and
  `ExteriorAlgebra.posDef_toQuadraticMap_sesqExteriorAlgebra_innerₗ`: symmetry and positive
  definiteness of `(innerₗ V).sesqExteriorAlgebra` without finite-dimensionality on `V`.
* `OrthonormalBasis.toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_one` and
  `OrthonormalBasis.toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_baseChangeEquiv`:
  identification of the complexified orthonormal wedge-basis form with the complexified
  Euclidean exterior Gram metric.
* `exteriorPower.sesqComplexification_sesqExteriorAlgebra_innerₗ_subtype_baseChange`: in degree
  `k`, `LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra` restricts to
  `LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V))`.
* `ExteriorAlgebra.isSymm_sesqComplexification_sesqExteriorAlgebra_innerₗ` and
  `ExteriorAlgebra.sesqComplexification_sesqExteriorAlgebra_innerₗ_self_pos`: Hermitian symmetry
  and strict positive definiteness of the complexified Euclidean exterior Gram metric.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., World Scientific (2020),
  §2.2.4.
-/

public section

open scoped RealInnerProductSpace TensorProduct ComplexOrder
open Matrix

namespace OrthonormalBasis

variable {V I : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The real bilinear form making `b.toBasis.ExteriorAlgebra` orthonormal is
`(innerₗ V).sesqExteriorAlgebra`. -/
theorem toLinearMap₂_toBasis_exteriorAlgebra_one [Fintype I] [LinearOrder I]
    (b : OrthonormalBasis I ℝ V) :
    Matrix.toLinearMap₂ b.toBasis.ExteriorAlgebra b.toBasis.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) ℝ) =
      (innerₗ V).sesqExteriorAlgebra := by
  rw [Matrix.toLinearMap₂, Module.Basis.toLinearMapₛₗ₂_exteriorAlgebra_one]
  refine congrArg LinearMap.sesqExteriorAlgebra
    (LinearMap.ext_basis b.toBasis b.toBasis fun i j ↦ ?_)
  have h := LinearMap.congr_fun₂ b.toLinearMapₛₗ₂_real (b.toBasis i) (b.toBasis j)
  rw [Matrix.toLinearMapₛₗ₂_apply_basis] at h ⊢
  exact h

/-- The Hermitian form on `ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)` making
`(b.toBasis.baseChange ℂ).ExteriorAlgebra` orthonormal is
`(LinearMap.BilinForm.sesqComplexification (innerₗ V)).sesqExteriorAlgebra`, independent of the
orthonormal basis `b`. -/
theorem toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_one [Fintype I] [LinearOrder I]
    (b : OrthonormalBasis I ℝ V) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) (b.toBasis.baseChange ℂ).ExteriorAlgebra
        (b.toBasis.baseChange ℂ).ExteriorAlgebra (1 : Matrix (Finset I) (Finset I) ℂ) =
      (LinearMap.BilinForm.sesqComplexification (innerₗ V)).sesqExteriorAlgebra := by
  rw [Module.Basis.toLinearMapₛₗ₂_exteriorAlgebra_one, b.toLinearMapₛₗ₂_baseChange_complex]

/-- Under `ExteriorAlgebra.baseChangeEquiv ℝ V ℂ`, the Hermitian wedge-basis form of an orthonormal
basis `b` pulls back to
`LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra`. -/
theorem toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_baseChangeEquiv
    [Fintype I] [LinearOrder I] (b : OrthonormalBasis I ℝ V)
    (x y : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) (b.toBasis.baseChange ℂ).ExteriorAlgebra
        (b.toBasis.baseChange ℂ).ExteriorAlgebra (1 : Matrix (Finset I) (Finset I) ℂ)
        (ExteriorAlgebra.baseChangeEquiv ℝ V ℂ x)
        (ExteriorAlgebra.baseChangeEquiv ℝ V ℂ y) =
      LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra x y := by
  rw [b.toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_one,
    LinearMap.BilinForm.sesqExteriorAlgebra_sesqComplexification_baseChangeEquiv]

end OrthonormalBasis

namespace exteriorPower

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- In homogeneous degree `k`,
`LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra` restricts along
`(⋀[ℝ]^k V).subtype.baseChange ℂ` to
`LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V))`. -/
theorem sesqComplexification_sesqExteriorAlgebra_innerₗ_subtype_baseChange (k : ℕ)
    (x y : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra
        ((⋀[ℝ]^k V).subtype.baseChange ℂ x) ((⋀[ℝ]^k V).subtype.baseChange ℂ y) =
      LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V)) x y := by
  rw [LinearMap.BilinForm.sesqComplexification_sesqExteriorAlgebra_subtype_baseChange,
    sesqExteriorPower_innerₗ]

end exteriorPower

namespace ExteriorAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The real Euclidean exterior Gram form `(innerₗ V).sesqExteriorAlgebra` is symmetric. -/
theorem isSymm_sesqExteriorAlgebra_innerₗ :
    LinearMap.BilinForm.IsSymm (innerₗ V).sesqExteriorAlgebra :=
  LinearMap.BilinForm.isSymm_iff.mpr (isSymm_inner.sesqExteriorAlgebra fun _ ↦ rfl)

/-- The real Euclidean exterior Gram form `(innerₗ V).sesqExteriorAlgebra` is positive definite
(without any finite-dimensionality assumption on `V`). -/
theorem posDef_toQuadraticMap_sesqExteriorAlgebra_innerₗ :
    (LinearMap.BilinMap.toQuadraticMap (innerₗ V).sesqExteriorAlgebra).PosDef := by
  intro x hx
  obtain ⟨W, _, y, rfl⟩ := x.exists_finite_submodule_mem_range_map_subtype
  have hy : y ≠ 0 := by rintro rfl; exact hx (map_zero _)
  let b := stdOrthonormalBasis ℝ W
  have hsub : ∀ u v : W, innerₗ V (W.subtype u) (W.subtype v) = innerₗ W u v :=
    fun u v ↦ by simp [Submodule.coe_inner]
  rw [LinearMap.BilinMap.toQuadraticMap_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    LinearMap.sesqExteriorAlgebra_map_map hsub, ← b.toLinearMap₂_toBasis_exteriorAlgebra_one]
  exact (Matrix.toLinearMapₛₗ₂_one_self_nonneg b.toBasis.ExteriorAlgebra y).lt_of_ne'
    ((Matrix.toLinearMapₛₗ₂_one_self_eq_zero_iff b.toBasis.ExteriorAlgebra).not.mpr hy)

/-- The complexified Euclidean exterior Gram metric is Hermitian. -/
theorem isSymm_sesqComplexification_sesqExteriorAlgebra_innerₗ :
    (LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra).IsSymm :=
  LinearMap.BilinForm.IsSymm.sesqComplexification (isSymm_sesqExteriorAlgebra_innerₗ (V := V))

/-- The complexified Euclidean exterior Gram metric is strictly positive definite on nonzero forms
in `ℂ ⊗[ℝ] ExteriorAlgebra ℝ V` (without any finite-dimensionality assumption on `V`). -/
theorem sesqComplexification_sesqExteriorAlgebra_innerₗ_self_pos
    {x : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V} (hx : x ≠ 0) :
    0 < LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra x x :=
  LinearMap.BilinForm.sesqComplexification_self_pos
    (B := (innerₗ V).sesqExteriorAlgebra)
    (isSymm_sesqExteriorAlgebra_innerₗ (V := V)) posDef_toQuadraticMap_sesqExteriorAlgebra_innerₗ hx

end ExteriorAlgebra

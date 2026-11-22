/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Complexification
import TauCeti.Analysis.InnerProductSpace.Orthonormal.SesquilinearForm

/-!
# The complexified Euclidean exterior Gram metric

Identifying the basis-free complexified Euclidean exterior Gram metric
`LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra` on
`ℂ ⊗[ℝ] ExteriorAlgebra ℝ V` with the orthonormal wedge-basis Hermitian form on
`ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)` turns coordinate Clifford/Hilbert–Schmidt trace identities into
basis-free metric comparisons for spinor endomorphisms (`AlgEquiv.cliffordFormsEquivEnd`) and
spinor tensors (`AlgEquiv.cliffordFormsEquivTensor`).

For a real inner product space `V`, this file proves that the sesquilinear complexification of
`(innerₗ V).sesqExteriorAlgebra` is Hermitian and strictly positive definite without any
finite-dimensionality assumption on `V`, and connects it to the wedge-basis Hermitian form of any
finite orthonormal basis `b` of `V`:

* under `ExteriorAlgebra.baseChangeEquiv ℝ V ℂ`, the Hermitian form making
  `(b.toBasis.baseChange ℂ).ExteriorAlgebra` orthonormal pulls back to
  `LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra`, independent of `b`;
* when `V` is finite-dimensional, its restriction in homogeneous degree `k` along
  `(⋀[ℝ]^k V).subtype.baseChange ℂ` is
  `LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V))`;
* distinct complexified exterior powers `(⋀[ℝ]^p V).baseChange ℂ` and `(⋀[ℝ]^q V).baseChange ℂ`
  (`p ≠ q`) are orthogonal.

## Main results

* `exteriorPower.sesqComplexification_sesqExteriorAlgebra_innerₗ_subtype_baseChange`: in degree
  `k`, `LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra` restricts to
  `LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V))`.
* `ExteriorAlgebra.isSymm_sesqComplexification_sesqExteriorAlgebra_innerₗ` and
  `ExteriorAlgebra.sesqComplexification_sesqExteriorAlgebra_innerₗ_self_pos`: Hermitian symmetry
  and strict positive definiteness of the complexified Euclidean exterior Gram metric.
* `OrthonormalBasis.toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_one` and
  `OrthonormalBasis.toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_baseChangeEquiv`:
  identification of the complexified orthonormal wedge-basis form with the complexified
  Euclidean exterior Gram metric.

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

/-- The Hermitian form on `ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)` making
`(b.toBasis.baseChange ℂ).ExteriorAlgebra` orthonormal is
`(LinearMap.BilinForm.sesqComplexification (innerₗ V)).sesqExteriorAlgebra`, independent of the
orthonormal basis `b`. -/
theorem toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_one [Fintype I] [LinearOrder I]
    (b : OrthonormalBasis I ℝ V) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) (b.toBasis.baseChange ℂ).ExteriorAlgebra
        (b.toBasis.baseChange ℂ).ExteriorAlgebra (1 : Matrix (Finset I) (Finset I) ℂ) =
      (LinearMap.BilinForm.sesqComplexification (innerₗ V)).sesqExteriorAlgebra := by
  rw [ExteriorAlgebra.toLinearMapₛₗ₂_exteriorAlgebra_one, b.toLinearMapₛₗ₂_baseChange_complex]

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

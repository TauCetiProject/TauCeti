/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ExteriorPower
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Complexification

/-!
# The complexified Euclidean exterior Gram metric

For a finite-dimensional real inner product space `V`, Mathlib equips each exterior power
`⋀[ℝ]^k V` with the Gram-determinant inner product (`exteriorPower.inner_ιMulti_ιMulti`). This file
identifies `innerₗ (⋀[ℝ]^k V)` with `(innerₗ V).sesqExteriorPower k`, shows that the orthogonal
direct-sum form `(innerₗ V).sesqExteriorAlgebra` and its sesquilinear complexification on
`ℂ ⊗[ℝ] ExteriorAlgebra ℝ V` are symmetric/Hermitian and positive definite, and connects them to
the wedge-basis Hermitian form of any orthonormal basis `b` of `V`:

* under `ExteriorAlgebra.baseChangeEquiv ℝ V ℂ`, the Hermitian form making
  `(b.toBasis.baseChange ℂ).ExteriorAlgebra` orthonormal pulls back to
  `LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra`, independent of `b`;
* in homogeneous degree `k`, its restriction along `(⋀[ℝ]^k V).subtype.baseChange ℂ` is
  `LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V))`;
* distinct complexified exterior powers `(⋀[ℝ]^p V).baseChange ℂ` and `(⋀[ℝ]^q V).baseChange ℂ`
  (`p ≠ q`) are orthogonal.

## Main results

* `exteriorPower.innerₗ_sesqExteriorPower`: `(innerₗ V).sesqExteriorPower k = innerₗ (⋀[ℝ]^k V)`.
* `exteriorPower.innerₗ_sesqExteriorAlgebra_sesqComplexification_subtype_baseChange`: in degree `k`,
  `LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra` restricts to
  `LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V))`.
* `exteriorPower.innerₗ_sesqExteriorAlgebra_posDef` and
  `exteriorPower.innerₗ_sesqExteriorAlgebra_sesqComplexification_self_pos`: positive definiteness of
  the real and complexified Euclidean exterior Gram metrics.
* `OrthonormalBasis.toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_baseChangeEquiv`,
  `OrthonormalBasis.toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_subtype_baseChange`, and
  `OrthonormalBasis.toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_eq_zero_of_ne`: comparison of
  the complexified orthonormal wedge-basis form with
  `LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V))` and orthogonality of distinct
  degrees.

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

/-- The real bilinear form making an orthonormal basis `b` of `V` orthonormal is `innerₗ V`. -/
@[simp]
theorem toLinearMap₂_toBasis_one [Fintype I] [DecidableEq I] (b : OrthonormalBasis I ℝ V) :
    toLinearMap₂ b.toBasis b.toBasis (1 : Matrix I I ℝ) = innerₗ V := by
  refine LinearMap.ext_basis b.toBasis b.toBasis fun i j ↦ ?_
  rw [toLinearMap₂_apply_basis, innerₗ_apply_apply, OrthonormalBasis.coe_toBasis,
    orthonormal_iff_ite.mp b.orthonormal, Matrix.one_apply]

/-- The Hermitian form on `ℂ ⊗[ℝ] V` making `b.toBasis.baseChange ℂ` orthonormal is the
sesquilinear complexification of `innerₗ V`. -/
theorem toLinearMapₛₗ₂_baseChange_complex_one [Fintype I] [DecidableEq I]
    (b : OrthonormalBasis I ℝ V) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) (b.toBasis.baseChange ℂ) (b.toBasis.baseChange ℂ)
        (1 : Matrix I I ℂ) =
      LinearMap.BilinForm.sesqComplexification (innerₗ V) := by
  rw [Matrix.toLinearMapₛₗ₂_baseChange_complex_one, b.toLinearMap₂_toBasis_one]

/-- The real bilinear form making `b.toBasis.ExteriorAlgebra` orthonormal is
`(innerₗ V).sesqExteriorAlgebra`. -/
theorem toLinearMap₂_toBasis_exteriorAlgebra_one [Fintype I] [LinearOrder I]
    (b : OrthonormalBasis I ℝ V) :
    toLinearMap₂ b.toBasis.ExteriorAlgebra b.toBasis.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) ℝ) =
      (innerₗ V).sesqExteriorAlgebra := by
  rw [toLinearMap₂, ExteriorAlgebra.toLinearMapₛₗ₂_exteriorAlgebra_one, ← toLinearMap₂,
    b.toLinearMap₂_toBasis_one]

/-- The Hermitian form on `ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)` making
`(b.toBasis.baseChange ℂ).ExteriorAlgebra` orthonormal is
`(LinearMap.BilinForm.sesqComplexification (innerₗ V)).sesqExteriorAlgebra`, independent of the
orthonormal basis `b`. -/
theorem toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_one [Fintype I] [LinearOrder I]
    (b : OrthonormalBasis I ℝ V) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) (b.toBasis.baseChange ℂ).ExteriorAlgebra
        (b.toBasis.baseChange ℂ).ExteriorAlgebra (1 : Matrix (Finset I) (Finset I) ℂ) =
      (LinearMap.BilinForm.sesqComplexification (innerₗ V)).sesqExteriorAlgebra := by
  rw [ExteriorAlgebra.toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_one,
    b.toLinearMap₂_toBasis_one]

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
    LinearMap.BilinForm.sesqComplexification_sesqExteriorAlgebra_baseChangeEquiv]

end OrthonormalBasis

namespace exteriorPower

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- On a finite-dimensional real inner product space `V`, the `k`-th exterior Gram form of
`innerₗ V` is `innerₗ (⋀[ℝ]^k V)`. -/
@[simp]
theorem innerₗ_sesqExteriorPower (k : ℕ) :
    (innerₗ V).sesqExteriorPower k = innerₗ (⋀[ℝ]^k V) := by
  symm
  rw [LinearMap.eq_sesqExteriorPower_iff]
  intro u v
  rw [innerₗ_apply_apply, inner_ιMulti_ιMulti, ← Matrix.det_transpose]
  rfl

/-- In homogeneous degree `k`,
`LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra` restricts along
`(⋀[ℝ]^k V).subtype.baseChange ℂ` to
`LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V))`. -/
theorem innerₗ_sesqExteriorAlgebra_sesqComplexification_subtype_baseChange (k : ℕ)
    (x y : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra
        ((⋀[ℝ]^k V).subtype.baseChange ℂ x) ((⋀[ℝ]^k V).subtype.baseChange ℂ y) =
      LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V)) x y := by
  rw [LinearMap.BilinForm.sesqExteriorAlgebra_sesqComplexification_subtype_baseChange,
    innerₗ_sesqExteriorPower]

omit [FiniteDimensional ℝ V] in
/-- The real Euclidean exterior Gram form `(innerₗ V).sesqExteriorAlgebra` is symmetric. -/
theorem innerₗ_sesqExteriorAlgebra_isSymm :
    LinearMap.BilinForm.IsSymm (innerₗ V).sesqExteriorAlgebra := by
  have hsymm : (innerₗ V).IsSymm := LinearMap.isSymm_def.mpr fun x y ↦ real_inner_comm y x
  exact LinearMap.BilinForm.isSymm_iff.mpr (hsymm.sesqExteriorAlgebra fun _ ↦ rfl)

omit [FiniteDimensional ℝ V] in
/-- The real Euclidean exterior Gram form `(innerₗ V).sesqExteriorAlgebra` is positive definite
(without any finite-dimensionality assumption on `V`). -/
theorem innerₗ_sesqExteriorAlgebra_posDef :
    (LinearMap.BilinMap.toQuadraticMap (innerₗ V).sesqExteriorAlgebra).PosDef := by
  have hsub (x : ExteriorAlgebra ℝ V) :
      ∃ (W : Submodule ℝ V) (_ : FiniteDimensional ℝ W) (y : ExteriorAlgebra ℝ W),
        ExteriorAlgebra.map W.subtype y = x := by
    induction x using CliffordAlgebra.left_induction with
    | algebraMap r =>
      exact ⟨⊥, inferInstance, algebraMap ℝ _ r, AlgHom.commutes _ r⟩
    | add x₁ x₂ hx₁ hx₂ =>
      obtain ⟨W₁, _, y₁, rfl⟩ := hx₁
      obtain ⟨W₂, _, y₂, rfl⟩ := hx₂
      refine ⟨W₁ ⊔ W₂, inferInstance,
        ExteriorAlgebra.map (Submodule.inclusion le_sup_left) y₁ +
          ExteriorAlgebra.map (Submodule.inclusion le_sup_right) y₂, ?_⟩
      rw [map_add, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map,
        ExteriorAlgebra.map_comp_map]
      rfl
    | ι_mul s m hs =>
      obtain ⟨W, _, y, rfl⟩ := hs
      refine ⟨W ⊔ (ℝ ∙ m), inferInstance,
        ExteriorAlgebra.ι ℝ ⟨m, Submodule.mem_sup_right (Submodule.mem_span_singleton_self m)⟩ *
          ExteriorAlgebra.map (Submodule.inclusion le_sup_left) y, ?_⟩
      rw [map_mul, ExteriorAlgebra.map_apply_ι, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
      rfl
  intro x hx
  obtain ⟨W, _, y, rfl⟩ := hsub x
  have hy : y ≠ 0 := by rintro rfl; exact hx (map_zero _)
  let b := stdOrthonormalBasis ℝ W
  rw [LinearMap.BilinMap.toQuadraticMap_apply,
    LinearMap.sesqExteriorAlgebra_map_map (B := innerₗ W) (fun _ _ ↦ rfl),
    ← b.toLinearMap₂_toBasis_exteriorAlgebra_one]
  conv_rhs => rw [← b.toBasis.ExteriorAlgebra.sum_repr y]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    toLinearMap₂_apply_basis, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  by_contra! hle
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun S _ ↦
    mul_self_nonneg (b.toBasis.ExteriorAlgebra.repr y S)).mp
      (le_antisymm hle (Finset.sum_nonneg fun S _ ↦ mul_self_nonneg _))
  exact hy (b.toBasis.ExteriorAlgebra.ext_elem fun S ↦ by
    simpa using mul_self_eq_zero.mp (hzero S (Finset.mem_univ S)))

omit [FiniteDimensional ℝ V] in
/-- The complexified Euclidean exterior Gram metric is Hermitian. -/
theorem innerₗ_sesqExteriorAlgebra_sesqComplexification_isSymm :
    (LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra).IsSymm :=
  LinearMap.BilinForm.IsSymm.sesqComplexification (innerₗ_sesqExteriorAlgebra_isSymm (V := V))

omit [FiniteDimensional ℝ V] in
/-- The complexified Euclidean exterior Gram metric is strictly positive definite on nonzero forms
in `ℂ ⊗[ℝ] ExteriorAlgebra ℝ V` (without any finite-dimensionality assumption on `V`). -/
theorem innerₗ_sesqExteriorAlgebra_sesqComplexification_self_pos
    {x : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V} (hx : x ≠ 0) :
    0 < LinearMap.BilinForm.sesqComplexification (innerₗ V).sesqExteriorAlgebra x x :=
  LinearMap.BilinForm.sesqComplexification_self_pos
    (B := (innerₗ V).sesqExteriorAlgebra)
    (innerₗ_sesqExteriorAlgebra_isSymm (V := V)) innerₗ_sesqExteriorAlgebra_posDef hx

end exteriorPower

namespace OrthonormalBasis

variable {V I : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [Fintype I] [LinearOrder I] (b : OrthonormalBasis I ℝ V)

/-- **Complexified wedge-basis form in degree `k`**: under `ExteriorAlgebra.baseChangeEquiv ℝ V ℂ`,
the Hermitian form making `(b.toBasis.baseChange ℂ).ExteriorAlgebra` orthonormal restricts in
homogeneous degree `k` to `LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V))`. -/
theorem toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_subtype_baseChange
    (k : ℕ) (x y : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) (b.toBasis.baseChange ℂ).ExteriorAlgebra
        (b.toBasis.baseChange ℂ).ExteriorAlgebra (1 : Matrix (Finset I) (Finset I) ℂ)
        (ExteriorAlgebra.baseChangeEquiv ℝ V ℂ ((⋀[ℝ]^k V).subtype.baseChange ℂ x))
        (ExteriorAlgebra.baseChangeEquiv ℝ V ℂ ((⋀[ℝ]^k V).subtype.baseChange ℂ y)) =
      LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V)) x y := by
  rw [b.toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_baseChangeEquiv,
    exteriorPower.innerₗ_sesqExteriorAlgebra_sesqComplexification_subtype_baseChange]

omit [FiniteDimensional ℝ V] in
/-- **Distinct complexified degrees are orthogonal** for the Hermitian wedge-basis form pulled back
along `ExteriorAlgebra.baseChangeEquiv ℝ V ℂ`. -/
theorem toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_eq_zero_of_ne
    {p q : ℕ} (hpq : p ≠ q) {x y : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V}
    (hx : x ∈ (⋀[ℝ]^p V).baseChange ℂ) (hy : y ∈ (⋀[ℝ]^q V).baseChange ℂ) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) (b.toBasis.baseChange ℂ).ExteriorAlgebra
        (b.toBasis.baseChange ℂ).ExteriorAlgebra (1 : Matrix (Finset I) (Finset I) ℂ)
        (ExteriorAlgebra.baseChangeEquiv ℝ V ℂ x)
        (ExteriorAlgebra.baseChangeEquiv ℝ V ℂ y) = 0 := by
  rw [b.toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_baseChangeEquiv]
  exact LinearMap.BilinForm.sesqExteriorAlgebra_sesqComplexification_eq_zero_of_mem_baseChange_of_ne
    (innerₗ V) hpq hx hy

end OrthonormalBasis

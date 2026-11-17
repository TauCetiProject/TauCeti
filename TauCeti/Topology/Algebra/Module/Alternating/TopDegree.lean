/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import Mathlib.LinearAlgebra.Determinant

/-!
# Top-degree continuous alternating forms

Top-degree scalar-valued continuous alternating forms over a commutative ring are determined
by their basis coefficient, which vanishes only for the zero form. Pullback by a continuous
linear endomorphism multiplies that coefficient by its determinant. Pullback along a continuous
linear map `A : E → F` multiplies it by the determinant of `C⁻¹ ∘ A` for any continuous linear
equivalence `C : E ≃ F`, the target coefficient being taken in the transported basis. Evaluating a
scalar-valued continuous alternating form on column- or row-combinations of a family by a square
matrix `A` scales its value by `A.det`. Above the top degree, continuous alternating maps on a
finite-dimensional space over a division ring vanish. No compatibility between the topology and the
module structure is required for those statements.
-/

public section

open scoped Matrix

namespace ContinuousAlternatingMap

variable {R E ι : Type*} [CommRing R] [TopologicalSpace R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E] [Fintype ι] [DecidableEq ι]

/-- A top-degree alternating form is determined by its scalar coefficient in a basis. -/
theorem apply_eq_det_mul (ω : E [⋀^ι]→L[R] R) (b : Module.Basis ι R E) (v : ι → E) :
    ω v = b.det v * ω b := by
  have h := congrArg (fun f : E [⋀^ι]→ₗ[R] R ↦ f v) (ω.toAlternatingMap.eq_smul_basis_det b)
  simpa only [coe_toAlternatingMap, _root_.smul_apply, smul_eq_mul, mul_comm] using h

/-- Evaluating an alternating form on column-combinations `j ↦ ∑ i, A i j • v i` of a family `v`
multiplies `φ v` by `A.det`. -/
theorem apply_sum_smul_col_eq_det_mul (φ : E [⋀^ι]→L[R] R) (v : ι → E) (A : Matrix ι ι R) :
    φ (fun j ↦ ∑ i, A i j • v i) = A.det * φ v := by
  let e : Module.Basis ι R (ι → R) := Pi.basisFun R ι
  let ψ : (ι → R) [⋀^ι]→ₗ[R] R := φ.toAlternatingMap.compLinearMap (Fintype.linearCombination R v)
  have hψ := DFunLike.congr_fun (ψ.eq_smul_basis_det e) (fun j i ↦ A i j)
  have he : ψ e = φ v := by simp [ψ, e]
  have hL : ψ (fun j i ↦ A i j) = φ (fun j ↦ ∑ i, A i j • v i) := by
    simp [ψ, Fintype.linearCombination_apply]
  have hdet : e.det (fun j i ↦ A i j) = A.det := (Pi.basisFun_det_apply _).trans A.det_transpose
  rw [← hL, hψ, _root_.smul_apply, he, hdet, smul_eq_mul, mul_comm]

/-- Evaluating an alternating form on row-combinations `j ↦ ∑ i, A j i • v i` of a family `v`
multiplies `φ v` by `A.det`. -/
theorem apply_sum_smul_row_eq_det_mul (φ : E [⋀^ι]→L[R] R) (v : ι → E) (A : Matrix ι ι R) :
    φ (fun j ↦ ∑ i, A j i • v i) = A.det * φ v := by
  simpa only [Matrix.transpose_apply, Matrix.det_transpose] using
    φ.apply_sum_smul_col_eq_det_mul v Aᵀ

omit [Fintype ι] [DecidableEq ι] in
/-- Pullback of a top-degree coefficient multiplies by the determinant. -/
theorem compContinuousLinearMap_apply_basis [Finite ι] (ω : E [⋀^ι]→L[R] R)
    (b : Module.Basis ι R E) (A : E →L[R] E) :
    (ω.compContinuousLinearMap A) b = A.toLinearMap.det * ω b := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rw [compContinuousLinearMap_apply, apply_eq_det_mul ω b]
  simp only [← ContinuousLinearMap.coe_coe A, b.det_comp, b.det_self, mul_one]

omit [Fintype ι] [DecidableEq ι] in
/-- Pullback along a continuous linear map `A : E → F` multiplies the coefficient of a
top-degree form by the determinant of `A` read in `E` through a continuous linear equivalence
`C : E ≃ F`: the coefficient of `A^* ω` in a basis `b` of `E` is `det (C⁻¹ ∘ A)` times the
coefficient of `ω` in the basis `C ∘ b` of `F`. -/
theorem compContinuousLinearMap_apply_basis_map [Finite ι] {F : Type*} [AddCommGroup F]
    [Module R F] [TopologicalSpace F] (ω : F [⋀^ι]→L[R] R) (b : Module.Basis ι R E)
    (A : E →L[R] F) (C : E ≃L[R] F) :
    (ω.compContinuousLinearMap A) b =
      ((C.symm : F →L[R] E) ∘L A).toLinearMap.det * ω (b.map C.toLinearEquiv) := by
  have hA : ω.compContinuousLinearMap A =
      (ω.compContinuousLinearMap (C : E →L[R] F)).compContinuousLinearMap
        ((C.symm : F →L[R] E) ∘L A) := by
    ext v
    simp [Function.comp_def]
  rw [hA, compContinuousLinearMap_apply_basis, compContinuousLinearMap_apply,
    Module.Basis.coe_map, ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.coe_coe]

omit [Fintype ι] [DecidableEq ι] in
/-- A top-degree alternating form vanishes on a basis exactly when it is zero. -/
@[simp]
theorem map_basis_eq_zero_iff [Finite ι] (ω : E [⋀^ι]→L[R] R) (b : Module.Basis ι R E) :
    ω b = 0 ↔ ω = 0 := by
  rw [← coe_toAlternatingMap, AlternatingMap.map_basis_eq_zero_iff,
    ← toAlternatingMap_zero, toAlternatingMap_injective.eq_iff]

omit [Fintype ι] [DecidableEq ι] in
/-- A nonzero top-degree alternating form is nonzero on every basis. -/
theorem map_basis_ne_zero_iff [Finite ι] (ω : E [⋀^ι]→L[R] R) (b : Module.Basis ι R E) :
    ω b ≠ 0 ↔ ω ≠ 0 :=
  not_congr (ω.map_basis_eq_zero_iff b)

section AboveTopDegree

variable {K E F ι : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
  [TopologicalSpace E] [AddCommGroup F] [Module K F] [TopologicalSpace F]

/-- A continuous alternating map in more variables than the dimension of its domain is zero. -/
theorem eq_zero_of_finrank_lt [Module.Finite K E] [Fintype ι] (f : E [⋀^ι]→L[K] F)
    (h : Module.finrank K E < Fintype.card ι) : f = 0 := by
  ext v
  exact f.toAlternatingMap.map_linearDependent v fun hv ↦ hv.fintype_card_le_finrank.not_gt h

end AboveTopDegree

end ContinuousAlternatingMap

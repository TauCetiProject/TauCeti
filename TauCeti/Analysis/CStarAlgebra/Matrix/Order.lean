/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Spectrum
import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic

/-!
# Spectral order on scalar and Hilbert-space operator matrices

The spectral order on `CStarMatrix n n ℂ` agrees with the positive-semidefinite order
on ordinary complex matrices: the algebraic star equivalence between the two carriers
preserves and reflects order, independently of their different norm instances.

More generally, for a complex Hilbert space `H`, `M : CStarMatrix n n (H →L[ℂ] H)` is positive in
the spectral order if and only if all vector quadratic forms `∑ i, ∑ j, ⟪ξ i, M i j (ξ j)⟫_ℂ` are
nonnegative in `ℂ`. Consequently the C⋆-norm of such an operator matrix is its norm acting on
`Hⁿ`: `‖M‖ ≤ C` if and only if `∑ₖ ‖∑ₗ Mₖₗ ξₗ‖² ≤ C² ∑ₗ ‖ξₗ‖²` for all `ξ`
(`CStarMatrix.norm_le_iff_forall_sum_norm_sq_le`, `CStarMatrix.sum_norm_sq_le`).

A complex C⋆-matrix has finite real spectrum (`CStarMatrix.finite_real_spectrum`).
-/

public section

open scoped MatrixOrder ComplexOrder InnerProductSpace

namespace CStarMatrix

/-- Positivity in the matrix C⋆-algebra is ordinary positive semidefiniteness. -/
theorem nonneg_iff_posSemidef {n : Type*} [Fintype n]
    {M : CStarMatrix n n ℂ} : 0 ≤ M ↔ (ofMatrix.symm M).PosSemidef := by
  classical
  rw [← Matrix.nonneg_iff_posSemidef]
  simpa only [map_zero, ← ofMatrix_eq_ofMatrixStarAlgEquiv, Equiv.apply_symm_apply] using
    (map_le_map_iff (ofMatrixStarAlgEquiv (n := n) (A := ℂ))
      (a := 0) (b := ofMatrix.symm M))

/-- The quadratic form of `M⋆ M` on a family of vectors `ξ` is the squared norm of `M ξ`:
`∑ᵢ ∑ⱼ ⟪ξᵢ, (M⋆ M)ᵢⱼ ξⱼ⟫ = ∑ₖ ‖∑ₗ Mₖₗ ξₗ‖²`. -/
theorem sum_inner_star_mul_self_apply {n H : Type*} [Fintype n]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : CStarMatrix n n (H →L[ℂ] H)) (ξ : n → H) :
    ∑ i, ∑ j, ⟪ξ i, (star M * M) i j (ξ j)⟫_ℂ = ∑ k, ((‖∑ l, M k l (ξ l)‖ : ℂ) ^ 2) := by
  have hrew : (∑ i, ∑ j, ⟪ξ i, (star M * M) i j (ξ j)⟫_ℂ) =
      ∑ l, ⟪∑ i, M l i (ξ i), ∑ j, M l j (ξ j)⟫_ℂ := by
    simp_rw [CStarMatrix.mul_apply, CStarMatrix.star_apply, _root_.sum_apply,
      ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.star_eq_adjoint, sum_inner, inner_sum,
      ContinuousLinearMap.adjoint_inner_right]
    exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
  rw [hrew]
  exact Finset.sum_congr rfl fun _ _ => inner_self_eq_norm_sq_to_K _

/-- The quadratic form of the scalar matrix `c • 1` is `c ∑ᵢ ‖ξᵢ‖²`. -/
theorem sum_inner_algebraMap_apply {n H : Type*} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (c : ℝ) (ξ : n → H) :
    ∑ i, ∑ j, ⟪ξ i, (algebraMap ℝ (CStarMatrix n n (H →L[ℂ] H)) c) i j (ξ j)⟫_ℂ =
      (c : ℂ) * ∑ i, ((‖ξ i‖ : ℂ) ^ 2) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [CStarMatrix.algebraMap_apply, hj.symm])
    (by simp)]
  simp [CStarMatrix.algebraMap_apply, Algebra.algebraMap_eq_smul_one, inner_self_eq_norm_sq_to_K]

/-- An operator matrix over a complex Hilbert space is positive in the spectral order if and only
if all of its vector quadratic forms are nonnegative in `ℂ`. -/
theorem nonneg_iff_forall_sum_inner_nonneg {n H : Type*} [Fintype n]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : CStarMatrix n n (H →L[ℂ] H)} :
    0 ≤ M ↔ ∀ ξ : n → H, 0 ≤ ∑ i, ∑ j, ⟪ξ i, M i j (ξ j)⟫_ℂ := by
  refine ⟨fun hM ξ => ?_, fun hξ => nonneg_iff_forall_sum_nonneg.mpr fun X => ?_⟩
  · obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM
    rw [sum_inner_star_mul_self_apply]
    exact Finset.sum_nonneg fun _ _ => by positivity
  · refine ContinuousLinearMap.nonneg_iff_isPositive.mpr
      ((ContinuousLinearMap.isPositive_iff_complex _).mpr fun v => ?_)
    have hv : 0 ≤ ⟪(∑ i, ∑ j, star (X i) * M i j * X j) v, v⟫_ℂ := by
      rw [← inner_conj_symm, ← Complex.star_def, star_nonneg_iff]
      simpa only [_root_.sum_apply, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.star_eq_adjoint, inner_sum,
        ContinuousLinearMap.adjoint_inner_right] using hξ fun i => X i v
    exact ⟨(Complex.eq_re_of_ofReal_le hv).symm, (RCLike.nonneg_iff.mp hv).1⟩

/-- The C⋆-norm of an operator matrix `M` over a complex Hilbert space `H` is its norm acting on
families `ξ : n → H`: for `0 ≤ C`, `‖M‖ ≤ C` if and only if
`∑ₖ ‖∑ₗ Mₖₗ ξₗ‖² ≤ C² ∑ₗ ‖ξₗ‖²` for all `ξ`. -/
theorem norm_le_iff_forall_sum_norm_sq_le {n H : Type*} [Fintype n]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : CStarMatrix n n (H →L[ℂ] H)} {C : ℝ} (hC : 0 ≤ C) :
    ‖M‖ ≤ C ↔ ∀ ξ : n → H, ∑ k, ‖∑ l, M k l (ξ l)‖ ^ 2 ≤ C ^ 2 * ∑ l, ‖ξ l‖ ^ 2 := by
  classical
  have key (ξ : n → H) :
      0 ≤ ∑ i, ∑ j, ⟪ξ i, (algebraMap ℝ (CStarMatrix n n (H →L[ℂ] H)) (C ^ 2) - star M * M) i j
        (ξ j)⟫_ℂ ↔ ∑ k, ‖∑ l, M k l (ξ l)‖ ^ 2 ≤ C ^ 2 * ∑ l, ‖ξ l‖ ^ 2 := by
    simp only [CStarMatrix.sub_apply, _root_.sub_apply, inner_sub_right,
      Finset.sum_sub_distrib, sum_inner_algebraMap_apply, sum_inner_star_mul_self_apply]
    refine Iff.trans ?_ (Complex.zero_le_real.trans sub_nonneg)
    norm_cast
  rw [← sq_le_sq₀ (norm_nonneg _) hC, sq, ← CStarRing.norm_star_mul_self,
    CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg C) (star_mul_self_nonneg M),
    ← sub_nonneg, nonneg_iff_forall_sum_inner_nonneg]
  exact forall_congr' key

/-- An operator matrix `M` over a complex Hilbert space `H` acts on families `ξ : n → H` with norm
at most `‖M‖`: `∑ₖ ‖∑ₗ Mₖₗ ξₗ‖² ≤ ‖M‖² ∑ₗ ‖ξₗ‖²`. -/
theorem sum_norm_sq_le {n H : Type*} [Fintype n]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : CStarMatrix n n (H →L[ℂ] H)) (ξ : n → H) :
    ∑ k, ‖∑ l, M k l (ξ l)‖ ^ 2 ≤ ‖M‖ ^ 2 * ∑ l, ‖ξ l‖ ^ 2 :=
  (norm_le_iff_forall_sum_norm_sq_le (norm_nonneg M)).1 le_rfl ξ

/-- A complex C⋆-matrix has finite real spectrum. -/
theorem finite_real_spectrum {n : Type*} [Fintype n] [DecidableEq n] (x : CStarMatrix n n ℂ) :
    (spectrum ℝ x).Finite := by
  -- transport `Matrix.finite_real_spectrum` along `CStarMatrix.ofMatrixStarAlgEquiv`
  have h := AlgEquiv.spectrum_eq
    ((ofMatrixStarAlgEquiv (n := n) (A := ℂ)).toAlgEquiv.restrictScalars ℝ) (ofMatrix.symm x)
  simp only [AlgEquiv.coe_restrictScalars, StarAlgEquiv.coe_toAlgEquiv,
    ← ofMatrix_eq_ofMatrixStarAlgEquiv, Equiv.apply_symm_apply] at h
  exact h ▸ (ofMatrix.symm x).finite_real_spectrum

end CStarMatrix

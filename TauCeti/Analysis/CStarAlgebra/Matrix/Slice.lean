/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Analysis.InnerProductSpace.TensorProduct.Completion
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import TauCeti.Analysis.CStarAlgebra.Matrix.Order
import TauCeti.Analysis.InnerProductSpace.Completion

/-!
# Operator matrices of slices of an operator on `H ⊗₂ F`

Let `T` be a bounded operator on the completed Hilbert tensor product `H ⊗₂ F` of a complex Hilbert
space `H` and a complex inner product space `F`. For a finite orthonormal family `e₁, …, eₙ` in
`F`, the right slices `TensorProduct.sliceRight (eₗ) (eₖ) T ∈ B(H)` form an operator matrix in
`Mₙ(B(H))`: the compression of `T` to the subspace `H ⊗ span {eₖ}`. This file shows that the norm
of `T` is the supremum of the norms of these operator matrices:

* `TensorProduct.norm_ofMatrix_sliceRight_le`: each such matrix has norm at most `‖T‖`;
* `TensorProduct.opNorm_le_of_forall_norm_ofMatrix_sliceRight_le`: conversely, `‖T‖` is at most
  any common bound on their norms, because every pair of vectors of the algebraic tensor product
  `H ⊗ F` lies in `H ⊗ V` for a finite-dimensional subspace `V` of `F`.
-/

public section

noncomputable section

open UniformSpace
open scoped InnerProductSpace ComplexOrder

namespace TensorProduct

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The vector `∑ᵢ ξᵢ ⊗ eᵢ` of the completed tensor product. -/
private def tensorSum {ι : Type*} [Fintype ι] (e : ι → F) (ξ : ι → H) :
    Completion (H ⊗[ℂ] F) :=
  ∑ i, ((ξ i ⊗ₜ[ℂ] e i : H ⊗[ℂ] F) : Completion (H ⊗[ℂ] F))

omit [CompleteSpace H] in
private theorem inner_tensorSum {ι : Type*} [Fintype ι] {e : ι → F} (he : Orthonormal ℂ e)
    (ζ ξ : ι → H) : ⟪tensorSum e ζ, tensorSum e ξ⟫_ℂ = ∑ i, ⟪ζ i, ξ i⟫_ℂ := by
  classical
  simp [tensorSum, Completion.inner_coe, sum_inner, inner_sum, orthonormal_iff_ite.1 he]

omit [CompleteSpace H] in
private theorem norm_tensorSum_sq {ι : Type*} [Fintype ι] {e : ι → F} (he : Orthonormal ℂ e)
    (ξ : ι → H) : ‖tensorSum e ξ‖ ^ 2 = ∑ i, ‖ξ i‖ ^ 2 := by
  have h := inner_tensorSum he ξ ξ
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

/-- On vectors `∑ₗ ξₗ ⊗ eₗ`, the matrix coefficients of `T` are those of the operator matrix
`[sliceRight (eₗ) (eₖ) T]ₖₗ`. -/
private theorem inner_tensorSum_apply {ι : Type*} [Fintype ι] {e : ι → F} (he : Orthonormal ℂ e)
    (T : Completion (H ⊗[ℂ] F) →L[ℂ] Completion (H ⊗[ℂ] F)) (ζ ξ : ι → H) :
    ⟪tensorSum e ζ, T (tensorSum e ξ)⟫_ℂ =
      ⟪tensorSum e ζ, tensorSum e fun k ↦ ∑ l, sliceRight (e l) (e k) T (ξ l)⟫_ℂ := by
  rw [inner_tensorSum he]
  simp only [tensorSum, map_sum, sum_inner, inner_sum, inner_sliceRight_apply]
  exact Finset.sum_comm

/-- For an orthonormal family `e`, the operator matrix `[sliceRight (eₗ) (eₖ) T]ₖₗ` is a
compression of `T`, so its norm is at most `‖T‖`. -/
theorem norm_ofMatrix_sliceRight_le {ι : Type*} [Fintype ι] {e : ι → F} (he : Orthonormal ℂ e)
    (T : Completion (H ⊗[ℂ] F) →L[ℂ] Completion (H ⊗[ℂ] F)) :
    ‖CStarMatrix.ofMatrix fun k l ↦ sliceRight (e l) (e k) T‖ ≤ ‖T‖ := by
  refine (CStarMatrix.norm_le_iff_forall_sum_norm_sq_le (norm_nonneg T)).2 fun ξ ↦ ?_
  set ζ : ι → H := fun k ↦ ∑ l, sliceRight (e l) (e k) T (ξ l)
  have h := inner_tensorSum_apply he T ζ ξ
  rw [inner_self_eq_norm_sq_to_K] at h
  -- `‖∑ ζₖ ⊗ eₖ‖² = ⟪∑ ζₖ ⊗ eₖ, T (∑ ξₗ ⊗ eₗ)⟫ ≤ ‖∑ ζₖ ⊗ eₖ‖ ‖T‖ ‖∑ ξₗ ⊗ eₗ‖`
  have h1 : ‖tensorSum e ζ‖ * ‖tensorSum e ζ‖ ≤ ‖tensorSum e ζ‖ * (‖T‖ * ‖tensorSum e ξ‖) := by
    have := norm_inner_le_norm (𝕜 := ℂ) (tensorSum e ζ) (T (tensorSum e ξ))
    simp only [h, norm_pow, RCLike.norm_ofReal, abs_norm] at this
    rw [sq] at this
    exact this.trans (mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _))
  have h2 : ‖tensorSum e ζ‖ ≤ ‖T‖ * ‖tensorSum e ξ‖ := by
    rcases (norm_nonneg (tensorSum e ζ)).eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · exact le_of_mul_le_mul_left h1 h0
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rwa [mul_pow, norm_tensorSum_sq he, norm_tensorSum_sq he] at h3

/-- The norm of `T` is at most any bound `C` on the norms of the operator matrices
`[sliceRight (eₗ) (eₖ) T]ₖₗ` over all finite orthonormal families `e` in `F`. -/
theorem opNorm_le_of_forall_norm_ofMatrix_sliceRight_le
    (T : Completion (H ⊗[ℂ] F) →L[ℂ] Completion (H ⊗[ℂ] F)) {C : ℝ}
    (h : ∀ (n : ℕ) (e : Fin n → F), Orthonormal ℂ e →
      ‖CStarMatrix.ofMatrix fun k l ↦ sliceRight (e l) (e k) T‖ ≤ C) :
    ‖T‖ ≤ C := by
  classical
  have hC : 0 ≤ C := (norm_nonneg _).trans (h 0 Fin.elim0 ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩)
  refine T.opNorm_le_of_forall_inner_coe_le hC fun z x ↦ ?_
  obtain ⟨V, hV, hs⟩ := exists_finite_submodule_right_of_setFinite ({z, x} : Set (H ⊗[ℂ] F))
    (Set.toFinite _)
  obtain ⟨z', rfl⟩ := hs (Set.mem_insert _ _)
  obtain ⟨x', rfl⟩ := hs (Set.mem_insert_of_mem _ rfl)
  let b := stdOrthonormalBasis ℂ V
  set e : Fin _ → F := fun i ↦ (b i : F)
  have he : Orthonormal ℂ e := b.orthonormal.comp_linearIsometry V.subtypeₗᵢ
  -- Expand elements of `H ⊗ V` along the basis `b`.
  have hsum (w : H ⊗[ℂ] V) : ((V.subtype.lTensor H w : H ⊗[ℂ] F) : Completion (H ⊗[ℂ] F)) =
      tensorSum e (equivFinsuppOfBasisRight b.toBasis w) := by
    conv_lhs => rw [← (equivFinsuppOfBasisRight b.toBasis).symm_apply_apply w]
    rw [equivFinsuppOfBasisRight_symm_apply, Finsupp.sum_fintype _ _ (by simp), map_sum]
    simp only [tensorSum, e, LinearMap.lTensor_tmul, Submodule.subtype_apply,
      OrthonormalBasis.coe_toBasis]
    simp only [← UniformSpace.Completion.toCompl_apply, map_sum]
  set ζ := equivFinsuppOfBasisRight b.toBasis z'
  set ξ := equivFinsuppOfBasisRight b.toBasis x'
  rw [← Completion.norm_coe (V.subtype.lTensor H z'),
    ← Completion.norm_coe (V.subtype.lTensor H x'), hsum, hsum, inner_tensorSum_apply he]
  set M := CStarMatrix.ofMatrix fun k l ↦ sliceRight (e l) (e k) T
  have hM : ‖tensorSum e fun k ↦ ∑ l, sliceRight (e l) (e k) T (ξ l)‖ ≤
      ‖M‖ * ‖tensorSum e ξ‖ := by
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
    rw [mul_pow, norm_tensorSum_sq he, norm_tensorSum_sq he]
    exact CStarMatrix.sum_norm_sq_le M ξ
  calc _ ≤ ‖tensorSum e ζ‖ * ‖tensorSum e fun k ↦ ∑ l, sliceRight (e l) (e k) T (ξ l)‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖tensorSum e ζ‖ * (C * ‖tensorSum e ξ‖) := by
        gcongr
        exact hM.trans (mul_le_mul_of_nonneg_right (h _ e he) (norm_nonneg _))
    _ = C * ‖tensorSum e ζ‖ * ‖tensorSum e ξ‖ := by ring

end TensorProduct

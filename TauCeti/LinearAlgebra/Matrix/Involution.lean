/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.Data.Fintype.Prod
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import TauCeti.LinearAlgebra.Matrix.Alternating
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InnerAut

/-!
# Involutions of a matrix algebra

A `K`-linear involution `φ` of the matrix algebra `Mₙ(K)` reversing products is the adjoint
involution of a nondegenerate bilinear form: `φ X = C⁻¹ Xᵀ C` for an invertible matrix `C`, which
is either symmetric or skew-symmetric. Composing `φ` with the transpose gives an algebra
automorphism, which is inner by the Skolem–Noether theorem for matrix algebras; involutivity then
forces `Cᵀ = ±C`.

When `2 ≠ 0`, the two cases are told apart by the dimension of the skew elements: when `C` is
symmetric (an orthogonal involution), the matrices on which `φ` acts as `-1`, Mathlib's
`skewAdjointMatricesSubmodule C`, form a space of dimension at most `n(n - 1) / 2`. When `C` is
skew-symmetric (a symplectic involution), a symplectic basis of the alternating form of `C`
conjugates `φ` into the standard symplectic adjoint `X ↦ J⁻¹ Xᵀ J = -(J Xᵀ J)`, whose
unitary group is Mathlib's `Matrix.symplecticGroup`.

## Main results

* `Matrix.exists_forall_eq_inv_mul_transpose_mul`: an involutive anti-automorphism of `Mₙ(K)` is
  `X ↦ C⁻¹ Xᵀ C` with `Cᵀ = C` or `Cᵀ = -C`.
* `Matrix.finrank_skewAdjointMatricesSubmodule_le_choose_two`: for invertible symmetric `C` and
  `2 ≠ 0`, the matrices on which `X ↦ C⁻¹ Xᵀ C` is `-1` form a space of dimension at most
  `n.choose 2`.
* `Matrix.exists_algEquiv_inv_mul_transpose_mul_eq_neg_J_mul_transpose_mul_J`: for invertible
  skew-symmetric `C` and `2 ≠ 0`, an algebra isomorphism `Mₙ(K) ≃ M_{2m}(K)` carries
  `X ↦ C⁻¹ Xᵀ C` to `X ↦ -(J Xᵀ J)`.

## References

* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998),
  Proposition 2.7 and §2.A.
-/

public section

open Module

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- **Involutions of a matrix algebra are adjoint involutions.** A `K`-linear map of `Mₙ(K)` that
reverses products and is its own inverse is `X ↦ C⁻¹ Xᵀ C` for an invertible matrix `C` that is
either symmetric or skew-symmetric. -/
theorem exists_forall_eq_inv_mul_transpose_mul (φ : Matrix n n K →ₗ[K] Matrix n n K)
    (hmul : ∀ X Y, φ (X * Y) = φ Y * φ X) (hφ : Function.Involutive φ) :
    ∃ C : GL n K, ((C : Matrix n n K)ᵀ = C ∨ (C : Matrix n n K)ᵀ = -C) ∧
      ∀ X, φ X = (↑C⁻¹ : Matrix n n K) * Xᵀ * (C : Matrix n n K) := by
  have h1 : φ 1 = 1 := by
    have h := hmul (φ 1) 1
    rw [Matrix.mul_one, hφ 1, Matrix.mul_one] at h
    exact h.symm
  -- `X ↦ φ Xᵀ` is an algebra automorphism, hence inner.
  let τ : Matrix n n K ≃ₐ[K] Matrix n n K :=
    AlgEquiv.ofLinearEquiv
      ((transposeLinearEquiv n n K K).trans (LinearEquiv.ofInvolutive φ hφ))
      (by simp [h1]) (fun X Y => by simp [hmul])
  obtain ⟨g, hg⟩ := GeneralLinearGroup.innerAut_surjective K τ
  have hφg : ∀ X, φ X = (g : Matrix n n K) * Xᵀ * (↑g⁻¹ : Matrix n n K) := by
    intro X
    have h := AlgEquiv.congr_fun hg Xᵀ
    simp only [GeneralLinearGroup.innerAut_apply, ← coe_units_inv] at h
    rw [h]
    simp [τ]
  refine ⟨g⁻¹, ?_, fun X => by rw [hφg, inv_inv]⟩
  set C : Matrix n n K := ↑g⁻¹ with hC
  set D : Matrix n n K := ↑g with hD
  have hCD : C * D = 1 := Units.inv_mul g
  -- Involutivity says that `D Cᵀ` commutes with every matrix, so it is a scalar `a`.
  have hcomm : ∀ X, Commute X (D * Cᵀ) := by
    intro X
    have h := hφ X
    rw [hφg, hφg, transpose_mul, transpose_mul, transpose_transpose] at h
    have hinv : (Dᵀ * C) * (D * Cᵀ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc C, hCD, Matrix.one_mul, ← transpose_mul, hCD,
        transpose_one]
    calc X * (D * Cᵀ) = D * (Cᵀ * (X * Dᵀ)) * C * (D * Cᵀ) := by rw [h]
      _ = D * Cᵀ * X * ((Dᵀ * C) * (D * Cᵀ)) := by simp only [Matrix.mul_assoc]
      _ = D * Cᵀ * X := by rw [hinv, Matrix.mul_one]
  obtain ⟨a, ha⟩ := mem_range_scalar_iff_commute_single'.mpr fun i j => hcomm _
  have hCt : Cᵀ = a • C := by
    calc Cᵀ = C * (D * Cᵀ) := by rw [← Matrix.mul_assoc, hCD, Matrix.one_mul]
      _ = a • C := by rw [← ha, scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul,
        Matrix.mul_one]
  have haC : (a * a - 1) • C = 0 := by
    have h := congrArg transpose hCt
    rw [transpose_transpose, transpose_smul, hCt, smul_smul] at h
    rw [sub_smul, one_smul, ← h, sub_self]
  rcases smul_eq_zero.mp haC with ha1 | hC0
  · rcases mul_self_eq_one_iff.mp (sub_eq_zero.mp ha1) with rfl | rfl
    · exact Or.inl (by rw [hCt, one_smul])
    · exact Or.inr (by rw [hCt, neg_one_smul])
  · exact Or.inl (by rw [hC0, transpose_zero])

/-- **Skew elements of an orthogonal involution.** For an invertible symmetric matrix `C` over a
field with `2 ≠ 0`, the matrices that are skew-adjoint for `C`, that is `Xᵀ C = -C X`, or
equivalently `C⁻¹ Xᵀ C = -X`, form a space of dimension at most `n(n - 1) / 2`: left
multiplication by `C` embeds them into the skew-symmetric matrices, which are determined by their
entries above the diagonal. -/
theorem finrank_skewAdjointMatricesSubmodule_le_choose_two [NeZero (2 : K)] {C : Matrix n n K}
    (hC : Cᵀ = C) (hCu : IsUnit C) :
    finrank K (skewAdjointMatricesSubmodule C) ≤ (Fintype.card n).choose 2 := by
  let _ : LinearOrder n := LinearOrder.lift' _ (Fintype.equivFin n).injective
  have h2 : ∀ x : K, x + x = 0 → x = 0 := fun x hx => by
    rw [← two_mul] at hx
    exact (mul_eq_zero.mp hx).resolve_left (NeZero.ne 2)
  -- Left multiplication by `C` lands in the skew-symmetric matrices.
  have hskew : ∀ X ∈ skewAdjointMatricesSubmodule C, (C * X)ᵀ = -(C * X) := by
    intro X hX
    rw [mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, IsAdjointPair] at hX
    rw [transpose_mul, hC, hX, Matrix.mul_neg]
  let f : skewAdjointMatricesSubmodule C →ₗ[K] ({p : n × n // p.1 < p.2} → K) :=
    { toFun := fun X p => (C * X) p.1.1 p.1.2
      map_add' := fun X Y => by ext; simp [Matrix.mul_add]
      map_smul' := fun a X => by ext; simp }
  have hf : Function.Injective f := by
    intro X Y hXY
    exact Subtype.ext <| hCu.mul_left_cancel <|
      ext_of_lt_of_transpose_eq_neg (hskew X X.2) (hskew Y Y.2)
        (diag_eq_zero_of_transpose_eq_neg (hskew X X.2) h2)
        (diag_eq_zero_of_transpose_eq_neg (hskew Y Y.2) h2)
        fun a b hab => congrFun hXY ⟨(a, b), hab⟩
  calc finrank K (skewAdjointMatricesSubmodule C) ≤ finrank K ({p : n × n // p.1 < p.2} → K) :=
        LinearMap.finrank_le_finrank_of_injective hf
    _ = (Fintype.card n).choose 2 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype,
        Fintype.card_product_filter_lt]

/-- **Symplectic involutions of a matrix algebra are standard.** For a skew-symmetric invertible
matrix `C` over a field with `2 ≠ 0`, a symplectic basis of the alternating form of `C` gives an
algebra isomorphism `Mₙ(K) ≃ M_{2m}(K)` carrying the adjoint involution `X ↦ C⁻¹ Xᵀ C` to the
standard symplectic adjoint `X ↦ J⁻¹ Xᵀ J = -(J Xᵀ J)`. -/
theorem exists_algEquiv_inv_mul_transpose_mul_eq_neg_J_mul_transpose_mul_J [NeZero (2 : K)]
    {C : GL n K} (hC : (C : Matrix n n K)ᵀ = -C) :
    ∃ (m : ℕ) (ψ : Matrix n n K ≃ₐ[K] Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K),
      m + m = Fintype.card n ∧
        ∀ X, ψ ((↑C⁻¹ : Matrix n n K) * Xᵀ * (C : Matrix n n K)) =
          -(J (Fin m) K * (ψ X)ᵀ * J (Fin m) K) := by
  set Cm : Matrix n n K := (C : Matrix n n K) with hCm
  set Ci : Matrix n n K := ↑C⁻¹ with hCi
  -- The bilinear form of `C` is alternating and nondegenerate.
  have hB : (toBilin' Cm).IsAlt := by
    intro x
    have h : x ⬝ᵥ Cm *ᵥ x = -(x ⬝ᵥ Cm *ᵥ x) := by
      conv_lhs => rw [dotProduct_mulVec, ← mulVec_transpose, hC, neg_mulVec, neg_dotProduct,
        dotProduct_comm]
    rw [toBilin'_apply']
    have h2 : (2 : K) * (x ⬝ᵥ Cm *ᵥ x) = 0 := by
      rw [two_mul]
      nth_rewrite 1 [h]
      exact neg_add_cancel _
    exact (mul_eq_zero.mp h2).resolve_left (NeZero.ne 2)
  have hnd : (toBilin' Cm).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' Cm (isUnits_det_units C).ne_zero
  obtain ⟨m, b, hb⟩ := hB.exists_basis_toMatrix_eq_J hnd
  have hCmCi : ∀ Z : Matrix n (Fin m ⊕ Fin m) K, Cm * (Ci * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hCm, hCi, Units.mul_inv, Matrix.one_mul]
  let ψ : Matrix n n K ≃ₐ[K] Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
    toLinAlgEquiv'.trans (LinearMap.toMatrixAlgEquiv b)
  set P := (Pi.basisFun K n).toMatrix b with hP
  set P' := b.toMatrix (Pi.basisFun K n) with hP'
  have hPP' : ∀ Z : Matrix n (Fin m ⊕ Fin m) K, P * (P' * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hP, hP', Basis.toMatrix_mul_toMatrix_flip, Matrix.one_mul]
  have hPt : ∀ Z : Matrix n (Fin m ⊕ Fin m) K, P'ᵀ * (Pᵀ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, ← transpose_mul, hP, hP', Basis.toMatrix_mul_toMatrix_flip,
      transpose_one, Matrix.one_mul]
  have hψ : ∀ X, ψ X = P' * X * P := fun X => by
    have h := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b := b)
      (b' := Pi.basisFun K n) (c := b) (c' := Pi.basisFun K n) (toLin' X)
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin'] at h
    rw [hP', hP, h, AlgEquiv.trans_apply, LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply]
    congr 1
  have hJ : Pᵀ * Cm * P = J (Fin m) K := by
    rw [← hb, ← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun K n),
      LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin']
  have hJinv : P' * Ci * P'ᵀ = -J (Fin m) K := by
    have hJY : J (Fin m) K * (P' * Ci * P'ᵀ) = 1 := by
      rw [← hJ]
      simp only [Matrix.mul_assoc, hPP', hCmCi]
      rw [← transpose_mul, hP, hP', Basis.toMatrix_mul_toMatrix_flip, transpose_one]
    calc P' * Ci * P'ᵀ = (-J (Fin m) K * J (Fin m) K) * (P' * Ci * P'ᵀ) := by
          rw [Matrix.neg_mul, J_squared, neg_neg, Matrix.one_mul]
      _ = -J (Fin m) K := by rw [Matrix.mul_assoc, hJY, Matrix.mul_one]
  refine ⟨m, ψ, ?_, fun X => ?_⟩
  · rw [← Module.finrank_fintype_fun_eq_card (R := K), Module.finrank_eq_card_basis b,
      Fintype.card_sum, Fintype.card_fin]
  · rw [← Matrix.neg_mul, ← Matrix.neg_mul, ← hJinv, ← hJ, hψ, hψ]
    simp only [transpose_mul, Matrix.mul_assoc, hPt]

end Matrix

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import TauCeti.LinearAlgebra.Matrix.Determinant.ComplementaryMinor

/-!
# Complementary order embeddings and Jacobi minors

Given an order embedding `I : Fin a ↪o Fin N` with `a + b = N`, its complementary order embedding
`Fin.orderEmbCompl hab I : Fin b ↪o Fin N` enumerates the `b` indices outside the range of `I` in
increasing order.

For any finite index type `m` with enumerations `e, pos : m ≃ Fin N`, Jacobi's complementary-minor
identity yields a sign `u : ℤˣ` independent of `R` and `A` such that whenever `A * B = 1`, `u`
times the minor of `A` on the rows outside `I` and the first `b` columns equals `det A` times the
minor of `Bᵀ` on the rows `I` and the last `a` columns in reverse order
(`Matrix.exists_sign_det_submatrix_orderEmbCompl`), and similarly for `B = A⁻¹` when `IsUnit A.det`
(`Matrix.exists_sign_det_submatrix_orderEmbCompl_nonsing_inv`).

## Main definitions and results

* `Fin.orderEmbCompl`: the increasing enumeration of the complement of `I : Fin a ↪o Fin N`.
* `Fin.range_orderEmbCompl`, `Fin.orderEmbCompl_injective`: range and injectivity of the complement.
* `Matrix.exists_sign_det_submatrix_orderEmbCompl`: ring-independent sign relating complementary
  minors of `A` and `Bᵀ` for `A * B = 1`.
* `Matrix.exists_sign_det_submatrix_orderEmbCompl_nonsing_inv`: specialization to `B = A⁻¹`.

## Provenance

Generalized from `grh-lean` (https://github.com/lsernau/grh-lean at commit
72fead102f663d5c7a407964a13dc0cf9d977207, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/GLn/Dual.lean` (`columnComplement`, `range_columnComplement`,
`columnComplement_injective`, `GL.exists_sign_minor_columnComplement`).
-/

public section

namespace Fin

/-- The order embedding `Fin b ↪o Fin N` enumerating the indices outside the range of
`I : Fin a ↪o Fin N`, where `a + b = N`. -/
noncomputable def orderEmbCompl {N a b : ℕ} (hab : a + b = N) (I : Fin a ↪o Fin N) :
    Fin b ↪o Fin N :=
  (Finset.univ.image I)ᶜ.orderEmbOfFin <| by
    simp [Finset.card_compl, Finset.card_image_of_injective _ I.injective, ← hab]

/-- The range of `Fin.orderEmbCompl hab I` is the complement of the range of `I`. -/
@[simp]
theorem range_orderEmbCompl {N a b : ℕ} (hab : a + b = N) (I : Fin a ↪o Fin N) :
    Set.range (orderEmbCompl hab I) = (Set.range I)ᶜ := by
  simp [orderEmbCompl]

/-- Taking the complementary order embedding is injective. -/
theorem orderEmbCompl_injective {N a b : ℕ} (hab : a + b = N) :
    Function.Injective (orderEmbCompl hab : (Fin a ↪o Fin N) → (Fin b ↪o Fin N)) := by
  intro I I' h_eq
  refine RelEmbedding.ext fun x ↦ ?_
  have h_range : Set.range I = Set.range I' := compl_injective <| by
    rw [← range_orderEmbCompl hab, ← range_orderEmbCompl hab, h_eq]
  exact congrFun ((I.strictMono.range_inj_of_wellFoundedLT I'.strictMono).mp h_range) x

end Fin

namespace Matrix

universe u v

/-- Given `a + b = N`, enumerations `e, pos : m ≃ Fin N`, and an order embedding
`I : Fin a ↪o Fin N`, there is a sign `u : ℤˣ` (independent of `R`, `A`, `B`) such that for every
commutative ring `R` and matrices `A, B : Matrix m m R` with `A * B = 1`, `u` times the minor of
`A` on the rows outside `I` and the first `b` columns equals `A.det` times the minor of `Bᵀ` on the
rows `I` and the last `a` columns in reverse order. -/
theorem exists_sign_det_submatrix_orderEmbCompl {m : Type u} [Fintype m] [DecidableEq m]
    {N a b : ℕ} (hab : a + b = N) (e pos : m ≃ Fin N) (I : Fin a ↪o Fin N) :
    ∃ u : ℤˣ, ∀ {R : Type v} [CommRing R] {A B : Matrix m m R}, A * B = 1 →
      ((u : ℤ) : R) * (A.submatrix (pos.symm ∘ Fin.orderEmbCompl hab I)
          (e.symm ∘ Fin.castLE (Nat.le_of_add_left_le hab.le))).det =
        A.det * (Bᵀ.submatrix (pos.symm ∘ I)
          (e.symm ∘ Fin.rev ∘ Fin.castLE (Nat.le_of_add_right_le hab.le))).det := by
  let ρ : Fin a ⊕ Fin b ≃ m := ((Equiv.refl (Fin a)).sumCongr Fin.revPerm).trans
    (((finSumFinEquiv.trans (finCongr hab)).trans Fin.revPerm).trans e.symm)
  have h_inl (t : Fin a) : ρ (.inl t) = e.symm (Fin.castLE (by omega) t).rev := by
    simp [ρ, Fin.ext_iff]
  have h_inr (t : Fin b) : ρ (.inr t) = e.symm (Fin.castLE (by omega) t) := by
    have h_index : N - (a + (b - (t + 1)) + 1) = t := by omega
    simp [ρ, Fin.ext_iff, h_index]
  let I' : Fin b ↪o Fin N := Fin.orderEmbCompl hab I
  have h_bij : (Sum.elim I I').Bijective := by
    refine (Fintype.bijective_iff_surjective_and_card _).mpr ⟨?_, by simp [hab]⟩
    rw [← Set.range_eq_univ, Set.Sum.elim_range, Fin.range_orderEmbCompl, Set.union_compl_self]
  let σ : Fin a ⊕ Fin b ≃ m := (Equiv.ofBijective _ h_bij).trans pos.symm
  let π : Equiv.Perm m := ρ.symm.trans σ
  have h_rows (s : Fin a ⊕ Fin b) : π (ρ s) = pos.symm (Sum.elim I I' s) := by simp [π, σ]
  refine ⟨π.sign, fun {R} _ {A B} hAB ↦ ?_⟩
  have h_jacobi := det_submatrix_comp_inr_eq_sign_mul_det_mul_det_submatrix_comp_inl A B hAB ρ 1 π
  simp only [Function.comp_def, h_rows, Sum.elim_inl, Sum.elim_inr] at h_jacobi
  simp only [Equiv.Perm.coe_one, id_eq, h_inl, h_inr, Equiv.Perm.sign_one, Units.val_one,
    Int.cast_one, one_mul, ← det_transpose (B.submatrix _ _), transpose_submatrix] at h_jacobi
  simp only [Function.comp_def]
  rw [h_jacobi, ← mul_assoc, ← mul_assoc, ← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one,
    one_mul]

/-- Specialization of `Matrix.exists_sign_det_submatrix_orderEmbCompl` to `B = A⁻¹` for a matrix
with invertible determinant. -/
theorem exists_sign_det_submatrix_orderEmbCompl_nonsing_inv {m : Type u} [Fintype m] [DecidableEq m]
    {N a b : ℕ} (hab : a + b = N) (e pos : m ≃ Fin N) (I : Fin a ↪o Fin N) :
    ∃ u : ℤˣ, ∀ {R : Type v} [CommRing R] {A : Matrix m m R}, IsUnit A.det →
      ((u : ℤ) : R) * (A.submatrix (pos.symm ∘ Fin.orderEmbCompl hab I)
          (e.symm ∘ Fin.castLE (Nat.le_of_add_left_le hab.le))).det =
        A.det * (A⁻¹ᵀ.submatrix (pos.symm ∘ I)
          (e.symm ∘ Fin.rev ∘ Fin.castLE (Nat.le_of_add_right_le hab.le))).det := by
  obtain ⟨u, hu⟩ := exists_sign_det_submatrix_orderEmbCompl.{u, v} hab e pos I
  exact ⟨u, fun hA ↦ hu (mul_nonsing_inv _ hA)⟩

end Matrix

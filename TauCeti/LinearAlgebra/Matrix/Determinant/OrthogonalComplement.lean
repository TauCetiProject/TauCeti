/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.LinearAlgebra.Matrix.Congruence
import TauCeti.LinearAlgebra.Matrix.ConjTranspose
import TauCeti.LinearAlgebra.Matrix.Determinant.ComplementaryMinor
import TauCeti.LinearAlgebra.Matrix.Submatrix

/-!
# The orthogonal complement of a frame and Jacobi's identity

Let `A` be a commutative ring with a ring endomorphism `σ` (of any type `S` of ring
homomorphisms), and write `Mᴴ = (M.map σ)ᵀ`. Let `J` be a square matrix indexed by `ν` and `g` a
square matrix such that `G = gᴴ J g` has a left inverse `H`. Split the columns of `g` along an
equivalence `e : β ⊕ α ≃ ν` into a frame `n = g_{·, β}` and the rest, and put `k = g H_{·, α}` and
`λ = (gᴴ J)_{α, ·}`. Then

* `λ k = 1` (`Matrix.submatrix_mul_mul_submatrix_eq_one`) and `nᴴ J k = 0`
  (`Matrix.transpose_map_submatrix_mul_mul_eq_zero`);
* every matrix `F` with `nᴴ J F = 0` is `k (λ F)`, and every vector `u` with `nᴴ J u = 0` is
  `k (λ u)` (`Matrix.eq_mul_of_mul_eq_zero`, `Matrix.eq_mulVec_of_mulVec_eq_zero`), so the
  columns of `k` are a basis of the `J`-orthogonal complement of the columns of `n`;
* **Jacobi's identity**: `det (kᴴ J k) = σ (det H * det (nᴴ J n))`
  (`Matrix.det_transpose_map_mul_mul_eq_map_det_mul_det`). Indeed `kᴴ J k = (Hᴴ)_{α, α}`, and
  Jacobi's complementary-minor identity gives `det H_{α, α} = det H * det G_{β, β}` with
  `G_{β, β} = nᴴ J n`. If `σ` is an involution and `J` is `σ`-hermitian, `Jᴴ = J`, both
  determinants are fixed by `σ`, and `det (kᴴ J k) = det H * det (nᴴ J n)`
  (`Matrix.det_transpose_map_mul_mul_eq_det_mul_det`).

Over a ring whose unimodular frames complete to invertible matrices, this applies to every frame
`n` with a left inverse. Together with the change of basis
`det ((k C)ᴴ J (k C)) = σ (det C) * det (kᴴ J k) * det C`
(`Matrix.det_transpose_map_mul_mul_mul`) it compares the Gram determinant of a matrix `F` whose
columns are `J`-orthogonal to `n` with that of `n`.

## Main results

* `Matrix.submatrix_mul_mul_submatrix_eq_one`, `Matrix.transpose_map_submatrix_mul_mul_eq_zero`:
  `λ k = 1` and `nᴴ J k = 0`.
* `Matrix.eq_mul_of_mul_eq_zero`, `Matrix.eq_mulVec_of_mulVec_eq_zero`: the columns of `k` span
  the `J`-orthogonal complement of `n`.
* `Matrix.det_transpose_map_mul_mul_eq_map_det_mul_det`,
  `Matrix.det_transpose_map_mul_mul_eq_det_mul_det`: Jacobi's identity between the Gram
  determinants of `n` and of `k`, in twisted form and for a hermitian `J`.

## References

* C. G. J. Jacobi, *De formatione et proprietatibus determinantium*, Journal fuer die reine und
  angewandte Mathematik 22 (1841), 285-318.
-/

public section

open Equiv

namespace Matrix

variable {A : Type*} [CommRing A] {S : Type*} [FunLike S A A] {σ : S}
  {ν β α γ : Type*} [Fintype ν] [DecidableEq ν] {J g H : Matrix ν ν A}

/-- `H * G = 1` for `G = gᴴ J g` makes `g` invertible, with inverse `H gᴴ J`. -/
private theorem mul_mul_eq_one (hH : H * ((g.map σ)ᵀ * J * g) = 1) :
    g * (H * ((g.map σ)ᵀ * J)) = 1 :=
  mul_eq_one_comm.1 (by rw [Matrix.mul_assoc, hH])

/-- With `G = gᴴ J g`, `H * G = 1` and a splitting `e : β ⊕ α ≃ ν`, the matrix
`λ = (gᴴ J)_{α, ·}` is a left inverse of `k = g H_{·, α}`. -/
theorem submatrix_mul_mul_submatrix_eq_one [DecidableEq α] (hH : H * ((g.map σ)ᵀ * J * g) = 1)
    (e : β ⊕ α ≃ ν) :
    ((g.map σ)ᵀ * J).submatrix (e ∘ Sum.inr) id * (g * H.submatrix id (e ∘ Sum.inr)) = 1 := by
  rw [mul_submatrix_id, ← submatrix_mul _ _ _ _ _ Function.bijective_id, ← Matrix.mul_assoc,
    mul_eq_one_comm.1 hH,
    submatrix_one _ (e.injective.comp Sum.inr_injective)]

/-- With `G = gᴴ J g` and `H * G = 1`, let `n = g_{·, β}` and `k = g H_{·, α}` for a splitting
`e : β ⊕ α ≃ ν`. The columns of `k` are `J`-orthogonal to those of `n`: `nᴴ J k = 0`. -/
theorem transpose_map_submatrix_mul_mul_eq_zero (hH : H * ((g.map σ)ᵀ * J * g) = 1)
    (e : β ⊕ α ≃ ν) :
    ((g.submatrix id (e ∘ Sum.inl)).map σ)ᵀ * J * (g * H.submatrix id (e ∘ Sum.inr)) = 0 := by
  rw [mul_submatrix_id, transpose_map_submatrix_mul_mul_submatrix, ← Matrix.mul_assoc,
    mul_eq_one_comm.1 hH]
  exact Matrix.ext fun _ _ ↦ one_apply_ne fun h ↦ Sum.inl_ne_inr (e.injective h)

/-- With `G = gᴴ J g` and `H * G = 1`, let `n = g_{·, β}` and `k = g H_{·, α}` for a splitting
`e : β ⊕ α ≃ ν`. Every vector `u` with `nᴴ J u = 0` is `k (λ u)` for `λ = (gᴴ J)_{α, ·}`. -/
theorem eq_mulVec_of_mulVec_eq_zero [Fintype α] (hH : H * ((g.map σ)ᵀ * J * g) = 1)
    (e : β ⊕ α ≃ ν) {u : ν → A}
    (hu : (((g.submatrix id (e ∘ Sum.inl)).map σ)ᵀ * J) *ᵥ u = 0) :
    u = (g * H.submatrix id (e ∘ Sum.inr)) *ᵥ ((((g.map σ)ᵀ * J) *ᵥ u) ∘ e ∘ Sum.inr) := by
  rw [transpose_map_submatrix_mul] at hu
  -- the entries `e (β)` of `gᴴ J u` are those of `nᴴ J u`
  have hx : (((g.map σ)ᵀ * J) *ᵥ u) ∘ e ∘ Sum.inl = 0 := funext fun b ↦ congrFun hu b
  calc u
    _ = g *ᵥ (H *ᵥ (((g.map σ)ᵀ * J) *ᵥ u)) := by
      rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, mul_mul_eq_one hH, one_mulVec]
    _ = _ := by rw [mulVec_eq_mulVec_comp_of_comp_eq_zero e hx, mulVec_mulVec]

/-- With `G = gᴴ J g` and `H * G = 1`, let `n = g_{·, β}` and `k = g H_{·, α}` for a splitting
`e : β ⊕ α ≃ ν`. Every matrix `F` with `nᴴ J F = 0` is `k (λ F)` for `λ = (gᴴ J)_{α, ·}`: this is
`Matrix.eq_mulVec_of_mulVec_eq_zero` for each column of `F`. -/
theorem eq_mul_of_mul_eq_zero [Fintype α] {F : Matrix ν γ A} (hH : H * ((g.map σ)ᵀ * J * g) = 1)
    (e : β ⊕ α ≃ ν) (hF : ((g.submatrix id (e ∘ Sum.inl)).map σ)ᵀ * J * F = 0) :
    F = (g * H.submatrix id (e ∘ Sum.inr)) * ((g.map σ)ᵀ * J * F).submatrix (e ∘ Sum.inr) id := by
  refine ext_col fun j ↦ ?_
  have hu : (((g.submatrix id (e ∘ Sum.inl)).map σ)ᵀ * J) *ᵥ F.col j = 0 := by
    rw [← col_mul_eq_mulVec_col, hF, col_zero, Pi.zero_apply]
  rw [col_mul_eq_mulVec_col, col_submatrix_eq_comp, col_mul_eq_mulVec_col]
  exact eq_mulVec_of_mulVec_eq_zero hH e hu

/-- **Jacobi's identity for the orthogonal complement of a frame, twisted form.** Let `H * G = 1`
for `G = gᴴ J g`, where `Mᴴ = (M.map σ)ᵀ`, and split the columns along `e : β ⊕ α ≃ ν` into the
frame `n = g_{·, β}` and the basis `k = g H_{·, α}` of its `J`-orthogonal complement. Then
`det (kᴴ J k) = σ (det H * det (nᴴ J n))`: `kᴴ J k` is the block `(Hᴴ)_{α, α}`, and Jacobi's
complementary-minor identity gives `det H_{α, α} = det H * det G_{β, β}`. -/
theorem det_transpose_map_mul_mul_eq_map_det_mul_det [RingHomClass S A A] [Fintype β]
    [DecidableEq β] [Fintype α] [DecidableEq α] (hH : H * ((g.map σ)ᵀ * J * g) = 1)
    (e : β ⊕ α ≃ ν) :
    det (((g * H.submatrix id (e ∘ Sum.inr)).map σ)ᵀ * J * (g * H.submatrix id (e ∘ Sum.inr))) =
      σ (H.det *
        det (((g.submatrix id (e ∘ Sum.inl)).map σ)ᵀ * J * g.submatrix id (e ∘ Sum.inl))) := by
  set G := (g.map σ)ᵀ * J * g with hG_def
  -- `kᴴ J k` is the block `(Hᴴ G H)_{α, α} = (Hᴴ)_{α, α}`, since `G H = 1`.
  have hk : ((g * H.submatrix id (e ∘ Sum.inr)).map σ)ᵀ * J * (g * H.submatrix id (e ∘ Sum.inr)) =
      ((H.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)).map σ)ᵀ := by
    have h := transpose_map_mul_mul_mul (σ : A →+* A) J g H
    simp only [RingHom.coe_coe] at h
    rw [mul_submatrix_id, transpose_map_submatrix_mul_mul_submatrix, h, ← hG_def,
      Matrix.mul_assoc, mul_eq_one_comm.1 hH, Matrix.mul_one, ← submatrix_map, transpose_submatrix]
  have hJac := det_submatrix_comp_inr_eq_sign_mul_det_mul_det_submatrix_comp_inl H G hH e 1 1
  simp only [Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Perm.coe_one,
    Function.id_comp] at hJac
  have hdet := RingHom.map_det (σ : A →+* A) (H.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr))
  simp only [RingHom.coe_coe, RingHom.mapMatrix_apply] at hdet
  -- the block `G_{β, β}` is `nᴴ J n`
  rw [hk, det_transpose, ← hdet, hJac, transpose_map_submatrix_mul_mul_submatrix]

/-- **Jacobi's identity for the orthogonal complement of a frame.** Let `σ` be an involution and
`J` be `σ`-hermitian, `Jᴴ = J` for `Mᴴ = (M.map σ)ᵀ`; let `H * G = 1` for `G = gᴴ J g`, and split
the columns along `e : β ⊕ α ≃ ν` into the frame `n = g_{·, β}` and the basis `k = g H_{·, α}` of
its `J`-orthogonal complement. Then `det (kᴴ J k) = det H * det (nᴴ J n)`: the twisted form
`Matrix.det_transpose_map_mul_mul_eq_map_det_mul_det`, where both determinants are fixed by `σ`. -/
theorem det_transpose_map_mul_mul_eq_det_mul_det [RingHomClass S A A] [Fintype β] [DecidableEq β]
    [Fintype α] [DecidableEq α]
    (hσ : Function.Involutive σ) (hJ : (J.map σ)ᵀ = J) (hH : H * ((g.map σ)ᵀ * J * g) = 1)
    (e : β ⊕ α ≃ ν) :
    det (((g * H.submatrix id (e ∘ Sum.inr)).map σ)ᵀ * J * (g * H.submatrix id (e ∘ Sum.inr))) =
      H.det * det (((g.submatrix id (e ∘ Sum.inl)).map σ)ᵀ * J * g.submatrix id (e ∘ Sum.inl)) := by
  -- `H` is hermitian as the inverse of the hermitian `gᴴ J g`
  have hHh : (H.map σ)ᵀ = H := by
    have hHG : (H.map σ)ᵀ * ((g.map σ)ᵀ * J * g) = 1 := by
      rw [← transpose_map_transpose_map_mul_mul hσ hJ g, ← transpose_map_mul, mul_eq_one_comm.1 hH,
        Matrix.map_one _ (map_zero σ) (map_one σ), transpose_one]
    calc (H.map σ)ᵀ
      _ = (H.map σ)ᵀ * (((g.map σ)ᵀ * J * g) * H) := by rw [mul_eq_one_comm.1 hH, Matrix.mul_one]
      _ = H := by rw [← Matrix.mul_assoc, hHG, Matrix.one_mul]
  rw [det_transpose_map_mul_mul_eq_map_det_mul_det hH e, map_mul,
    map_det_eq_det_of_transpose_map_eq hHh,
    map_det_eq_det_of_transpose_map_eq (transpose_map_transpose_map_mul_mul hσ hJ _)]

end Matrix

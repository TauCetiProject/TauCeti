/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.LinearAlgebra.SymplecticGroup
import Mathlib.Tactic.NoncommRing

/-!
# Membership in the symplectic Lie algebra

The symplectic Lie algebra `LieAlgebra.Symplectic.sp l R` is cut out by a condition relating a
matrix to its transpose through the canonical skew-symmetric matrix `Matrix.J l R`. This file
spells that condition out as `Aᵀ * J = -(J * A)`, the symplectic counterpart of Mathlib's
`LieAlgebra.Orthogonal.mem_so`, and rewrites it as a **conjugation by `J`**,
`Aᵀ = J * (-A) * J⁻¹`, which is the form the matrix exponential consumes.

Since `J * J = -1`, all of this is available over an arbitrary commutative ring with no
invertibility side conditions; `Matrix.eq_J_conj_iff_mul_J_eq` is the cancellation that moves a
matrix past `J`.

## Main results

* `LieAlgebra.Symplectic.mem_sp`: membership in the symplectic Lie algebra, spelled out as
  `Aᵀ * J = -(J * A)`.
* `LieAlgebra.Symplectic.mem_sp_iff_transpose_eq_J_conj_neg`: the same condition as a conjugation,
  `Aᵀ = J * (-A) * J⁻¹`.
* `LieAlgebra.Symplectic.mem_sp_iff_J_mul_transpose_mul_J_eq`: the same condition as a fixed
  point, `J * Aᵀ * J = A`.
* `LieAlgebra.Symplectic.mul_J_add_J_mul_transpose_eq_zero`: the additive form
  `A * J + J * Aᵀ = 0`.
* `LieAlgebra.Symplectic.transpose_mem_sp` and `LieAlgebra.Symplectic.conjTranspose_mem_sp`: the
  symplectic Lie algebra is stable under transpose, and under conjugate transpose over a star
  ring.
* `LieAlgebra.Symplectic.J_conj_eq_neg_transpose`: on symplectic Lie matrices, conjugation by `J`
  is negative transpose.
* `Matrix.mem_symplecticLieAlgebra_iff`: the entrywise block criterion, with symmetric
  off-diagonal blocks and opposite transposed diagonal blocks.
* `Matrix.mem_range_scalar_of_commute_sp`: a matrix commuting with every element of `sp l R` is
  scalar, over every commutative ring.
* `Matrix.J_mulVec`: the action of the standard symplectic matrix on a vector.
* `LieAlgebra.Symplectic.trace_eq_zero_of_mem_sp`: symplectic Lie matrices have trace zero.
-/

public section

open Matrix

namespace LieAlgebra.Symplectic

variable {l : Type*} [DecidableEq l] [Fintype l] {R : Type*} [CommRing R]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **Membership in the symplectic Lie algebra**: `A` is skew-adjoint for the canonical
skew-symmetric form exactly when `Aᵀ * J = -(J * A)`. The symplectic counterpart of Mathlib's
`LieAlgebra.Orthogonal.mem_so`, whose `J = 1` makes the two multiplications disappear. -/
@[simp]
theorem mem_sp (A : Matrix (l ⊕ l) (l ⊕ l) R) :
    A ∈ sp l R ↔ Aᵀ * J l R = -(J l R * A) := by
  rw [sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, mul_neg]

/-- **Membership in the symplectic Lie algebra, as a conjugation**: `Aᵀ = J * (-A) * J⁻¹`. This is
the shape `NormedSpace.exp` transports, by `Matrix.exp_conj`. -/
theorem mem_sp_iff_transpose_eq_J_conj_neg (A : Matrix (l ⊕ l) (l ⊕ l) R) :
    A ∈ sp l R ↔ Aᵀ = J l R * (-A) * (J l R)⁻¹ := by
  rw [mem_sp, Matrix.eq_J_conj_iff_mul_J_eq, mul_neg]

/-- **Membership in the symplectic Lie algebra, as a fixed point**: `A` lies in `sp l R` exactly
when it is fixed by `Z ↦ J * Zᵀ * J`. -/
theorem mem_sp_iff_J_mul_transpose_mul_J_eq (A : Matrix (l ⊕ l) (l ⊕ l) R) :
    A ∈ sp l R ↔ J l R * Aᵀ * J l R = A := by
  rw [mem_sp_iff_transpose_eq_J_conj_neg, J_inv]
  simp only [mul_neg, neg_mul, neg_neg]
  constructor
  · intro h
    rw [h, J_mul_mul_J_mul_J]
  · intro h
    rw [← J_mul_mul_J_mul_J Aᵀ, h]

/-- **Membership in the symplectic Lie algebra, in additive form**: `A * J + J * Aᵀ = 0`. This is
the shape a congruence computation `X ↦ X * J * Xᵀ` differentiates to. -/
theorem mul_J_add_J_mul_transpose_eq_zero {A : Matrix (l ⊕ l) (l ⊕ l) R} (hA : A ∈ sp l R) :
    A * J l R + J l R * Aᵀ = 0 := by
  rw [(mem_sp_iff_transpose_eq_J_conj_neg A).mp hA, J_inv]
  calc A * J l R + J l R * (J l R * (-A) * (-J l R))
      = A * J l R + (J l R * J l R) * (-A) * (-J l R) := by noncomm_ring
    _ = 0 := by rw [J_squared]; noncomm_ring

/-- Membership in the symplectic Lie algebra is equivalent to the linearized
symplectic-group equation, also in characteristic two. -/
theorem mem_sp_iff_mul_J_add_J_mul_transpose_eq_zero (A : Matrix (l ⊕ l) (l ⊕ l) R) :
    A ∈ sp l R ↔ A * J l R + J l R * Aᵀ = 0 := by
  constructor
  · exact mul_J_add_J_mul_transpose_eq_zero
  · intro h
    rw [mem_sp_iff_transpose_eq_J_conj_neg, J_inv]
    have h' : J l R * A * J l R - Aᵀ = 0 := by
      simpa [mul_add, ← mul_assoc, J_squared, sub_eq_add_neg] using
        congrArg (fun X ↦ J l R * X) h
    rw [← sub_eq_zero.mp h']
    noncomm_ring

/-- Transpose preserves the symplectic Lie algebra. -/
theorem transpose_mem_sp {X : Matrix (l ⊕ l) (l ⊕ l) R} (hX : X ∈ sp l R) :
    Xᵀ ∈ sp l R := by
  rw [mem_sp, transpose_transpose, eq_neg_iff_add_eq_zero]
  exact mul_J_add_J_mul_transpose_eq_zero hX

/-- **Conjugate transpose preserves the symplectic Lie algebra**, over any commutative star ring:
the conjugate transpose of `A * J + J * Aᵀ = 0` is the same equation for `Aᴴ`, since `Jᴴ = -J`.
Over `ℂ` this makes the complex symplectic Lie algebra a star-closed subspace of the complex
matrices, whose skew-Hermitian elements form the Lie algebra of the compact symplectic group. -/
theorem conjTranspose_mem_sp [StarRing R] {X : Matrix (l ⊕ l) (l ⊕ l) R} (hX : X ∈ sp l R) :
    Xᴴ ∈ sp l R := by
  have h := congrArg conjTranspose (mul_J_add_J_mul_transpose_eq_zero hX)
  rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul, ← star_eq_conjTranspose (J l R),
    star_J, conjTranspose_zero, conjTranspose_transpose_eq_transpose_conjTranspose] at h
  rw [mem_sp, eq_neg_iff_add_eq_zero, ← neg_eq_zero, ← h]
  noncomm_ring

/-- On the symplectic Lie algebra, conjugation by `J` is negative transpose. -/
theorem J_conj_eq_neg_transpose {X : Matrix (l ⊕ l) (l ⊕ l) R} (hX : X ∈ sp l R) :
    J l R * X * (J l R)⁻¹ = -Xᵀ := by
  rw [(mem_sp_iff_transpose_eq_J_conj_neg X).mp hX]
  simp

end LieAlgebra.Symplectic

namespace Matrix

variable {l : Type*} [DecidableEq l] [Fintype l] {R : Type*} [CommRing R]

/-- The standard symplectic matrix acts on a vector as minus that vector multiplied on the left. -/
theorem J_mulVec (v : l ⊕ l → R) : J l R *ᵥ v = -(v ᵥ* J l R) := by
  rw [← mulVec_transpose, J_transpose, neg_mulVec, neg_neg]

/-- A symplectic Lie matrix has symmetric off-diagonal blocks and diagonal blocks
which are negatives of each other's transposes. This criterion includes characteristic two. -/
theorem mem_symplecticLieAlgebra_iff (A : Matrix (l ⊕ l) (l ⊕ l) R) :
    A ∈ LieAlgebra.Symplectic.sp l R ↔
      (∀ i j, A (.inl i) (.inr j) = A (.inl j) (.inr i)) ∧
      (∀ i j, A (.inr i) (.inl j) = A (.inr j) (.inl i)) ∧
      (∀ i j, A (.inr i) (.inr j) = -A (.inl j) (.inl i)) := by
  rw [← A.fromBlocks_toBlocks, LieAlgebra.Symplectic.mem_sp]
  simp only [J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_neg,
    mul_zero, zero_mul, mul_one, one_mul, mul_neg, neg_mul, add_zero, zero_add,
    fromBlocks_inj, neg_inj, neg_neg]
  simp only [← Matrix.ext_iff, transpose_apply, toBlocks₁₁, toBlocks₁₂,
    toBlocks₂₁, toBlocks₂₂, Matrix.neg_apply, Matrix.of_apply, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂]
  grind

/-- The long root vector `E_(i, n + i)` lies in `sp l R`. -/
theorem single_inl_inr_mem_sp (i : l) :
    single (Sum.inl i) (Sum.inr i) (1 : R) ∈ LieAlgebra.Symplectic.sp l R := by
  rw [mem_symplecticLieAlgebra_iff]
  refine ⟨fun a b ↦ ?_, fun a b ↦ ?_, fun a b ↦ ?_⟩ <;> grind

/-- The long root vector `E_(n + i, i)` lies in `sp l R`. -/
theorem single_inr_inl_mem_sp (i : l) :
    single (Sum.inr i) (Sum.inl i) (1 : R) ∈ LieAlgebra.Symplectic.sp l R := by
  rw [mem_symplecticLieAlgebra_iff]
  refine ⟨fun a b ↦ ?_, fun a b ↦ ?_, fun a b ↦ ?_⟩ <;> grind

/-- The Levi element `E_(i, j) - E_(n + j, n + i)` lies in `sp l R`. -/
theorem single_inl_inl_sub_single_inr_inr_mem_sp (i j : l) :
    single (Sum.inl i) (Sum.inl j) (1 : R) - single (Sum.inr j) (Sum.inr i) 1 ∈
      LieAlgebra.Symplectic.sp l R := by
  rw [mem_symplecticLieAlgebra_iff]
  refine ⟨fun a b ↦ ?_, fun a b ↦ ?_, fun a b ↦ ?_⟩ <;> grind [Matrix.sub_apply]

/-- **A matrix commuting with the symplectic Lie algebra is scalar**, over every commutative
ring: commuting with the long root vectors `E_(i, n + i)` and `E_(n + i, i)` kills the
off-diagonal entries and pairs `i` with `n + i`, and commuting with `E_(i, j) - E_(n + j, n + i)`
compares the diagonal entries at `i` and `j`. -/
theorem mem_range_scalar_of_commute_sp (M : Matrix (l ⊕ l) (l ⊕ l) R)
    (hM : ∀ X ∈ LieAlgebra.Symplectic.sp l R, Commute M X) :
    M ∈ Set.range (scalar (l ⊕ l)) := by
  cases isEmpty_or_nonempty l with
  | inl _ => exact ⟨0, by ext a; exact isEmptyElim a⟩
  | inr h =>
  obtain ⟨z⟩ := h
  -- Commuting with the long root vectors makes `M` diagonal, with equal entries at `i` and
  -- `n + i`.
  have hp (i : l) := (hM _ (single_inl_inr_mem_sp (R := R) i)).symm
  have hn (i : l) := (hM _ (single_inr_inl_mem_sp (R := R) i)).symm
  have hoff (a b : l ⊕ l) (hab : a ≠ b) : M a b = 0 := by
    cases b with
    | inl i => exact col_eq_zero_of_commute_single (hp i) hab
    | inr i => exact col_eq_zero_of_commute_single (hn i) hab
  -- Commuting with a Levi element compares the diagonal entries at `i` and `j`.
  have hd (i : l) : M (Sum.inl i) (Sum.inl i) = M (Sum.inl z) (Sum.inl z) := by
    have he := congrArg (fun N : Matrix (l ⊕ l) (l ⊕ l) R ↦ N (Sum.inl i) (Sum.inl z))
      (hM _ (single_inl_inl_sub_single_inr_inr_mem_sp (R := R) i z)).eq
    simpa [mul_sub, sub_mul, mul_apply, single_apply, Finset.sum_ite_eq', Finset.sum_ite_eq]
      using he
  refine ⟨M (Sum.inl z) (Sum.inl z), ?_⟩
  ext a b
  by_cases hab : a = b
  · subst b
    rw [scalar_apply, diagonal_apply_eq]
    cases a with
    | inl i => exact (hd i).symm
    | inr i => exact ((diag_eq_of_commute_single (hp i)).symm.trans (hd i)).symm
  · simp [scalar_apply, diagonal_apply_ne _ hab, hoff a b hab]

end Matrix

namespace LieAlgebra.Symplectic

variable {l : Type*} [DecidableEq l] [Fintype l] {R : Type*} [CommRing R]

/-- **Symplectic Lie matrices have trace zero**, over every commutative ring: the two diagonal
blocks are negatives of each other's transposes. -/
theorem trace_eq_zero_of_mem_sp {A : Matrix (l ⊕ l) (l ⊕ l) R} (hA : A ∈ sp l R) :
    A.trace = 0 := by
  obtain ⟨-, -, h⟩ := (Matrix.mem_symplecticLieAlgebra_iff A).mp hA
  simp [Matrix.trace, Fintype.sum_sum_type, h]

end LieAlgebra.Symplectic

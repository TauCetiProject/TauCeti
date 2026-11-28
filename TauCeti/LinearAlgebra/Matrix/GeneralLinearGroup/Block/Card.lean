/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring

/-!
# Cardinality of block upper triangular subgroups of `GL`

For finite index types `N` and `T` and a natural number `j`, let `blockChainIndex N T j` be the
disjoint union of `N` and `j` copies of `T`, with block numbering `blockChainNumber N T j` sending
`N` to `0` and the `l`-th copy of `T` to `l`. The corresponding block upper triangular subgroup
`TauCeti.blockTriangularGroup R (blockChainNumber N T j)` of `GL (blockChainIndex N T j) R` has
cardinality `#GL N R * (#GL T R) ^ j * #R ^ k`, where the exponent `k` depends only on `N`, `T`,
and `j` and not on the commutative ring `R`.

## Main definitions and results

* `TauCeti.blockChainIndex`: the index type for one block `N` followed by `j` blocks `T`.
* `TauCeti.blockChainNumber`: the block numbering `blockChainIndex N T j → Fin (j + 1)`.
* `TauCeti.blockTriangular_fromBlocks_blockChainNumber_succ_iff`: block upper triangularity of a
  `fromBlocks` matrix on `blockChainIndex N T (j + 1)`.
* `TauCeti.card_blockTriangularGroup_blockChainNumber_succ`: one-step cardinality recursion.
* `TauCeti.exists_card_blockTriangularGroup_blockChainNumber_eq`: the closed-form cardinality
  formula with exponent independent of `R`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file `src/New/Determinant/Chain/TriangleNorms.lean`
(`New.blockTriangular_fromBlocks_blockNumber_succ_iff`, `New.card_parabolic_blockNumber_succ`,
`New.exists_card_parabolic_blockNumber_eq`).
-/

public section

open Matrix Fintype

namespace TauCeti

universe v

/-- The disjoint union of one block `N` and `j` copies of `T`, constructed iteratively. -/
abbrev blockChainIndex (N T : Type v) : ℕ → Type v
  | 0 => N
  | j + 1 => blockChainIndex N T j ⊕ T

instance instFintypeBlockChainIndex {N T : Type v} [Fintype N] [Fintype T] :
    ∀ j : ℕ, Fintype (blockChainIndex N T j)
  | 0 => inferInstanceAs (Fintype N)
  | j + 1 => @instFintypeSum _ _ (instFintypeBlockChainIndex j) _

instance instDecidableEqBlockChainIndex {N T : Type v} [DecidableEq N] [DecidableEq T] :
    ∀ j : ℕ, DecidableEq (blockChainIndex N T j)
  | 0 => inferInstanceAs (DecidableEq N)
  | j + 1 => @instDecidableEqSum _ _ (instDecidableEqBlockChainIndex j) _

/-- The block numbering on `blockChainIndex N T j`, assigning `0` to `N` and `l` to the `l`-th
copy of `T`. -/
def blockChainNumber (N T : Type v) : ∀ j : ℕ, blockChainIndex N T j → Fin (j + 1)
  | 0, _ => 0
  | j + 1, .inl a => (blockChainNumber N T j a).castSucc
  | j + 1, .inr _ => Fin.last (j + 1)

/-- A `fromBlocks` matrix on `blockChainIndex N T (j + 1) = blockChainIndex N T j ⊕ T` is block
upper triangular for `blockChainNumber N T (j + 1)` if and only if its upper-left block is block
upper triangular for `blockChainNumber N T j` and its lower-left block vanishes. -/
theorem blockTriangular_fromBlocks_blockChainNumber_succ_iff {N T : Type v} {R : Type*} [Zero R]
    {j : ℕ} {A : Matrix (blockChainIndex N T j) (blockChainIndex N T j) R}
    {B : Matrix (blockChainIndex N T j) T R}
    {C : Matrix T (blockChainIndex N T j) R} {D : Matrix T T R} :
    (fromBlocks A B C D).BlockTriangular (blockChainNumber N T (j + 1)) ↔
      A.BlockTriangular (blockChainNumber N T j) ∧ C = 0 := by
  refine ⟨fun h ↦ ⟨fun a b hlt ↦ h (i := .inl a) (j := .inl b)
      (by simpa [blockChainNumber] using hlt),
    Matrix.ext fun a b ↦ h (i := .inr a) (j := .inl b) (by simp [blockChainNumber])⟩, ?_⟩
  rintro ⟨hA, rfl⟩ (a | a) (b | b) hlt
  · exact hA (by simpa [blockChainNumber] using hlt)
  · simp [blockChainNumber, ← Fin.top_eq_last] at hlt
  · simp
  · simp [blockChainNumber] at hlt

/-- An invertible block upper triangular matrix for `blockChainNumber N T (j + 1)` decomposes into
an invertible block upper triangular matrix for `blockChainNumber N T j`, an arbitrary upper-right
block, and an invertible last diagonal block, so the cardinalities multiply. -/
theorem card_blockTriangularGroup_blockChainNumber_succ (N T : Type v) [Fintype N] [Fintype T]
    [DecidableEq N] [DecidableEq T] (R : Type*) [CommRing R] (j : ℕ) :
    Nat.card (blockTriangularGroup R (blockChainNumber N T (j + 1))) =
      Nat.card (blockTriangularGroup R (blockChainNumber N T j)) *
        (Nat.card (Matrix (blockChainIndex N T j) T R) * Nat.card (GL T R)) := by
  let P (k : ℕ) : Subgroup (GL (blockChainIndex N T k) R) :=
    blockTriangularGroup R (blockChainNumber N T k)
  let mat (u : P (j + 1)) : Matrix (blockChainIndex N T j ⊕ T) (blockChainIndex N T j ⊕ T) R :=
    (u : GL (blockChainIndex N T (j + 1)) R).val
  have h_corners (u : P (j + 1)) :
      (mat u).toBlocks₁₁.BlockTriangular (blockChainNumber N T j) ∧ (mat u).toBlocks₂₁ = 0 := by
    rw [← blockTriangular_fromBlocks_blockChainNumber_succ_iff, fromBlocks_toBlocks]
    exact mem_blockTriangularGroup_iff.mp u.property
  have h_blocks (u : P (j + 1)) :
      fromBlocks (mat u).toBlocks₁₁ (mat u).toBlocks₁₂ 0 (mat u).toBlocks₂₂ = mat u := by
    rw [← (h_corners u).right, fromBlocks_toBlocks]
  have h_unit (u : P (j + 1)) : IsUnit (mat u).toBlocks₁₁ ∧ IsUnit (mat u).toBlocks₂₂ := by
    rw [← isUnit_fromBlocks_zero₂₁, h_blocks]
    exact Units.isUnit _
  let e : P (j + 1) ≃ P j × Matrix (blockChainIndex N T j) T R × GL T R :=
    { toFun u :=
        (⟨(h_unit u).left.unit, mem_blockTriangularGroup_iff.mpr (h_corners u).left⟩,
          (mat u).toBlocks₁₂, (h_unit u).right.unit)
      invFun := fun (x, y, z) ↦
        ⟨(isUnit_fromBlocks_zero₂₁ (B := y).mpr ⟨x.val.isUnit, z.isUnit⟩).unit,
          mem_blockTriangularGroup_iff.mpr <|
            blockTriangular_fromBlocks_blockChainNumber_succ_iff.mpr
              ⟨mem_blockTriangularGroup_iff.mp x.property, rfl⟩⟩
      left_inv u := Subtype.ext (Units.ext (h_blocks u))
      right_inv := fun (x, y, z) ↦
        Prod.ext (Subtype.ext (Units.ext rfl)) (Prod.ext rfl (Units.ext rfl)) }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod]

/-- The block upper triangular subgroup of `GL` with one diagonal block indexed by `N` and `j`
diagonal blocks indexed by `T` has cardinality `#GL N R * (#GL T R) ^ j * #R ^ k`, with `k`
independent of the commutative ring `R`. -/
theorem exists_card_blockTriangularGroup_blockChainNumber_eq.{u} (N T : Type v) [Fintype N]
    [Fintype T] [DecidableEq N] [DecidableEq T] (j : ℕ) :
    ∃ k : ℕ, ∀ (R : Type u) [CommRing R],
      Nat.card (blockTriangularGroup R (blockChainNumber N T j)) =
        Nat.card (GL N R) * Nat.card (GL T R) ^ j * Nat.card R ^ k := by
  induction j with
  | zero =>
    refine ⟨0, fun R _ ↦ ?_⟩
    have h_top : blockTriangularGroup R (blockChainNumber N T 0) = (⊤ : Subgroup (GL N R)) :=
      eq_top_iff.mpr fun g _ ↦ mem_blockTriangularGroup_iff.mpr fun a b hlt ↦ by
        simp [blockChainNumber] at hlt
    rw [h_top, pow_zero, pow_zero, mul_one, mul_one]
    exact Subgroup.card_top
  | succ j ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + card (blockChainIndex N T j) * card T, fun R _ ↦ ?_⟩
    have h_matrix : Nat.card (Matrix (blockChainIndex N T j) T R) =
        Nat.card R ^ (card (blockChainIndex N T j) * card T) := by
      simp [Matrix, Nat.card_fun, ← pow_mul, mul_comm]
    rw [card_blockTriangularGroup_blockChainNumber_succ, hk, h_matrix]
    ring

end TauCeti

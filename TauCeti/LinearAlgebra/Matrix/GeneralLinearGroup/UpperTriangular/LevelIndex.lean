/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Block
public import Mathlib.Data.Rat.Defs
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Ring

/-!
# Index normalization for a chain of block triangular levels

Over a finite commutative ring, compare the flag with blocks `N, T, …, T` with the
flag with blocks `N, T`. Weight the indices by the appropriate general linear group
orders. The remaining power of the ring cardinality counts the entries between pairs
of *later* blocks: the entries from `N` to a later block cancel.

This is the finite-ring calculation used at the twist places in
`New.Data.exists_stdLevelIndex_lastLevel_eq` in `grh/src/New/Determinant/Chain/ChainNorms.lean`
of [grh-lean](https://github.com/lsernau/grh-lean) (revision `72fead1`).
-/

public section

open Matrix

namespace TauCeti

/-- For a flag with one initial block `N` and `m` copies of `T`, write `I_j` for the index of
its first `j + 1` blocks' upper triangular group in the full general linear group of order `G_j`.
Then `I_m G₀ G₁^m / G_m = (I₁ G₀)^m / (#R ^ (m.choose 2 * #T²))`. The exponent counts
matrix positions between distinct later blocks, with the row block before the column block. -/
theorem blockTriangularGroup_index_ratio (N T : Type*) [Fintype N] [DecidableEq N]
    [Fintype T] [DecidableEq T] (m : ℕ) (R : Type*) [CommRing R] [Finite R] :
    let G (j : ℕ) := (Nat.card (GL (N ⊕ Fin j × T) R) : ℚ)
    let I (j : ℕ) := ((blockTriangularGroup R
      (Sum.elim (fun _ ↦ 0) (·.1.succ) : N ⊕ Fin j × T → Fin (j + 1))).index : ℚ)
    I m * Nat.card (GL N R) * G 1 ^ m / G m =
      (I 1 * Nat.card (GL N R)) ^ m / (Nat.card R : ℚ) ^ (m.choose 2 * Nat.card T ^ 2) := by
  intro G I
  let q : ℚ := Nat.card R
  let A : ℚ := Nat.card (GL N R)
  let B : ℚ := Nat.card (GL T R)
  have h (j : ℕ) :
      I j * (A * B ^ j * q ^ (Nat.card N * j * Nat.card T + j.choose 2 * Nat.card T ^ 2)) =
        G j := by
    have hindex := (blockTriangularGroup R
      (Sum.elim (fun _ ↦ 0) (·.1.succ) : N ⊕ Fin j × T → Fin (j + 1))).index_mul_card
    rw [natCard_blockTriangularGroup_sum N T j R] at hindex
    dsimp only [I, A, B, q, G]
    exact_mod_cast hindex
  have h₁ : G 1 = I 1 * A * B * q ^ (Nat.card N * Nat.card T) := by
    simpa [Nat.choose_eq_zero_of_lt (by decide : 1 < 2), mul_assoc] using (h 1).symm
  have hg : G m ≠ 0 := Nat.cast_ne_zero.mpr (Nat.card_pos (α := GL (N ⊕ Fin m × T) R)).ne'
  have hq : q ≠ 0 := Nat.cast_ne_zero.mpr (Nat.card_pos (α := R)).ne'
  apply (div_eq_div_iff hg (pow_ne_zero _ hq)).mpr
  rw [h₁, ← h m, mul_pow, mul_pow, mul_pow, ← pow_mul, pow_add]
  have hnt : Nat.card N * Nat.card T * m = Nat.card N * m * Nat.card T := by ring
  rw [hnt]
  ring

end TauCeti

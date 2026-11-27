/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Instances.Matrix

/-!
# Flattening square matrices

Listing the entries of an `n × n` matrix along an enumeration of `n × n`
(`Matrix.entryEquiv`) identifies `Matrix n n R` with the coordinate space `Fin N → R`, where
`N = card n * card n`, as a continuous linear equivalence for the entrywise product topology
(`Matrix.flattenEquiv`). The number of entries is written `card n * card n - 1 + 1`, so that the
projective space of the matrices is the standard projective space of dimension
`card n * card n - 1`.
-/

public noncomputable section

namespace Matrix

variable (n : Type*) [Fintype n] [Nonempty n] (R : Type*)

/-- An enumeration of the entries of `n × n` matrices by `Fin (card n * card n - 1 + 1)`. -/
def entryEquiv : n × n ≃ Fin (Fintype.card n * Fintype.card n - 1 + 1) :=
  Fintype.equivFinOfCardEq <| by
    have : 0 < Fintype.card n * Fintype.card n := Nat.mul_pos Fintype.card_pos Fintype.card_pos
    rw [Fintype.card_prod]
    omega

variable [Semiring R] [TopologicalSpace R]

/-- The entries of an `n × n` matrix, listed along `Matrix.entryEquiv n`, as a continuous linear
equivalence. -/
def flattenEquiv : Matrix n n R ≃L[R] Fin (Fintype.card n * Fintype.card n - 1 + 1) → R where
  toFun A k := A ((entryEquiv n).symm k).1 ((entryEquiv n).symm k).2
  invFun v := Matrix.of fun i j ↦ v (entryEquiv n (i, j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv A := by ext i j; simp
  right_inv v := by ext k; simp
  continuous_toFun := continuous_pi fun _ ↦ continuous_id.matrix_elem _ _
  continuous_invFun := continuous_pi fun _ ↦ continuous_pi fun _ ↦ continuous_apply _

variable {n R}

@[simp]
theorem flattenEquiv_apply (A : Matrix n n R) (k : Fin (Fintype.card n * Fintype.card n - 1 + 1)) :
    flattenEquiv n R A k = A ((entryEquiv n).symm k).1 ((entryEquiv n).symm k).2 :=
  (rfl)

@[simp]
theorem flattenEquiv_symm_apply (v : Fin (Fintype.card n * Fintype.card n - 1 + 1) → R)
    (i j : n) : (flattenEquiv n R).symm v i j = v (entryEquiv n (i, j)) :=
  (rfl)

end Matrix

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

/-!
# Equivalences for finite indices and consecutive blocks of natural numbers

The equivalence omitting the last finite index embeds preceding indices by `Fin.castSucc`.
The quotient-remainder equivalence identifies a natural number with a block number and a
position inside that block. This file records the induced block permutations and compatibility
of nested blocks with the finite-product indexing equivalence.
It also concatenates two finite blocks with the second block read in reverse order.
-/

public section

namespace TauCeti

/-- Omitting the last index embeds each preceding index by `Fin.castSucc`. -/
@[simp]
theorem finSuccAboveEquiv_last_apply (n : ℕ) (i : Fin n) :
    finSuccAboveEquiv (Fin.last n) i = ⟨i.castSucc, Fin.castSucc_ne_last i⟩ :=
  (finSuccAboveEquiv_apply (Fin.last n) i).trans
    (by apply Subtype.ext; exact Fin.succAbove_last_apply i)

/-- Concatenate two finite blocks, keeping the first in order and reversing the second. -/
def finSumFinRevEquiv (p q n : ℕ) (hpq : p + q = n) : Fin p ⊕ Fin q ≃ Fin n :=
  ((Equiv.sumCongr (Equiv.refl _) Fin.revPerm).trans finSumFinEquiv).trans (finCongr hpq)

/-- The first block keeps its original index. -/
@[simp]
theorem finSumFinRevEquiv_inl_val (p q n : ℕ) (hpq : p + q = n) (i : Fin p) :
    (finSumFinRevEquiv p q n hpq (Sum.inl i) : ℕ) = i := by
  simp [finSumFinRevEquiv]

/-- The second block follows the first in reverse order. -/
@[simp]
theorem finSumFinRevEquiv_inr_val (p q n : ℕ) (hpq : p + q = n) (i : Fin q) :
    (finSumFinRevEquiv p q n hpq (Sum.inr i) : ℕ) = p + (q - 1 - i) := by
  simp [finSumFinRevEquiv, Fin.rev]
  omega

end TauCeti

/-- The permutation of path coordinates that permutes the consecutive blocks of width `m` by `τ`
and preserves the position inside each block. -/
def _root_.Nat.blockPerm (m : ℕ) [NeZero m] (τ : Equiv.Perm ℕ) : Equiv.Perm ℕ :=
  (Nat.divModEquiv m).symm.permCongr (Equiv.prodCongr τ (Equiv.refl (Fin m)))

/-- The block permutation moves position `j` of block `i` to position `j` of block `τ i`. -/
@[simp]
theorem _root_.Nat.blockPerm_mul_add (m : ℕ) [NeZero m] (τ : Equiv.Perm ℕ) (i : ℕ) (j : Fin m) :
    Nat.blockPerm m τ (i * m + j) = τ i * m + j := by
  have h (k : ℕ) : k * m + (j : ℕ) = (Nat.divModEquiv m).symm (k, j) :=
    (Nat.divModEquiv_symm_apply m (k, j)).symm
  -- Keep the indices in `divModEquiv` form so that `simp` cancels the equivalence.
  rw [h, h]
  simp [Nat.blockPerm, -Nat.divModEquiv_symm_apply]

/-- Flattening nested finite blocks agrees with the quotient-remainder inverse. -/
theorem Nat.divModEquiv_symm_finProdFinEquiv (m n : ℕ) [NeZero m] [NeZero n]
    (i : ℕ) (r : Fin n) (j : Fin m) :
    (Nat.divModEquiv (n * m)).symm (i, finProdFinEquiv (r, j)) =
      (Nat.divModEquiv m).symm (i * n + r, j) := by
  -- Evaluate the inverse quotient-remainder maps and the underlying natural number of the
  -- finite-product index by definition; this leaves a polynomial identity for `ring`.
  change i * (n * m) + (j + m * r) = (i * n + r) * m + j
  ring

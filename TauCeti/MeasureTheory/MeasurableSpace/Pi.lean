/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Splitting a finite block of coordinates into consecutive subblocks

A function on `Fin (n * m)` carries the same data as `n` consecutive blocks of `m` coordinates:
the flattened index `finProdFinEquiv (r, j) = j + m * r` is position `j` of block `r`. This file
records that reindexing as a measurable equivalence, together with the restriction to one fixed
subblock.

These are general measurable finite-product constructions, independent of any measure or
stochastic process.

## Main definitions

* `TauCeti.MeasureTheory.blockSplitEquiv` -- the measurable equivalence
  `(Fin (n * m) → α) ≃ᵐ (Fin n → Fin m → α)`;
* `TauCeti.MeasureTheory.blockRestriction` -- restriction to the `r`-th subblock of width `m`.
-/

public section

noncomputable section

namespace TauCeti

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- The measurable equivalence that splits a block of width `n * m` into `n` consecutive blocks
of width `m`. The outer coordinate chooses the small block and the inner coordinate chooses a
position within it. -/
def blockSplitEquiv (α : Type*) [MeasurableSpace α] (m n : ℕ) :
    (Fin (n * m) → α) ≃ᵐ (Fin n → Fin m → α) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (n * m) => α)
    (finProdFinEquiv : Fin n × Fin m ≃ Fin (n * m))).symm.trans
      (MeasurableEquiv.curry (Fin n) (Fin m) α)

/-- Splitting a finite block reads its `(r, j)` coordinate at the flattened index
`j + m * r`. -/
@[simp]
theorem blockSplitEquiv_apply (m n : ℕ) (x : Fin (n * m) → α) (r : Fin n) (j : Fin m) :
    blockSplitEquiv α m n x r j = x (finProdFinEquiv (r, j)) := by
  have h : (MeasurableEquiv.piCongrLeft (fun _ : Fin (n * m) => α)
      (finProdFinEquiv : Fin n × Fin m ≃ Fin (n * m))).toEquiv
      = Equiv.piCongrLeft (fun _ : Fin (n * m) => α) finProdFinEquiv :=
    Equiv.coe_fn_injective (MeasurableEquiv.coe_piCongrLeft finProdFinEquiv)
  rw [blockSplitEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.coe_curry,
    Function.curry_apply, ← MeasurableEquiv.coe_toEquiv_symm, h, Equiv.piCongrLeft_symm_apply]

/-- Joining split blocks reads a flattened coordinate from its quotient and remainder. -/
@[simp]
theorem blockSplitEquiv_symm_apply (m n : ℕ) (x : Fin n → Fin m → α) (k : Fin (n * m)) :
    (blockSplitEquiv α m n).symm x k =
      x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := by
  conv_rhs => rw [← (blockSplitEquiv α m n).apply_symm_apply x]
  rw [blockSplitEquiv_apply, Prod.mk.eta, Equiv.apply_symm_apply]

/-- Restriction of a block of width `n * m` to its `r`-th consecutive subblock of width `m`. -/
def blockRestriction (m n : ℕ) (r : Fin n) : (Fin (n * m) → α) → (Fin m → α) :=
  fun x => blockSplitEquiv α m n x r

/-- Restricting a finite block reads the corresponding flattened coordinate. -/
@[simp]
theorem blockRestriction_apply (m n : ℕ) (r : Fin n) (x : Fin (n * m) → α) (j : Fin m) :
    blockRestriction (α := α) m n r x j = x (finProdFinEquiv (r, j)) := by
  simp only [blockRestriction, blockSplitEquiv_apply]

/-- Restriction to a fixed subblock is measurable. -/
theorem measurable_blockRestriction (m n : ℕ) (r : Fin n) :
    Measurable (blockRestriction (α := α) m n r) :=
  (measurable_pi_apply r).comp (blockSplitEquiv α m n).measurable

end MeasureTheory

end TauCeti

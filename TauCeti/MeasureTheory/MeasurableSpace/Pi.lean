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

It also records that extending a family along an arbitrary map of index types, with a fixed
default outside the range, is measurable in the family (`TauCeti.MeasureTheory.measurable_extend`).

It also records that recombining a block `z` on a finset `s` with the remaining coordinates of a
point `w` of a dependent product is the finset update of `w` by `z`
(`Finset.measurableEquiv_piEquivPiSubtypeProd_symm_apply_eq_updateFinset`).

These are general measurable product constructions, independent of any measure or stochastic
process.

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
  (MeasurableEquiv.arrowCongr' finProdFinEquiv.symm (.refl α)).trans
    (MeasurableEquiv.curry (Fin n) (Fin m) α)

/-- Splitting a finite block reads its `(r, j)` coordinate at the flattened index
`j + m * r`. -/
@[simp]
theorem blockSplitEquiv_apply (m n : ℕ) (x : Fin (n * m) → α) (r : Fin n) (j : Fin m) :
    blockSplitEquiv α m n x r j = x (finProdFinEquiv (r, j)) :=
  (rfl)

/-- Joining split blocks reads a flattened coordinate from its quotient and remainder. -/
@[simp]
theorem blockSplitEquiv_symm_apply (m n : ℕ) (x : Fin n → Fin m → α) (k : Fin (n * m)) :
    (blockSplitEquiv α m n).symm x k =
      x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 :=
  (rfl)

/-- Restriction of a block of width `n * m` to its `r`-th consecutive subblock of width `m`. -/
def blockRestriction (m n : ℕ) (r : Fin n) : (Fin (n * m) → α) → (Fin m → α) :=
  fun x => blockSplitEquiv α m n x r

/-- Restricting a finite block reads the corresponding flattened coordinate. -/
@[simp]
theorem blockRestriction_apply (m n : ℕ) (r : Fin n) (x : Fin (n * m) → α) (j : Fin m) :
    blockRestriction (α := α) m n r x j = x (finProdFinEquiv (r, j)) :=
  (rfl)

/-- Restriction to a fixed subblock is measurable. -/
theorem measurable_blockRestriction (m n : ℕ) (r : Fin n) :
    Measurable (blockRestriction (α := α) m n r) :=
  (measurable_pi_apply r).comp (blockSplitEquiv α m n).measurable

/-- Extending a family `g : ι → α` along a map `f : ι → κ`, with the fixed default `e` off the
range of `f`, is measurable in `g`. For `f = Subtype.val` this is extension of a subfamily by a
default value. -/
theorem measurable_extend {ι κ : Type*} (f : ι → κ) (e : κ → α) :
    Measurable fun g : ι → α ↦ Function.extend f g e := by
  refine Measurable.of_eval fun k ↦ ?_
  simp only [Function.extend]
  split_ifs <;> fun_prop

/-- Recombining a block `z` on a finset `s` with the coordinates of `w` outside `s` is the update
of `w` on `s` by `z`. -/
theorem _root_.Finset.measurableEquiv_piEquivPiSubtypeProd_symm_apply_eq_updateFinset
    {ι : Type*} [DecidableEq ι] {π : ι → Type*} [∀ i, MeasurableSpace (π i)]
    (s : Finset ι) (w : ∀ i, π i) (z : ∀ i : s, π i) :
    (MeasurableEquiv.piEquivPiSubtypeProd π fun i => i ∈ s).symm
      (z, (MeasurableEquiv.piEquivPiSubtypeProd π (fun i => i ∈ s) w).2) =
      Function.updateFinset w s z := by
  ext i
  simp only [MeasurableEquiv.piEquivPiSubtypeProd_symm_apply,
    MeasurableEquiv.piEquivPiSubtypeProd_apply, Function.updateFinset_def]

end MeasureTheory

end TauCeti

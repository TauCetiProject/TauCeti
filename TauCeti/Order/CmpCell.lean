/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Set.Insert
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Monotone.Basic

/-!
# Cells of comparison patterns

For a tuple `a : Fin n → M` of points of a linear order and a comparison pattern
`σ : Fin n → Ordering`, the cell `TauCeti.cmpCell a σ` is the set of points `z` with
`cmp (a i) z = σ i` for every `i`. Listing the distinct entries of `a` in increasing order, the
cells are the open intervals between consecutive entries (including the two unbounded ones), the
singletons of the entries, and empty sets.

## Main definitions

* `TauCeti.cmpCell a σ`: the points of a linear order whose comparisons with the entries of the
  tuple `a` are prescribed by `σ`.

## Main results

* `TauCeti.mem_cmpCell_snoc`: the cells of an extended tuple are the cells of the original tuple
  cut by the new point.
* `TauCeti.cmpCell_snoc_elim0_of_gt`, `TauCeti.cmpCell_snoc_elim0_of_eq`,
  `TauCeti.cmpCell_snoc_elim0_of_lt`: the cells of a single point `x` are `Set.Iio x`, `{x}` and
  `Set.Ioi x`.
* `StrictMono.mem_cmpCell_comp`: cells pull back along strictly monotone maps.
-/

public section

universe w w'

namespace TauCeti

open Fin

variable {M : Type w} {N : Type w'} [LinearOrder M] [LinearOrder N] {n : ℕ}

/-- The cell of the comparison pattern `σ` for the tuple `a`: the points `z` with
`cmp (a i) z = σ i` for every `i`. -/
@[expose] def cmpCell (a : Fin n → M) (σ : Fin n → Ordering) : Set M :=
  {z | ∀ i, cmp (a i) z = σ i}

@[simp]
theorem mem_cmpCell {a : Fin n → M} {σ : Fin n → Ordering} {z : M} :
    z ∈ cmpCell a σ ↔ ∀ i, cmp (a i) z = σ i :=
  Iff.rfl

/-- The empty tuple has a single cell, the whole order. -/
@[simp]
theorem cmpCell_fin_zero (a : Fin 0 → M) (σ : Fin 0 → Ordering) : cmpCell a σ = Set.univ := by
  ext z
  simp

/-- The cells of an extended tuple are the cells of the original tuple cut by the new point. -/
theorem mem_cmpCell_snoc {a : Fin n → M} {x z : M} {σ : Fin (n + 1) → Ordering} :
    z ∈ cmpCell (snoc a x) σ ↔ z ∈ cmpCell a (init σ) ∧ cmp x z = σ (last n) := by
  simp [forall_fin_succ', init]

/-- The cells of a single point `x` are cut out by the comparison with `x`. -/
theorem mem_cmpCell_snoc_elim0 {x z : M} {τ : Fin 1 → Ordering} :
    z ∈ cmpCell (snoc (Fin.elim0 : Fin 0 → M) x) τ ↔ cmp x z = τ (last 0) := by
  rw [mem_cmpCell_snoc, cmpCell_fin_zero]
  exact and_iff_right (Set.mem_univ z)

/-- Cells pull back along strictly monotone maps: `f z` lies in the cell of `f ∘ a` for `σ`
exactly when `z` lies in the cell of `a` for `σ`. -/
theorem _root_.StrictMono.mem_cmpCell_comp {f : M → N} (hf : StrictMono f) {a : Fin n → M}
    {σ : Fin n → Ordering} {z : M} : f z ∈ cmpCell (f ∘ a) σ ↔ z ∈ cmpCell a σ := by
  simp only [mem_cmpCell, Function.comp_apply, hf.cmp_map_eq]

/-- The cells of a single point pull back along strictly monotone maps. -/
theorem _root_.StrictMono.mem_cmpCell_snoc_elim0 {f : M → N} (hf : StrictMono f) {x z : M}
    {τ : Fin 1 → Ordering} :
    f z ∈ cmpCell (snoc (Fin.elim0 : Fin 0 → N) (f x)) τ ↔
      z ∈ cmpCell (snoc (Fin.elim0 : Fin 0 → M) x) τ := by
  rw [← hf.mem_cmpCell_comp, comp_snoc, Subsingleton.elim (f ∘ Fin.elim0) Fin.elim0]

/-- The cell of a single point `x` below it is `Set.Iio x`. -/
theorem cmpCell_snoc_elim0_of_gt {x : M} {τ : Fin 1 → Ordering} (h : τ (last 0) = .gt) :
    cmpCell (snoc (Fin.elim0 : Fin 0 → M) x) τ = Set.Iio x := by
  ext z
  rw [mem_cmpCell_snoc_elim0, h, cmp_eq_gt_iff, Set.mem_Iio]

/-- The cell of a single point `x` at it is `{x}`. -/
theorem cmpCell_snoc_elim0_of_eq {x : M} {τ : Fin 1 → Ordering} (h : τ (last 0) = .eq) :
    cmpCell (snoc (Fin.elim0 : Fin 0 → M) x) τ = {x} := by
  ext z
  rw [mem_cmpCell_snoc_elim0, h, cmp_eq_eq_iff, Set.mem_singleton_iff, eq_comm]

/-- The cell of a single point `x` above it is `Set.Ioi x`. -/
theorem cmpCell_snoc_elim0_of_lt {x : M} {τ : Fin 1 → Ordering} (h : τ (last 0) = .lt) :
    cmpCell (snoc (Fin.elim0 : Fin 0 → M) x) τ = Set.Ioi x := by
  ext z
  rw [mem_cmpCell_snoc_elim0, h, cmp_eq_lt_iff, Set.mem_Ioi]

/-- Every point lies in the cell of its own comparison pattern. -/
theorem mem_cmpCell_cmp (a : Fin n → M) (x : M) : x ∈ cmpCell a (fun i => cmp (a i) x) :=
  fun _ => rfl

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.DiscreteSeries.RegularParameter.Basic
import Mathlib.Data.Fintype.Fin

/-!
# Decreasing positions of Harish-Chandra parameters

A doubled Harish-Chandra parameter lists the entries of the strictly decreasing sequence
`doubledHCParameter n κ e` in some order. This file identifies that order intrinsically:
the entry `l i` is at position `#{j | l i < l j}`. In particular the permutation of the
parameter entries is uniquely determined by their values. These positions are the column
indices of the highest evaluation vector in the coefficient representation of a compact
unitary group.

The results include the equivalence with a permutation of the standard parameter and the
pointwise characterization by decreasing positions. They hold also for the empty index type.

The positional identification `eq_doubledHCParameter_card_filter` follows the statement of
`[ShortProof]` `New.IsHCParam.eq_hcParameter`, in grh-lean
(https://github.com/lsernau/grh-lean, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`),
`src/Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean`. The proofs here use the strict
antitonicity of the standard parameter and a finite bijection of its entries.
-/

public section

open Finset

namespace TauCeti

namespace IsDoubledHCParameter

variable {ι : Type*} [Fintype ι] {κ : ℕ → ℕ} {e : ℤ} {l : ι → ℤ}

/-- If `l i` is entry `p` of the standard parameter, exactly `p` entries of `l` exceed it. -/
theorem card_filter_lt_eq (h : IsDoubledHCParameter κ e l) (i : ι)
    {p : ℕ} (hi : l i = doubledHCParameter (Fintype.card ι) κ e p) :
    #{j | l i < l j} = p := by
  classical
  obtain ⟨q, hq, hqi⟩ := h.exists_lt_eq i
  have hqp : q = p := (doubledHCParameter_strictAnti _ κ e).injective (hqi.symm.trans hi)
  subst p
  obtain ⟨σ, hσ⟩ := h.exists_equiv
  have hcard : #{j | l i < l j} = #{k : Fin (Fintype.card ι) | k < q} := by
    apply Finset.card_equiv σ
    intro j
    simp only [mem_filter, mem_univ, true_and, hi, hσ j]
    exact (doubledHCParameter_strictAnti _ κ e).lt_iff_gt
  rw [hcard, Fin.card_filter_val_lt, Nat.min_eq_right hq.le]

/-- Every entry of a doubled parameter is the standard entry at its position in decreasing
order, the number of entries strictly larger than itself. -/
theorem eq_doubledHCParameter_card_filter (h : IsDoubledHCParameter κ e l) (i : ι) :
    l i = doubledHCParameter (Fintype.card ι) κ e #{j | l i < l j} := by
  obtain ⟨p, _, hi⟩ := h.exists_lt_eq i
  rw [h.card_filter_lt_eq i hi]
  exact hi

/-- An entry equals standard entry `p` exactly when its decreasing position is `p`. -/
theorem card_filter_lt_eq_iff (h : IsDoubledHCParameter κ e l) (i : ι) (p : ℕ) :
    #{j | l i < l j} = p ↔ l i = doubledHCParameter (Fintype.card ι) κ e p := by
  constructor
  · rintro rfl
    exact h.eq_doubledHCParameter_card_filter i
  · exact h.card_filter_lt_eq i

end IsDoubledHCParameter

/-- Listing the standard parameter along a bijection gives exactly the doubled parameters. -/
theorem isDoubledHCParameter_iff_exists_equiv {ι : Type*} [Fintype ι]
    {κ : ℕ → ℕ} {e : ℤ} {l : ι → ℤ} :
    IsDoubledHCParameter κ e l ↔
      ∃ σ : ι ≃ Fin (Fintype.card ι),
        ∀ i, l i = doubledHCParameter (Fintype.card ι) κ e (σ i) := by
  constructor
  · exact IsDoubledHCParameter.exists_equiv
  · rintro ⟨σ, hσ⟩
    refine isDoubledHCParameter_iff.mpr ⟨?_, fun i ↦ ⟨σ i, (σ i).isLt, hσ i⟩⟩
    intro i j hij
    apply σ.injective
    apply Fin.ext
    exact (doubledHCParameter_strictAnti _ κ e).injective (by rwa [hσ i, hσ j] at hij)

/-- A vector with distinct entries is a doubled parameter exactly when each entry equals
the standard entry at its decreasing position. -/
theorem isDoubledHCParameter_iff_eq_card_filter {ι : Type*} [Fintype ι]
    {κ : ℕ → ℕ} {e : ℤ} {l : ι → ℤ} :
    IsDoubledHCParameter κ e l ↔
      l.Injective ∧
        ∀ i, l i = doubledHCParameter (Fintype.card ι) κ e #{j | l i < l j} := by
  constructor
  · intro h
    exact ⟨h.injective, h.eq_doubledHCParameter_card_filter⟩
  · rintro ⟨hinj, hl⟩
    refine isDoubledHCParameter_iff.mpr ⟨hinj, fun i ↦ ?_⟩
    refine ⟨#{j | l i < l j}, ?_, hl i⟩
    classical
    exact card_lt_card (filter_ssubset.mpr ⟨i, mem_univ i, lt_irrefl _⟩)

end TauCeti

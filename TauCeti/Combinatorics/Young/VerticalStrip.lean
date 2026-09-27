/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.BetaNumbers
public import TauCeti.Combinatorics.Young.Interlacing
public import TauCeti.Combinatorics.Young.OfRowLens

/-!
# Vertical strips of Young diagrams

A skew shape `μ / ν` is a **vertical strip** when it has at most one cell in each *row*: `ν` is
contained in `μ`, and no row of `μ` is longer than the corresponding row of `ν` by more than one
cell.  This file defines that relation, `YoungDiagram.IsVerticalStrip`, and identifies the vertical
strips over a fixed `ν` inside `N` rows with the sets of rows that grow.

Vertical strips are the shapes added by multiplying a Schur polynomial by an elementary symmetric
polynomial, just as the horizontal strips of `YoungDiagram.InterlacedBy` — at most one cell in each
*column* — are those added by a complete homogeneous one.  Row lengths are the convenient
coordinates: one inequality `ν.rowLen i ≤ μ.rowLen i ≤ ν.rowLen i + 1` per row, so a vertical strip
over `ν` is exactly a shift of the row lengths of `ν` by the indicator of a set of rows.  The two
directions of that correspondence are `YoungDiagram.isVerticalStrip_ofRowLensFin` and
`YoungDiagram.IsVerticalStrip.ofRowLensFin_lengthenedRows`.

## Main definitions

* `YoungDiagram.IsVerticalStrip`: `IsVerticalStrip μ ν` says that `μ / ν` is a vertical strip.  The
  larger shape is written first, as in `YoungDiagram.IsRimHook`.
* `YoungDiagram.lengthenedRows`: the rows below `N` on which `μ` is longer than `ν`.

## Main results

* `YoungDiagram.IsVerticalStrip.le`: the shape below a vertical strip is a sub-diagram.
* `YoungDiagram.isVerticalStrip_iff_interlacedBy_transpose`: a vertical strip is a transposed
  horizontal strip, so the relation is the transpose of `YoungDiagram.InterlacedBy`.
* `YoungDiagram.isVerticalStrip_ofRowLensFin` and `YoungDiagram.card_ofRowLensFin_add_ite`: adding
  one cell to each row in a set `T` gives a vertical strip whenever the resulting row lengths are
  still weakly decreasing, and it has `T.card` more cells.
* `YoungDiagram.antitone_rowLen_add_ite_of_injective`: raising by one the beta-numbers
  (`YoungDiagram.betaNumber`) indexed by a set `T` keeps the row lengths weakly decreasing as soon
  as it keeps the beta-numbers pairwise distinct.
* `YoungDiagram.IsVerticalStrip.ofRowLensFin_lengthenedRows`: conversely, a vertical strip over `ν`
  with at most `N` rows is obtained in this way from `YoungDiagram.lengthenedRows`, whose size is
  computed by `YoungDiagram.IsVerticalStrip.card_lengthenedRows`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 5, where horizontal and vertical strips index the two Pieri rules.
-/

public section

open Finset

namespace YoungDiagram

variable {μ ν : YoungDiagram}

/-- `μ / ν` is a **vertical strip**: every row of `μ` is at least as long as the corresponding row
of `ν` and at most one cell longer, so the skew shape has at most one cell in each row.

As for the horizontal strips of `YoungDiagram.InterlacedBy`, the two shapes are compared row by
row; the larger one is written first, as in `YoungDiagram.IsRimHook`. -/
def IsVerticalStrip (μ ν : YoungDiagram) : Prop :=
  ∀ i, ν.rowLen i ≤ μ.rowLen i ∧ μ.rowLen i ≤ ν.rowLen i + 1

/-- Being a vertical strip unfolded: the pair of inequalities at each row.  This is the
introduction and elimination rule for `YoungDiagram.IsVerticalStrip`, whose body is not
exposed. -/
@[simp]
theorem isVerticalStrip_iff :
    IsVerticalStrip μ ν ↔ ∀ i, ν.rowLen i ≤ μ.rowLen i ∧ μ.rowLen i ≤ ν.rowLen i + 1 :=
  Iff.rfl

/-- A vertical strip reaches at least as far as the shape below it in every row. -/
theorem IsVerticalStrip.rowLen_le (h : IsVerticalStrip μ ν) (i : ℕ) : ν.rowLen i ≤ μ.rowLen i :=
  (h i).1

/-- A vertical strip reaches at most one cell further than the shape below it in every row. -/
theorem IsVerticalStrip.rowLen_le_succ (h : IsVerticalStrip μ ν) (i : ℕ) :
    μ.rowLen i ≤ ν.rowLen i + 1 :=
  (h i).2

/-- The shape below a vertical strip is a sub-diagram. -/
theorem IsVerticalStrip.le (h : IsVerticalStrip μ ν) : ν ≤ μ :=
  le_of_forall_rowLen_le h.rowLen_le

/-- In every row, a vertical strip is the shape below it lengthened by `0` or `1` cell, according
to whether that row grows. -/
theorem IsVerticalStrip.rowLen_eq_add_ite (h : IsVerticalStrip μ ν) (i : ℕ) :
    μ.rowLen i = ν.rowLen i + if ν.rowLen i < μ.rowLen i then 1 else 0 := by
  have := h.rowLen_le i
  have := h.rowLen_le_succ i
  split_ifs with hlt <;> omega

/-- **Vertical strips are the transposes of horizontal strips.**  A skew shape has at most one cell
in each row exactly when its transpose has at most one cell in each column, which is the interlacing
condition `YoungDiagram.InterlacedBy`.  So the two relations determine each other, and the reason to
carry both is one of coordinates: interlacing compares columns, whereas the rows of
`YoungDiagram.IsVerticalStrip` are what exhibit a vertical strip as an indicator shift of row
lengths, the form the Pieri rule is computed in. -/
theorem isVerticalStrip_iff_interlacedBy_transpose :
    IsVerticalStrip μ ν ↔ InterlacedBy μ.transpose ν.transpose := by
  rw [isVerticalStrip_iff, interlacedBy_iff]
  constructor
  · intro h i
    refine ⟨le_rowLen_of_forall_mem fun a ha => ?_, ?_⟩
    · -- A cell of `μ` in column `i + 1` sits in a row whose `ν`-part already reaches column `i`.
      rw [rowLen_transpose] at ha
      have hμa := _root_.YoungDiagram.mem_iff_lt_rowLen.mp
        (_root_.YoungDiagram.mem_iff_lt_colLen.mpr ha)
      have hνa : ((a, i) : ℕ × ℕ) ∈ ν :=
        _root_.YoungDiagram.mem_iff_lt_rowLen.mpr (by have := (h a).2; omega)
      exact mem_transpose.mpr hνa
    · exact rowLen_le_of_le (_root_.YoungDiagram.transpose_mono
        (le_of_forall_rowLen_le fun a => (h a).1)) i
  · intro h i
    refine ⟨rowLen_le_of_le (_root_.YoungDiagram.transpose_le_iff.mp
      (le_of_forall_rowLen_le fun a => (h a).2)) i, ?_⟩
    -- Two cells of `μ / ν` in row `i` would put `ν` one column short in the second of them.
    by_contra hcon
    have hlt : i < μ.transpose.rowLen (ν.rowLen i + 1) := by
      rw [rowLen_transpose]
      exact _root_.YoungDiagram.mem_iff_lt_colLen.mp
        (_root_.YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
    have h1 : ((ν.rowLen i, i) : ℕ × ℕ) ∈ ν.transpose :=
      _root_.YoungDiagram.mem_iff_lt_rowLen.mpr (hlt.trans_le (h (ν.rowLen i)).1)
    have h2 : ((i, ν.rowLen i) : ℕ × ℕ) ∈ ν := mem_transpose.mp h1
    exact absurd (_root_.YoungDiagram.mem_iff_lt_rowLen.mp h2) (lt_irrefl _)

/-- **An injective indicator shift of the beta-numbers is a shape.**  The beta-numbers of `ν`
relative to `N` strictly decrease, so raising by one those indexed by a set `T` leaves them pairwise
distinct only if the shifted row lengths `ν_j + 1_T(j)` are still weakly decreasing: two adjacent
beta-numbers differ, and the indicator can move them by at most the single step that separates them.

This is the criterion under which such a shift describes a shape at all; only this implication is
used, the sets whose shifted beta-numbers repeat being discarded downstream because their alternant
vanishes. -/
theorem antitone_rowLen_add_ite_of_injective {N : ℕ} {T : Finset (Fin N)}
    (hinj : Function.Injective fun j : Fin N => ν.betaNumber N j + if j ∈ T then 1 else 0) :
    Antitone fun j : Fin N => ν.rowLen j + if j ∈ T then 1 else 0 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact fun a _ _ => absurd a.isLt (Nat.not_lt_zero _)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  rw [Fin.antitone_iff_succ_le]
  intro i
  -- Two adjacent beta-numbers are distinct, and the shift by an indicator moves them by at most
  -- the one step that separates them, so the row lengths cannot increase.
  have hne : (Fin.castSucc i) ≠ i.succ := fun h => by simpa using congrArg Fin.val h
  have hfne : ν.betaNumber (n + 1) (Fin.castSucc i) + (if Fin.castSucc i ∈ T then 1 else 0) ≠
      ν.betaNumber (n + 1) i.succ + (if i.succ ∈ T then 1 else 0) := fun h => hne (hinj h)
  have hrow : ν.rowLen ((i.succ : Fin (n + 1)) : ℕ) ≤
      ν.rowLen ((Fin.castSucc i : Fin (n + 1)) : ℕ) := ν.rowLen_anti _ _ (by simp)
  have hlt : ((Fin.castSucc i : Fin (n + 1)) : ℕ) < n + 1 := (Fin.castSucc i).isLt
  rw [betaNumber_def, betaNumber_def] at hfne
  simp only [Fin.val_succ, Fin.val_castSucc] at hfne hrow hlt ⊢
  split_ifs at hfne ⊢ <;> omega

section Rows

variable {N : ℕ} {T : Finset (Fin N)}
  (hT : Antitone fun j : Fin N => ν.rowLen j + if j ∈ T then 1 else 0)

include hT

/-- **Lengthening a set of rows by one cell each gives a vertical strip**, provided the resulting
row lengths are still weakly decreasing. -/
theorem isVerticalStrip_ofRowLensFin (hν : ν.colLen 0 ≤ N) :
    IsVerticalStrip (ofRowLensFin _ hT) ν := by
  intro i
  by_cases hi : i < N
  · have hrow : (ofRowLensFin _ hT).rowLen i
        = ν.rowLen i + if (⟨i, hi⟩ : Fin N) ∈ T then 1 else 0 := by
      simpa using rowLen_ofRowLensFin _ hT ⟨i, hi⟩
    rw [hrow]
    split_ifs <;> omega
  · rw [rowLen_ofRowLensFin_eq_zero_of_le _ hT (Nat.not_lt.mp hi),
      rowLen_eq_zero_of_colLen_le (hν.trans (Nat.not_lt.mp hi))]
    omega

/-- Lengthening a set of rows by one cell each adds `T.card` cells. -/
theorem card_ofRowLensFin_add_ite (hν : ν.colLen 0 ≤ N) :
    (ofRowLensFin _ hT).card = ν.card + T.card := by
  rw [card_ofRowLensFin, card_eq_sum_range_rowLen ν hν,
    ← Fin.sum_univ_eq_sum_range (fun i => ν.rowLen i) N, Finset.sum_add_distrib,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one]

end Rows

section Lengthened

variable (N : ℕ) (μ ν : YoungDiagram)

open scoped Classical in
/-- **The rows a vertical strip lengthens**: the indices `j < N` at which `μ` has a longer row than
`ν`.  For a vertical strip these are exactly the rows carrying a cell of `μ / ν`. -/
noncomputable def lengthenedRows : Finset (Fin N) :=
  {j : Fin N | ν.rowLen j < μ.rowLen j}

variable {N μ ν}

@[simp]
theorem mem_lengthenedRows {j : Fin N} :
    j ∈ lengthenedRows N μ ν ↔ ν.rowLen j < μ.rowLen j := by
  classical
  simp [lengthenedRows]

variable (h : IsVerticalStrip μ ν) (hμ : μ.colLen 0 ≤ N)

include h

/-- The row lengths of a vertical strip, read as the row lengths of the shape below it shifted by
the indicator of the rows it lengthens, are still weakly decreasing. -/
theorem IsVerticalStrip.antitone_rowLen_add_ite :
    Antitone fun j : Fin N => ν.rowLen j + if j ∈ lengthenedRows N μ ν then 1 else 0 :=
  fun a b hab => by
    simp only [mem_lengthenedRows, ← h.rowLen_eq_add_ite]
    exact μ.rowLen_anti _ _ hab

include hμ

/-- **A vertical strip is recovered from the rows it lengthens**: within `N` rows, `μ` is `ν` with
one cell added to each row of `YoungDiagram.lengthenedRows`. -/
theorem IsVerticalStrip.ofRowLensFin_lengthenedRows :
    ofRowLensFin _ (h.antitone_rowLen_add_ite (N := N)) = μ := by
  refine rowLen_injective (funext fun i => ?_)
  by_cases hi : i < N
  · have hrow : (ofRowLensFin _ (h.antitone_rowLen_add_ite (N := N))).rowLen i
        = ν.rowLen i + if ν.rowLen i < μ.rowLen i then 1 else 0 := by
      simpa using rowLen_ofRowLensFin _ (h.antitone_rowLen_add_ite (N := N)) ⟨i, hi⟩
    rw [hrow]
    exact (h.rowLen_eq_add_ite i).symm
  · rw [rowLen_ofRowLensFin_eq_zero_of_le _ _ (Nat.not_lt.mp hi),
      rowLen_eq_zero_of_colLen_le (hμ.trans (Nat.not_lt.mp hi))]

/-- A vertical strip lengthens exactly as many rows as it has cells over the shape below it. -/
theorem IsVerticalStrip.card_lengthenedRows :
    μ.card = ν.card + (lengthenedRows N μ ν).card := by
  -- The shape below the strip has no more rows than the strip itself.
  have hν : ν.colLen 0 ≤ N := by
    by_contra hcon
    have hmem : ((N, 0) : ℕ × ℕ) ∈ μ :=
      h.le (_root_.YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_le hcon))
    exact absurd (_root_.YoungDiagram.mem_iff_lt_colLen.mp hmem) (Nat.not_lt.mpr hμ)
  conv_lhs => rw [← h.ofRowLensFin_lengthenedRows hμ]
  exact card_ofRowLensFin_add_ite _ hν

end Lengthened

end YoungDiagram

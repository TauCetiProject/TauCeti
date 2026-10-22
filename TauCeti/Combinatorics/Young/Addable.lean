/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.HookLength.Basic

/-!
# Addable cells of a Young diagram and their contents

A cell `c` is *addable* to a Young diagram `μ` if `c ∉ μ` while every cell strictly below `c` in
the product order lies in `μ`; equivalently, adding `c` alone to `μ` gives a Young diagram, in
which `c` is a corner. Addable cells are the dual of the corners of `YoungDiagram.IsCorner`: they
index the edges `μ ⊂ μ + c` of the Young graph leaving `μ`, and hence the one-box branching rules
for symmetric groups and Hecke algebras.

The *content* of the cell `(i, j)` is `j - i`, its column index minus its row index. On a fixed
Young diagram the contents of the addable cells are well separated: two distinct addable cells
of `μ` have contents differing by at least `2` and by at most `μ.card + 1`. The upper bound is
sharp: for every `d ≥ 2`, some diagram `μ` with `μ.card + 1 = d` has two addable cells whose
contents differ by exactly `d` (for `d = 2` this also attains the lower bound). On the semisimple
Hecke algebra `Hₙ(q)` with `Q = q²` the Jucys–Murphy elements act on the new box of a one-box
branching `μ ⊂ μ + c` by the eigenvalue `Q ^ content c`. The bounds above therefore say exactly
when those eigenvalues separate the branches: for every diagram of size less than `n` the map
`c ↦ Q ^ content c` is injective on addable cells if and only if `Q ^ d ≠ 1` for `2 ≤ d ≤ n`.

## Main definitions

* `YoungDiagram.IsAddable`: the predicate cutting out the addable cells of a diagram.
* `YoungDiagram.addables`: the addable cells of a diagram, as a finite set of cells.
* `YoungDiagram.addCell`: the diagram with the principal lower set of a cell added; at an addable
  cell exactly that cell is added.

The content `YoungDiagram.cellContent` of a cell is defined in
`TauCeti.Combinatorics.Young.Diagram`.

## Main results

* `YoungDiagram.isAddable_iff_isLowerSet`: a cell outside `μ` is addable exactly when adding it
  to `μ` gives a Young diagram.
* `YoungDiagram.addCell_le_iff`: `addCell μ c` is the least diagram containing `μ` and `c`.
* `YoungDiagram.IsAddable.rowLen_addCell` and `YoungDiagram.IsAddable.colLen_addCell`: adding an
  addable cell lengthens its row and its column by one and leaves the others unchanged.
* `YoungDiagram.isAddable_iff_rowLen`: the cell `(i, j)` is addable exactly when `j` is the
  length of row `i` and, unless `i = 0`, row `i` is shorter than row `i - 1`.
* `YoungDiagram.IsAddable.isCorner_addCell` and `YoungDiagram.IsCorner.isAddable_erase`, with
  `YoungDiagram.IsAddable.erase_addCell` and `YoungDiagram.IsCorner.addCell_erase`: adding an
  addable cell and removing a corner are mutually inverse.
* `YoungDiagram.IsAddable.two_le_cellContent_sub` and
  `YoungDiagram.IsAddable.cellContent_sub_le`: contents of distinct addable cells differ by at
  least `2` and at most `μ.card + 1`.
* `YoungDiagram.injOn_zpow_cellContent_iff`: the powers `Q ^ content c` separate the addable
  cells of every diagram of size less than `n` if and only if `Q ^ d ≠ 1` for `2 ≤ d ≤ n`.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 1.1.
* A. Okounkov, A. Vershik, *A new approach to representation theory of symmetric groups*,
  Selecta Math. 2 (1996), 581–605, Section 5, where contents of addable cells give the spectrum of
  the Jucys–Murphy elements.
* A. Ram, *Seminormal representations of Weyl groups and Iwahori-Hecke algebras*, Proc. London
  Math. Soc. 75 (1997), 99–133, for the Hecke eigenvalues `Q ^ content`.
-/

public section

namespace YoungDiagram

variable {μ : YoungDiagram} {c d : ℕ × ℕ}

/-! ### Addable cells -/

/-- A cell `c` is **addable** to `μ` if it is not a cell of `μ` while every cell strictly below
it in the product order is. These are exactly the cells outside `μ` whose addition on its own to
`μ` gives a Young diagram (`YoungDiagram.isAddable_iff_isLowerSet`). -/
def IsAddable (μ : YoungDiagram) (c : ℕ × ℕ) : Prop :=
  c ∉ μ ∧ ∀ d < c, d ∈ μ

/-- The defining conjunction of `YoungDiagram.IsAddable`, for introducing and eliminating the
predicate. -/
theorem isAddable_def (μ : YoungDiagram) (c : ℕ × ℕ) :
    IsAddable μ c ↔ c ∉ μ ∧ ∀ d < c, d ∈ μ :=
  Iff.rfl

instance instDecidableIsAddable (μ : YoungDiagram) (c : ℕ × ℕ) : Decidable (IsAddable μ c) :=
  decidable_of_iff (c ∉ μ ∧ ∀ d ∈ Finset.Iio c, d ∈ μ) (by simp [isAddable_def])

namespace IsAddable

theorem notMem (h : IsAddable μ c) : c ∉ μ := h.1

theorem mem_of_lt (h : IsAddable μ c) (hd : d < c) : d ∈ μ := h.2 d hd

/-- The cell to the left of an addable cell lies in the diagram. -/
theorem mem_left (h : IsAddable μ c) {j : ℕ} (hj : c.2 = j + 1) : (c.1, j) ∈ μ :=
  h.mem_of_lt <| Prod.lt_iff.mpr <| .inr ⟨le_rfl, by omega⟩

/-- The cell above an addable cell lies in the diagram. -/
theorem mem_above (h : IsAddable μ c) {i : ℕ} (hi : c.1 = i + 1) : (i, c.2) ∈ μ :=
  h.mem_of_lt <| Prod.lt_iff.mpr <| .inl ⟨by omega, le_rfl⟩

/-- An addable cell sits at the end of its row. -/
theorem snd_eq_rowLen (h : IsAddable μ c) : c.2 = μ.rowLen c.1 := by
  have hle : μ.rowLen c.1 ≤ c.2 := not_lt.mp fun hlt ↦ h.notMem (mem_iff_lt_rowLen.mpr hlt)
  rcases Nat.eq_zero_or_pos c.2 with h0 | hpos
  · omega
  · have := mem_iff_lt_rowLen.mp (h.mem_left (j := c.2 - 1) (by omega))
    omega

/-- An addable cell sits at the end of its column. -/
theorem fst_eq_colLen (h : IsAddable μ c) : c.1 = μ.colLen c.2 := by
  have hle : μ.colLen c.2 ≤ c.1 := not_lt.mp fun hlt ↦ h.notMem (mem_iff_lt_colLen.mpr hlt)
  rcases Nat.eq_zero_or_pos c.1 with h0 | hpos
  · omega
  · have := mem_iff_lt_colLen.mp (h.mem_above (i := c.1 - 1) (by omega))
    omega

/-- The addable cells of a diagram sit in distinct rows. -/
theorem eq_of_fst_eq (hc : IsAddable μ c) (hd : IsAddable μ d) (h : c.1 = d.1) : c = d :=
  Prod.ext h (by rw [hc.snd_eq_rowLen, hd.snd_eq_rowLen, h])

/-- An addable cell lies in one of the rows of the diagram or in the row just below them. -/
theorem fst_le_colLen_zero (h : IsAddable μ c) : c.1 ≤ μ.colLen 0 :=
  h.fst_eq_colLen ▸ μ.colLen_anti _ _ (Nat.zero_le _)

end IsAddable

/-- The addable cells of a Young diagram, as a finite set of cells: each is the cell just past the
end of one of the rows `0, …, μ.colLen 0`. -/
def addables (μ : YoungDiagram) : Finset (ℕ × ℕ) :=
  ((Finset.range (μ.colLen 0 + 1)).image fun i ↦ (i, μ.rowLen i)).filter (IsAddable μ)

@[simp]
theorem mem_addables : c ∈ addables μ ↔ IsAddable μ c := by
  simp only [addables, Finset.mem_filter, Finset.mem_image, Finset.mem_range,
    and_iff_right_iff_imp]
  exact fun h ↦ ⟨c.1, Nat.lt_succ_of_le h.fst_le_colLen_zero, Prod.ext rfl h.snd_eq_rowLen.symm⟩

/-- **Addable cells by row lengths.** The cell `(i, j)` is addable to `μ` exactly when `j` is the
length of row `i` and, unless `i = 0`, row `i` is strictly shorter than row `i - 1`. -/
theorem isAddable_iff_rowLen {i j : ℕ} :
    IsAddable μ (i, j) ↔ j = μ.rowLen i ∧ ∀ i', i = i' + 1 → j < μ.rowLen i' := by
  refine ⟨fun h ↦ ⟨h.snd_eq_rowLen, fun i' hi' ↦ mem_iff_lt_rowLen.mp (h.mem_above hi')⟩, ?_⟩
  rintro ⟨rfl, hrow⟩
  refine ⟨fun h ↦ (mem_iff_lt_rowLen.mp h).false, ?_⟩
  rintro ⟨i₁, j₁⟩ hlt
  rw [mem_iff_lt_rowLen]
  rcases Prod.lt_iff.mp hlt with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by simp only at hi; omega⟩
    exact hj.trans_lt ((hrow i' rfl).trans_le (μ.rowLen_anti _ _ (by simp only at hi; omega)))
  · exact hj.trans_le (μ.rowLen_anti _ _ hi)

/-- Transposition exchanges the addable cells of `μ` and `μ.transpose`. -/
@[simp]
theorem isAddable_transpose : IsAddable μ.transpose c ↔ IsAddable μ c.swap := by
  simp only [isAddable_def, mem_transpose]
  refine and_congr Iff.rfl ⟨fun h d hd ↦ ?_, fun h d hd ↦ h d.swap (Prod.swap_lt_swap.mpr hd)⟩
  simpa using h d.swap (by simpa using Prod.swap_lt_swap.mpr hd)

/-! ### Adding a cell -/

/-- The Young diagram obtained from `μ` by adding the cell `c` together with every cell below it in
the product order. It is defined without a hypothesis on `c`, dually to `YoungDiagram.erase`; at
an addable cell exactly the cell `c` is added (`YoungDiagram.IsAddable.cells_addCell_eq_insert`). -/
def addCell (μ : YoungDiagram) (c : ℕ × ℕ) : YoungDiagram where
  cells := μ.cells ∪ Finset.range (c.1 + 1) ×ˢ Finset.range (c.2 + 1)
  isLowerSet := by
    intro a b hba ha
    simp only [Finset.coe_union, Finset.coe_product, Finset.coe_range, Set.mem_union,
      Finset.mem_coe, mem_cells, Set.mem_prod, Set.mem_Iio] at ha ⊢
    rcases ha with ha | ⟨h1, h2⟩
    · exact .inl (μ.isLowerSet hba ha)
    · exact .inr ⟨hba.1.trans_lt h1, hba.2.trans_lt h2⟩

theorem cells_addCell (μ : YoungDiagram) (c : ℕ × ℕ) :
    (addCell μ c).cells = μ.cells ∪ Finset.range (c.1 + 1) ×ˢ Finset.range (c.2 + 1) :=
  (rfl)

@[simp]
theorem mem_addCell : d ∈ addCell μ c ↔ d ∈ μ ∨ d ≤ c := by
  rw [← mem_cells, cells_addCell]
  simp [Prod.le_def]

theorem le_addCell (μ : YoungDiagram) (c : ℕ × ℕ) : μ ≤ addCell μ c :=
  fun _ hd ↦ mem_addCell.mpr (.inl hd)

theorem mem_addCell_self (μ : YoungDiagram) (c : ℕ × ℕ) : c ∈ addCell μ c :=
  mem_addCell.mpr (.inr le_rfl)

/-- `addCell μ c` is the least Young diagram containing `μ` and the cell `c`. -/
@[simp]
theorem addCell_le_iff {ν : YoungDiagram} : addCell μ c ≤ ν ↔ μ ≤ ν ∧ c ∈ ν := by
  refine ⟨fun h ↦ ⟨(le_addCell μ c).trans h, h (mem_addCell_self μ c)⟩, fun ⟨hμ, hc⟩ d hd ↦ ?_⟩
  rcases mem_addCell.mp hd with hd | hd
  · exact hμ hd
  · exact ν.isLowerSet hd hc

namespace IsAddable

/-- Adding an addable cell adds exactly that cell. -/
theorem mem_addCell_iff (h : IsAddable μ c) : d ∈ addCell μ c ↔ d ∈ μ ∨ d = c := by
  rw [mem_addCell]
  refine ⟨fun hd ↦ ?_, fun hd ↦ hd.imp_right le_of_eq⟩
  rcases hd with hd | hdc
  · exact .inl hd
  · by_cases hne : d = c
    · exact .inr hne
    · exact .inl (h.mem_of_lt (lt_of_le_of_ne hdc hne))

@[simp]
theorem cells_addCell_eq_insert (h : IsAddable μ c) :
    (addCell μ c).cells = insert c μ.cells := by
  ext d
  simp [h.mem_addCell_iff, or_comm]

/-- Adding an addable cell raises the number of cells by one. -/
@[simp]
theorem card_addCell (h : IsAddable μ c) : (addCell μ c).card = μ.card + 1 := by
  simp only [YoungDiagram.card, h.cells_addCell_eq_insert]
  exact Finset.card_insert_of_notMem (by simpa using h.notMem)

/-- Adding an addable cell lengthens its row by one and leaves every other row unchanged. -/
@[simp]
theorem rowLen_addCell (h : IsAddable μ c) (i : ℕ) :
    (addCell μ c).rowLen i = if c.1 = i then μ.rowLen i + 1 else μ.rowLen i := by
  refine eq_of_forall_lt_iff fun j ↦ ?_
  have hc := h.snd_eq_rowLen
  rw [← mem_iff_lt_rowLen, h.mem_addCell_iff, mem_iff_lt_rowLen, Prod.ext_iff]
  split_ifs with hi
  · subst hi
    simp only [true_and]
    omega
  · simp [Ne.symm hi]

/-- Adding an addable cell lengthens its column by one and leaves every other column unchanged. -/
@[simp]
theorem colLen_addCell (h : IsAddable μ c) (j : ℕ) :
    (addCell μ c).colLen j = if c.2 = j then μ.colLen j + 1 else μ.colLen j := by
  refine eq_of_forall_lt_iff fun i ↦ ?_
  have hc := h.fst_eq_colLen
  rw [← mem_iff_lt_colLen, h.mem_addCell_iff, mem_iff_lt_colLen, Prod.ext_iff]
  split_ifs with hj
  · subst hj
    simp only [and_true]
    omega
  · simp [Ne.symm hj]

/-- An addable cell is a corner of the diagram obtained by adding it. -/
theorem isCorner_addCell (h : IsAddable μ c) : IsCorner (addCell μ c) c := by
  refine (isCorner_def _ _).mpr ⟨mem_addCell_self μ c, ?_, ?_⟩ <;> rw [h.mem_addCell_iff] <;>
    rintro (hd | hd)
  · exact h.notMem (μ.up_left_mem le_rfl (Nat.le_succ _) hd)
  · simpa using congrArg Prod.snd hd
  · exact h.notMem (μ.up_left_mem (Nat.le_succ _) le_rfl hd)
  · simpa using congrArg Prod.fst hd

/-- Removing an addable cell after adding it recovers the diagram. -/
@[simp]
theorem erase_addCell (h : IsAddable μ c) : erase (addCell μ c) c = μ := by
  ext d
  rw [mem_cells, h.isCorner_addCell.mem_erase_iff, h.mem_addCell_iff]
  exact ⟨fun ⟨hd, hne⟩ ↦ hd.resolve_right hne, fun hd ↦ ⟨.inl hd, fun he ↦ h.notMem (he ▸ hd)⟩⟩

end IsAddable

/-- A cell is addable to `μ` exactly when it lies outside `μ` and adding it to the cells of `μ`
gives a lower set, that is, the cells of a Young diagram. -/
theorem isAddable_iff_isLowerSet :
    IsAddable μ c ↔ c ∉ μ ∧ IsLowerSet (insert c (μ.cells : Set (ℕ × ℕ))) := by
  refine ⟨fun h ↦ ⟨h.notMem, ?_⟩, fun ⟨hc, hl⟩ ↦ ⟨hc, fun d hd ↦ ?_⟩⟩
  · have := (addCell μ c).isLowerSet
    rwa [h.cells_addCell_eq_insert, Finset.coe_insert] at this
  · rcases hl hd.le (Set.mem_insert c _) with rfl | hd'
    · exact absurd hd (lt_irrefl _)
    · simpa using hd'

namespace IsCorner

/-- A corner of `μ` is addable to the diagram obtained by removing it. -/
theorem isAddable_erase (h : IsCorner μ c) : IsAddable (erase μ c) c := by
  refine ⟨h.notMem_erase, fun d hd ↦ ?_⟩
  rw [h.mem_erase_iff]
  exact ⟨μ.isLowerSet hd.le h.mem, hd.ne⟩

/-- Adding a corner back after removing it recovers the diagram. -/
@[simp]
theorem addCell_erase (h : IsCorner μ c) : addCell (erase μ c) c = μ := by
  ext d
  rw [mem_cells, h.isAddable_erase.mem_addCell_iff, h.mem_erase_iff]
  by_cases hd : d = c
  · simp [hd, h.mem]
  · simp [hd]

end IsCorner

@[simp]
theorem addCell_transpose (μ : YoungDiagram) (c : ℕ × ℕ) :
    addCell μ.transpose c = (addCell μ c.swap).transpose := by
  ext d
  simp only [mem_cells, mem_addCell, mem_transpose]
  exact or_congr_right ⟨fun h ↦ Prod.swap_le_swap.mpr h, fun h ↦ Prod.swap_le_swap.mp h⟩

/-! ### Contents -/

namespace IsAddable

/-- **Addable contents are `2`-separated.** If the addable cell `c` lies in a higher row than the
addable cell `d`, then the content of `c` exceeds that of `d` by at least `2`. -/
theorem two_le_cellContent_sub (hc : IsAddable μ c) (hd : IsAddable μ d) (h : c.1 < d.1) :
    2 ≤ cellContent c - cellContent d := by
  obtain ⟨i, hi⟩ : ∃ i, d.1 = i + 1 := ⟨d.1 - 1, by omega⟩
  have habove : d.2 < μ.rowLen i := mem_iff_lt_rowLen.mp (hd.mem_above hi)
  have hrow : μ.rowLen i ≤ c.2 := hc.snd_eq_rowLen ▸ μ.rowLen_anti _ _ (by omega)
  simp only [cellContent_def]
  omega

/-- **Addable contents are bounded.** The contents of two addable cells of `μ` differ by at most
`μ.card + 1`. -/
theorem cellContent_sub_le (hc : IsAddable μ c) (hd : IsAddable μ d) :
    cellContent c - cellContent d ≤ μ.card + 1 := by
  have hrow : c.2 ≤ μ.rowLen 0 := hc.snd_eq_rowLen ▸ μ.rowLen_anti _ _ (Nat.zero_le _)
  have hcol : d.1 ≤ μ.colLen 0 := hd.fst_eq_colLen ▸ μ.colLen_anti _ _ (Nat.zero_le _)
  have hcard := μ.rowLen_zero_add_colLen_zero_le
  simp only [cellContent_def]
  omega

/-- Distinct addable cells of `μ` have contents at distance between `2` and `μ.card + 1`. -/
theorem natAbs_cellContent_sub_mem (hc : IsAddable μ c) (hd : IsAddable μ d) (hne : c ≠ d) :
    (cellContent c - cellContent d).natAbs ∈ Finset.Icc 2 (μ.card + 1) := by
  rw [Finset.mem_Icc]
  rcases lt_trichotomy c.1 d.1 with h | h | h
  · have h₁ := hc.two_le_cellContent_sub hd h
    have h₂ := hc.cellContent_sub_le hd
    omega
  · exact absurd (hc.eq_of_fst_eq hd h) hne
  · have h₁ := hd.two_le_cellContent_sub hc h
    have h₂ := hd.cellContent_sub_le hc
    omega

end IsAddable

/-- Distinct addable cells of a Young diagram have distinct contents. -/
theorem injOn_cellContent (μ : YoungDiagram) : Set.InjOn cellContent {c | IsAddable μ c} := by
  intro c hc d hd h
  by_contra hne
  have := Finset.mem_Icc.mp (hc.natAbs_cellContent_sub_mem hd hne)
  rw [h, sub_self] at this
  simp at this

/-- **The upper content bound is sharp.** For `2 ≤ d`, some diagram of size `d - 1` has two
addable cells whose contents differ by exactly `d`: the one-row diagram with `d - 1` cells has the
addable cells `(0, d - 1)` and `(1, 0)`. -/
theorem exists_isAddable_cellContent_sub_eq {d : ℕ} (hd : 2 ≤ d) :
    ∃ μ : YoungDiagram, μ.card + 1 = d ∧ ∃ c c', IsAddable μ c ∧ IsAddable μ c' ∧
      cellContent c - cellContent c' = d := by
  refine ⟨addCell ⊥ (0, d - 2), ?_, (0, d - 1), (1, 0), ?_, ?_, by simp; omega⟩
  · simp only [YoungDiagram.card, cells_addCell, cells_bot, Finset.empty_union,
      Finset.card_product, Finset.card_range]
    omega
  · refine ⟨by simp; omega, fun e he ↦ ?_⟩
    simp only [mem_addCell, notMem_bot, false_or, Prod.le_def]
    rcases Prod.lt_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only at h1 h2 <;> omega
  · refine ⟨by simp, fun e he ↦ ?_⟩
    simp only [mem_addCell, notMem_bot, false_or, Prod.le_def]
    rcases Prod.lt_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only at h1 h2 <;> omega

/-! ### Separation by the powers of a parameter -/

/-- **Separation of `Q`-contents.** If `Q ^ d ≠ 1` for `2 ≤ d ≤ n`, then on every Young diagram of
size less than `n` the powers `Q ^ content c` of distinct addable cells are distinct. -/
theorem injOn_zpow_cellContent {G : Type*} [Group G] {Q : G} {n : ℕ}
    (hQ : ∀ d : ℕ, 2 ≤ d → d ≤ n → Q ^ d ≠ 1) (hμ : μ.card < n) :
    Set.InjOn (fun c ↦ Q ^ cellContent c) {c | IsAddable μ c} := by
  intro c hc d hd h
  by_contra hne
  have hmem := Finset.mem_Icc.mp (hc.natAbs_cellContent_sub_mem hd hne)
  refine hQ _ hmem.1 (by omega) ?_
  rw [pow_natAbs_eq_one, zpow_sub, mul_inv_eq_one]
  exact h

/-- **The separation criterion is sharp.** The powers `Q ^ content c` separate the addable cells
of every Young diagram of size less than `n` if and only if `Q ^ d ≠ 1` for `2 ≤ d ≤ n`. -/
theorem injOn_zpow_cellContent_iff {G : Type*} [Group G] {Q : G} {n : ℕ} :
    (∀ μ : YoungDiagram, μ.card < n →
        Set.InjOn (fun c ↦ Q ^ cellContent c) {c | IsAddable μ c}) ↔
      ∀ d : ℕ, 2 ≤ d → d ≤ n → Q ^ d ≠ 1 := by
  refine ⟨fun h d hd hdn hQd ↦ ?_, fun hQ μ hμ ↦ injOn_zpow_cellContent hQ hμ⟩
  obtain ⟨μ, hμ, c, c', hc, hc', hcc'⟩ := exists_isAddable_cellContent_sub_eq hd
  have heq : c = c' := h μ (by omega) hc hc' <| by
    rw [← mul_inv_eq_one, ← zpow_sub, hcc', zpow_natCast, hQd]
  rw [heq, sub_self] at hcc'
  omega

end YoungDiagram

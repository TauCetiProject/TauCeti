/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Diagram
public import TauCeti.Combinatorics.Young.Kostka
public import TauCeti.Data.List.Range

/-!
# Skew semistandard Young tableaux

For Young diagrams `λ ≤ ν`, a **semistandard tableau of skew shape `ν / λ`** fills the cells of `ν`
that do not lie in `λ` with natural numbers, weakly increasing along each row and strictly
increasing down each column. Skew tableaux index the monomials of skew Schur polynomials, and the
Littlewood–Richardson coefficients, which expand a product of Schur polynomials in Schur
polynomials, count the skew tableaux of prescribed content whose reading word is a lattice word.

As for Mathlib's `SemistandardYoungTableau`, a tableau is a function `ℕ → ℕ → ℕ`, required to vanish
off the skew cells, so that it is determined by its entries on those cells
(`TauCeti.SkewSemistandardYoungTableau.ext`). Containment `λ ≤ ν` is part of the data: there are no
skew tableaux of shape `ν / λ` unless `λ ≤ ν`. The straight shapes `ν / ⊥` are exactly Mathlib's
semistandard tableaux of shape `ν` (`TauCeti.SkewSemistandardYoungTableau.botEquiv`).

The **reading word** of a skew tableau lists its entries row by row from the top, each row from
right to left. It contains each letter as often as the tableau does
(`TauCeti.SkewSemistandardYoungTableau.count_readingWord`), and it is the word on which the ballot
condition defining a Littlewood–Richardson tableau is imposed.

A row of a skew tableau is weakly increasing, so it is the sorted list of its entries: it is
determined by the number `T.rowCount i k` of entries `k` in each row `i`
(`TauCeti.SkewSemistandardYoungTableau.eq_of_rowCount_eq`). Conversely, prescribed row counts
satisfying a column condition on their partial sums are the row counts of a skew tableau
(`TauCeti.SkewSemistandardYoungTableau.ofRowCount`).

## Main definitions

* `TauCeti.SkewSemistandardYoungTableau λ ν`: the semistandard tableaux of skew shape `ν / λ`.
* `TauCeti.SkewSemistandardYoungTableau.content`: how often each natural number occurs as an entry.
* `TauCeti.SkewSemistandardYoungTableau.rowReadingWord`: the entries of one row, right to left.
* `TauCeti.SkewSemistandardYoungTableau.readingWord`: the rows read from top to bottom, each from
  right to left.
* `TauCeti.SkewSemistandardYoungTableau.rowCount`: the number of entries `k` in row `i`.
* `TauCeti.SkewSemistandardYoungTableau.ofRowCount`: the skew tableau with prescribed row counts.
* `TauCeti.SkewSemistandardYoungTableau.botEquiv`: the skew tableaux of shape `ν / ⊥` are the
  semistandard tableaux of shape `ν`.

## Main results

* `TauCeti.SkewSemistandardYoungTableau.sum_content`: the content of a tableau of shape `ν / λ`
  adds up to the number `|ν| - |λ|` of skew cells.
* `TauCeti.SkewSemistandardYoungTableau.count_readingWord`: the reading word has the content of the
  tableau.
* `TauCeti.SkewSemistandardYoungTableau.eq_of_rowCount_eq`: a skew tableau is determined by its
  row counts.
* `TauCeti.SkewSemistandardYoungTableau.rowLen_add_sum_range_rowCount_succ_le`: column strictness
  as an inequality between partial sums of row counts.
* `TauCeti.SkewSemistandardYoungTableau.content_botEquiv`: the identification of straight skew
  tableaux with semistandard tableaux preserves the content.

## References

* W. Fulton, *Young Tableaux*, Cambridge University Press (1997), Sections 5.1 and 5.2.
* R. P. Stanley, *Enumerative Combinatorics, Volume 2*, Cambridge University Press (1999),
  Section 7.10.
-/

public section

namespace TauCeti

/-- A **semistandard Young tableau of skew shape `outer / inner`**: a filling of the cells of
`outer` outside `inner` by natural numbers, weakly increasing along each row and strictly increasing
down each column. It is stored as a function `ℕ → ℕ → ℕ` vanishing off those cells, and it carries
the containment `inner ≤ outer`, so there are no tableaux of shape `outer / inner` otherwise. -/
structure SkewSemistandardYoungTableau (inner outer : YoungDiagram) where
  /-- `entry i j` is the entry in row `i` and column `j`. -/
  entry : ℕ → ℕ → ℕ
  /-- The inner diagram is contained in the outer one. -/
  le : inner ≤ outer
  /-- The entries in each row of the skew shape are weakly increasing, from left to right. -/
  row_weak' : ∀ {i j₁ j₂ : ℕ}, j₁ < j₂ → (i, j₁) ∉ inner → (i, j₂) ∈ outer →
    entry i j₁ ≤ entry i j₂
  /-- The entries in each column of the skew shape are strictly increasing, from top to bottom. -/
  col_strict' : ∀ {i₁ i₂ j : ℕ}, i₁ < i₂ → (i₁, j) ∉ inner → (i₂, j) ∈ outer →
    entry i₁ j < entry i₂ j
  /-- `entry` vanishes on the cells of the inner diagram. -/
  zeros_inner' : ∀ {i j : ℕ}, (i, j) ∈ inner → entry i j = 0
  /-- `entry` vanishes off the outer diagram. -/
  zeros' : ∀ {i j : ℕ}, (i, j) ∉ outer → entry i j = 0

namespace SkewSemistandardYoungTableau

variable {inner outer : YoungDiagram}

instance instFunLike : FunLike (SkewSemistandardYoungTableau inner outer) ℕ (ℕ → ℕ) where
  coe := entry
  coe_injective T T' h := by
    cases T
    cases T'
    congr

/-- The `entry` field of a skew tableau is its coercion to a function. -/
@[simp]
theorem entry_eq_coe (T : SkewSemistandardYoungTableau inner outer) : T.entry = ⇑T :=
  rfl

/-- Two skew tableaux of the same shape with the same entries are equal. -/
@[ext]
theorem ext {T T' : SkewSemistandardYoungTableau inner outer} (h : ∀ i j, T i j = T' i j) :
    T = T' :=
  DFunLike.ext T T' fun i => funext (h i)

/-- The entries of a skew tableau are weakly increasing along each row of the skew shape. -/
theorem row_weak (T : SkewSemistandardYoungTableau inner outer) {i j₁ j₂ : ℕ} (hj : j₁ < j₂)
    (h₁ : (i, j₁) ∉ inner) (h₂ : (i, j₂) ∈ outer) : T i j₁ ≤ T i j₂ :=
  T.row_weak' hj h₁ h₂

/-- The entries of a skew tableau are weakly increasing along each row of the skew shape, stated
for weakly ordered columns. -/
theorem row_weak_of_le (T : SkewSemistandardYoungTableau inner outer) {i j₁ j₂ : ℕ}
    (hj : j₁ ≤ j₂) (h₁ : (i, j₁) ∉ inner) (h₂ : (i, j₂) ∈ outer) : T i j₁ ≤ T i j₂ := by
  rcases hj.eq_or_lt with rfl | hj
  · exact le_rfl
  · exact T.row_weak hj h₁ h₂

/-- The entries of a skew tableau are strictly increasing down each column of the skew shape. -/
theorem col_strict (T : SkewSemistandardYoungTableau inner outer) {i₁ i₂ j : ℕ} (hi : i₁ < i₂)
    (h₁ : (i₁, j) ∉ inner) (h₂ : (i₂, j) ∈ outer) : T i₁ j < T i₂ j :=
  T.col_strict' hi h₁ h₂

/-- A skew tableau vanishes on the cells of the inner diagram. -/
theorem zeros_of_mem_inner (T : SkewSemistandardYoungTableau inner outer) {i j : ℕ}
    (h : (i, j) ∈ inner) : T i j = 0 :=
  T.zeros_inner' h

/-- A skew tableau vanishes off the outer diagram. -/
theorem zeros (T : SkewSemistandardYoungTableau inner outer) {i j : ℕ} (h : (i, j) ∉ outer) :
    T i j = 0 :=
  T.zeros' h

/-- A skew tableau vanishes off its skew cells. -/
theorem zeros_of_notMem_sdiff (T : SkewSemistandardYoungTableau inner outer) {i j : ℕ}
    (h : (i, j) ∉ outer.cells \ inner.cells) : T i j = 0 := by
  rw [Finset.mem_sdiff, YoungDiagram.mem_cells, YoungDiagram.mem_cells, not_and_not_right] at h
  by_cases ho : (i, j) ∈ outer
  · exact T.zeros_of_mem_inner (h ho)
  · exact T.zeros ho

/-! ### Content -/

/-- The content, or weight, of a skew tableau: `content T k` is the number of skew cells whose
entry is `k`. -/
noncomputable def content (T : SkewSemistandardYoungTableau inner outer) : ℕ →₀ ℕ :=
  ((outer.cells \ inner.cells).val.map fun c => T c.1 c.2).toFinsupp

/-- The content of a skew tableau counts the skew cells carrying a given entry. -/
theorem content_apply (T : SkewSemistandardYoungTableau inner outer) (k : ℕ) :
    T.content k = ((outer.cells \ inner.cells).filter fun c => T c.1 c.2 = k).card := by
  rw [content, Multiset.toFinsupp_apply, Multiset.count_map]
  simp [Finset.card, Finset.filter_val, eq_comm]

/-- **The content of a skew tableau adds up to the number of skew cells**, `|outer| - |inner|`. -/
theorem sum_content (T : SkewSemistandardYoungTableau inner outer) :
    (T.content.sum fun _ m => m) = outer.card - inner.card := by
  refine (Finsupp.card_toMultiset T.content).symm.trans ?_
  rw [content, Multiset.toFinsupp_toMultiset, Multiset.card_map, ← Finset.card_def,
    Finset.card_sdiff_of_subset (YoungDiagram.cells_subset_iff.mpr T.le)]

/-! ### The reading word -/

/-- The entries of row `i` of a skew tableau, read from right to left. -/
def rowReadingWord (T : SkewSemistandardYoungTableau inner outer) (i : ℕ) : List ℕ :=
  ((List.range' (inner.rowLen i) (outer.rowLen i - inner.rowLen i)).map (T i)).reverse

/-- Unfolds `TauCeti.SkewSemistandardYoungTableau.rowReadingWord`. -/
theorem rowReadingWord_def (T : SkewSemistandardYoungTableau inner outer) (i : ℕ) :
    T.rowReadingWord i =
      ((List.range' (inner.rowLen i) (outer.rowLen i - inner.rowLen i)).map (T i)).reverse :=
  (rfl)

/-- The letters of a row of the reading word are the entries of that row of the skew shape. -/
theorem mem_rowReadingWord (T : SkewSemistandardYoungTableau inner outer) {i k : ℕ} :
    k ∈ T.rowReadingWord i ↔ ∃ j, (i, j) ∉ inner ∧ (i, j) ∈ outer ∧ T i j = k := by
  simp only [rowReadingWord_def, List.mem_reverse, List.mem_map, List.mem_range'_1,
    YoungDiagram.mem_iff_lt_rowLen, not_lt]
  exact exists_congr fun j => by omega

/-- A nonempty row of the skew shape is read starting from its last entry, the entry in column
`outer.rowLen i - 1`. -/
theorem rowReadingWord_eq_cons (T : SkewSemistandardYoungTableau inner outer) {i : ℕ}
    (h : inner.rowLen i < outer.rowLen i) :
    ∃ t, T.rowReadingWord i = T i (outer.rowLen i - 1) :: t := by
  obtain ⟨n, hn⟩ : ∃ n, outer.rowLen i - inner.rowLen i = n + 1 :=
    ⟨outer.rowLen i - inner.rowLen i - 1, by omega⟩
  refine ⟨((List.range' (inner.rowLen i) n).map (T i)).reverse, ?_⟩
  rw [rowReadingWord_def, hn, List.range'_concat, List.map_append, List.reverse_append]
  have hlast : inner.rowLen i + 1 * n = outer.rowLen i - 1 := by omega
  simp only [List.map_cons, List.map_nil, List.reverse_singleton, List.cons_append,
    List.nil_append, List.cons.injEq, and_true]
  rw [hlast]

/-- The **reading word** of a skew tableau: its rows read from top to bottom, each from right to
left. -/
def readingWord (T : SkewSemistandardYoungTableau inner outer) : List ℕ :=
  (List.range (outer.colLen 0)).flatMap T.rowReadingWord

/-- Unfolds `TauCeti.SkewSemistandardYoungTableau.readingWord`. -/
theorem readingWord_def (T : SkewSemistandardYoungTableau inner outer) :
    T.readingWord = (List.range (outer.colLen 0)).flatMap T.rowReadingWord :=
  (rfl)

/-- The rows above row `i`, followed by the first letter read in row `i`, form a prefix of the
reading word. -/
theorem flatMap_range_append_prefix_readingWord (T : SkewSemistandardYoungTableau inner outer)
    {i : ℕ} (h : inner.rowLen i < outer.rowLen i) :
    (List.range i).flatMap T.rowReadingWord ++ [T i (outer.rowLen i - 1)] <+: T.readingWord := by
  have hi : i + 1 ≤ outer.colLen 0 := by
    have := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.sub_one_lt_of_lt h)
    exact YoungDiagram.lt_colLen_zero_of_mem this
  obtain ⟨t, ht⟩ := T.rowReadingWord_eq_cons h
  rw [readingWord_def, ← Nat.add_sub_cancel' hi, List.range_add, List.flatMap_append,
    List.range_succ, List.flatMap_append, List.flatMap_singleton, ht, List.append_assoc]
  exact (List.prefix_append_right_inj _).mpr (by simp)

section RowCount

open Finset

/-! ### Row counts -/

/-- The number of entries `k` in row `i` of a skew tableau. -/
def rowCount (T : SkewSemistandardYoungTableau inner outer) (i k : ℕ) : ℕ :=
  #{j ∈ Ico (inner.rowLen i) (outer.rowLen i) | T i j = k}

theorem rowCount_def (T : SkewSemistandardYoungTableau inner outer) (i k : ℕ) :
    T.rowCount i k = #{j ∈ Ico (inner.rowLen i) (outer.rowLen i) | T i j = k} :=
  (rfl)

/-- A row past the last row of the outer diagram is empty. -/
theorem rowCount_eq_zero_of_colLen_le (T : SkewSemistandardYoungTableau inner outer) {i : ℕ}
    (hi : outer.colLen 0 ≤ i) (k : ℕ) : T.rowCount i k = 0 := by
  simp [rowCount, YoungDiagram.rowLen_eq_zero_of_colLen_le hi]

/-- Summing the row counts over the letters below `x` counts the entries smaller than `x`. -/
theorem sum_range_rowCount (T : SkewSemistandardYoungTableau inner outer) (i x : ℕ) :
    ∑ k ∈ range x, T.rowCount i k =
      #{j ∈ Ico (inner.rowLen i) (outer.rowLen i) | T i j < x} := by
  rw [card_eq_sum_card_fiberwise (f := T i) (t := range x)
    fun j hj => mem_range.mpr (mem_filter.mp hj).2]
  refine sum_congr rfl fun k hk => ?_
  rw [rowCount, filter_filter]
  exact congrArg card <| filter_congr fun j _ =>
    ⟨fun h => ⟨h ▸ mem_range.mp hk, h⟩, fun h => h.2⟩

/-- **A row of a skew tableau is determined by its counts**: the entry in column `j` is smaller
than `x` exactly when `j` lies among the first `∑_{k < x} rowCount i k` cells of the row. -/
theorem apply_lt_iff (T : SkewSemistandardYoungTableau inner outer) {i j x : ℕ}
    (hi : inner.rowLen i ≤ j) (ho : j < outer.rowLen i) :
    T i j < x ↔ j - inner.rowLen i < ∑ k ∈ range x, T.rowCount i k := by
  have hin : ∀ {j'}, inner.rowLen i ≤ j' → (i, j') ∉ inner := fun h hm =>
    (YoungDiagram.mem_iff_lt_rowLen.mp hm).not_ge h
  have hout : (i, j) ∈ outer := YoungDiagram.mem_iff_lt_rowLen.mpr ho
  rw [sum_range_rowCount]
  constructor
  · intro h
    have hsub : Ico (inner.rowLen i) (j + 1) ⊆
        {j' ∈ Ico (inner.rowLen i) (outer.rowLen i) | T i j' < x} := by
      intro j' hj'
      rw [mem_Ico] at hj'
      exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hj'.1, by omega⟩,
        (T.row_weak_of_le (by omega) (hin hj'.1) hout).trans_lt h⟩
    have := card_le_card hsub
    rw [Nat.card_Ico] at this
    omega
  · intro h
    by_contra hx
    have hsub : {j' ∈ Ico (inner.rowLen i) (outer.rowLen i) | T i j' < x} ⊆
        Ico (inner.rowLen i) j := by
      intro j' hj'
      rw [mem_filter, mem_Ico] at hj'
      refine mem_Ico.mpr ⟨hj'.1.1, not_le.mp fun hj => ?_⟩
      exact hx ((T.row_weak_of_le hj (hin hi)
        (YoungDiagram.mem_iff_lt_rowLen.mpr hj'.1.2)).trans_lt hj'.2)
    have := card_le_card hsub
    rw [Nat.card_Ico] at this
    omega

/-- The counts of the letters below `x` in a row add up to at most the length of the row. -/
theorem sum_range_rowCount_le (T : SkewSemistandardYoungTableau inner outer) (i x : ℕ) :
    ∑ k ∈ range x, T.rowCount i k ≤ outer.rowLen i - inner.rowLen i := by
  rw [sum_range_rowCount, ← Nat.card_Ico]
  exact card_filter_le _ _

/-- When every entry of a row is smaller than `x`, the counts of the letters below `x` add up to
the length of the row. -/
theorem sum_range_rowCount_of_forall_lt (T : SkewSemistandardYoungTableau inner outer) {i x : ℕ}
    (h : ∀ j, inner.rowLen i ≤ j → j < outer.rowLen i → T i j < x) :
    ∑ k ∈ range x, T.rowCount i k = outer.rowLen i - inner.rowLen i := by
  rw [sum_range_rowCount, filter_true_of_mem fun j hj => h j (mem_Ico.mp hj).1 (mem_Ico.mp hj).2,
    Nat.card_Ico]

/-- **The column sums of the row counts are the content.** -/
theorem sum_range_rowCount_eq_content (T : SkewSemistandardYoungTableau inner outer) (k : ℕ)
    {N : ℕ} (hN : outer.colLen 0 ≤ N) : ∑ i ∈ range N, T.rowCount i k = T.content k := by
  have hsdiff : (outer.cells \ inner.cells).filter (fun c => T c.1 c.2 = k) =
      outer.cells.filter fun c => c ∉ inner ∧ T c.1 c.2 = k := by
    ext c
    simp [and_assoc]
  rw [content_apply, hsdiff, YoungDiagram.card_filter_cells outer _ hN]
  refine sum_congr rfl fun i _ => congrArg card ?_
  ext j
  simp only [mem_filter, mem_range, mem_Ico, YoungDiagram.mem_iff_lt_rowLen, not_lt]
  tauto

/-- **A skew tableau is determined by its row counts.** -/
theorem eq_of_rowCount_eq {T T' : SkewSemistandardYoungTableau inner outer}
    (h : ∀ i k, T.rowCount i k = T'.rowCount i k) : T = T' := by
  ext i j
  by_cases hc : (i, j) ∈ outer.cells \ inner.cells
  · rw [mem_sdiff, YoungDiagram.mem_cells, YoungDiagram.mem_cells,
      YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen, not_lt] at hc
    have key : ∀ x, T i j < x ↔ T' i j < x := fun x => by
      rw [T.apply_lt_iff hc.2 hc.1, T'.apply_lt_iff hc.2 hc.1, sum_congr rfl fun k _ => h i k]
    exact le_antisymm (Nat.lt_succ_iff.mp ((key _).mpr (Nat.lt_add_one _)))
      (Nat.lt_succ_iff.mp ((key _).mp (Nat.lt_add_one _)))
  · rw [T.zeros_of_notMem_sdiff hc, T'.zeros_of_notMem_sdiff hc]

/-- **Column strictness in terms of row counts**: the cells of row `i + 1` holding a letter at
most `x`, shifted by the inner diagram, end no later than the cells of row `i` holding a letter
smaller than `x`. -/
theorem rowLen_add_sum_range_rowCount_succ_le (T : SkewSemistandardYoungTableau inner outer)
    (i x : ℕ) :
    inner.rowLen (i + 1) + ∑ k ∈ range (x + 1), T.rowCount (i + 1) k ≤
      inner.rowLen i + ∑ k ∈ range x, T.rowCount i k := by
  have hpl := T.sum_range_rowCount_le (i + 1) (x + 1)
  have hanti := inner.rowLen_anti i (i + 1) (by omega)
  have hanti' := outer.rowLen_anti i (i + 1) (by omega)
  generalize hp : ∑ k ∈ range (x + 1), T.rowCount (i + 1) k = p at hpl ⊢
  rcases Nat.eq_zero_or_pos p with h0 | hpos
  · omega
  -- The last cell of row `i + 1` holding a letter at most `x`.
  obtain ⟨j, hj⟩ : ∃ j, j = inner.rowLen (i + 1) + p - 1 := ⟨_, rfl⟩
  have hTj : T (i + 1) j < x + 1 := (T.apply_lt_iff (by omega) (by omega)).mpr (by omega)
  by_cases hin : (i, j) ∈ inner
  · have := YoungDiagram.mem_iff_lt_rowLen.mp hin
    omega
  · have hlt := T.col_strict (Nat.lt_add_one i) hin
      (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
    have hi : inner.rowLen i ≤ j := not_lt.mp (YoungDiagram.mem_iff_lt_rowLen.not.mp hin)
    have := (T.apply_lt_iff (x := x) hi (by omega : j < outer.rowLen i)).mp (by omega)
    omega

/-- The row reading word of row `i` contains the letter `k` as often as the row does. -/
@[simp]
theorem count_rowReadingWord (T : SkewSemistandardYoungTableau inner outer) (i k : ℕ) :
    (T.rowReadingWord i).count k = T.rowCount i k := by
  rw [rowReadingWord_def, List.count_reverse, List.count_map_range', rowCount,
    Nat.add_sub_cancel' (YoungDiagram.rowLen_le_of_le T.le i)]

/-- The rows above row `x` of the reading word contain the letter `k` as often as the rows above
row `x` of the tableau do. -/
theorem count_flatMap_range_rowReadingWord (T : SkewSemistandardYoungTableau inner outer)
    (x k : ℕ) :
    ((List.range x).flatMap T.rowReadingWord).count k = ∑ r ∈ range x, T.rowCount r k := by
  rw [List.count_flatMap, sum_eq_multiset_sum, range_val, Multiset.range, Multiset.map_coe,
    Multiset.sum_coe]
  simp [Function.comp_def]

/-- Reading any number `n` of rows past the last row of the outer diagram gives the reading
word. -/
theorem flatMap_range_rowReadingWord (T : SkewSemistandardYoungTableau inner outer)
    {n : ℕ} (hn : outer.colLen 0 ≤ n) :
    (List.range n).flatMap T.rowReadingWord = T.readingWord := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hnil : ((List.range d).map (outer.colLen 0 + ·)).flatMap T.rowReadingWord = [] := by
    refine List.flatMap_eq_nil_iff.mpr fun r hr => ?_
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hr
    simp [rowReadingWord_def, YoungDiagram.rowLen_eq_zero_of_colLen_le (Nat.le_add_right _ r)]
  rw [readingWord_def, List.range_add, List.flatMap_append, hnil, List.append_nil]

/-- **The reading word has the content of the tableau**: it contains each letter `k` as often as
the tableau does. -/
@[simp]
theorem count_readingWord (T : SkewSemistandardYoungTableau inner outer) (k : ℕ) :
    T.readingWord.count k = T.content k := by
  rw [readingWord_def, count_flatMap_range_rowReadingWord, sum_range_rowCount_eq_content _ _ le_rfl]

end RowCount

section OfRowCount

open Finset

/-! ### The skew tableau with prescribed row counts -/

/-- The entries of the skew tableau with prescribed row counts `m i k`, the letters lying below
`K`: the entry in column `j` of row `i` is the largest `x ≤ K` such that the letters below `x`
fill at most the first `j - inner.rowLen i` cells of the row. -/
private def fillEntry (inner outer : YoungDiagram) (K : ℕ) (m : ℕ → ℕ → ℕ) (i j : ℕ) : ℕ :=
  if (i, j) ∈ outer ∧ (i, j) ∉ inner then
    Nat.findGreatest (fun x => ∑ l ∈ range x, m i l ≤ j - inner.rowLen i) K
  else 0

variable {K : ℕ} {m : ℕ → ℕ → ℕ}

private theorem le_fillEntry_iff
    (hsum : ∀ i, ∑ l ∈ range K, m i l = outer.rowLen i - inner.rowLen i)
    {i j x : ℕ} (hi : inner.rowLen i ≤ j) (ho : j < outer.rowLen i) :
    x ≤ fillEntry inner outer K m i j ↔ ∑ l ∈ range x, m i l ≤ j - inner.rowLen i := by
  rw [fillEntry, ite_eq_left ⟨YoungDiagram.mem_iff_lt_rowLen.mpr ho,
    fun h => (YoungDiagram.mem_iff_lt_rowLen.mp h).not_ge hi⟩]
  constructor
  · intro hx
    exact (sum_le_sum_of_subset (range_subset_range.mpr hx)).trans
      (Nat.findGreatest_spec (P := fun x => ∑ l ∈ range x, m i l ≤ j - inner.rowLen i)
        (Nat.zero_le K) (by simp))
  · intro hx
    refine Nat.le_findGreatest (not_lt.mp fun hK => ?_) hx
    have := sum_le_sum_of_subset (f := m i) (range_subset_range.mpr hK.le)
    rw [hsum] at this
    omega

/-- **The skew tableau with prescribed row counts.** Given counts `m i k` of the letters `k < K`
in the rows `i` of the skew shape `outer / inner`, filling each row with these letters in
increasing order gives a semistandard tableau when, row by row, the cells of row `i + 1` holding a
letter at most `x` end no later than the cells of row `i` holding a letter smaller than `x`. -/
def ofRowCount (hle : inner ≤ outer) (K : ℕ) (m : ℕ → ℕ → ℕ)
    (hsum : ∀ i, ∑ l ∈ range K, m i l = outer.rowLen i - inner.rowLen i)
    (hcol : ∀ i x, inner.rowLen (i + 1) + ∑ l ∈ range (x + 1), m (i + 1) l ≤
      inner.rowLen i + ∑ l ∈ range x, m i l) :
    SkewSemistandardYoungTableau inner outer where
  entry := fillEntry inner outer K m
  le := hle
  row_weak' {i j₁ j₂} hj h₁ h₂ := by
    have hi : inner.rowLen i ≤ j₁ := not_lt.mp (YoungDiagram.mem_iff_lt_rowLen.not.mp h₁)
    have ho := YoungDiagram.mem_iff_lt_rowLen.mp h₂
    refine (le_fillEntry_iff hsum (by omega) ho).mpr ?_
    exact ((le_fillEntry_iff hsum hi (by omega)).mp le_rfl).trans (by omega)
  col_strict' {i₁ i₂ j} hi h₁ h₂ := by
    have hi₁ : inner.rowLen i₁ ≤ j := not_lt.mp (YoungDiagram.mem_iff_lt_rowLen.not.mp h₁)
    -- Two adjacent rows, by `hcol`.
    have step : ∀ i, inner.rowLen i ≤ j → j < outer.rowLen (i + 1) →
        fillEntry inner outer K m i j < fillEntry inner outer K m (i + 1) j := by
      intro i hi ho
      have hanti := inner.rowLen_anti i (i + 1) (by omega)
      have ho' := ho.trans_le (outer.rowLen_anti i (i + 1) (by omega))
      have h := (le_fillEntry_iff hsum hi ho').mp le_rfl
      rw [Nat.lt_iff_add_one_le]
      refine (le_fillEntry_iff hsum (by omega) ho).mpr ?_
      have := hcol i (fillEntry inner outer K m i j)
      omega
    have ho₂ := YoungDiagram.mem_iff_lt_rowLen.mp h₂
    induction i₂, hi using Nat.le_induction with
    | base => exact step i₁ hi₁ ho₂
    | succ i hi ih =>
      have hanti := inner.rowLen_anti i₁ i (by omega)
      have ho := ho₂.trans_le (outer.rowLen_anti i (i + 1) (by omega))
      exact (ih (YoungDiagram.mem_iff_lt_rowLen.mpr ho) ho).trans (step i (by omega) ho₂)
  zeros_inner' h := ite_eq_right fun h' => h'.2 h
  zeros' h := ite_eq_right fun h' => h h'.1

private theorem ofRowCount_apply (hle : inner ≤ outer) (hsum hcol) (i j : ℕ) :
    ofRowCount hle K m hsum hcol i j = fillEntry inner outer K m i j :=
  (rfl)

/-- **The entries of the skew tableau with prescribed row counts**: the entry in column `j` of
row `i` is at least `x` exactly when the letters below `x` fill at most the first
`j - inner.rowLen i` cells of the row. -/
theorem le_ofRowCount_iff (hle : inner ≤ outer) (hsum hcol) {i j x : ℕ}
    (hi : inner.rowLen i ≤ j) (ho : j < outer.rowLen i) :
    x ≤ ofRowCount hle K m hsum hcol i j ↔ ∑ l ∈ range x, m i l ≤ j - inner.rowLen i :=
  le_fillEntry_iff hsum hi ho

/-- **The filled tableau has the prescribed row counts.** -/
@[simp]
theorem rowCount_ofRowCount (hle : inner ≤ outer) (hsum hcol) (hzero : ∀ i l, K ≤ l → m i l = 0)
    (i k : ℕ) : (ofRowCount hle K m hsum hcol).rowCount i k = m i k := by
  -- The prescribed counts below `x` never exceed the row length.
  have hle' : ∀ x, ∑ l ∈ range x, m i l ≤ outer.rowLen i - inner.rowLen i := fun x => by
    rcases le_total x K with hx | hx
    · exact (hsum i).symm ▸ sum_le_sum_of_subset (range_subset_range.mpr hx)
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hx
      rw [sum_range_add, sum_eq_zero fun l _ => hzero i _ (Nat.le_add_right _ _), add_zero,
        hsum i]
  have hS : ∀ x, ∑ l ∈ range x, (ofRowCount hle K m hsum hcol).rowCount i l =
      ∑ l ∈ range x, m i l := fun x => by
      rw [sum_range_rowCount]
      have hfilter : {j ∈ Ico (inner.rowLen i) (outer.rowLen i) |
          ofRowCount hle K m hsum hcol i j < x} =
          Ico (inner.rowLen i) (inner.rowLen i + ∑ l ∈ range x, m i l) := by
        ext j
        simp only [mem_filter, mem_Ico, ofRowCount_apply]
        constructor
        · rintro ⟨⟨hi, ho⟩, hx⟩
          have := (le_fillEntry_iff hsum hi ho).not.mp (not_le.mpr hx)
          omega
        · rintro ⟨hi, hj⟩
          have ho : j < outer.rowLen i := by have := hle' x; omega
          exact ⟨⟨hi, ho⟩, not_le.mp ((le_fillEntry_iff hsum hi ho).not.mpr (by omega))⟩
      rw [hfilter, Nat.card_Ico]
      omega
  have h₁ := hS (k + 1)
  rw [sum_range_succ, sum_range_succ, hS k] at h₁
  omega

end OfRowCount

/-! ### Straight shapes -/

/-- **The skew tableaux of straight shape `μ / ⊥` are the semistandard tableaux of shape `μ`.**
Both are fillings of the cells of `μ` stored as functions `ℕ → ℕ → ℕ`, and the equivalence keeps
the entries. -/
def botEquiv (μ : YoungDiagram) :
    SkewSemistandardYoungTableau ⊥ μ ≃ SemistandardYoungTableau μ where
  toFun T :=
    { entry := T
      row_weak' := fun hj h => T.row_weak hj (YoungDiagram.notMem_bot _) h
      col_strict' := fun hi h => T.col_strict hi (YoungDiagram.notMem_bot _) h
      zeros' := fun h => T.zeros h }
  invFun T :=
    { entry := T
      le := bot_le
      row_weak' := fun hj _ h => T.row_weak hj h
      col_strict' := fun hi _ h => T.col_strict hi h
      zeros_inner' := fun h => absurd h (YoungDiagram.notMem_bot _)
      zeros' := fun h => T.zeros h }
  left_inv _ := rfl
  right_inv _ := rfl

/-- `TauCeti.SkewSemistandardYoungTableau.botEquiv` keeps the entries. -/
@[simp]
theorem botEquiv_apply {μ : YoungDiagram} (T : SkewSemistandardYoungTableau ⊥ μ) (i j : ℕ) :
    botEquiv μ T i j = T i j :=
  (rfl)

/-- The inverse of `TauCeti.SkewSemistandardYoungTableau.botEquiv` keeps the entries. -/
@[simp]
theorem botEquiv_symm_apply {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (i j : ℕ) :
    (botEquiv μ).symm T i j = T i j :=
  (rfl)

/-- The identification of straight skew tableaux with semistandard tableaux preserves the
content. -/
@[simp]
theorem content_botEquiv {μ : YoungDiagram} (T : SkewSemistandardYoungTableau ⊥ μ) :
    SemistandardYoungTableau.content (botEquiv μ T) = T.content := by
  ext k
  rw [SemistandardYoungTableau.content_apply, content_apply, YoungDiagram.cells_bot,
    Finset.sdiff_empty]
  simp

end SkewSemistandardYoungTableau

end TauCeti

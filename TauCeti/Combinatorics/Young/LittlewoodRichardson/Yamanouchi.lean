/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.LittlewoodRichardson.Basic
public import TauCeti.Combinatorics.Young.Yamanouchi

/-!
# Littlewood–Richardson tableaux and Yamanouchi tableaux

There are two common ways of counting the Littlewood–Richardson coefficient `c^ν_{λ μ}`:

* the Littlewood–Richardson tableaux `TauCeti.LRTableau λ ν μ`, semistandard tableaux of skew shape
  `ν / λ` and content `μ` whose row reading word is a lattice word;
* Stembridge's `λ`-Yamanouchi tableaux (`SemistandardYoungTableau.IsYamanouchi`), semistandard
  tableaux `T` of straight shape `μ` with `λ + c(T) = ν`.

This file proves that the two sets are in bijection (`TauCeti.lrTableauEquivYamanouchi`). Both
kinds of tableau are determined by a matrix of natural numbers: a skew tableau `S` by the number
`S.rowCount i k` of entries `k` in its row `i` (a row is weakly increasing, so it is the sorted list
of its entries), and a tableau `T` of shape `μ` likewise by the number of entries `i` in its row
`k`. The bijection transposes this matrix: row `k` of `T` lists, in increasing order, the rows of
`S` in which the letter `k` occurs, each as often as it occurs there. The four defining conditions
then match in pairs, all of them inequalities between partial sums of the matrix
(`TauCeti.SkewSemistandardYoungTableau.rowLen_add_sum_range_rowCount_succ_le`):

* the lattice condition on the reading word of `S` is the column strictness of `T`
  (`TauCeti.SkewSemistandardYoungTableau.isLatticeWord_readingWord_iff`);
* for a semistandard `T`, being `λ`-Yamanouchi is the column strictness of `S`
  (`SemistandardYoungTableau.isYamanouchi_iff_rowCount`).

Consequently the Littlewood–Richardson coefficient may be read off either side
(`TauCeti.natCard_lrTableau_eq_natCard_isYamanouchi`).

## Main definitions

* `TauCeti.SkewSemistandardYoungTableau.rowCount`: the number of entries `k` in row `i`.
* `TauCeti.lrTableauEquivYamanouchi`: the bijection between the Littlewood–Richardson tableaux of
  shape `ν / λ` and content `μ` and the `λ`-Yamanouchi tableaux of shape `μ` and content `ν - λ`.

## Main results

* `TauCeti.SkewSemistandardYoungTableau.eq_of_rowCount_eq`: a skew tableau is determined by its
  row counts.
* `TauCeti.SkewSemistandardYoungTableau.isLatticeWord_readingWord_iff`: the lattice condition in
  terms of row counts.
* `SemistandardYoungTableau.isYamanouchi_iff_rowCount`: Stembridge's Yamanouchi condition in terms
  of row counts.
* `TauCeti.natCard_lrTableau_eq_natCard_isYamanouchi`: the two counts of `c^ν_{λ μ}` agree.

## References

* J. R. Stembridge, *A concise proof of the Littlewood–Richardson rule*, Electron. J. Combin.
  **9** (2002), Note 5.
* W. Fulton, *Young Tableaux*, Cambridge University Press (1997), Section 5.2.
* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 9.
-/

public section

open Finset

namespace TauCeti

namespace SkewSemistandardYoungTableau

variable {inner outer : YoungDiagram}

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
theorem lt_apply_iff (T : SkewSemistandardYoungTableau inner outer) {i j x : ℕ}
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
      rw [T.lt_apply_iff hc.2 hc.1, T'.lt_apply_iff hc.2 hc.1, sum_congr rfl fun k _ => h i k]
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
  have hTj : T (i + 1) j < x + 1 := (T.lt_apply_iff (by omega) (by omega)).mpr (by omega)
  by_cases hin : (i, j) ∈ inner
  · have := YoungDiagram.mem_iff_lt_rowLen.mp hin
    omega
  · have hlt := T.col_strict (Nat.lt_add_one i) hin
      (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
    have hi : inner.rowLen i ≤ j := not_lt.mp (YoungDiagram.mem_iff_lt_rowLen.not.mp hin)
    have := (T.lt_apply_iff (x := x) hi (by omega : j < outer.rowLen i)).mp (by omega)
    omega

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

/-! ### The lattice condition -/

private theorem count_map_range' (f : ℕ → ℕ) (s n c : ℕ) :
    ((List.range' s n).map f).count c = #{j ∈ Ico s (s + n) | f j = c} := by
  rw [List.count, List.countP_map, List.countP_eq_length_filter, Nat.Ico_eq_range']
  simp [Finset.card, Finset.filter_val, Function.comp_def, beq_eq_decide]

/-- The row reading word of row `i` contains the letter `k` as often as the row does. -/
@[simp]
theorem count_rowReadingWord (T : SkewSemistandardYoungTableau inner outer) (i k : ℕ) :
    (T.rowReadingWord i).count k = T.rowCount i k := by
  rw [rowReadingWord_def, List.count_reverse, count_map_range', rowCount,
    Nat.add_sub_cancel' (YoungDiagram.rowLen_le_of_le T.le i)]

private theorem count_flatMap_range_rowReadingWord (T : SkewSemistandardYoungTableau inner outer)
    (x k : ℕ) :
    ((List.range x).flatMap T.rowReadingWord).count k = ∑ r ∈ range x, T.rowCount r k := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [List.range_succ, List.flatMap_append, List.count_append, ih, List.flatMap_singleton,
      count_rowReadingWord, sum_range_succ]

private theorem flatMap_range_rowReadingWord (T : SkewSemistandardYoungTableau inner outer)
    {n : ℕ} (hn : outer.colLen 0 ≤ n) :
    (List.range n).flatMap T.rowReadingWord = T.readingWord := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hnil : ((List.range d).map (outer.colLen 0 + ·)).flatMap T.rowReadingWord = [] := by
    refine List.flatMap_eq_nil_iff.mpr fun r hr => ?_
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hr
    simp [rowReadingWord_def, YoungDiagram.rowLen_eq_zero_of_colLen_le (Nat.le_add_right _ r)]
  rw [readingWord_def, List.range_add, List.flatMap_append, hnil, List.append_nil]

private theorem exists_eq_flatMap_range_append {f : ℕ → List ℕ} {n : ℕ} {p : List ℕ}
    (hp : p <+: (List.range n).flatMap f) :
    ∃ x q, q <+: f x ∧ p = (List.range x).flatMap f ++ q := by
  induction n generalizing p with
  | zero => exact ⟨0, [], List.nil_prefix, by simpa using hp⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton] at hp
    obtain ⟨t, ht⟩ := hp
    rcases List.append_eq_append_iff.mp ht with ⟨a, ha, -⟩ | ⟨c, hc, hn⟩
    · exact ih ⟨a, ha.symm⟩
    · exact ⟨n, c, ⟨t, hn.symm⟩, hc⟩

/-- **The lattice condition in terms of row counts**: the reading word of a skew tableau is a
lattice word exactly when, for every row `x` and letter `k`, the rows up to `x` contain `k + 1`
at most as often as the rows above `x` contain `k`. -/
theorem isLatticeWord_readingWord_iff (T : SkewSemistandardYoungTableau inner outer) :
    T.readingWord.IsLatticeWord ↔
      ∀ k x, ∑ r ∈ range (x + 1), T.rowCount r (k + 1) ≤ ∑ r ∈ range x, T.rowCount r k := by
  constructor
  · intro h k x
    -- The prefix ending just before the first letter at most `k` of row `x`.
    have hab := YoungDiagram.rowLen_le_of_le T.le x
    have hr := T.sum_range_rowCount_le x (k + 1)
    have hlt : ∀ {j}, inner.rowLen x ≤ j → j < outer.rowLen x →
        (T x j < k + 1 ↔ j - inner.rowLen x < ∑ l ∈ range (k + 1), T.rowCount x l) :=
      fun hi ho => T.lt_apply_iff hi ho
    generalize ∑ l ∈ range (k + 1), T.rowCount x l = r at hr hlt
    set q := (T.rowReadingWord x).take (outer.rowLen x - inner.rowLen x - r) with hq_def
    have hq : q = ((List.range' (inner.rowLen x + r)
        (outer.rowLen x - inner.rowLen x - r)).map (T x)).reverse := by
      rw [hq_def, rowReadingWord_def, List.take_reverse, List.length_map, List.length_range',
        ← List.map_drop, List.drop_range']
      congr 3 <;> omega
    have hpre : (List.range x).flatMap T.rowReadingWord ++ q <+: T.readingWord := by
      rw [← T.flatMap_range_rowReadingWord (Nat.le_add_left _ (x + 1)), List.range_add,
        List.flatMap_append, List.range_succ, List.flatMap_append, List.flatMap_singleton,
        List.append_assoc]
      exact (List.prefix_append_right_inj _).mpr ((List.take_prefix _ _).trans
        (List.prefix_append _ _))
    have hk : q.count k = 0 := by
      rw [hq, List.count_reverse, count_map_range', card_eq_zero, filter_eq_empty_iff]
      intro j hj hjk
      rw [mem_Ico] at hj
      have := (hlt (j := j) (by omega) (by omega)).not.mpr (by omega)
      omega
    have hk₁ : q.count (k + 1) = T.rowCount x (k + 1) := by
      rw [hq, List.count_reverse, count_map_range', rowCount]
      congr 1
      ext j
      simp only [mem_filter, mem_Ico]
      constructor
      · rintro ⟨hj, hjk⟩
        exact ⟨⟨by omega, by omega⟩, hjk⟩
      · rintro ⟨hj, hjk⟩
        refine ⟨⟨not_lt.mp fun hjr => ?_, by omega⟩, hjk⟩
        have := (hlt hj.1 hj.2).mpr (by omega)
        omega
    have := List.isLatticeWord_iff.mp h _ hpre k
    rw [List.count_append, List.count_append, count_flatMap_range_rowReadingWord,
      count_flatMap_range_rowReadingWord, hk, hk₁] at this
    rw [sum_range_succ]
    omega
  · refine fun h => List.isLatticeWord_iff.mpr fun p hp k => ?_
    rw [← T.flatMap_range_rowReadingWord le_rfl] at hp
    obtain ⟨x, q, hq, rfl⟩ := exists_eq_flatMap_range_append hp
    rw [List.count_append, List.count_append, count_flatMap_range_rowReadingWord,
      count_flatMap_range_rowReadingWord]
    have h₁ := hq.count_le (k + 1)
    rw [count_rowReadingWord] at h₁
    have h₂ := h k x
    rw [sum_range_succ] at h₂
    omega

end SkewSemistandardYoungTableau

end TauCeti

/-! ### The Yamanouchi condition -/

namespace SemistandardYoungTableau

open TauCeti TauCeti.SkewSemistandardYoungTableau

variable {μ : YoungDiagram}

private theorem rowCount_symm_botEquiv (T : SemistandardYoungTableau μ) (r i : ℕ) :
    ((botEquiv μ).symm T).rowCount r i = #{c ∈ range (μ.rowLen r) | T r c = i} := by
  rw [rowCount, YoungDiagram.rowLen_bot, ← range_eq_Ico]
  simp only [botEquiv_symm_apply]

private theorem contentFromCol_eq_sum (T : SemistandardYoungTableau μ) (j i : ℕ) {N : ℕ}
    (hN : μ.colLen 0 ≤ N) :
    T.contentFromCol j i = ∑ r ∈ range N, #{c ∈ range (μ.rowLen r) | j ≤ c ∧ T r c = i} := by
  rw [contentFromCol_def, YoungDiagram.card_filter_cells μ _ hN]

private theorem sum_range_ite_lt (f : ℕ → ℕ) {x N : ℕ} (h : x ≤ N) :
    ∑ r ∈ range N, (if r < x then f r else 0) = ∑ r ∈ range x, f r := by
  rw [← sum_filter]
  congr 1
  ext r
  simp only [mem_filter, mem_range]
  omega

/-- A `λ`-Yamanouchi tableau satisfies the row-count condition at `(i, x)`: it is Stembridge's
condition at the first column of row `x` not holding a letter at most `i`. Left of that column,
column strictness keeps the letters `i` and `i + 1` out of the rows above `x`; from it on, it keeps
them out of the rows below. -/
private theorem rowLen_add_sum_rowCount_le_of_isYamanouchi {lam : YoungDiagram}
    {T : SemistandardYoungTableau μ} (h : T.IsYamanouchi lam) (i x : ℕ) :
      lam.rowLen (i + 1) + ∑ r ∈ range (x + 1), ((botEquiv μ).symm T).rowCount r (i + 1) ≤
        lam.rowLen i + ∑ r ∈ range x, ((botEquiv μ).symm T).rowCount r i := by
  set T' := (botEquiv μ).symm T
  have hmem : ∀ {r c}, c < μ.rowLen r → (r, c) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr
  -- A cell below a cell of the diagram lies in the diagram.
  have hup : ∀ {r r' c}, r' ≤ r → c < μ.rowLen r → c < μ.rowLen r' := fun h hc =>
    hc.trans_le (μ.rowLen_anti _ _ h)
  have hcol : ∀ {r r' c}, r' < r → c < μ.rowLen r → T r' c < T r c := fun h hc =>
    T.col_strict h (hmem hc)
  -- The first column of row `x` not holding a letter at most `i`.
  set P := T.rowCountLt x (i + 1)
  have hP : P ≤ μ.rowLen x := T.rowCountLt_le_rowLen x (i + 1)
  have hlt : ∀ {c}, c < μ.rowLen x → (T x c < i + 1 ↔ c < P) := fun hc =>
    (T.lt_rowCountLt_iff hc).symm
  have hN : μ.colLen 0 ≤ μ.colLen 0 + x + 1 := by omega
  have h₁ : T.contentFromCol P (i + 1) = ∑ r ∈ range (x + 1), T'.rowCount r (i + 1) := by
    rw [contentFromCol_eq_sum T P (i + 1) hN,
      ← sum_range_ite_lt _ (by omega : x + 1 ≤ μ.colLen 0 + x + 1)]
    refine sum_congr rfl fun r _ => ?_
    split_ifs with hr
    · rw [rowCount_symm_botEquiv]
      refine congrArg card (filter_congr fun c hc => ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩)
      rw [mem_range] at hc
      rcases (Nat.lt_succ_iff.mp hr).lt_or_eq with hr | rfl
      · refine not_lt.mp fun hcP => ?_
        have := hcol hr (hcP.trans_le hP)
        have := (hlt (hcP.trans_le hP)).mpr hcP
        omega
      · exact not_lt.mp fun hcP => by have := (hlt hc).mpr hcP; omega
    · refine card_eq_zero.mpr (filter_eq_empty_iff.mpr fun c hc ⟨hPc, hc'⟩ => ?_)
      rw [mem_range] at hc
      have := hcol (by omega : x < r) hc
      have := (hlt (hup (by omega) hc)).mp (by omega)
      omega
  have h₂ : T.contentFromCol P i = ∑ r ∈ range x, T'.rowCount r i := by
    rw [contentFromCol_eq_sum T P i hN, ← sum_range_ite_lt _ (by omega : x ≤ μ.colLen 0 + x + 1)]
    refine sum_congr rfl fun r _ => ?_
    split_ifs with hr
    · rw [rowCount_symm_botEquiv]
      refine congrArg card (filter_congr fun c hc => ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩)
      refine not_lt.mp fun hcP => ?_
      have := hcol hr (hcP.trans_le hP)
      have := (hlt (hcP.trans_le hP)).mpr hcP
      omega
    · refine card_eq_zero.mpr (filter_eq_empty_iff.mpr fun c hc ⟨hPc, hc'⟩ => ?_)
      rw [mem_range] at hc
      have hle : T x c ≤ T r c := by
        rcases (not_lt.mp hr).lt_or_eq with hr | rfl
        · exact (hcol hr hc).le
        · exact le_rfl
      have := (hlt (hup (not_lt.mp hr) hc)).mp (by omega)
      omega
  have := isYamanouchi_iff.mp h P i
  rwa [h₁, h₂] at this

/-- The row-count condition implies Stembridge's condition at every column `j` and letter `i`.
Let `k` be the lowest row holding a letter `i + 1` in a column at least `j`. If every letter `i`
in the rows above `k` lies in a column at least `j`, the row-count condition at `(i, k)` suffices.
Otherwise some letter `i` of row `k - 1` lies left of column `j`, so row `k - 1` holds `i` in
every column from `j` up to the end of its letters at most `i`; the row-count condition at
`(i, k - 1)` and column strictness between rows `k - 1` and `k` then bound the letters `i + 1` of
row `k` from column `j` on. -/
private theorem isYamanouchi_of_rowLen_add_sum_rowCount_le {lam : YoungDiagram}
    {T : SemistandardYoungTableau μ} (h : ∀ i x,
      lam.rowLen (i + 1) + ∑ r ∈ range (x + 1), ((botEquiv μ).symm T).rowCount r (i + 1) ≤
        lam.rowLen i + ∑ r ∈ range x, ((botEquiv μ).symm T).rowCount r i) :
    T.IsYamanouchi lam := by
  set T' := (botEquiv μ).symm T
  have hmem : ∀ {r c}, c < μ.rowLen r → (r, c) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr
  -- A cell below a cell of the diagram lies in the diagram.
  have hup : ∀ {r r' c}, r' ≤ r → c < μ.rowLen r → c < μ.rowLen r' := fun h hc =>
    hc.trans_le (μ.rowLen_anti _ _ h)
  have hcol : ∀ {r r' c}, r' < r → c < μ.rowLen r → T r' c < T r c := fun h hc =>
    T.col_strict h (hmem hc)
  refine isYamanouchi_iff.mpr fun j i => ?_
  classical
  have hanti := lam.rowLen_anti i (i + 1) (Nat.le_succ i)
  by_cases hex : ∃ k c, c < μ.rowLen k ∧ j ≤ c ∧ T k c = i + 1
  swap
  · have : T.contentFromCol j (i + 1) = 0 := by
      rw [contentFromCol_def]
      refine card_eq_zero.mpr (filter_eq_empty_iff.mpr fun c hc h' => hex ?_)
      exact ⟨c.1, c.2, YoungDiagram.mem_iff_lt_rowLen.mp ((YoungDiagram.mem_cells c).mp hc),
        h'⟩
    omega
  -- The lowest row holding a letter `i + 1` in a column at least `j`.
  obtain ⟨k, hk⟩ : ∃ k, k = Nat.findGreatest
      (fun k => ∃ c, c < μ.rowLen k ∧ j ≤ c ∧ T k c = i + 1) (μ.colLen 0) := ⟨_, rfl⟩
  obtain ⟨k₀, c₀, hc₀, hjc₀, hT₀⟩ := hex
  have hk₀ : k₀ ≤ μ.colLen 0 := (YoungDiagram.lt_colLen_zero_of_mem (hmem hc₀)).le
  have hspec := Nat.findGreatest_spec
    (P := fun k => ∃ c, c < μ.rowLen k ∧ j ≤ c ∧ T k c = i + 1) hk₀ ⟨c₀, hc₀, hjc₀, hT₀⟩
  rw [← hk] at hspec
  obtain ⟨c, hc, hjc, hTc⟩ := hspec
  have hmax : ∀ r, k < r → ∀ c', c' < μ.rowLen r → j ≤ c' → T r c' ≠ i + 1 := by
    intro r hr c' hc' hjc' hTc'
    have hr' : r ≤ μ.colLen 0 := (YoungDiagram.lt_colLen_zero_of_mem (hmem hc')).le
    exact Nat.findGreatest_is_greatest
      (P := fun k => ∃ c, c < μ.rowLen k ∧ j ≤ c ∧ T k c = i + 1) (hk ▸ hr) hr'
      ⟨c', hc', hjc', hTc'⟩
  set N := μ.colLen 0 + k + 1
  have hN : μ.colLen 0 ≤ N := by omega
  -- The cells holding `i + 1` in a column at least `j` lie in the rows up to `k`.
  have hf : T.contentFromCol j (i + 1) ≤ ∑ r ∈ range (k + 1), T'.rowCount r (i + 1) := by
    rw [contentFromCol_eq_sum T j (i + 1) hN, ← sum_range_ite_lt _ (by omega : k + 1 ≤ N)]
    refine sum_le_sum fun r _ => ?_
    split_ifs with hr
    · rw [rowCount_symm_botEquiv]
      exact card_le_card fun c' hc' =>
        mem_filter.mpr ⟨(mem_filter.mp hc').1, (mem_filter.mp hc').2.2⟩
    · refine (card_eq_zero.mpr (filter_eq_empty_iff.mpr fun c' hc' ⟨hjc', hc''⟩ =>
        hmax r (by omega) c' (mem_range.mp hc') hjc' hc'')).le
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- In the top row the condition is `hcol` at `x = 0`.
    have := h i k
    rw [hk0] at this hf
    simp only [sum_range_zero, add_zero] at this
    omega
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  -- The first column of row `k'` not holding a letter at most `i`.
  set P' := T.rowCountLt k' (i + 1)
  have hP' : P' ≤ μ.rowLen k' := T.rowCountLt_le_rowLen k' (i + 1)
  have hlt' : ∀ {c'}, c' < μ.rowLen k' → (T k' c' < i + 1 ↔ c' < P') := fun hc' =>
    (T.lt_rowCountLt_iff hc').symm
  have hcP' : c < P' := (hlt' (hup (Nat.le_succ k') hc)).mp (by
    have := hcol (Nat.lt_add_one k') hc
    omega)
  -- The letters `i` in the rows above `k'` lie in columns at least `P'`.
  have habove : ∀ r, r < k' → ∀ c', c' < μ.rowLen r → T r c' = i → P' ≤ c' := by
    intro r hr c' hc' hTc'
    refine not_lt.mp fun hlt => ?_
    have := hcol hr (hlt.trans_le hP')
    have := (hlt' (hlt.trans_le hP')).mpr hlt
    omega
  by_cases hleft : ∃ c', c' < j ∧ c' < μ.rowLen k' ∧ T k' c' = i
  · -- Some letter `i` of row `k'` lies left of column `j`.
    obtain ⟨c₁, hc₁j, hc₁, hTc₁⟩ := hleft
    set P := T.rowCountLt (k' + 1) (i + 2)
    have hlt : ∀ {c'}, c' < μ.rowLen (k' + 1) → (T (k' + 1) c' < i + 2 ↔ c' < P) :=
      fun hc' => (T.lt_rowCountLt_iff hc').symm
    have hPP' : P ≤ P' := T.rowCountLt_succ_le k' (i + 1)
    have hf' : T.contentFromCol j (i + 1) ≤
        ∑ r ∈ range (k' + 1), T'.rowCount r (i + 1) + (P - j) := by
      rw [contentFromCol_eq_sum T j (i + 1) hN, show N = k' + 1 + 1 + μ.colLen 0 by omega,
        sum_range_add, sum_range_succ]
      have h₁ : ∑ r ∈ range (k' + 1), #{c ∈ range (μ.rowLen r) | j ≤ c ∧ T r c = i + 1} ≤
          ∑ r ∈ range (k' + 1), T'.rowCount r (i + 1) := by
        refine sum_le_sum fun r _ => ?_
        rw [rowCount_symm_botEquiv]
        exact card_le_card fun c' hc' =>
        mem_filter.mpr ⟨(mem_filter.mp hc').1, (mem_filter.mp hc').2.2⟩
      have h₂ : #{c ∈ range (μ.rowLen (k' + 1)) | j ≤ c ∧ T (k' + 1) c = i + 1} ≤ P - j := by
        rw [← Nat.card_Ico]
        refine card_le_card fun c' hc' => ?_
        rw [mem_filter, mem_range] at hc'
        exact mem_Ico.mpr ⟨hc'.2.1, (hlt hc'.1).mp (by omega)⟩
      have h₃ : ∑ r ∈ range (μ.colLen 0),
          #{c ∈ range (μ.rowLen (k' + 1 + 1 + r)) | j ≤ c ∧ T (k' + 1 + 1 + r) c = i + 1} = 0 :=
        sum_eq_zero fun r _ => card_eq_zero.mpr (filter_eq_empty_iff.mpr
          fun c' hc' ⟨hjc', hc''⟩ => hmax _ (by omega) c' (mem_range.mp hc') hjc' hc'')
      omega
    have hg : ∑ r ∈ range k', T'.rowCount r i + (P' - j) ≤ T.contentFromCol j i := by
      rw [contentFromCol_eq_sum T j i hN]
      refine le_trans ?_ (sum_le_sum_of_subset (range_subset_range.mpr
        (by omega : k' + 1 ≤ N)))
      rw [sum_range_succ]
      refine add_le_add (sum_le_sum fun r hr => ?_) ?_
      · rw [rowCount_symm_botEquiv]
        refine card_le_card fun c' hc' => ?_
        rw [mem_filter, mem_range] at hc' ⊢
        exact ⟨hc'.1, (Nat.le_of_lt_succ (Nat.lt_succ_of_le
          (habove r (mem_range.mp hr) c' hc'.1 hc'.2))).trans' (by omega), hc'.2⟩
      · rw [← Nat.card_Ico]
        refine card_le_card fun c' hc' => ?_
        rw [mem_Ico] at hc'
        have hc'k : c' < μ.rowLen k' := hc'.2.trans_le hP'
        have h₁ := (hlt' hc'k).mpr hc'.2
        have h₂ := T.row_weak (by omega : c₁ < c') (hmem hc'k)
        exact mem_filter.mpr ⟨mem_range.mpr hc'k, hc'.1, by omega⟩
    have := h i k'
    omega
  · -- Every letter `i` in the rows above `k' + 1` lies in a column at least `j`.
    push Not at hleft
    have hg : ∑ r ∈ range (k' + 1), T'.rowCount r i ≤ T.contentFromCol j i := by
      rw [contentFromCol_eq_sum T j i hN]
      refine le_trans ?_ (sum_le_sum_of_subset (range_subset_range.mpr
        (by omega : k' + 1 ≤ N)))
      refine sum_le_sum fun r hr => ?_
      rw [rowCount_symm_botEquiv]
      refine card_le_card fun c' hc' => ?_
      rw [mem_filter, mem_range] at hc' ⊢
      refine ⟨hc'.1, ?_, hc'.2⟩
      rcases (Nat.lt_succ_iff.mp (mem_range.mp hr)).lt_or_eq with hr | rfl
      · have := habove r hr c' hc'.1 hc'.2
        omega
      · exact not_lt.mp fun hc'j => hleft c' hc'j hc'.1 hc'.2
    have := h i (k' + 1)
    omega

/-- **Stembridge's Yamanouchi condition in terms of row counts.** For a semistandard tableau `T`
of shape `μ`, being `λ`-Yamanouchi says that for every letter `i` and row `x`,
`λ_{i+1} + #{i + 1 in the rows up to x} ≤ λ_i + #{i in the rows above x}`. -/
theorem isYamanouchi_iff_rowCount (lam : YoungDiagram) (T : SemistandardYoungTableau μ) :
    T.IsYamanouchi lam ↔ ∀ i x,
      lam.rowLen (i + 1) + ∑ r ∈ range (x + 1), ((botEquiv μ).symm T).rowCount r (i + 1) ≤
        lam.rowLen i + ∑ r ∈ range x, ((botEquiv μ).symm T).rowCount r i :=
  ⟨rowLen_add_sum_rowCount_le_of_isYamanouchi, isYamanouchi_of_rowLen_add_sum_rowCount_le⟩

end SemistandardYoungTableau

/-! ### The bijection -/

namespace TauCeti

open SkewSemistandardYoungTableau

/-- The entries of a tableau with `λ + c(T) = ν` are letters of rows of `ν`. -/
theorem SemistandardYoungTableau.apply_lt_colLen_zero_of_rowLen_add_content_eq
    {lam ν μ : YoungDiagram} {T : _root_.SemistandardYoungTableau μ}
    (h : ∀ i, lam.rowLen i + SemistandardYoungTableau.content T i = ν.rowLen i) {i c : ℕ}
    (hc : (i, c) ∈ μ) : T i c < ν.colLen 0 := by
  have hpos : 0 < SemistandardYoungTableau.content T (T i c) := by
    rw [SemistandardYoungTableau.content_apply]
    exact card_pos.mpr ⟨(i, c), mem_filter.mpr ⟨(YoungDiagram.mem_cells _).mpr hc, rfl⟩⟩
  have := h (T i c)
  exact YoungDiagram.lt_colLen_zero_of_mem (j := 0)
    (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))

variable {lam ν μ : YoungDiagram}

/-- The `λ`-Yamanouchi tableau of a Littlewood–Richardson tableau: row `k` lists the rows holding
the letter `k`. -/
private def toYamanouchi (S : LRTableau lam ν μ) : SkewSemistandardYoungTableau ⊥ μ :=
  ofRowCount bot_le (ν.colLen 0) (fun k i => S.1.rowCount i k)
    (fun k => by
      rw [YoungDiagram.rowLen_bot, Nat.sub_zero, S.1.sum_range_rowCount_eq_content k le_rfl]
      exact congrFun S.2.1 k)
    (fun k x => by
      simpa [YoungDiagram.rowLen_bot] using
        (S.1.isLatticeWord_readingWord_iff.mp S.2.2) k x)

private theorem rowCount_toYamanouchi (S : LRTableau lam ν μ) (k i : ℕ) :
    (toYamanouchi S).rowCount k i = S.1.rowCount i k :=
  rowCount_ofRowCount _ _ _ (fun _ _ hi => S.1.rowCount_eq_zero_of_colLen_le hi _) k i

/-- The Littlewood–Richardson tableau of a `λ`-Yamanouchi tableau: row `i` lists the rows holding
the letter `i`. -/
private def ofYamanouchi
    (T : {T : _root_.SemistandardYoungTableau μ //
      T.IsYamanouchi lam ∧ ∀ i, lam.rowLen i + SemistandardYoungTableau.content T i = ν.rowLen i}) :
    SkewSemistandardYoungTableau lam ν :=
  ofRowCount (YoungDiagram.le_of_forall_rowLen_le fun i => (T.2.2 i).symm ▸ Nat.le_add_right _ _)
    (μ.colLen 0) (fun i k => ((botEquiv μ).symm T.1).rowCount k i)
    (fun i => by
      rw [((botEquiv μ).symm T.1).sum_range_rowCount_eq_content i le_rfl, ← content_botEquiv,
        Equiv.apply_symm_apply, ← T.2.2 i, Nat.add_sub_cancel_left])
    ((T.1.isYamanouchi_iff_rowCount lam).mp T.2.1)

private theorem rowCount_ofYamanouchi
    (T : {T : _root_.SemistandardYoungTableau μ //
      T.IsYamanouchi lam ∧ ∀ i, lam.rowLen i + SemistandardYoungTableau.content T i = ν.rowLen i})
    (i k : ℕ) : (ofYamanouchi T).rowCount i k = ((botEquiv μ).symm T.1).rowCount k i :=
  rowCount_ofRowCount _ _ _
    (fun _ _ hk => ((botEquiv μ).symm T.1).rowCount_eq_zero_of_colLen_le hk _) i k

/-- **Littlewood–Richardson tableaux are Yamanouchi tableaux.** The Littlewood–Richardson tableaux
of skew shape `ν / λ` and content `μ` correspond to Stembridge's `λ`-Yamanouchi tableaux `T` of
shape `μ` with `λ + c(T) = ν`. A tableau `S` of the first kind corresponds to the tableau whose row
`k` lists, in increasing order, the rows of `S` in which `k` occurs, each as often as it occurs
there (`TauCeti.rowCount_lrTableauEquivYamanouchi`). -/
def lrTableauEquivYamanouchi (lam ν μ : YoungDiagram) :
    LRTableau lam ν μ ≃ {T : _root_.SemistandardYoungTableau μ //
      T.IsYamanouchi lam ∧ ∀ i, lam.rowLen i + SemistandardYoungTableau.content T i = ν.rowLen i}
    where
  toFun S := ⟨botEquiv μ (toYamanouchi S), by
    refine ⟨(SemistandardYoungTableau.isYamanouchi_iff_rowCount lam _).mpr fun i x => ?_,
      fun i => ?_⟩
    · simp only [Equiv.symm_apply_apply, rowCount_toYamanouchi]
      exact S.1.rowLen_add_sum_range_rowCount_succ_le i x
    · rw [content_botEquiv, ← (toYamanouchi S).sum_range_rowCount_eq_content i le_rfl]
      simp only [rowCount_toYamanouchi]
      rw [S.1.sum_range_rowCount_of_forall_lt fun j hj hj' => ?_]
      · have := YoungDiagram.rowLen_le_of_le S.1.le i
        omega
      · -- The letters of `S` are rows of `μ`.
        have hpos : 0 < S.1.content (S.1 i j) := by
          rw [content_apply]
          refine card_pos.mpr ⟨(i, j), mem_filter.mpr ⟨?_, rfl⟩⟩
          rw [mem_sdiff, YoungDiagram.mem_cells, YoungDiagram.mem_cells,
            YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen, not_lt]
          exact ⟨hj', hj⟩
        rw [congrFun S.2.1] at hpos
        exact YoungDiagram.lt_colLen_zero_of_mem (j := 0)
          (YoungDiagram.mem_iff_lt_rowLen.mpr hpos)⟩
  invFun T := ⟨ofYamanouchi T, by
    refine ⟨funext fun k => ?_, (ofYamanouchi T).isLatticeWord_readingWord_iff.mpr fun k x => ?_⟩
    · rw [← (ofYamanouchi T).sum_range_rowCount_eq_content k le_rfl]
      simp only [rowCount_ofYamanouchi]
      rw [((botEquiv μ).symm T.1).sum_range_rowCount_of_forall_lt fun j _ hj => by
        rw [botEquiv_symm_apply]
        exact SemistandardYoungTableau.apply_lt_colLen_zero_of_rowLen_add_content_eq T.2.2
          (YoungDiagram.mem_iff_lt_rowLen.mpr hj)]
      simp [YoungDiagram.rowLen_bot]
    · simp only [rowCount_ofYamanouchi]
      simpa [YoungDiagram.rowLen_bot] using
        ((botEquiv μ).symm T.1).rowLen_add_sum_range_rowCount_succ_le k x⟩
  left_inv S := Subtype.ext <| eq_of_rowCount_eq fun i k => by
    simp only [rowCount_ofYamanouchi, Equiv.symm_apply_apply, rowCount_toYamanouchi]
  right_inv T := Subtype.ext <| (botEquiv μ).symm.injective <| eq_of_rowCount_eq fun k i => by
    simp only [Equiv.symm_apply_apply, rowCount_toYamanouchi, rowCount_ofYamanouchi]

/-- The tableau of shape `μ` attached to a Littlewood–Richardson tableau `S` holds the letter `i`
in its row `k` as often as `S` holds the letter `k` in its row `i`. -/
@[simp]
theorem rowCount_lrTableauEquivYamanouchi (S : LRTableau lam ν μ) (k i : ℕ) :
    ((botEquiv μ).symm (lrTableauEquivYamanouchi lam ν μ S).1).rowCount k i =
      S.1.rowCount i k := by
  simp [lrTableauEquivYamanouchi, rowCount_toYamanouchi]

/-- The Littlewood–Richardson tableau attached to a Yamanouchi tableau `T` holds the letter `k`
in its row `i` as often as `T` holds the letter `i` in its row `k`. -/
@[simp]
theorem rowCount_lrTableauEquivYamanouchi_symm
    (T : {T : _root_.SemistandardYoungTableau μ //
      T.IsYamanouchi lam ∧ ∀ i, lam.rowLen i + SemistandardYoungTableau.content T i = ν.rowLen i})
    (i k : ℕ) :
    ((lrTableauEquivYamanouchi lam ν μ).symm T).1.rowCount i k =
      ((botEquiv μ).symm T.1).rowCount k i :=
  rowCount_ofYamanouchi T i k

/-- **The two counts of the Littlewood–Richardson coefficient agree**: `c^ν_{λ μ}` is the number
of `λ`-Yamanouchi tableaux `T` of shape `μ` with `λ + c(T) = ν`. -/
theorem natCard_lrTableau_eq_natCard_isYamanouchi (lam ν μ : YoungDiagram) :
    Nat.card (LRTableau lam ν μ) = Nat.card {T : _root_.SemistandardYoungTableau μ //
      T.IsYamanouchi lam ∧ ∀ i, lam.rowLen i + SemistandardYoungTableau.content T i = ν.rowLen i} :=
  Nat.card_congr (lrTableauEquivYamanouchi lam ν μ)

end TauCeti

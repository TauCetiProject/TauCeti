/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.Range
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

* `TauCeti.lrTableauEquivYamanouchi`: the bijection between the Littlewood–Richardson tableaux of
  shape `ν / λ` and content `μ` and the `λ`-Yamanouchi tableaux of shape `μ` and content `ν - λ`.

## Main results

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

/-! ### The lattice condition -/

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
      fun hi ho => T.apply_lt_iff hi ho
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
      rw [hq, List.count_reverse, List.count_map_range', card_eq_zero, filter_eq_empty_iff]
      intro j hj hjk
      rw [mem_Ico] at hj
      have := (hlt (j := j) (by omega) (by omega)).not.mpr (by omega)
      omega
    have hk₁ : q.count (k + 1) = T.rowCount x (k + 1) := by
      rw [hq, List.count_reverse, List.count_map_range', rowCount_def]
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
    obtain ⟨x, q, hq, rfl⟩ := List.exists_eq_flatMap_range_append hp
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

/-- The skew tableau of straight shape attached to a tableau `T` holds as many letters below `x` in
its row `i` as `T` does. -/
theorem sum_range_rowCount_symm_botEquiv (T : SemistandardYoungTableau μ) (i x : ℕ) :
    ∑ k ∈ range x, ((botEquiv μ).symm T).rowCount i k = T.rowCountLt i x := by
  rw [sum_range_rowCount, YoungDiagram.rowLen_bot, ← range_eq_Ico]
  simp only [botEquiv_symm_apply]
  rw [T.filter_lt_eq_range, card_range]

private theorem rowCount_symm_botEquiv (T : SemistandardYoungTableau μ) (r i : ℕ) :
    ((botEquiv μ).symm T).rowCount r i = #{c ∈ range (μ.rowLen r) | T r c = i} := by
  rw [rowCount_def, YoungDiagram.rowLen_bot, ← range_eq_Ico]
  simp only [botEquiv_symm_apply]

/-- The letters `i` of row `r` in the columns from `j` on are among all its letters `i`. -/
private theorem card_filter_le_rowCount_symm_botEquiv (T : SemistandardYoungTableau μ)
    (r j i : ℕ) :
    #{c ∈ range (μ.rowLen r) | j ≤ c ∧ T r c = i} ≤ ((botEquiv μ).symm T).rowCount r i := by
  rw [rowCount_symm_botEquiv]
  exact card_le_card fun c hc => mem_filter.mpr ⟨(mem_filter.mp hc).1, (mem_filter.mp hc).2.2⟩

private theorem contentFromCol_eq_sum (T : SemistandardYoungTableau μ) (j i : ℕ) {N : ℕ}
    (hN : μ.colLen 0 ≤ N) :
    T.contentFromCol j i = ∑ r ∈ range N, #{c ∈ range (μ.rowLen r) | j ≤ c ∧ T r c = i} := by
  rw [contentFromCol_def, YoungDiagram.card_filter_cells μ _ hN]

/-- Column strictness, for a cell given by a bound on its column. -/
private theorem col_strict_of_lt_rowLen (T : SemistandardYoungTableau μ) {r r' c : ℕ}
    (h : r' < r) (hc : c < μ.rowLen r) : T r' c < T r c :=
  T.col_strict h (YoungDiagram.mem_iff_lt_rowLen.mpr hc)

/-- A letter at least `i` in a row above row `k` lies in a column at least the number of letters
at most `i` in row `k`: by column strictness, the letter below it is larger than `i`. -/
private theorem rowCountLt_le_of_lt (T : SemistandardYoungTableau μ) {r k c i : ℕ} (hr : r < k)
    (hi : i ≤ T r c) : T.rowCountLt k (i + 1) ≤ c := by
  refine not_lt.mp fun hlt => ?_
  have hck := hlt.trans_le (T.rowCountLt_le_rowLen k (i + 1))
  have := T.col_strict_of_lt_rowLen hr hck
  have := (T.lt_rowCountLt_iff hck).mp hlt
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
  -- The first column of row `x` not holding a letter at most `i`.
  set P := T.rowCountLt x (i + 1)
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
      · exact T.rowCountLt_le_of_lt hr (by omega)
      · exact not_lt.mp fun hcP => by have := (hlt hc).mpr hcP; omega
    · refine card_eq_zero.mpr (filter_eq_empty_iff.mpr fun c hc ⟨hPc, hc'⟩ => ?_)
      rw [mem_range] at hc
      have := T.col_strict_of_lt_rowLen (by omega : x < r) hc
      have := (hlt (hc.trans_le (μ.rowLen_anti _ _ (by omega)))).mp (by omega)
      omega
  have h₂ : T.contentFromCol P i = ∑ r ∈ range x, T'.rowCount r i := by
    rw [contentFromCol_eq_sum T P i hN, ← sum_range_ite_lt _ (by omega : x ≤ μ.colLen 0 + x + 1)]
    refine sum_congr rfl fun r _ => ?_
    split_ifs with hr
    · rw [rowCount_symm_botEquiv]
      refine congrArg card (filter_congr fun c hc => ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩)
      exact T.rowCountLt_le_of_lt hr h.ge
    · refine card_eq_zero.mpr (filter_eq_empty_iff.mpr fun c hc ⟨hPc, hc'⟩ => ?_)
      rw [mem_range] at hc
      have hle : T x c ≤ T r c := by
        rcases (not_lt.mp hr).lt_or_eq with hr | rfl
        · exact (T.col_strict_of_lt_rowLen hr hc).le
        · exact le_rfl
      have := (hlt (hc.trans_le (μ.rowLen_anti _ _ (not_lt.mp hr)))).mp (by omega)
      omega
  have := isYamanouchi_iff.mp h P i
  rwa [h₁, h₂] at this

/-- Stembridge's condition at column `j` and letter `i`, from the row-count condition at `(i, k)`,
when no row below `k + 1` holds a letter `i + 1` in a column at least `j` and some letter `i` of
row `k` lies left of column `j`. Row `k` then holds `i` in every column from `j` up to the end of
its letters at most `i`, and column strictness between rows `k` and `k + 1` bounds the letters
`i + 1` of row `k + 1` from column `j` on. -/
private theorem rowLen_add_contentFromCol_le_of_lt {lam : YoungDiagram}
    {T : SemistandardYoungTableau μ} {i j k c₁ : ℕ}
    (h : lam.rowLen (i + 1) + ∑ r ∈ range (k + 1), ((botEquiv μ).symm T).rowCount r (i + 1) ≤
      lam.rowLen i + ∑ r ∈ range k, ((botEquiv μ).symm T).rowCount r i)
    (hzero : ∀ r, k + 1 < r → #{c ∈ range (μ.rowLen r) | j ≤ c ∧ T r c = i + 1} = 0)
    (hjP : j ≤ T.rowCountLt k (i + 1)) (hc₁j : c₁ < j) (hTc₁ : T k c₁ = i) :
    lam.rowLen (i + 1) + T.contentFromCol j (i + 1) ≤ lam.rowLen i + T.contentFromCol j i := by
  have hP := T.rowCountLt_le_rowLen k (i + 1)
  have hPP := T.rowCountLt_succ_le k (i + 1)
  have hN : μ.colLen 0 ≤ k + 1 + 1 + μ.colLen 0 := by omega
  have hf : T.contentFromCol j (i + 1) ≤
      ∑ r ∈ range (k + 1), ((botEquiv μ).symm T).rowCount r (i + 1) +
        (T.rowCountLt (k + 1) (i + 1 + 1) - j) := by
    rw [contentFromCol_eq_sum T j (i + 1) hN, sum_range_add, sum_range_succ,
      sum_eq_zero fun r (_ : r ∈ range (μ.colLen 0)) => hzero (k + 1 + 1 + r) (by omega),
      add_zero]
    refine add_le_add (sum_le_sum fun r _ => T.card_filter_le_rowCount_symm_botEquiv r j _) ?_
    rw [← Nat.card_Ico]
    refine card_le_card fun c' hc' => ?_
    rw [mem_filter, mem_range] at hc'
    exact mem_Ico.mpr ⟨hc'.2.1, (T.lt_rowCountLt_iff hc'.1).mpr (by omega)⟩
  have hg : ∑ r ∈ range k, ((botEquiv μ).symm T).rowCount r i + (T.rowCountLt k (i + 1) - j) ≤
      T.contentFromCol j i := by
    rw [contentFromCol_eq_sum T j i hN]
    refine le_trans ?_ (sum_le_sum_of_subset (range_subset_range.mpr (by omega :
      k + 1 ≤ k + 1 + 1 + μ.colLen 0)))
    rw [sum_range_succ]
    refine add_le_add (sum_le_sum fun r hr => ?_) ?_
    · rw [rowCount_symm_botEquiv]
      refine card_le_card fun c' hc' => ?_
      rw [mem_filter, mem_range] at hc' ⊢
      have := T.rowCountLt_le_of_lt (mem_range.mp hr) hc'.2.ge
      exact ⟨hc'.1, by omega, hc'.2⟩
    · rw [← Nat.card_Ico]
      refine card_le_card fun c' hc' => ?_
      rw [mem_Ico] at hc'
      have hc'k : c' < μ.rowLen k := hc'.2.trans_le hP
      have h₁ := (T.lt_rowCountLt_iff hc'k).mp hc'.2
      have h₂ := T.row_weak (by omega : c₁ < c') (YoungDiagram.mem_iff_lt_rowLen.mpr hc'k)
      exact mem_filter.mpr ⟨mem_range.mpr hc'k, hc'.1, by omega⟩
  omega

/-- The row-count condition implies Stembridge's condition at every column `j` and letter `i`.
Let `k` be the lowest row holding a letter `i + 1` in a column at least `j`. If every letter `i`
in the rows above `k` lies in a column at least `j`, the row-count condition at `(i, k)` suffices.
Otherwise some letter `i` of row `k - 1` lies left of column `j`, and
`rowLen_add_contentFromCol_le_of_lt` applies. -/
private theorem isYamanouchi_of_rowLen_add_sum_rowCount_le {lam : YoungDiagram}
    {T : SemistandardYoungTableau μ} (h : ∀ i x,
      lam.rowLen (i + 1) + ∑ r ∈ range (x + 1), ((botEquiv μ).symm T).rowCount r (i + 1) ≤
        lam.rowLen i + ∑ r ∈ range x, ((botEquiv μ).symm T).rowCount r i) :
    T.IsYamanouchi lam := by
  set T' := (botEquiv μ).symm T
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
  have hk₀ : k₀ ≤ μ.colLen 0 :=
    (YoungDiagram.lt_colLen_zero_of_mem (YoungDiagram.mem_iff_lt_rowLen.mpr hc₀)).le
  have hspec := Nat.findGreatest_spec
    (P := fun k => ∃ c, c < μ.rowLen k ∧ j ≤ c ∧ T k c = i + 1) hk₀ ⟨c₀, hc₀, hjc₀, hT₀⟩
  rw [← hk] at hspec
  obtain ⟨c, hc, hjc, hTc⟩ := hspec
  -- No row below `k` holds a letter `i + 1` in a column at least `j`.
  have hzero : ∀ r, k < r → #{c ∈ range (μ.rowLen r) | j ≤ c ∧ T r c = i + 1} = 0 := by
    refine fun r hr => card_eq_zero.mpr (filter_eq_empty_iff.mpr fun c' hc' ⟨hjc', hTc'⟩ => ?_)
    have hc' := mem_range.mp hc'
    exact Nat.findGreatest_is_greatest
      (P := fun k => ∃ c, c < μ.rowLen k ∧ j ≤ c ∧ T k c = i + 1) (hk ▸ hr)
      (YoungDiagram.lt_colLen_zero_of_mem (YoungDiagram.mem_iff_lt_rowLen.mpr hc')).le
      ⟨c', hc', hjc', hTc'⟩
  set N := μ.colLen 0 + k + 1
  have hN : μ.colLen 0 ≤ N := by omega
  -- The cells holding `i + 1` in a column at least `j` lie in the rows up to `k`.
  have hf : T.contentFromCol j (i + 1) ≤ ∑ r ∈ range (k + 1), T'.rowCount r (i + 1) := by
    rw [contentFromCol_eq_sum T j (i + 1) hN, ← sum_range_ite_lt _ (by omega : k + 1 ≤ N)]
    refine sum_le_sum fun r _ => ?_
    split_ifs with hr
    · exact T.card_filter_le_rowCount_symm_botEquiv r j _
    · exact (hzero r (by omega)).le
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- In the top row the condition is the row-count condition at `x = 0`.
    have := h i k
    rw [hk0] at this hf
    simp only [sum_range_zero, add_zero] at this
    omega
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  -- The cell above the letter `i + 1` at `(k' + 1, c)` holds a letter at most `i`.
  have hjP : j ≤ T.rowCountLt k' (i + 1) := by
    have hc' : c < μ.rowLen k' := hc.trans_le (μ.rowLen_anti _ _ (Nat.le_succ k'))
    have := T.col_strict_of_lt_rowLen (Nat.lt_add_one k') hc
    exact hjc.trans ((T.lt_rowCountLt_iff hc').mpr (by omega)).le
  by_cases hleft : ∃ c', c' < j ∧ c' < μ.rowLen k' ∧ T k' c' = i
  · -- Some letter `i` of row `k'` lies left of column `j`.
    obtain ⟨c₁, hc₁j, -, hTc₁⟩ := hleft
    exact rowLen_add_contentFromCol_le_of_lt (h i k') hzero hjP hc₁j hTc₁
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
      · have := T.rowCountLt_le_of_lt hr hc'.2.ge
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

/-- The entries of a tableau with `λ + c(T) = ν` are letters of rows of `ν`. -/
theorem apply_lt_colLen_zero_of_rowLen_add_content_eq
    {lam ν : YoungDiagram} {T : SemistandardYoungTableau μ}
    (h : ∀ i, lam.rowLen i + SemistandardYoungTableau.content T i = ν.rowLen i) {i c : ℕ}
    (hc : (i, c) ∈ μ) : T i c < ν.colLen 0 := by
  have hpos : 0 < SemistandardYoungTableau.content T (T i c) := by
    rw [SemistandardYoungTableau.content_apply]
    exact card_pos.mpr ⟨(i, c), mem_filter.mpr ⟨(YoungDiagram.mem_cells _).mpr hc, rfl⟩⟩
  have := h (T i c)
  exact YoungDiagram.lt_colLen_zero_of_mem (j := 0)
    (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))

end SemistandardYoungTableau

/-! ### The bijection -/

namespace TauCeti

open SkewSemistandardYoungTableau

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

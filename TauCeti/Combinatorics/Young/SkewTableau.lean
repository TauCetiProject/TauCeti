/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Diagram
public import TauCeti.Combinatorics.Young.Kostka

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

## Main definitions

* `TauCeti.SkewSemistandardYoungTableau λ ν`: the semistandard tableaux of skew shape `ν / λ`.
* `TauCeti.SkewSemistandardYoungTableau.content`: how often each natural number occurs as an entry.
* `TauCeti.SkewSemistandardYoungTableau.rowReadingWord`: the entries of one row, right to left.
* `TauCeti.SkewSemistandardYoungTableau.readingWord`: the rows read from top to bottom, each from
  right to left.
* `TauCeti.SkewSemistandardYoungTableau.botEquiv`: the skew tableaux of shape `ν / ⊥` are the
  semistandard tableaux of shape `ν`.

## Main results

* `TauCeti.SkewSemistandardYoungTableau.sum_content`: the content of a tableau of shape `ν / λ`
  adds up to the number `|ν| - |λ|` of skew cells.
* `TauCeti.SkewSemistandardYoungTableau.count_readingWord`: the reading word has the content of the
  tableau.
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

/-- **The reading word has the content of the tableau**: it contains each letter `k` as often as
the tableau does. -/
@[simp]
theorem count_readingWord (T : SkewSemistandardYoungTableau inner outer) (k : ℕ) :
    T.readingWord.count k = T.content k := by
  have hsdiff : (outer.cells \ inner.cells).filter (fun c => T c.1 c.2 = k) =
      outer.cells.filter fun c => c ∉ inner ∧ T c.1 c.2 = k := by
    ext c
    simp [and_assoc]
  rw [content_apply, hsdiff, YoungDiagram.card_filter_cells outer _ le_rfl, readingWord_def,
    List.count_flatMap]
  simp only [Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range, Multiset.map_coe,
    Multiset.sum_coe]
  refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
  have hrow : (Finset.range (outer.rowLen i)).filter (fun j => (i, j) ∉ inner ∧ T i j = k) =
      (Finset.Ico (inner.rowLen i) (outer.rowLen i)).filter fun j => T i j = k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico,
      YoungDiagram.mem_iff_lt_rowLen, not_lt]
    tauto
  rw [Function.comp_apply, rowReadingWord_def, List.count_reverse, hrow, List.count,
    List.countP_map, List.countP_eq_length_filter, Nat.Ico_eq_range']
  simp [Finset.card, Finset.filter_val, Function.comp_def, beq_eq_decide]

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

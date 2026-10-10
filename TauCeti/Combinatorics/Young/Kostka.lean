/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Young.SemistandardTableau
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.Combinatorics.Enumerative.Partition.Conjugate
public import TauCeti.Combinatorics.Young.SemistandardTableau
public import TauCeti.Combinatorics.Young.StandardTableau.Basic

/-!
# Kostka numbers

The *content* of a semistandard Young tableau records how often each natural number is used as an
entry, and the *Kostka number* `K_{μ w}` counts the semistandard tableaux of shape `μ` and content
`w`.  This file defines both, proves that the tableaux of a given content are finite, and
establishes the two facts that make the Kostka numbers a triangular array for the dominance order:
the tableau of shape `μ` whose `i`-th row consists of `i`s is the only one of content
`μ.rowLen` (so `K_{μ μ} = 1`), and a tableau of shape `μ` and content `w` forces every partial sum
`∑_{i < k} w i` to be at most the corresponding partial sum of the row lengths of `μ` (so, for
partitions, `K_{μ ν} = 0` unless `μ` dominates `ν`).

The mechanism behind both is a single observation, `SemistandardYoungTableau.le_entry`: the
entries of a semistandard tableau strictly increase down each column, so the entry in row `i` is at
least `i`, and therefore the cells carrying an entry smaller than `k` all lie in the first `k`
rows.

The file also evaluates the opposite end of the array, the **all-ones content**
`fun i => if i < μ.card then 1 else 0` of the partition `(1ⁿ)`.  A semistandard tableau of that
content uses each of the labels `0, …, μ.card - 1` exactly once, hence increases strictly along its
rows as well as down its columns: it is a standard Young tableau, and conversely every standard
Young tableau is semistandard of that content.  So the last column of the Kostka matrix is the
count `f^μ` of standard Young tableaux, `TauCeti.kostkaNumber_ones`.

Mathlib's `SemistandardYoungTableau` fills the cells with natural numbers starting at `0`, so the
alphabet here is `0, 1, 2, …` rather than the classical `1, 2, 3, …` and the content of the
highest-weight tableau `SemistandardYoungTableau.highestWeight μ` is `μ.rowLen` on the nose.

## Main definitions

* `SemistandardYoungTableau.content`: the content (or weight) of a semistandard Young
  tableau, `content T i` being the number of cells filled with `i`.
* `TauCeti.BoundedSSYT`: the semistandard Young tableaux of a given shape whose entries lie below
  a given bound, that is, those written in a finite alphabet.
* `TauCeti.diagramKostkaNumber`: the number of semistandard Young tableaux of a given shape and
  content.
* `TauCeti.kostkaNumber`: the Kostka number of two partitions of the same natural number, the
  shape and the content being read off their Young diagrams.
* `TauCeti.StandardYoungTableau.toSemistandard` and `TauCeti.StandardYoungTableau.ofSemistandard`:
  the two passages between standard Young tableaux and the semistandard tableaux of the all-ones
  content, packaged as `TauCeti.StandardYoungTableau.equivContentOnes`.

## Main results

* `SemistandardYoungTableau.sum_content_le_sum_take_rowLens`: the partial sums of the
  content of a tableau of shape `μ` are bounded by those of the row lengths of `μ`.
* `SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen`: a tableau of shape `μ`
  and content `μ.rowLen` is the highest-weight tableau.
* `SemistandardYoungTableau.finite_content_eq`: the tableaux of a fixed shape and content
  are finite, so the Kostka number counts them faithfully.
* `TauCeti.finite_boundedSSYT`: likewise the tableaux of a fixed shape written in a finite alphabet,
  `TauCeti.BoundedSSYT`, are finite.
* `TauCeti.BoundedSSYT.isEmpty_of_lt_colLen`: a shape taller than its alphabet admits no tableau.
* `TauCeti.kostkaNumber_self`: `K_{μ μ} = 1`.
* `TauCeti.kostkaNumber_eq_zero_of_not_dominates`: `K_{μ ν} = 0` unless `μ` dominates `ν`.
* `SemistandardYoungTableau.lt_card_of_content_eq_ones` and
  `SemistandardYoungTableau.eq_of_entry_eq_of_content_eq_ones`: a tableau of the all-ones content
  uses only the labels `0, …, μ.card - 1`, and uses none of them twice.
* `TauCeti.StandardYoungTableau.content_toSemistandard`: a standard Young tableau has the all-ones
  content.
* `TauCeti.diagramKostkaNumber_ones` and `TauCeti.kostkaNumber_ones`: `K_{μ (1ⁿ)} = f^μ`, the
  Kostka number at the all-ones content counts standard Young tableaux.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 2.2.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 1.
-/

public section

namespace SemistandardYoungTableau

variable {μ : YoungDiagram}

/-- The content, or weight, of a semistandard Young tableau: the multiset of its entries, read as
a finitely supported multiplicity function, so `content T i` is the number of cells of the shape
whose entry is `i`. -/
noncomputable def content (T : _root_.SemistandardYoungTableau μ) : ℕ →₀ ℕ :=
  (μ.cells.val.map fun c => T c.1 c.2).toFinsupp

/-- The content of a tableau counts the cells of its shape carrying a given entry. -/
theorem content_apply (T : _root_.SemistandardYoungTableau μ) (i : ℕ) :
    content T i = (μ.cells.filter fun c => T c.1 c.2 = i).card := by
  rw [content, Multiset.toFinsupp_apply, Multiset.count_map]
  simp [Finset.card, Finset.filter_val, eq_comm]

/-- The support of the content of a tableau is the set of entries it uses. -/
@[simp]
theorem support_content (T : _root_.SemistandardYoungTableau μ) :
    (content T).support = μ.cells.image fun c => T c.1 c.2 := by
  rw [content, Multiset.toFinsupp_support, Multiset.toFinset_map, Finset.val_toFinset]

/-- The entries of a semistandard Young tableau increase strictly down a column, so the entry in
row `i` is at least `i`. -/
theorem le_entry (T : _root_.SemistandardYoungTableau μ) {i j : ℕ} (h : (i, j) ∈ μ) :
    i ≤ T i j := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    have hm : (m, j) ∈ μ := μ.up_left_mem (Nat.le_succ m) le_rfl h
    exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih hm) (T.col_strict (Nat.lt_succ_self m) h))

/-- The cells carrying an entry smaller than `k` all lie in the first `k` rows. -/
theorem filter_entry_lt_subset_filter_fst_lt (T : _root_.SemistandardYoungTableau μ) (k : ℕ) :
    (μ.cells.filter fun c => T c.1 c.2 < k) ⊆ μ.cells.filter fun c => c.1 < k := by
  intro c hc
  rw [Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, lt_of_le_of_lt (le_entry T (by simpa using hc.1)) hc.2⟩

/-- The first `k` values of the content of a tableau count the cells carrying an entry smaller
than `k`. -/
theorem sum_content_eq_card_filter (T : _root_.SemistandardYoungTableau μ) (k : ℕ) :
    ∑ i ∈ Finset.range k, content T i = (μ.cells.filter fun c => T c.1 c.2 < k).card := by
  symm
  calc
    (μ.cells.filter fun c => T c.1 c.2 < k).card =
        ∑ i ∈ Finset.range k,
          ((μ.cells.filter fun c => T c.1 c.2 < k).filter fun c => T c.1 c.2 = i).card := by
      refine Finset.card_eq_sum_card_fiberwise fun c hc => ?_
      simp only [Finset.mem_coe, Finset.mem_filter] at hc
      exact Finset.mem_range.mpr hc.2
    _ = ∑ i ∈ Finset.range k, content T i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hik : i < k := Finset.mem_range.mp hi
      rw [content_apply]
      refine congrArg Finset.card (Finset.ext fun c => ?_)
      simp only [Finset.mem_filter, and_assoc]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.2 ▸ hik, h.2⟩⟩

/-- The content of a tableau of shape `μ` is a composition of the number of cells of `μ`, once the
range of summation covers all the entries. -/
theorem sum_content_eq_card {T : _root_.SemistandardYoungTableau μ} {N : ℕ}
    (hN : ∀ c ∈ μ.cells, T c.1 c.2 < N) :
    ∑ i ∈ Finset.range N, content T i = μ.card := by
  rw [sum_content_eq_card_filter, Finset.filter_true_of_mem hN]

/-- **Dominance bound for the content of a tableau**: the partial sums of the content of a
semistandard tableau of shape `μ` never exceed the partial sums of the row lengths of `μ`. -/
theorem sum_content_le_sum_take_rowLens (T : _root_.SemistandardYoungTableau μ) (k : ℕ) :
    ∑ i ∈ Finset.range k, content T i ≤ (μ.rowLens.take k).sum := by
  rw [sum_content_eq_card_filter, YoungDiagram.sum_take_rowLens_eq_card_filter_fst]
  exact Finset.card_le_card (filter_entry_lt_subset_filter_fst_lt T k)

/-- The highest-weight tableau, whose `i`-th row consists of `i`s, has content the row lengths of
its shape. -/
@[simp]
theorem content_highestWeight (μ : YoungDiagram) :
    ⇑(content (_root_.SemistandardYoungTableau.highestWeight μ)) = μ.rowLen := by
  funext i
  rw [content_apply, μ.rowLen_eq_card]
  refine congrArg Finset.card (Finset.ext fun c => ?_)
  simp only [_root_.YoungDiagram.mem_row_iff,
    _root_.SemistandardYoungTableau.highestWeight_apply]
  aesop

/-- **Uniqueness of the highest-weight tableau**: a semistandard tableau of shape `μ` whose content
is the row lengths of `μ` has an `i` in every cell of row `i`, so it is
`SemistandardYoungTableau.highestWeight μ`. -/
theorem eq_highestWeight_of_content_eq_rowLen {T : _root_.SemistandardYoungTableau μ}
    (h : ⇑(content T) = μ.rowLen) : T = _root_.SemistandardYoungTableau.highestWeight μ := by
  have key : ∀ i j : ℕ, (i, j) ∈ μ → T i j = i := by
    intro i j hij
    have hcards : (μ.cells.filter fun c => T c.1 c.2 < i + 1).card =
        (μ.cells.filter fun c => c.1 < i + 1).card := by
      rw [← sum_content_eq_card_filter, ← YoungDiagram.sum_range_rowLen_eq_card_filter_fst]
      exact Finset.sum_congr rfl fun k _ => congrFun h k
    have hsets := Finset.eq_of_subset_of_card_le
      (filter_entry_lt_subset_filter_fst_lt T (i + 1)) hcards.ge
    have hmem : ((i, j) : ℕ × ℕ) ∈ μ.cells.filter fun c => T c.1 c.2 < i + 1 := by
      rw [hsets, Finset.mem_filter]
      exact ⟨hij, Nat.lt_succ_self i⟩
    exact le_antisymm (Nat.lt_succ_iff.mp (Finset.mem_filter.mp hmem).2) (le_entry T hij)
  ext i j
  by_cases hij : (i, j) ∈ μ
  · rw [key i j hij, _root_.SemistandardYoungTableau.highestWeight_apply, ite_eq_left hij]
  · rw [T.zeros hij, _root_.SemistandardYoungTableau.highestWeight_apply, ite_eq_right hij]

/-- The semistandard tableaux of a fixed shape and content are finite. -/
instance finite_content_eq (μ : YoungDiagram) (w : ℕ → ℕ) :
    Finite {T : _root_.SemistandardYoungTableau μ // ⇑(content T) = w} := by
  by_cases hne : Nonempty {T : _root_.SemistandardYoungTableau μ // ⇑(content T) = w}
  swap
  · rw [not_nonempty_iff] at hne
    infer_instance
  obtain ⟨T₀, hT₀⟩ := hne.some
  have hmem : ∀ T : _root_.SemistandardYoungTableau μ, ⇑(content T) = w →
      ∀ c ∈ μ.cells, T c.1 c.2 ∈ μ.cells.image fun d => T₀ d.1 d.2 := by
    intro T hT c hc
    rw [← support_content T₀, DFunLike.coe_injective (hT₀.trans hT.symm), support_content T]
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  refine Finite.of_injective
    (fun (T : {T : _root_.SemistandardYoungTableau μ // ⇑(content T) = w}) (c : ↥μ.cells) =>
      (⟨T.1 (c : ℕ × ℕ).1 (c : ℕ × ℕ).2, hmem T.1 T.2 _ c.2⟩ :
        ↥(μ.cells.image fun d => T₀ d.1 d.2))) fun T T' hTT' => ?_
  refine Subtype.ext (_root_.SemistandardYoungTableau.ext fun i j => ?_)
  by_cases hij : (i, j) ∈ μ
  · exact congrArg Subtype.val (congrFun hTT' ⟨(i, j), hij⟩)
  · rw [T.1.zeros hij, T'.1.zeros hij]

/-! ### The all-ones content

A tableau whose content is `1` on each of `0, …, μ.card - 1` and `0` beyond uses each of those
labels exactly once.  The two statements below are the two halves of that reading: the entries stay
below `μ.card`, and no entry is repeated.
-/

/-- A semistandard tableau of the **all-ones content** uses only the labels `0, …, μ.card - 1`: a
larger entry would be used no times at all. -/
theorem lt_card_of_content_eq_ones {T : _root_.SemistandardYoungTableau μ}
    (hT : ⇑(content T) = fun i => if i < μ.card then 1 else 0) {i j : ℕ} (h : (i, j) ∈ μ) :
    T i j < μ.card := by
  by_contra hlt
  have hne : (μ.cells.filter fun c => T c.1 c.2 = T i j).card ≠ 0 :=
    Finset.card_ne_zero_of_mem (a := ((i, j) : ℕ × ℕ))
      (Finset.mem_filter.mpr ⟨(YoungDiagram.mem_cells _).mpr h, rfl⟩)
  rw [← content_apply, congrFun hT (T i j), ite_eq_right hlt] at hne
  exact hne rfl

/-- **A semistandard tableau of the all-ones content is injective on cells**: an entry used twice
would have content at least two. -/
theorem eq_of_entry_eq_of_content_eq_ones {T : _root_.SemistandardYoungTableau μ}
    (hT : ⇑(content T) = fun i => if i < μ.card then 1 else 0) {c c' : ℕ × ℕ} (hc : c ∈ μ)
    (hc' : c' ∈ μ) (h : T c.1 c.2 = T c'.1 c'.2) : c = c' := by
  by_contra hne
  have hone : (μ.cells.filter fun d => T d.1 d.2 = T c.1 c.2).card = 1 := by
    rw [← content_apply, congrFun hT (T c.1 c.2),
      ite_eq_left (lt_card_of_content_eq_ones hT hc)]
  have htwo : 1 < (μ.cells.filter fun d => T d.1 d.2 = T c.1 c.2).card :=
    Finset.one_lt_card.mpr ⟨c, Finset.mem_filter.mpr ⟨(YoungDiagram.mem_cells _).mpr hc, rfl⟩,
      c', Finset.mem_filter.mpr ⟨(YoungDiagram.mem_cells _).mpr hc', h.symm⟩, hne⟩
  omega

end SemistandardYoungTableau

namespace TauCeti

/-- The semistandard Young tableaux of shape `μ` written in the alphabet `{0, …, n - 1}`, that
is, those all of whose entries are smaller than `n`.  Mathlib's `SemistandardYoungTableau μ`
allows arbitrary natural-number entries and is infinite for a nonempty `μ`, so bounding the
alphabet is what makes the tableaux of a fixed shape finitely many. -/
abbrev BoundedSSYT (n : ℕ) (μ : YoungDiagram) : Type :=
  {T : _root_.SemistandardYoungTableau μ // ∀ i c : ℕ, (i, c) ∈ μ → T i c < n}

namespace BoundedSSYT

variable {n : ℕ} {μ : YoungDiagram}

/-- The entries of a tableau written in the alphabet `{0, …, n - 1}` all use letters of that
alphabet. -/
theorem entry_lt (T : BoundedSSYT n μ) {i c : ℕ} (h : (i, c) ∈ μ) : T.1 i c < n :=
  T.2 i c h

/-- **A shape taller than its alphabet admits no tableau**: entries increase strictly down a
column, so a column of more than `n` cells cannot be filled from an `n`-letter alphabet. -/
theorem isEmpty_of_lt_colLen (h : n < μ.colLen 0) : IsEmpty (BoundedSSYT n μ) := by
  refine ⟨fun T => absurd (entry_lt T (YoungDiagram.mem_iff_lt_colLen.mpr h)) (not_lt.mpr ?_)⟩
  exact SemistandardYoungTableau.le_entry T.1 (YoungDiagram.mem_iff_lt_colLen.mpr h)

/-- The empty shape has a unique tableau, the empty one. -/
instance (n : ℕ) : Unique (BoundedSSYT n (⊥ : YoungDiagram)) where
  default := ⟨_root_.SemistandardYoungTableau.highestWeight ⊥, fun _ _ hic => absurd hic (by simp)⟩
  uniq T := Subtype.ext <| _root_.SemistandardYoungTableau.ext fun _ _ => by
    rw [T.1.zeros (by simp), _root_.SemistandardYoungTableau.highestWeight_apply,
      ite_eq_right (by simp)]

end BoundedSSYT

/-- **Bounded semistandard tableaux of a fixed shape are finitely many**: such a tableau is
determined by its restriction to the finitely many cells of `μ`, where it takes one of `n` values.
Mathlib's `SemistandardYoungTableau μ` allows unbounded entries and is infinite for a nonempty
`μ`, so the bound is what makes the count finite.  No relation between `n` and the number of rows
of `μ` is needed: for a shape taller than `n` the type is empty, columns being strict. -/
instance finite_boundedSSYT (n : ℕ) (μ : YoungDiagram) : Finite (BoundedSSYT n μ) := by
  refine Finite.of_injective (β := μ.cells → Fin n)
    (fun T x => ⟨T.1 x.1.1 x.1.2, T.2 _ _ ((YoungDiagram.mem_cells _).mp x.2)⟩) ?_
  rintro ⟨T, hT⟩ ⟨T', hT'⟩ h
  refine Subtype.ext (_root_.SemistandardYoungTableau.ext fun i c => ?_)
  by_cases hc : (i, c) ∈ μ
  · exact congrArg Fin.val (congrFun h ⟨(i, c), (YoungDiagram.mem_cells _).mpr hc⟩)
  · rw [T.zeros hc, T'.zeros hc]

noncomputable instance (n : ℕ) (μ : YoungDiagram) : Fintype (BoundedSSYT n μ) := .ofFinite _

/-- The **Kostka number** `K_{μ w}` of a shape and a weight function: the number of semistandard
Young tableaux of shape `μ` whose content is `w`. -/
noncomputable def diagramKostkaNumber (μ : YoungDiagram) (w : ℕ → ℕ) : ℕ :=
  Nat.card {T : _root_.SemistandardYoungTableau μ // ⇑(SemistandardYoungTableau.content T) = w}

/-- The Kostka number of a shape and a weight function counts the semistandard tableaux of that
shape whose content is that weight. -/
theorem diagramKostkaNumber_def (μ : YoungDiagram) (w : ℕ → ℕ) :
    diagramKostkaNumber μ w =
      Nat.card
        {T : _root_.SemistandardYoungTableau μ // ⇑(SemistandardYoungTableau.content T) = w} :=
  (rfl)

/-- A Kostka number is nonzero exactly when a tableau of the prescribed shape and content
exists. -/
theorem diagramKostkaNumber_ne_zero_iff {μ : YoungDiagram} {w : ℕ → ℕ} :
    diagramKostkaNumber μ w ≠ 0 ↔
      ∃ T : _root_.SemistandardYoungTableau μ, ⇑(SemistandardYoungTableau.content T) = w := by
  rw [diagramKostkaNumber_def, Nat.card_ne_zero]
  exact ⟨fun h => h.1.elim fun T => ⟨T.1, T.2⟩, fun ⟨T, hT⟩ => ⟨⟨⟨T, hT⟩⟩, inferInstance⟩⟩

/-- **The diagonal Kostka number is `1`**: the highest-weight tableau is the only semistandard
tableau of shape `μ` whose content is the row lengths of `μ`. -/
@[simp]
theorem diagramKostkaNumber_rowLen (μ : YoungDiagram) : diagramKostkaNumber μ μ.rowLen = 1 := by
  rw [diagramKostkaNumber_def, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun T T' => Subtype.ext ?_⟩,
    ⟨⟨_root_.SemistandardYoungTableau.highestWeight μ,
      SemistandardYoungTableau.content_highestWeight μ⟩⟩⟩
  rw [SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen T.2,
    SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen T'.2]

/-- **Partial-sum bound for a nonzero Kostka number**: if `K_{μ w} ≠ 0` then every partial sum of
`w` is bounded by the corresponding partial sum of the row lengths of `μ`.  For partitions this
becomes the dominance statement `TauCeti.dominates_of_kostkaNumber_ne_zero`. -/
theorem sum_le_sum_take_rowLens_of_diagramKostkaNumber_ne_zero {μ : YoungDiagram} {w : ℕ → ℕ}
    (h : diagramKostkaNumber μ w ≠ 0) (k : ℕ) :
    ∑ i ∈ Finset.range k, w i ≤ (μ.rowLens.take k).sum := by
  obtain ⟨T, hT⟩ := diagramKostkaNumber_ne_zero_iff.mp h
  calc
    ∑ i ∈ Finset.range k, w i = ∑ i ∈ Finset.range k, SemistandardYoungTableau.content T i :=
      Finset.sum_congr rfl fun i _ => (congrFun hT i).symm
    _ ≤ (μ.rowLens.take k).sum := SemistandardYoungTableau.sum_content_le_sum_take_rowLens T k

/-- The **Kostka number** `K_{μ ν}` of two partitions of the same natural number: the number of
semistandard tableaux of the shape of `μ` whose content is the row lengths of the diagram of `ν`,
that is (by `TauCeti.rowLen_diagramOf`), the tableaux using the entry `i` exactly as often as the
`i`-th largest part of `ν` prescribes. -/
noncomputable def kostkaNumber {n : ℕ} (μ ν : n.Partition) : ℕ :=
  diagramKostkaNumber (diagramOf μ) (diagramOf ν).rowLen

/-- The Kostka number of two partitions is the Kostka number of the diagram of `μ` together with
the row lengths of the diagram of `ν`. -/
theorem kostkaNumber_def {n : ℕ} (μ ν : n.Partition) :
    kostkaNumber μ ν = diagramKostkaNumber (diagramOf μ) (diagramOf ν).rowLen := (rfl)

/-- A Kostka number of two partitions is nonzero exactly when a tableau of shape `μ` and content
`ν` exists. -/
theorem kostkaNumber_ne_zero_iff {n : ℕ} {μ ν : n.Partition} :
    kostkaNumber μ ν ≠ 0 ↔ ∃ T : _root_.SemistandardYoungTableau (diagramOf μ),
      ⇑(SemistandardYoungTableau.content T) = (diagramOf ν).rowLen := by
  rw [kostkaNumber_def, diagramKostkaNumber_ne_zero_iff]

/-- A partition contributes exactly one tableau to its own Kostka number. -/
@[simp]
theorem kostkaNumber_self {n : ℕ} (μ : n.Partition) : kostkaNumber μ μ = 1 :=
  (kostkaNumber_def μ μ).trans (diagramKostkaNumber_rowLen _)

/-- **The Kostka numbers are triangular for the dominance order**: `K_{μ ν} ≠ 0` forces `μ` to
dominate `ν`. -/
theorem dominates_of_kostkaNumber_ne_zero {n : ℕ} {μ ν : n.Partition}
    (h : kostkaNumber μ ν ≠ 0) : Dominates μ ν := by
  refine dominates_iff.mpr fun k => ?_
  rw [kostkaNumber_def] at h
  have hk := sum_le_sum_take_rowLens_of_diagramKostkaNumber_ne_zero h k
  rwa [YoungDiagram.sum_range_rowLen_eq_card_filter_fst,
    ← YoungDiagram.sum_take_rowLens_eq_card_filter_fst, rowLens_diagramOf,
    rowLens_diagramOf] at hk

/-- **The Kostka numbers vanish off the dominance order**: there is no semistandard tableau of
shape `μ` and content `ν` unless `μ` dominates `ν`. -/
theorem kostkaNumber_eq_zero_of_not_dominates {n : ℕ} {μ ν : n.Partition}
    (h : ¬ Dominates μ ν) : kostkaNumber μ ν = 0 :=
  not_not.mp fun h' => h (dominates_of_kostkaNumber_ne_zero h')

/-! ### The all-ones content: standard Young tableaux

A standard Young tableau of shape `μ` is a bijective labelling of the cells of `μ` by
`0, …, μ.card - 1` increasing strictly along rows and down columns.  Forgetting the bijectivity
makes it a semistandard tableau whose content is the **all-ones content**
`fun i => if i < μ.card then 1 else 0`: every label is used exactly once.  Conversely a
semistandard tableau of that content uses every label at most once, so its weakly increasing rows
increase strictly and it is standard.  The two passages are inverse, so the Kostka number at the
all-ones content is the number `f^μ` of standard Young tableaux.
-/

namespace StandardYoungTableau

variable {μ : YoungDiagram}

/-- **A standard Young tableau is semistandard**: its labels increase strictly along each row,
hence weakly, and strictly down each column.  Outside the diagram the entry is `0`, as Mathlib's
`SemistandardYoungTableau` requires. -/
def toSemistandard (S : StandardYoungTableau μ) : _root_.SemistandardYoungTableau μ where
  entry i j := if h : (i, j) ∈ μ then (S ⟨(i, j), h⟩ : ℕ) else 0
  row_weak' {_ _ _} h hcell := by
    rw [dite_eq_left (μ.up_left_mem le_rfl h.le hcell), dite_eq_left hcell]
    exact (S.row_strict h hcell).le
  col_strict' {_ _ _} h hcell := by
    rw [dite_eq_left (μ.up_left_mem h.le le_rfl hcell), dite_eq_left hcell]
    exact S.col_strict h hcell
  zeros' h := dite_eq_right h

/-- The entries of the semistandard tableau of a standard Young tableau are its labels. -/
@[simp]
theorem toSemistandard_apply (S : StandardYoungTableau μ) {i j : ℕ} (h : (i, j) ∈ μ) :
    S.toSemistandard i j = (S ⟨(i, j), h⟩ : ℕ) :=
  dite_eq_left h

/-- The entries of the semistandard tableau of a standard Young tableau, read at a cell.

Not a `simp` lemma: `TauCeti.StandardYoungTableau.toSemistandard_apply` already rewrites this
left-hand side, discharging its membership side condition from `c.2`. -/
theorem toSemistandard_apply_cell (S : StandardYoungTableau μ) (c : ↥μ.cells) :
    S.toSemistandard (c : ℕ × ℕ).1 (c : ℕ × ℕ).2 = (S c : ℕ) :=
  dite_eq_left c.2

/-- The labels of a standard Young tableau are smaller than the number of cells. -/
theorem toSemistandard_lt_card (S : StandardYoungTableau μ) {i j : ℕ} (h : (i, j) ∈ μ) :
    S.toSemistandard i j < μ.card := by
  rw [S.toSemistandard_apply h]
  exact (S ⟨(i, j), h⟩).isLt

/-- **Each label of a standard Young tableau occupies exactly one cell.** -/
theorem filter_toSemistandard_eq_singleton (S : StandardYoungTableau μ) {i : ℕ}
    (hi : i < μ.card) :
    (μ.cells.filter fun c => S.toSemistandard c.1 c.2 = i) =
      {((S.toTableau.symm ⟨i, hi⟩ : ↥μ.cells) : ℕ × ℕ)} := by
  refine Finset.ext fun c => ?_
  rw [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hc, hci⟩
    rw [S.toSemistandard_apply_cell ⟨c, hc⟩] at hci
    have hd : S.toTableau ⟨c, hc⟩ = ⟨i, hi⟩ := Fin.ext hci
    rw [← hd, Equiv.symm_apply_apply]
  · rintro rfl
    refine ⟨(S.toTableau.symm ⟨i, hi⟩).2, ?_⟩
    rw [S.toSemistandard_apply_cell (S.toTableau.symm ⟨i, hi⟩)]
    exact congrArg Fin.val (Equiv.apply_symm_apply S.toTableau ⟨i, hi⟩)

/-- **The content of a standard Young tableau is the all-ones content**: each of the labels
`0, …, μ.card - 1` is used exactly once, and no other entry occurs. -/
@[simp]
theorem content_toSemistandard (S : StandardYoungTableau μ) :
    ⇑(SemistandardYoungTableau.content S.toSemistandard) =
      fun i => if i < μ.card then 1 else 0 := by
  funext i
  rw [SemistandardYoungTableau.content_apply]
  rcases lt_or_ge i μ.card with hi | hi
  · rw [S.filter_toSemistandard_eq_singleton hi, Finset.card_singleton, ite_eq_left hi]
  · rw [Finset.filter_eq_empty_iff.mpr fun {c} hc =>
      ((S.toSemistandard_lt_card ((YoungDiagram.mem_cells _).mp hc)).trans_le hi).ne,
      Finset.card_empty, ite_eq_right (not_lt.mpr hi)]

/-- **A semistandard tableau of the all-ones content is standard**: it uses each of the labels
`0, …, μ.card - 1` exactly once, so it is a bijective labelling, and its rows then increase
strictly rather than weakly. -/
noncomputable def ofSemistandard {T : _root_.SemistandardYoungTableau μ}
    (hT : ⇑(SemistandardYoungTableau.content T) = fun i => if i < μ.card then 1 else 0) :
    StandardYoungTableau μ where
  toTableau := Equiv.ofBijective
    (fun c : ↥μ.cells => (⟨T (c : ℕ × ℕ).1 (c : ℕ × ℕ).2,
      SemistandardYoungTableau.lt_card_of_content_eq_ones hT
        ((YoungDiagram.mem_cells _).mp c.2)⟩ : Fin μ.card))
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun c c' hcc' => Subtype.ext
        (SemistandardYoungTableau.eq_of_entry_eq_of_content_eq_ones hT
          ((YoungDiagram.mem_cells _).mp c.2) ((YoungDiagram.mem_cells _).mp c'.2)
          (congrArg Fin.val hcc')),
        by rw [Fintype.card_coe, Fintype.card_fin]⟩)
  row_strict' {i j₁ j₂} h hcell := by
    have hlt : T i j₁ < T i j₂ := by
      refine lt_of_le_of_ne (T.row_weak h hcell) fun heq => absurd
        (SemistandardYoungTableau.eq_of_entry_eq_of_content_eq_ones hT
          (μ.up_left_mem le_rfl h.le hcell) hcell heq) ?_
      simp only [Prod.mk.injEq, true_and]
      exact h.ne
    -- The labels are `Fin μ.card`, whose order is that of the underlying entries.
    exact hlt
  col_strict' {_ _ _} h hcell := T.col_strict h hcell

/-- The labels of the standard tableau of a semistandard tableau of the all-ones content are the
entries of that semistandard tableau. -/
@[simp]
theorem ofSemistandard_apply_cell {T : _root_.SemistandardYoungTableau μ}
    (hT : ⇑(SemistandardYoungTableau.content T) = fun i => if i < μ.card then 1 else 0)
    (c : ↥μ.cells) :
    (ofSemistandard hT c : ℕ) = T (c : ℕ × ℕ).1 (c : ℕ × ℕ).2 :=
  (rfl)

/-- The semistandard tableau of the standard tableau of a semistandard tableau of the all-ones
content is the tableau itself. -/
@[simp]
theorem toSemistandard_ofSemistandard {T : _root_.SemistandardYoungTableau μ}
    (hT : ⇑(SemistandardYoungTableau.content T) = fun i => if i < μ.card then 1 else 0) :
    (ofSemistandard hT).toSemistandard = T := by
  refine _root_.SemistandardYoungTableau.ext fun i j => ?_
  by_cases h : ((i, j) : ℕ × ℕ) ∈ μ
  · rw [toSemistandard_apply _ h]
    exact ofSemistandard_apply_cell hT ⟨(i, j), h⟩
  · rw [(ofSemistandard hT).toSemistandard.zeros h, T.zeros h]

/-- The standard tableau of the semistandard tableau of a standard tableau is the tableau
itself. -/
@[simp]
theorem ofSemistandard_toSemistandard (S : StandardYoungTableau μ) :
    ofSemistandard (content_toSemistandard S) = S :=
  ext fun c => Fin.ext
    ((ofSemistandard_apply_cell (content_toSemistandard S) c).trans (S.toSemistandard_apply_cell c))

/-- **The standard Young tableaux of shape `μ` are the semistandard tableaux of the all-ones
content**: forgetting bijectivity is a bijection onto them. -/
noncomputable def equivContentOnes (μ : YoungDiagram) :
    StandardYoungTableau μ ≃ {T : _root_.SemistandardYoungTableau μ //
      ⇑(SemistandardYoungTableau.content T) = fun i => if i < μ.card then 1 else 0} where
  toFun S := ⟨S.toSemistandard, content_toSemistandard S⟩
  invFun T := ofSemistandard T.2
  left_inv S := ofSemistandard_toSemistandard S
  right_inv T := Subtype.ext (toSemistandard_ofSemistandard T.2)

end StandardYoungTableau

/-- **The Kostka number at the all-ones content is the number of standard Young tableaux**,
`K_{μ (1ⁿ)} = f^μ`: a semistandard tableau using each of the labels `0, …, μ.card - 1` exactly
once is a standard Young tableau. -/
theorem diagramKostkaNumber_ones (μ : YoungDiagram) :
    diagramKostkaNumber μ (fun i => if i < μ.card then 1 else 0) = standardCount μ := by
  rw [diagramKostkaNumber_def, Nat.card_congr (StandardYoungTableau.equivContentOnes μ).symm,
    standardCount_def, Nat.card_eq_fintype_card]

/-- **The last column of the Kostka matrix counts standard Young tableaux**,
`K_{μ (1ⁿ)} = f^μ`.  Together with `TauCeti.spechtMultiplicity_ones` this is Young's rule at the
all-ones partition, where `M^{(1ⁿ)}` is the regular representation of `Sₙ`. -/
theorem kostkaNumber_ones {n : ℕ} (μ : n.Partition) :
    kostkaNumber μ (Nat.Partition.ones n) = standardCount (diagramOf μ) := by
  rw [kostkaNumber_def, ← diagramKostkaNumber_ones (diagramOf μ)]
  exact congrArg _ (funext fun i => by rw [rowLen_diagramOf_ones, card_diagramOf])

end TauCeti

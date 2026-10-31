/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.RobinsonSchensted
public import TauCeti.Combinatorics.Young.SkewTableau

/-!
# Littlewood–Richardson tableaux

A **Littlewood–Richardson tableau** of shape `ν / λ` and content `μ` is a semistandard tableau of
skew shape `ν / λ` containing each letter `k` exactly `μ_k` times, whose reading word (the rows
from top to bottom, each from right to left) is a lattice word: every prefix contains the letter
`k` at least as often as `k + 1`. Their number is the **Littlewood–Richardson coefficient**
`c^ν_{λ μ} = Nat.card (LRTableau λ ν μ)`. The Littlewood–Richardson rule, which is not proved
here, identifies it with the multiplicity of the Schur polynomial `s_ν` in the product `s_λ s_μ`,
and so with the multiplicity of the irreducible polynomial representation of `GLₙ` of highest
weight `ν` in the tensor product of those of highest weights `λ` and `μ`.

This file defines the tableaux and proves the elementary facts about them that need no insertion
or rectification. The key observation is that the lattice condition bounds the entries
(`TauCeti.LRTableau.entry_le`): reading row `i` from the right, its first letter is the largest
entry of the row, and the rows above it contain only letters smaller than `i` by induction, so a
first letter `m > i` would be read before any `m - 1`. Consequently

* a Littlewood–Richardson tableau is determined by its entries in the alphabet
  `{0, …, ℓ(ν) - 1}`, so there are finitely many and the coefficient counts them faithfully;
* the sizes add up, `|ν| = |λ| + |μ|`, since the content of a skew tableau counts its cells;
* for the straight shape `ν / ⊥`, where the entries in row `i` are also at least `i`, the only
  Littlewood–Richardson tableau is the highest-weight tableau, so `c^ν_{∅ μ} = δ_{ν μ}`; and the
  empty content forces the empty skew shape, so `c^ν_{λ ∅} = δ_{ν λ}`. These are the identities
  `s_∅ s_μ = s_μ` and `s_λ s_∅ = s_λ` that the rule specializes to.

## Main definitions

* `TauCeti.LRTableau λ ν μ`: the Littlewood–Richardson tableaux of shape `ν / λ` and content `μ`.
* `TauCeti.LRTableau.highestWeight μ`: the highest-weight tableau, the Littlewood–Richardson
  tableau of straight shape `μ / ⊥` and content `μ`.

## Main results

* `TauCeti.LRTableau.entry_le`: the entries in row `i` are at most `i`.
* `TauCeti.LRTableau.card_eq`: a Littlewood–Richardson tableau of shape `ν / λ` and content `μ`
  forces `|ν| = |λ| + |μ|`.
* `TauCeti.natCard_lrTableau_bot_left`: `c^ν_{∅ μ}` is `1` if `ν = μ` and `0` otherwise.
* `TauCeti.natCard_lrTableau_bot_right`: `c^ν_{λ ∅}` is `1` if `ν = λ` and `0` otherwise.

## References

* W. Fulton, *Young Tableaux*, Cambridge University Press (1997), Section 5.2.
* R. P. Stanley, *Enumerative Combinatorics, Volume 2*, Cambridge University Press (1999),
  Appendix 1, Section A1.3.
-/

public section

namespace TauCeti

open SkewSemistandardYoungTableau

/-- A **Littlewood–Richardson tableau** of shape `outer / inner` and content `μ`: a semistandard
tableau of skew shape `outer / inner` containing each letter `k` exactly `μ.rowLen k` times, whose
reading word `TauCeti.SkewSemistandardYoungTableau.readingWord` (rows from the top, each from right
to left) is a lattice word. The Littlewood–Richardson coefficient `c^ν_{λ μ}` is
`Nat.card (LRTableau λ ν μ)`. -/
abbrev LRTableau (inner outer μ : YoungDiagram) : Type :=
  {T : SkewSemistandardYoungTableau inner outer //
    ⇑T.content = μ.rowLen ∧ T.readingWord.IsLatticeWord}

namespace LRTableau

variable {inner outer μ : YoungDiagram}

/-- **The entries in row `i` of a Littlewood–Richardson tableau are at most `i`.** Row `i` is read
from the right, so its first letter is its largest entry; the rows above contain only smaller
letters, so a first letter `m > i` would occur in the reading word before any `m - 1`. -/
theorem entry_le (T : LRTableau inner outer μ) (i j : ℕ) : T.1 i j ≤ i := by
  induction i using Nat.strong_induction_on generalizing j with
  | _ i ih =>
  by_cases hc : (i, j) ∈ outer.cells \ inner.cells
  swap
  · rw [T.1.zeros_of_notMem_sdiff hc]
    exact Nat.zero_le _
  rw [Finset.mem_sdiff, YoungDiagram.mem_cells, YoungDiagram.mem_cells,
    YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen, not_lt] at hc
  have hlt : inner.rowLen i < outer.rowLen i := by omega
  have hlast : (i, outer.rowLen i - 1) ∈ outer := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
  refine (T.1.row_weak_of_le (by omega)
    (YoungDiagram.mem_iff_lt_rowLen.not.mpr (by omega)) hlast).trans ?_
  -- The letters read before row `i` are all smaller than `i`.
  have hsmall : ∀ x ∈ (List.range i).flatMap T.1.rowReadingWord, x < i := by
    intro x hx
    obtain ⟨r, hr, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨j', -, -, rfl⟩ := T.1.mem_rowReadingWord.mp hx
    exact (ih r (List.mem_range.mp hr) j').trans_lt (List.mem_range.mp hr)
  by_contra hm
  rw [not_le] at hm
  have hpre := List.isLatticeWord_iff.mp T.2.2 _
    (T.1.flatMap_range_append_prefix_readingWord hlt) (T.1 i (outer.rowLen i - 1) - 1)
  -- In that prefix the first letter `m` of row `i` occurs once and `m - 1` not at all.
  rw [Nat.sub_add_cancel (by omega), List.count_append, List.count_append,
    List.count_singleton_self,
    List.count_eq_zero_of_not_mem fun h => (hsmall _ h).not_ge (by omega),
    List.count_eq_zero_of_not_mem fun h => (hsmall _ h).not_ge (by omega),
    List.count_eq_zero_of_not_mem (by simp; omega)] at hpre
  omega

/-- **The sizes of the shapes of a Littlewood–Richardson tableau add up**: a tableau of shape
`ν / λ` and content `μ` forces `|ν| = |λ| + |μ|`. -/
theorem card_eq (T : LRTableau inner outer μ) : outer.card = inner.card + μ.card := by
  have hle : inner.card ≤ outer.card :=
    Finset.card_le_card (YoungDiagram.cells_subset_iff.mpr T.1.le)
  have hsum : (T.1.content.sum fun _ m => m) = μ.card := by
    have hs : T.1.content.support ⊆ Finset.range (μ.colLen 0) := by
      intro k hk
      rw [Finsupp.mem_support_iff, T.2.1] at hk
      exact Finset.mem_range.mpr
        (not_le.mp fun h => hk (YoungDiagram.rowLen_eq_zero_of_colLen_le h))
    rw [Finsupp.sum_of_support_subset _ hs _ fun _ _ => rfl, T.2.1]
    exact (YoungDiagram.card_eq_sum_range_rowLen μ le_rfl).symm
  have := T.1.sum_content
  omega

/-- The highest-weight tableau, whose `i`-th row consists of `i`s, is a Littlewood–Richardson
tableau of straight shape `μ / ⊥` and content `μ`. -/
def highestWeight (μ : YoungDiagram) : LRTableau ⊥ μ μ :=
  ⟨(botEquiv μ).symm (SemistandardYoungTableau.highestWeight μ), by
    rw [← content_botEquiv, Equiv.apply_symm_apply,
      SemistandardYoungTableau.content_highestWeight], by
    refine List.isLatticeWord_of_pairwise_le ?_ fun i => ?_
    · -- Row `r` of the reading word consists of the letter `r`.
      have hrow : ∀ r, ∀ x ∈ ((botEquiv μ).symm
          (SemistandardYoungTableau.highestWeight μ)).rowReadingWord r, x = r := by
        intro r x hx
        obtain ⟨j, -, hj, rfl⟩ := mem_rowReadingWord _ |>.mp hx
        simp [hj]
      rw [readingWord_def, List.pairwise_flatMap]
      refine ⟨fun r _ => List.pairwise_of_forall_mem_list fun x hx y hy => ?_,
        (List.pairwise_lt_range).imp_of_mem fun {a b} _ _ hab x hx y hy => ?_⟩
      · rw [hrow r x hx, hrow r y hy]
      · rw [hrow a x hx, hrow b y hy]
        exact hab.le
    · rw [count_readingWord, count_readingWord, ← content_botEquiv, Equiv.apply_symm_apply,
        SemistandardYoungTableau.content_highestWeight]
      exact μ.rowLen_anti _ _ (Nat.le_succ i)⟩

/-- The entries of `TauCeti.LRTableau.highestWeight μ`: `i` on the cells of row `i` of `μ`, and
`0` off `μ`. -/
@[simp]
theorem highestWeight_apply (μ : YoungDiagram) (i j : ℕ) :
    (highestWeight μ).1 i j = if (i, j) ∈ μ then i else 0 := by
  simp [highestWeight]

/-- A Littlewood–Richardson tableau of straight shape `outer / ⊥` is the highest-weight tableau of
shape `outer`: its entries in row `i` are at least `i`, columns being strict, and at most `i`. -/
theorem botEquiv_eq_highestWeight (T : LRTableau ⊥ outer μ) :
    botEquiv outer T.1 = SemistandardYoungTableau.highestWeight outer := by
  ext i j
  rw [SemistandardYoungTableau.highestWeight_apply, botEquiv_apply]
  split_ifs with h
  · exact le_antisymm (T.entry_le i j)
      (by simpa using SemistandardYoungTableau.le_entry (botEquiv outer T.1) h)
  · exact T.1.zeros h

/-- **A Littlewood–Richardson tableau of straight shape has its shape as content**: there is one
of shape `outer / ⊥` and content `μ` only if `outer = μ`. -/
theorem outer_eq_content (T : LRTableau ⊥ outer μ) : outer = μ := by
  refine YoungDiagram.rowLen_injective ?_
  rw [← T.2.1, ← content_botEquiv, botEquiv_eq_highestWeight,
    SemistandardYoungTableau.content_highestWeight]

/-- The highest-weight tableau is the only Littlewood–Richardson tableau of straight shape
`μ / ⊥` and content `μ`. -/
instance (μ : YoungDiagram) : Unique (LRTableau ⊥ μ μ) where
  default := highestWeight μ
  uniq T := Subtype.ext <| (botEquiv μ).injective <| by
    rw [botEquiv_eq_highestWeight, ← botEquiv_eq_highestWeight (highestWeight μ)]

/-- **A Littlewood–Richardson tableau with empty content has an empty skew shape**: there is one of
shape `outer / inner` and content `⊥` only if `outer = inner`. -/
theorem outer_eq_inner (T : LRTableau inner outer ⊥) : outer = inner := by
  have hcard := T.card_eq
  simp only [YoungDiagram.card, YoungDiagram.cells_bot, Finset.card_empty, add_zero] at hcard
  have hsub := YoungDiagram.cells_subset_iff.mpr T.1.le
  refine le_antisymm (YoungDiagram.cells_subset_iff.mp ?_) T.1.le
  rw [Finset.eq_of_subset_of_card_le hsub hcard.le]

/-- The empty tableau is the only Littlewood–Richardson tableau of shape `μ / μ` and content
`⊥`. -/
instance (μ : YoungDiagram) : Unique (LRTableau μ μ ⊥) where
  default :=
    ⟨{ entry := fun _ _ => 0
       le := le_rfl
       row_weak' := fun _ _ _ => le_rfl
       col_strict' := fun hi h₁ h₂ => absurd (μ.up_left_mem hi.le le_rfl h₂) h₁
       zeros_inner' := fun _ => rfl
       zeros' := fun _ => rfl }, by
      ext k
      rw [content_apply, Finset.sdiff_self, Finset.filter_empty, Finset.card_empty,
        YoungDiagram.rowLen_bot], by
      rw [readingWord_def, List.flatMap_eq_nil_iff.mpr]
      · exact List.isLatticeWord_nil
      · intro i _
        simp [rowReadingWord_def]⟩
  uniq T := Subtype.ext <| SkewSemistandardYoungTableau.ext fun i j =>
    T.1.zeros_of_notMem_sdiff (by simp)

end LRTableau

/-- There are no Littlewood–Richardson tableaux of shape `outer / inner` unless
`inner ≤ outer`. -/
theorem isEmpty_lrTableau_of_not_le {inner outer μ : YoungDiagram} (h : ¬inner ≤ outer) :
    IsEmpty (LRTableau inner outer μ) :=
  ⟨fun T => h T.1.le⟩

/-- There are no Littlewood–Richardson tableaux of shape `outer / inner` and content `μ` unless
`|outer| = |inner| + |μ|`. -/
theorem isEmpty_lrTableau_of_card_ne {inner outer μ : YoungDiagram}
    (h : outer.card ≠ inner.card + μ.card) : IsEmpty (LRTableau inner outer μ) :=
  ⟨fun T => h T.card_eq⟩

/-- **There are finitely many Littlewood–Richardson tableaux of a given shape and content**: by
`TauCeti.LRTableau.entry_le`, such a tableau is a function on the cells of `outer` with values in
the alphabet `{0, …, ℓ(outer) - 1}`. -/
instance (inner outer μ : YoungDiagram) : Finite (LRTableau inner outer μ) := by
  refine Finite.of_injective (β := outer.cells → Fin (outer.colLen 0))
    (fun T c => ⟨T.1 c.1.1 c.1.2, (T.entry_le _ _).trans_lt
      (YoungDiagram.lt_colLen_zero_of_mem ((YoungDiagram.mem_cells _).mp c.2))⟩) ?_
  intro T T' h
  refine Subtype.ext (SkewSemistandardYoungTableau.ext fun i j => ?_)
  by_cases hc : (i, j) ∈ outer
  · exact congrArg Fin.val (congrFun h ⟨(i, j), (YoungDiagram.mem_cells _).mpr hc⟩)
  · rw [T.1.zeros hc, T'.1.zeros hc]

open scoped Classical in
/-- **The Littlewood–Richardson coefficient `c^ν_{∅ μ}`** is `1` if `ν = μ` and `0` otherwise, as
`s_∅ s_μ = s_μ` requires. -/
theorem natCard_lrTableau_bot_left (ν μ : YoungDiagram) :
    Nat.card (LRTableau ⊥ ν μ) = if ν = μ then 1 else 0 := by
  split_ifs with h
  · subst h
    exact Nat.card_unique
  · exact @Nat.card_of_isEmpty _ ⟨fun T => h T.outer_eq_content⟩

open scoped Classical in
/-- **The Littlewood–Richardson coefficient `c^ν_{λ ∅}`** is `1` if `ν = λ` and `0` otherwise, as
`s_λ s_∅ = s_λ` requires. -/
theorem natCard_lrTableau_bot_right (lam ν : YoungDiagram) :
    Nat.card (LRTableau lam ν ⊥) = if ν = lam then 1 else 0 := by
  split_ifs with h
  · subst h
    exact Nat.card_unique
  · exact @Nat.card_of_isEmpty _ ⟨fun T => h T.outer_eq_inner⟩

end TauCeti

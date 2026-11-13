/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.Basic
import TauCeti.GroupTheory.FreeGroup.Basic
import TauCeti.Algebra.Group.Bool
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Finite.List

/-!
# Partition tables and the cancellation family of a system of equations

Let `S` be a finite system of equations over the free group `F(A)`, the `i`-th equation written
as a word `r_{i1} ⋯ r_{il_i}` in the letters of `X^{±1} ∪ A^{±1}` (variables `X`, constants
`A`). Following Makanin, Kharlampovich and Myasnikov associate with `S` a finite family of
generalised equations describing its solutions. A *partition table* assigns to each occurrence
`r_{ij}` a reduced word `V_{ij}` over `Z^{±1} ∪ A^{±1}`, for an alphabet `Z` of new letters, such
that

1. `V_{i1} ⋯ V_{il_i} = 1` in the free group `F(Z ∪ A)`;
2. `|V_{ij}| ≤ l_i - 1`;
3. `V_{ij} = a` whenever `r_{ij} = a ∈ A^{±1}`.

It records how the words of a solution cancel when they are substituted into `S`. At most
`|S| = ∑ (l_i - 1) l_i` letters of `Z` occur in a table, so `Z` has `|S|` letters.

The generalised equation `Ω_T` of a table has one item for each letter of the word
`V = V_{11} ⋯ V_{m l_m}`. Any two distinct occurrences of a letter `z ∈ Z` in `V` are joined by a
pair of dual bases of length one, any two distinct occurrences of a variable `x` in `S` are joined
by a pair of dual bases spanning their words `V_{ij}` in `V`, and the letters of `A^{±1}` in `V`
are constant bases. The *word map* `P_x` of a variable is the word `h[α, β] ^ ε` of the items
spanned by `V_{ij}` at an occurrence `r_{ij} = x ^ ε`.

## Main definitions

* `TauCeti.GenEq.ofEntries`: the generalised equation of a list of entries `(r_{ij}, V_{ij})`,
  with its equations described by `TauCeti.GenEq.forall_mem_equations_ofEntries`.
* `TauCeti.GenEq.wordMap`: the word maps `P_x`.
* `TauCeti.GenEq.IsPartitionTable`: partition tables of a system of words.
* `TauCeti.GenEq.cancellationFamily`: the finite set of partition tables with `|S|` letters in
  `Z`.
* `TauCeti.GenEq.Solution.ofLetterWords`: the solution of `Ω_T` obtained by giving words to the
  letters of `Z`, the items carrying the words of their letters.

## Main results

* `TauCeti.GenEq.finite_setOf_isPartitionTable`, `TauCeti.GenEq.card_cancellationFamily_le`:
  there are finitely many partition tables, at most `(2 (|S| + |A|) + 1) ^ |S|` with `|S|`
  letters in `Z` (Lemma 13(1)).
* `TauCeti.GenEq.length_wordMap_le`: the word maps have length at most the number of items
  (Lemma 14(2)), which is at most `|S|` for a partition table
  (`TauCeti.GenEq.IsPartitionTable.numItems_ofEntries_le`).
* `TauCeti.GenEq.Solution.substituteVars_segment_entryStart_eq_wordMap`: in a solution of `Ω_T`,
  the value `P_x(U)` does not depend on the occurrence of `x` at which it is read, when the words
  of the entries of `x` are empty together.
* `TauCeti.GenEq.IsPartitionTable.eval_eq_one_of_mem_V`: if `v` is a solution of the system
  `Ω_T*` in a group over `F(A)`, then `x ↦ P_x(v)` is a solution of `S` there (Lemma 14(4)).
* `TauCeti.GenEq.IsPartitionTable.eval_substituteVars_eq_one`: a solution of `Ω_T` gives the
  solution `x ↦ P_x(U)` of `S` in `F(A)`.

## Implementation notes

Two points of the construction are made precise. The source puts constant bases only on the
words `V_{ij} = a` of constant occurrences; the letter `a⁻¹` cancelling such an occurrence lies
inside the word of a variable occurrence and must be a constant base as well for a solution of
`Ω_T` to give a solution of `S`. So every letter of `A^{±1}` in `V` is a constant base. A variable
sent to `1` has empty words `V_{ij}`, while a base spans at least one item: dual bases join
only occurrences with nonempty words, and a partition table requires the words of all
occurrences of one letter to be empty together. A variable that does not occur in the system
has the empty word map.

Bases are indexed by ordered pairs of distinct occurrences, the dual of `(i, j)` being `(j, i)`.
The generalised equation `ofEntries E` is reducible, so that its items are, up to reducible
unfolding, the positions `Fin (E.flatMap Prod.snd).length` of the concatenated word.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §4.2, Lemmas 13 and 14.
* O. Kharlampovich, A. Myasnikov, *Effective JSJ decompositions*, Contemp. Math. 378 (2005),
  §4.2, Lemmas 4.6 and 4.7.
* G. S. Makanin, *Equations in a free group*, Izv. Akad. Nauk SSSR Ser. Mat. 46 (1982).
-/

public section

namespace TauCeti

namespace GenEq

open GroupAlgGeom
open FreeGroup (substituteVars)

/-! ### The generalised equation of a list of entries -/

section Entries

variable {X Z A : Type*} (E : List (((X ⊕ A) × Bool) × List ((Z ⊕ A) × Bool)))

/-- The boundary at which the word of the `k`-th entry begins in the concatenation of the words
of all entries: the total length of the words of the earlier entries. -/
def entryStart (k : ℕ) : ℕ :=
  ((E.take k).flatMap Prod.snd).length

@[simp]
theorem entryStart_zero : entryStart E 0 = 0 := by
  simp [entryStart]

/-- The word of each entry starts within the concatenated word. -/
theorem entryStart_le (k : ℕ) : entryStart E k ≤ (E.flatMap Prod.snd).length := by
  have h := congrArg (fun l => (l.flatMap Prod.snd).length) (List.take_append_drop k E)
  simp only [List.flatMap_append, List.length_append] at h
  rw [entryStart]
  lia

/-- The word of the `k`-th entry ends where the word of the next entry starts. -/
theorem entryStart_succ {k : ℕ} (hk : k < E.length) :
    entryStart E (k + 1) = entryStart E k + E[k].2.length := by
  rw [entryStart, entryStart, List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.length_append]

/-- The word of the `k`-th entry occupies the positions from `entryStart k` to
`entryStart (k + 1)` of the concatenation of the words of all entries. -/
theorem drop_take_entryStart {k : ℕ} (hk : k < E.length) :
    ((E.flatMap Prod.snd).take (entryStart E (k + 1))).drop (entryStart E k) = E[k].2 := by
  have := List.drop_take_succ_flatten_eq_getElem (E.map Prod.snd) k (by simpa using hk)
  rw [List.getElem_map] at this
  simpa [entryStart, List.flatMap_def, List.length_flatten, List.map_take] using this

/-- Two distinct entries carrying the same variable, both with nonempty words. These ordered
pairs index the dual bases joining the occurrences of a variable. -/
def IsVarPair (p : Fin E.length × Fin E.length) : Prop :=
  p.1 ≠ p.2 ∧ E[p.1].1.1.isLeft ∧ E[p.1].1.1 = E[p.2].1.1 ∧ E[p.1].2 ≠ [] ∧ E[p.2].2 ≠ []

/-- The defining conditions of a pair of entries of a variable. -/
theorem isVarPair_iff {p : Fin E.length × Fin E.length} : IsVarPair E p ↔
    p.1 ≠ p.2 ∧ E[p.1].1.1.isLeft ∧ E[p.1].1.1 = E[p.2].1.1 ∧ E[p.1].2 ≠ [] ∧ E[p.2].2 ≠ [] :=
  Iff.rfl

instance [DecidableEq X] [DecidableEq A] : DecidablePred (IsVarPair E) :=
  fun _ => decidable_of_iff _ (isVarPair_iff E).symm

variable {E} in
/-- Pairs of entries of a variable are symmetric. -/
theorem IsVarPair.swap {p : Fin E.length × Fin E.length} (h : IsVarPair E p) :
    IsVarPair E p.swap := by
  obtain ⟨a, b⟩ := p
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨Ne.symm h₁, ?_, h₃.symm, h₅, h₄⟩
  dsimp only [Prod.swap_prod_mk] at h₂ h₃ ⊢
  rwa [← h₃]

/-- Two distinct positions of the concatenated word carrying the same letter of `Z`. These
ordered pairs index the dual bases joining the occurrences of a letter of `Z`. -/
def IsLetterPair (q : Fin (E.flatMap Prod.snd).length × Fin (E.flatMap Prod.snd).length) : Prop :=
  q.1 ≠ q.2 ∧ (E.flatMap Prod.snd)[q.1].1.isLeft ∧
    (E.flatMap Prod.snd)[q.1].1 = (E.flatMap Prod.snd)[q.2].1

/-- The defining conditions of a pair of positions carrying the same letter of `Z`. -/
theorem isLetterPair_iff {q : Fin (E.flatMap Prod.snd).length × Fin (E.flatMap Prod.snd).length} :
    IsLetterPair E q ↔ q.1 ≠ q.2 ∧ (E.flatMap Prod.snd)[q.1].1.isLeft ∧
      (E.flatMap Prod.snd)[q.1].1 = (E.flatMap Prod.snd)[q.2].1 :=
  Iff.rfl

instance [DecidableEq Z] [DecidableEq A] : DecidablePred (IsLetterPair E) :=
  fun _ => decidable_of_iff _ (isLetterPair_iff E).symm

variable {E} in
/-- Pairs of positions carrying the same letter of `Z` are symmetric. -/
theorem IsLetterPair.swap {q : Fin (E.flatMap Prod.snd).length × Fin (E.flatMap Prod.snd).length}
    (h : IsLetterPair E q) : IsLetterPair E q.swap := by
  obtain ⟨a, b⟩ := q
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨Ne.symm h₁, ?_, h₃.symm⟩
  dsimp only [Prod.swap_prod_mk] at h₂ h₃ ⊢
  rwa [← h₃]

/-- The generalised equation `Ω_T` of a list of entries `(r, V_r)`: an occurrence `r` of a letter
of `X^{±1} ∪ A^{±1}` together with a word `V_r` over `Z^{±1} ∪ A^{±1}`. Its items are the letters
of the concatenation `V` of the words `V_r`. Any two distinct entries of the same variable with
nonempty words are joined by a pair of dual bases spanning their words, with the signs of the
occurrences; any two distinct positions of `V` carrying the same letter of `Z` are joined by a
pair of dual bases of length one, with the signs of the letters; and every position of `V`
carrying a letter of `A^{±1}` is a constant base with that letter. -/
@[reducible] noncomputable def ofEntries : GenEq A :=
  ofBases (β := {p // IsVarPair E p} ⊕ {q // IsLetterPair E q}) (E.flatMap Prod.snd).length
    (Sum.elim (fun p => ⟨entryStart E p.1.1, Nat.lt_succ_of_le (entryStart_le E _)⟩)
      fun q => q.1.1.castSucc)
    (Sum.elim (fun p => ⟨entryStart E ((p.1.1 : ℕ) + 1), Nat.lt_succ_of_le (entryStart_le E _)⟩)
      fun q => q.1.1.succ)
    (by
      rintro (⟨p, hp⟩ | ⟨q, -⟩)
      · have := List.length_pos_iff.2 hp.2.2.2.1
        simp only [Sum.elim_inl, Fin.mk_lt_mk, entryStart_succ E p.1.isLt,
          Fin.getElem_fin] at this ⊢
        lia
      · exact Fin.castSucc_lt_succ)
    (Sum.elim (fun p => E[p.1.1].1.2) fun q => (E.flatMap Prod.snd)[q.1.1].2)
    (Sum.map (fun p => ⟨p.1.swap, p.2.swap⟩) fun q => ⟨q.1.swap, q.2.swap⟩)
    (by rintro (_ | _) <;> rfl)
    (Finset.univ.filterMap
      (fun c : Fin (E.flatMap Prod.snd).length => ((E.flatMap Prod.snd)[c].1.getRight?).map
        fun a => (c, (a, (E.flatMap Prod.snd)[c].2)))
      (by
        intro c c' b hb hb'
        simp only [Option.mem_def, Option.map_eq_some_iff] at hb hb'
        obtain ⟨a, -, rfl⟩ := hb
        obtain ⟨a', -, h⟩ := hb'
        exact (congrArg Prod.fst h).symm))

/-- The items of `ofEntries E` are the positions of the concatenated word. -/
theorem numItems_ofEntries : (ofEntries E).numItems = (E.flatMap Prod.snd).length :=
  (rfl)

/-- The letter of the concatenated word at the position of an item of `ofEntries E`. -/
def itemLetter (c : Fin (ofEntries E).numItems) : (Z ⊕ A) × Bool :=
  (E.flatMap Prod.snd)[(c : ℕ)]'c.isLt

/-- The letter of an item is the letter of the concatenated word at its position. -/
theorem itemLetter_def (c : Fin (ofEntries E).numItems) :
    itemLetter E c = (E.flatMap Prod.snd)[(c : ℕ)]'(c.isLt.trans_eq (numItems_ofEntries E)) :=
  (rfl)

/-- Reading the letters of all items in order gives the concatenated word. -/
theorem map_itemLetter_finRange :
    (List.finRange (ofEntries E).numItems).map (itemLetter E) = E.flatMap Prod.snd := by
  apply List.ext_getElem <;> simp [itemLetter_def]

/-- The items spanned by the word of an entry are as many as the letters of that word. -/
theorem length_segment_entryStart {k : ℕ} (hk : k < E.length) (s : Bool) :
    ((ofEntries E).segment (entryStart E k) (entryStart E (k + 1)) s).length = E[k].2.length := by
  rw [length_segment, min_eq_left (entryStart_le E _), entryStart_succ E hk]
  lia

/-- The constant bases of `ofEntries E` are the items carrying a letter of `A^{±1}`, with that
letter. -/
theorem mem_constBases_ofEntries {c : Fin (ofEntries E).numItems} {a : A} {s : Bool} :
    (c, (a, s)) ∈ (ofEntries E).constBases ↔ itemLetter E c = (Sum.inr a, s) := by
  rw [Finset.mem_filterMap]
  simp only [Finset.mem_univ, true_and, Option.map_eq_some_iff, Sum.getRight?_eq_some_iff,
    Prod.mk.injEq]
  constructor
  · rintro ⟨c', a', h, rfl, rfl, rfl⟩
    exact Prod.ext h rfl
  · intro h
    refine ⟨c, a, ?_, rfl, rfl, ?_⟩
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h

/-- Two distinct entries of the same variable with nonempty words give the basic equation
`h[α, β] ^ ε = h[α', β'] ^ ε'` between the items spanned by their words, with the signs of the
occurrences. -/
theorem mem_equations_ofEntries_of_isVarPair {p : Fin E.length × Fin E.length}
    (hp : IsVarPair E p) :
    ((ofEntries E).segment (entryStart E p.1) (entryStart E ((p.1 : ℕ) + 1)) E[p.1].1.2,
      (ofEntries E).segment (entryStart E p.2) (entryStart E ((p.2 : ℕ) + 1)) E[p.2].1.2) ∈
      (ofEntries E).equations :=
  (mem_equations_ofBases_iff ..).2 (Or.inl ⟨Sum.inl ⟨p, hp⟩, rfl⟩)

/-- Two distinct items carrying the same letter `z` of `Z`, with signs `s` and `s'`, give the
basic equation `h_c ^ s = h_{c'} ^ s'`. -/
theorem mem_equations_ofEntries_of_itemLetter {c c' : Fin (ofEntries E).numItems} (h : c ≠ c')
    {z : Z} {s s' : Bool} (hc : itemLetter E c = (Sum.inl z, s))
    (hc' : itemLetter E c' = (Sum.inl z, s')) :
    ([(Sum.inl c, s)], [(Sum.inl c', s')]) ∈ (ofEntries E).equations := by
  rw [itemLetter_def] at hc hc'
  have hq : IsLetterPair E (c, c') := ⟨h, by simp [hc], by simp [hc, hc']⟩
  have : _ ∈ (ofEntries E).equations :=
    (mem_equations_ofBases_iff ..).2 (Or.inl ⟨Sum.inr ⟨(c, c'), hq⟩, rfl⟩)
  simp only [Sum.elim_inr, Sum.map_inr, Fin.val_castSucc, Fin.val_succ, Prod.fst_swap,
    Fin.getElem_fin, hc, hc'] at this
  rwa [segment_succ, segment_succ] at this

/-- The equations of `ofEntries E`: the basic equations of the pairs of distinct entries of a
variable with nonempty words and of the pairs of distinct items carrying the same letter of `Z`,
and the coefficient equations of the items carrying a letter of `A^{±1}`. -/
theorem forall_mem_equations_ofEntries {P : List ((Fin (ofEntries E).numItems ⊕ A) × Bool) ×
      List ((Fin (ofEntries E).numItems ⊕ A) × Bool) → Prop} :
    (∀ e ∈ (ofEntries E).equations, P e) ↔
      (∀ p, IsVarPair E p →
        P ((ofEntries E).segment (entryStart E p.1) (entryStart E ((p.1 : ℕ) + 1)) E[p.1].1.2,
          (ofEntries E).segment (entryStart E p.2) (entryStart E ((p.2 : ℕ) + 1)) E[p.2].1.2)) ∧
      (∀ c c', c ≠ c' → ∀ (z : Z) (s s' : Bool), itemLetter E c = (Sum.inl z, s) →
        itemLetter E c' = (Sum.inl z, s') → P ([(Sum.inl c, s)], [(Sum.inl c', s')])) ∧
      ∀ c (a : A) (s : Bool), itemLetter E c = (Sum.inr a, s) →
        P ([(Sum.inl c, true)], [(Sum.inr a, s)]) := by
  refine ⟨fun h => ⟨fun p hp => h _ (mem_equations_ofEntries_of_isVarPair E hp),
    fun c c' hcc z s s' hc hc' => h _ (mem_equations_ofEntries_of_itemLetter E hcc hc hc'),
    fun c a s hc => h _ (by
      have := (ofEntries E).coeffEquation_mem_equations ((mem_constBases_ofEntries E).2 hc)
      rwa [show (ofEntries E).coeffEquation (c, a, s) = ([(Sum.inl c, true)], [(Sum.inr a, s)])
        from Prod.ext (coeffEquation_fst _ _) (coeffEquation_snd _ _)] at this)⟩, ?_⟩
  rintro ⟨h₁, h₂, h₃⟩ e he
  rcases (mem_equations_ofBases_iff ..).1 he with ⟨⟨p, hp⟩ | ⟨q, hq⟩, rfl⟩ | ⟨⟨c, a, s⟩, hc, rfl⟩
  · exact h₁ p hp
  · obtain ⟨hne, hl, heq⟩ := hq
    obtain ⟨z, hz⟩ := Sum.isLeft_iff.1 hl
    simp only [Sum.elim_inr, Sum.map_inr, Fin.val_castSucc, Fin.val_succ, Prod.fst_swap]
    rw [segment_succ, segment_succ]
    exact h₂ q.1 q.2 hne z _ _ (Prod.ext hz rfl) (Prod.ext (heq.symm.trans hz) rfl)
  · convert h₃ c a s ((mem_constBases_ofEntries E).1 hc) using 1
    exact Prod.ext (coeffEquation_fst _ _) (coeffEquation_snd _ _)

open Classical in
/-- The word map `P_x`: the word `h[α, β] ^ ε` of the items spanned by the word of the first
entry carrying the variable `x`, with the sign `ε` of that occurrence; the empty word if `x` does
not occur. -/
noncomputable def wordMap (x : X) : List ((Fin (ofEntries E).numItems ⊕ A) × Bool) :=
  match (List.finRange E.length).find? fun k => E[k].1.1 = Sum.inl x with
  | some k => (ofEntries E).segment (entryStart E k) (entryStart E ((k : ℕ) + 1)) E[k].1.2
  | none => []

/-- The word map of a variable is read at the first entry carrying that variable. -/
theorem wordMap_eq {x : X} (k : Fin E.length) (hk : E[k].1.1 = Sum.inl x)
    (hlt : ∀ k' : Fin E.length, k' < k → E[k'].1.1 ≠ Sum.inl x) :
    wordMap E x = (ofEntries E).segment (entryStart E k) (entryStart E ((k : ℕ) + 1)) E[k].1.2 := by
  classical
  have h : ((List.finRange E.length).find? fun k => E[k].1.1 = Sum.inl x) = some k := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simpa using hk, k, by simp, by simp, fun j hj => ?_⟩
    have hj' : j < E.length := hj.trans k.isLt
    simpa using hlt ⟨j, hj'⟩ hj
  unfold wordMap
  rw [h]

/-- The word map of a variable is read at an entry carrying that variable. -/
theorem exists_wordMap_eq {x : X} (k : Fin E.length) (hk : E[k].1.1 = Sum.inl x) :
    ∃ k₀ : Fin E.length, E[k₀].1.1 = Sum.inl x ∧ wordMap E x =
      (ofEntries E).segment (entryStart E k₀) (entryStart E ((k₀ : ℕ) + 1)) E[k₀].1.2 := by
  classical
  unfold wordMap
  cases h : (List.finRange E.length).find? fun k => E[k].1.1 = Sum.inl x with
  | none =>
    rw [List.find?_eq_none] at h
    exact absurd hk (by simpa using h k (List.mem_finRange k))
  | some k₀ => exact ⟨k₀, by simpa using List.find?_some h, rfl⟩

/-- The word map of a variable that does not occur is empty. -/
theorem wordMap_eq_nil {x : X} (h : ∀ k : Fin E.length, E[k].1.1 ≠ Sum.inl x) :
    wordMap E x = [] := by
  unfold wordMap
  rw [List.find?_eq_none.2 (by simpa using h)]

/-- **Kharlampovich–Myasnikov, Lemma 14(2).** The word map of a variable has length at most the
number of items. -/
theorem length_wordMap_le (x : X) : (wordMap E x).length ≤ (ofEntries E).numItems := by
  unfold wordMap
  split
  · rw [length_segment]
    lia
  · exact Nat.zero_le _

variable {E} in
/-- In a solution of `ofEntries E`, the items spanned by the word of an entry of a variable `x`
spell the same word as the word map of `x`, letter by letter, when the words of the entries of `x`
are empty together: the value of `x` does not depend on the occurrence at which it is read. -/
theorem Solution.substituteVars_segment_entryStart_eq_wordMap (U : (ofEntries E).Solution)
    {x : X} (he : ∀ e ∈ E, ∀ e' ∈ E, e.1.1 = Sum.inl x → e'.1.1 = Sum.inl x →
      (e.2 = [] ↔ e'.2 = []))
    {k : Fin E.length} (hk : E[k].1.1 = Sum.inl x) :
    substituteVars U.word
        ((ofEntries E).segment (entryStart E k) (entryStart E ((k : ℕ) + 1)) E[k].1.2) =
      substituteVars U.word (wordMap E x) := by
  obtain ⟨k₀, hk₀, hw⟩ := exists_wordMap_eq E k hk
  have hiff := he _ (List.getElem_mem k.isLt) _ (List.getElem_mem k₀.isLt) hk hk₀
  have hnil (k' : Fin E.length) (h : E[k'].2 = []) :
      (ofEntries E).segment (entryStart E k') (entryStart E ((k' : ℕ) + 1)) E[k'].1.2 = [] :=
    List.eq_nil_of_length_eq_zero <| (length_segment_entryStart E k'.isLt _).trans <|
      List.length_eq_zero_iff.2 h
  rw [hw]
  by_cases h : k = k₀
  · rw [h]
  by_cases hne : E[k].2 = []
  · rw [hnil k hne, hnil k₀ (hiff.1 hne)]
  · exact U.subst_eq _ (mem_equations_ofEntries_of_isVarPair E (p := (k, k₀))
      ((isVarPair_iff E).2 ⟨h, by rw [hk]; rfl, hk.trans hk₀.symm, hne, mt hiff.2 hne⟩))

end Entries

/-! ### Solutions of `Ω_T` give solutions of the system -/

section Soundness

variable {X Z A H : Type*} [Group H]

variable {E : List (((X ⊕ A) × Bool) × List ((Z ⊕ A) × Bool))} {ι : FreeGroup A →* H}
  {v : Fin (ofEntries E).numItems → H}

/-- A point of `Ω_T*` determines values of the letters of `Z` under which every letter of the
concatenated word evaluates to its item: the letters of `Z` by the basic equations of length one,
the letters of `A^{±1}` by the coefficient equations. -/
private theorem exists_lift_mk_itemLetter (hv : v ∈ V ι (ofEntries E).toSystem) :
    ∃ ζ : Z → H, ∀ c, FreeGroup.lift (Sum.elim ζ (ι ∘ FreeGroup.of))
      (FreeGroup.mk [itemLetter E c]) = v c := by
  classical
  have hv' := (mem_V_toSystem_iff _).1 hv
  refine ⟨fun z => if h : ∃ c, (itemLetter E c).1 = Sum.inl z then
    cond (itemLetter E h.choose).2 (v h.choose) (v h.choose)⁻¹ else 1, fun c => ?_⟩
  rw [FreeGroup.lift_mk_singleton]
  obtain ⟨⟨y, s⟩, hy⟩ : ∃ y, itemLetter E c = y := ⟨_, rfl⟩
  rw [hy]
  rcases y with z | a
  · have h : ∃ c', (itemLetter E c').1 = Sum.inl z := ⟨c, by rw [hy]⟩
    obtain ⟨s₀, hs₀⟩ : ∃ s₀, itemLetter E h.choose = (Sum.inl z, s₀) :=
      ⟨_, Prod.ext h.choose_spec rfl⟩
    have hval : cond (itemLetter E h.choose).2 (v h.choose) (v h.choose)⁻¹ =
        cond s (v c) (v c)⁻¹ := by
      by_cases hc : h.choose = c
      · rw [hc, hy]
      · have := hv' _ (mem_equations_ofEntries_of_itemLetter E hc hs₀ hy)
        simpa [FreeGroup.lift_mk_singleton, hs₀] using this
    simp only [Sum.elim_inl, dite_eq_left h, hval, Bool.cond_cond_inv]
  · have := hv' _ ((ofEntries E).coeffEquation_mem_equations ((mem_constBases_ofEntries E).2 hy))
    simp only [coeffEquation_fst, coeffEquation_snd, FreeGroup.lift_mk_singleton, Sum.elim_inl,
      Sum.elim_inr, Function.comp_apply, Bool.cond_true] at this
    simp [this]

/-- Evaluating `h[i, j]` at the point is evaluating the corresponding subword of the concatenated
word at the values of the letters. -/
private theorem lift_mk_segment_true {ζ : Z → H}
    (hζ : ∀ c, FreeGroup.lift (Sum.elim ζ (ι ∘ FreeGroup.of)) (FreeGroup.mk [itemLetter E c]) =
      v c) (i j : ℕ) :
    FreeGroup.lift (Sum.elim v (ι ∘ FreeGroup.of)) (FreeGroup.mk ((ofEntries E).segment i j true)) =
      FreeGroup.lift (Sum.elim ζ (ι ∘ FreeGroup.of))
        (FreeGroup.mk (((E.flatMap Prod.snd).take j).drop i)) := by
  rw [segment_true, ← map_itemLetter_finRange E, ← List.map_take, ← List.map_drop,
    FreeGroup.lift_mk, FreeGroup.lift_mk, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  simp [← hζ c]

/-- Two entries of the same variable with nonempty words have the same value at a point of
`Ω_T*`. -/
private theorem lift_mk_segment_eq (hv : v ∈ V ι (ofEntries E).toSystem) {k k' : Fin E.length}
    (hk : E[k].1.1.isLeft) (heq : E[k].1.1 = E[k'].1.1) (hne : E[k].2 ≠ []) (hne' : E[k'].2 ≠ []) :
    FreeGroup.lift (Sum.elim v (ι ∘ FreeGroup.of)) (FreeGroup.mk
        ((ofEntries E).segment (entryStart E k) (entryStart E ((k : ℕ) + 1)) E[k].1.2)) =
      FreeGroup.lift (Sum.elim v (ι ∘ FreeGroup.of)) (FreeGroup.mk
        ((ofEntries E).segment (entryStart E k') (entryStart E ((k' : ℕ) + 1)) E[k'].1.2)) := by
  by_cases h : k = k'
  · rw [h]
  · exact (mem_V_toSystem_iff _).1 hv _
      (mem_equations_ofEntries_of_isVarPair E (p := (k, k')) ⟨h, hk, heq, hne, hne'⟩)

/-- Under the word maps, each entry evaluates to the value of its word. -/
private theorem lift_mk_entry
    (hc : ∀ e ∈ E, ∀ a : A, e.1.1 = Sum.inr a → e.2 = [(Sum.inr a, e.1.2)])
    (he : ∀ e ∈ E, ∀ e' ∈ E, e.1.1 = e'.1.1 → (e.2 = [] ↔ e'.2 = []))
    (hv : v ∈ V ι (ofEntries E).toSystem) {ζ : Z → H}
    (hζ : ∀ c, FreeGroup.lift (Sum.elim ζ (ι ∘ FreeGroup.of)) (FreeGroup.mk [itemLetter E c]) =
      v c) {e : ((X ⊕ A) × Bool) × List ((Z ⊕ A) × Bool)} (hmem : e ∈ E) :
    FreeGroup.lift (Sum.elim (fun x => FreeGroup.lift (Sum.elim v (ι ∘ FreeGroup.of))
      (FreeGroup.mk (wordMap E x))) (ι ∘ FreeGroup.of)) (FreeGroup.mk [e.1]) =
      FreeGroup.lift (Sum.elim ζ (ι ∘ FreeGroup.of)) (FreeGroup.mk e.2) := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hmem
  have hseg := lift_mk_segment_true hζ (entryStart E k) (entryStart E (k + 1))
  rw [drop_take_entryStart E hk] at hseg
  rw [FreeGroup.lift_mk_singleton]
  obtain ⟨⟨y, s⟩, hy⟩ : ∃ y, E[k].1 = y := ⟨_, rfl⟩
  rw [hy]
  rcases y with x | a
  · -- The word map of `x` is read at an entry `k₀` of `x`, whose word is empty iff that of `k` is.
    obtain ⟨k₀, hk₀, hw⟩ := exists_wordMap_eq E (x := x) ⟨k, hk⟩ (by simp [hy])
    have hsame : E[k₀].1.1 = E[k].1.1 := by rw [hk₀, hy]
    have hiff := he _ (List.getElem_mem _) _ (List.getElem_mem _) hsame
    simp only [Sum.elim_inl, hw]
    by_cases hnil : E[k].2 = []
    · rw [List.eq_nil_of_length_eq_zero ((length_segment_entryStart E k₀.isLt _).trans
        (List.length_eq_zero_iff.2 (hiff.2 hnil))), hnil]
      cases s <;> simp [← FreeGroup.one_eq_mk]
    · rw [lift_mk_segment_eq hv (k' := ⟨k, hk⟩) (by rw [hk₀]; rfl) hsame (mt hiff.1 hnil) hnil,
        lift_mk_segment]
      simp only [Fin.getElem_fin]
      rw [hseg, hy, Bool.cond_cond_inv]
  · rw [hc _ (List.getElem_mem _) a (by rw [hy]), hy]
    simp

/-- Under the word maps, a product of entries evaluates to the value of the product of their
words. -/
private theorem lift_mk_map_fst
    (hc : ∀ e ∈ E, ∀ a : A, e.1.1 = Sum.inr a → e.2 = [(Sum.inr a, e.1.2)])
    (he : ∀ e ∈ E, ∀ e' ∈ E, e.1.1 = e'.1.1 → (e.2 = [] ↔ e'.2 = []))
    (hv : v ∈ V ι (ofEntries E).toSystem) {ζ : Z → H}
    (hζ : ∀ c, FreeGroup.lift (Sum.elim ζ (ι ∘ FreeGroup.of)) (FreeGroup.mk [itemLetter E c]) =
      v c) (R : List (((X ⊕ A) × Bool) × List ((Z ⊕ A) × Bool))) (hR : ∀ e ∈ R, e ∈ E) :
    FreeGroup.lift (Sum.elim (fun x => FreeGroup.lift (Sum.elim v (ι ∘ FreeGroup.of))
      (FreeGroup.mk (wordMap E x))) (ι ∘ FreeGroup.of)) (FreeGroup.mk (R.map Prod.fst)) =
      FreeGroup.lift (Sum.elim ζ (ι ∘ FreeGroup.of)) (FreeGroup.mk (R.flatMap Prod.snd)) := by
  induction R with
  | nil => simp [← FreeGroup.one_eq_mk]
  | cons e R ih =>
    rw [List.map_cons, List.flatMap_cons, ← List.singleton_append, ← FreeGroup.mul_mk,
      ← FreeGroup.mul_mk, map_mul, map_mul, lift_mk_entry hc he hv hζ (hR e List.mem_cons_self),
      ih fun e he => hR e (List.mem_cons_of_mem _ he)]

end Soundness

/-! ### Partition tables -/

section Tables

variable {X Z A : Type*}

/-- The occurrences of letters in a system of words `r`: the pairs `(i, j)` with `j < |r i|`. -/
abbrev Occurrence {α : Type*} (r : List (List α)) : Type :=
  Σ i : Fin r.length, Fin r[i].length

/-- The size `|S| = ∑ (l_i - 1) l_i` of a system of words of lengths `l_i`: it bounds the total
length of the words of a partition table. -/
def systemSize {α : Type*} (r : List (List α)) : ℕ :=
  (r.map fun w => (w.length - 1) * w.length).sum

/-- Summing `l_i - 1` over the occurrences of a system of words gives its size. -/
theorem sum_occurrence_length_sub_one {α : Type*} (r : List (List α)) :
    ∑ o : Occurrence r, (r[o.1].length - 1) = systemSize r := by
  rw [systemSize, ← Fin.sum_univ_fun_getElem, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_const_nat (m := r[i].length - 1) fun _ _ => rfl]
  simp [mul_comm]

/-- A partition table (Kharlampovich–Myasnikov, §4.2) of a system of equations written as the
words `r`: a reduced word `T o = V_{ij}` over `Z^{±1} ∪ A^{±1}` for each occurrence `o = (i, j)`,
such that the product `V_{i1} ⋯ V_{il_i}` of each equation is trivial in `F(Z ∪ A)`, each
`V_{ij}` has length at most `l_i - 1`, and `V_{ij} = a` for a constant occurrence `r_{ij} = a`.
Moreover the words of two occurrences of the same letter are empty together, so that a variable
sent to `1` has empty words at all its occurrences. -/
structure IsPartitionTable (r : List (List ((X ⊕ A) × Bool)))
    (T : Occurrence r → List ((Z ⊕ A) × Bool)) : Prop where
  /-- The word of each occurrence is reduced. -/
  isReduced (o : Occurrence r) : FreeGroup.IsReduced (T o)
  /-- The product of the words of each equation is trivial in `F(Z ∪ A)`. -/
  mk_flatMap_eq_one (i : Fin r.length) :
    FreeGroup.mk ((List.finRange r[i].length).flatMap fun j => T ⟨i, j⟩) = 1
  /-- The word of an occurrence in an equation of length `l` has length at most `l - 1`. -/
  length_le (o : Occurrence r) : (T o).length ≤ r[o.1].length - 1
  /-- The word of a constant occurrence is that constant. -/
  eq_of_eq_inr (o : Occurrence r) {a : A} (h : r[o.1][o.2].1 = Sum.inr a) :
    T o = [(Sum.inr a, r[o.1][o.2].2)]
  /-- The words of two occurrences of the same letter are empty together. -/
  eq_nil_iff (o o' : Occurrence r) (h : r[o.1][o.2].1 = r[o'.1][o'.2].1) :
    T o = [] ↔ T o' = []

/-- The entries `(r_{ij}, V_{ij})` of a table, equation by equation. -/
def tableEntries (r : List (List ((X ⊕ A) × Bool))) (T : Occurrence r → List ((Z ⊕ A) × Bool)) :
    List (((X ⊕ A) × Bool) × List ((Z ⊕ A) × Bool)) :=
  (List.finRange r.length).flatMap fun i =>
    (List.finRange r[i].length).map fun j => (r[i][j], T ⟨i, j⟩)

variable {r : List (List ((X ⊕ A) × Bool))} {T : Occurrence r → List ((Z ⊕ A) × Bool)}

/-- The entries of a table are the occurrences of the system with their words. -/
@[simp]
theorem mem_tableEntries {e : ((X ⊕ A) × Bool) × List ((Z ⊕ A) × Bool)} :
    e ∈ tableEntries r T ↔ ∃ o : Occurrence r, (r[o.1][o.2], T o) = e := by
  simp [tableEntries, Sigma.exists]

/-- The concatenated word of a table has length the sum of the lengths of its words. -/
theorem length_flatMap_tableEntries :
    ((tableEntries r T).flatMap Prod.snd).length = ∑ o : Occurrence r, (T o).length := by
  rw [Fintype.sum_sigma]
  simp [tableEntries, List.flatMap_assoc, List.flatMap_map, List.length_flatMap,
    Fin.sum_univ_def]

/-! ### The cancellation family -/

variable (r) in
/-- **Kharlampovich–Myasnikov, Lemma 13(1).** A system of words over finite alphabets has finitely
many partition tables: their words have bounded length. -/
theorem finite_setOf_isPartitionTable [Finite Z] [Finite A] :
    {T : Occurrence r → List ((Z ⊕ A) × Bool) | IsPartitionTable r T}.Finite :=
  (Set.Finite.pi' fun o => List.finite_length_le _ (r[o.1].length - 1)).subset
    fun T (hT : IsPartitionTable r T) o => hT.length_le o

variable (r) in
/-- The cancellation family of a system of equations written as the words `r`: the finite set of
its partition tables with letters `Z = {0, …, |S| - 1}`. Each member `T` gives the generalised
equation `ofEntries (tableEntries r T)` and the word maps `wordMap (tableEntries r T)`. -/
noncomputable def cancellationFamily [Finite A] :
    Finset (Occurrence r → List ((Fin (systemSize r) ⊕ A) × Bool)) :=
  (finite_setOf_isPartitionTable r).toFinset

/-- The members of the cancellation family are the partition tables. -/
@[simp]
theorem mem_cancellationFamily [Finite A]
    {T : Occurrence r → List ((Fin (systemSize r) ⊕ A) × Bool)} :
    T ∈ cancellationFamily r ↔ IsPartitionTable r T := by
  rw [cancellationFamily, Set.Finite.mem_toFinset]
  rfl

variable (r) in
/-- **Kharlampovich–Myasnikov, Lemma 13(1).** A system of size `|S|` over an alphabet `A` has at
most `(2 (|S| + |A|) + 1) ^ |S|` partition tables. -/
theorem card_cancellationFamily_le [Fintype A] :
    (cancellationFamily r).card ≤ (2 * (systemSize r + Fintype.card A) + 1) ^ systemSize r := by
  classical
  let f (T : Occurrence r → List ((Fin (systemSize r) ⊕ A) × Bool)) (o : Occurrence r)
      (n : Fin (r[o.1].length - 1)) : Option ((Fin (systemSize r) ⊕ A) × Bool) :=
    (T o)[(n : ℕ)]?
  have hinj : Set.InjOn f (cancellationFamily r) := by
    intro T hT T' hT' h
    funext o
    have hl := (mem_cancellationFamily.1 hT).length_le o
    have hl' := (mem_cancellationFamily.1 hT').length_le o
    refine List.ext_getElem? fun n => ?_
    by_cases hn : n < r[o.1].length - 1
    · exact congrFun (congrFun h o) ⟨n, hn⟩
    · rw [List.getElem?_eq_none (by lia), List.getElem?_eq_none (by lia)]
  refine (Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    hinj).trans_eq ?_
  rw [Finset.card_univ, Fintype.card_pi, ← sum_occurrence_length_sub_one,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun o _ => ?_
  simp [mul_comm]

/-- The generalised equation of a partition table has at most `|S|` items. -/
theorem IsPartitionTable.numItems_ofEntries_le (hT : IsPartitionTable r T) :
    (ofEntries (tableEntries r T)).numItems ≤ systemSize r := by
  rw [← sum_occurrence_length_sub_one]
  exact length_flatMap_tableEntries.trans_le (Finset.sum_le_sum fun o _ => hT.length_le o)

/-- The word maps of a partition table have length at most `|S|`. -/
theorem IsPartitionTable.length_wordMap_le (hT : IsPartitionTable r T) (x : X) :
    (wordMap (tableEntries r T) x).length ≤ systemSize r :=
  (GenEq.length_wordMap_le _ x).trans hT.numItems_ofEntries_le

/-- **Kharlampovich–Myasnikov, Lemma 14(4).** If `v` is a solution of the system `Ω_T*` of the
generalised equation of a partition table `T` in a group `H` over `F(A)`, then the word maps give
the solution `x ↦ P_x(v)` of the system of equations `r` in `H`. -/
theorem IsPartitionTable.eval_eq_one_of_mem_V (hT : IsPartitionTable r T) {H : Type*} [Group H]
    {ι : FreeGroup A →* H} {v : Fin (ofEntries (tableEntries r T)).numItems → H}
    (hv : v ∈ V ι (ofEntries (tableEntries r T)).toSystem) {w : List ((X ⊕ A) × Bool)}
    (hw : w ∈ r) :
    EqIneqSystem.eval (fun x => EqIneqSystem.eval v (ι ∘ FreeGroup.of)
      (FreeGroup.mk (wordMap (tableEntries r T) x))) (ι ∘ FreeGroup.of) (FreeGroup.mk w) = 1 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
  obtain ⟨ζ, hζ⟩ := exists_lift_mk_itemLetter hv
  have hc : ∀ e ∈ tableEntries r T, ∀ a : A, e.1.1 = Sum.inr a → e.2 = [(Sum.inr a, e.1.2)] := by
    simp only [mem_tableEntries, forall_exists_index]
    rintro _ o rfl a h
    exact hT.eq_of_eq_inr o h
  have he : ∀ e ∈ tableEntries r T, ∀ e' ∈ tableEntries r T, e.1.1 = e'.1.1 →
      (e.2 = [] ↔ e'.2 = []) := by
    simp only [mem_tableEntries, forall_exists_index]
    rintro _ o rfl _ o' rfl h
    exact hT.eq_nil_iff o o' h
  set R := (List.finRange r[(⟨i, hi⟩ : Fin r.length)].length).map fun j =>
    (r[(⟨i, hi⟩ : Fin r.length)][j], T ⟨⟨i, hi⟩, j⟩) with hR
  have := lift_mk_map_fst hc he hv hζ R fun e he => mem_tableEntries.2 (by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 he
    exact ⟨⟨⟨i, hi⟩, j⟩, rfl⟩)
  have hfst : R.map Prod.fst = r[i] := by
    simp [hR, Function.comp_def, List.map_getElem_finRange]
  have hsnd : FreeGroup.mk (R.flatMap Prod.snd) = 1 := by
    simpa [hR, List.flatMap_map] using hT.mk_flatMap_eq_one ⟨i, hi⟩
  rw [hfst, hsnd, map_one] at this
  simpa [EqIneqSystem.eval_eq_lift] using this

/-- A solution `U` of the generalised equation of a partition table gives, through the word maps,
the solution `x ↦ P_x(U)` of the system of equations `r` in `F(A)`. -/
theorem IsPartitionTable.eval_substituteVars_eq_one (hT : IsPartitionTable r T)
    (U : (ofEntries (tableEntries r T)).Solution) {w : List ((X ⊕ A) × Bool)} (hw : w ∈ r) :
    EqIneqSystem.eval (fun x => FreeGroup.mk (substituteVars U.word (wordMap (tableEntries r T) x)))
      FreeGroup.of (FreeGroup.mk w) = 1 := by
  have := hT.eval_eq_one_of_mem_V U.point_mem_V hw
  rw [show U.point = fun k => FreeGroup.mk (U.word k) from funext U.point_apply] at this
  simpa [EqIneqSystem.eval_eq_lift, FreeGroup.mk_substituteVars] using this

end Tables

/-! ### Solutions from words for the letters of `Z` -/

section LetterWords

variable {X Z A : Type*}

variable (E : List (((X ⊕ A) × Bool) × List ((Z ⊕ A) × Bool))) (w : Z → List (A × Bool))

/-- The word of an item of `ofEntries E` when each letter `z` of `Z` is given the word `w z`: an
item carrying `z ^ ±1` gets `(w z) ^ ±1`, and an item carrying a letter of `A^{±1}` gets that
letter. -/
def itemWord (c : Fin (ofEntries E).numItems) : List (A × Bool) :=
  substituteVars w [itemLetter E c]

/-- The word of an item is its letter with the words `w z` substituted for the letters of `Z`. -/
theorem itemWord_def (c : Fin (ofEntries E).numItems) :
    itemWord E w c = substituteVars w [itemLetter E c] :=
  (rfl)

/-- An item carrying the letter `z ^ s` of `Z^{±1}` gets the word `(w z) ^ s`. -/
theorem itemWord_of_itemLetter_eq_inl {c : Fin (ofEntries E).numItems} {z : Z} {s : Bool}
    (hc : itemLetter E c = (Sum.inl z, s)) :
    itemWord E w c = cond s (w z) (FreeGroup.invRev (w z)) := by
  cases s <;> simp [itemWord_def, hc]

/-- An item carrying the letter `a ^ s` of `A^{±1}` gets the one-letter word `a ^ s`. -/
theorem itemWord_of_itemLetter_eq_inr {c : Fin (ofEntries E).numItems} {a : A} {s : Bool}
    (hc : itemLetter E c = (Sum.inr a, s)) : itemWord E w c = [(a, s)] := by
  simp [itemWord_def, hc]

/-- The words of the items between two boundaries spell the corresponding subword of the
concatenated word, with the letters of `Z` replaced by their words. -/
theorem substituteVars_itemWord_segment (i j : ℕ) :
    substituteVars (itemWord E w) ((ofEntries E).segment i j true) =
      substituteVars w (((E.flatMap Prod.snd).take j).drop i) := by
  rw [segment_true, FreeGroup.substituteVars_map_inl, ← map_itemLetter_finRange E,
    ← List.map_take, ← List.map_drop, FreeGroup.substituteVars, List.flatMap_map]
  congr 1
  funext c
  simp [itemWord_def, FreeGroup.substituteVars]

/-- The items spanned by the word of an entry carrying a letter with sign `s` spell the substituted
word of the entry, raised to `s`. -/
theorem substituteVars_itemWord_entry {k : ℕ} (hk : k < E.length) (s : Bool) :
    substituteVars (itemWord E w)
        ((ofEntries E).segment (entryStart E k) (entryStart E (k + 1)) s) =
      substituteVars w (cond s E[k].2 (FreeGroup.invRev E[k].2)) := by
  cases s
  · rw [segment_false, FreeGroup.substituteVars_invRev, substituteVars_itemWord_segment,
      drop_take_entryStart E hk, Bool.cond_false, FreeGroup.substituteVars_invRev]
  · rw [substituteVars_itemWord_segment, drop_take_entryStart E hk, Bool.cond_true]

private theorem substituteVars_itemWord_singleton {c : Fin (ofEntries E).numItems} {z : Z}
    {s : Bool} (hc : itemLetter E c = (Sum.inl z, s)) :
    substituteVars (itemWord E w) [(Sum.inl c, s)] = w z := by
  cases s <;> simp [itemWord_of_itemLetter_eq_inl E w hc, FreeGroup.invRev_invRev]

/-- The solution of `ofEntries E` given by words `w z` for the letters of `Z` that are nonempty
and reduced for every letter `z` occurring in the concatenated word, provided that the substituted
words of the entries of each variable with nonempty words are reduced and agree, raised to the
signs of the occurrences. -/
def Solution.ofLetterWords
    (hw : ∀ c z s, itemLetter E c = (Sum.inl z, s) → FreeGroup.IsReduced (w z))
    (hw₀ : ∀ c z s, itemLetter E c = (Sum.inl z, s) → w z ≠ [])
    (hred : ∀ p, IsVarPair E p → FreeGroup.IsReduced (substituteVars w E[p.1].2))
    (heq : ∀ p, IsVarPair E p →
      substituteVars w (cond E[p.1].1.2 E[p.1].2 (FreeGroup.invRev E[p.1].2)) =
        substituteVars w (cond E[p.2].1.2 E[p.2].2 (FreeGroup.invRev E[p.2].2))) :
    (ofEntries E).Solution where
  word := itemWord E w
  isReduced_word c := by
    obtain ⟨⟨z | a, s⟩, hy⟩ : ∃ y, itemLetter E c = y := ⟨_, rfl⟩
    · cases s <;> simp [itemWord_of_itemLetter_eq_inl E w hy, hw c z _ hy,
        FreeGroup.isReduced_invRev]
    · simp [itemWord_of_itemLetter_eq_inr E w hy, FreeGroup.IsReduced.singleton]
  word_ne_nil c := by
    obtain ⟨⟨z | a, s⟩, hy⟩ : ∃ y, itemLetter E c = y := ⟨_, rfl⟩
    · cases s <;> simp [itemWord_of_itemLetter_eq_inl E w hy, hw₀ c z _ hy, FreeGroup.invRev]
    · simp [itemWord_of_itemLetter_eq_inr E w hy]
  isReduced_subst := (forall_mem_equations_ofEntries E).2
    ⟨fun p hp => by
      rw [substituteVars_itemWord_entry E w p.1.isLt, substituteVars_itemWord_entry E w p.2.isLt]
      exact ⟨FreeGroup.isReduced_substituteVars_cond w _ _ (hred p hp),
        FreeGroup.isReduced_substituteVars_cond w _ _ (hred _ hp.swap)⟩,
    fun c c' _ z s s' hc hc' => by
      rw [substituteVars_itemWord_singleton E w hc, substituteVars_itemWord_singleton E w hc']
      exact ⟨hw c z s hc, hw c z s hc⟩,
    fun c a s hc => by
      simp [itemWord_of_itemLetter_eq_inr E w hc, FreeGroup.IsReduced.singleton]⟩
  subst_eq := (forall_mem_equations_ofEntries E).2
    ⟨fun p hp => by
      rw [substituteVars_itemWord_entry E w p.1.isLt, substituteVars_itemWord_entry E w p.2.isLt]
      exact heq p hp,
    fun c c' _ z s s' hc hc' => by
      rw [substituteVars_itemWord_singleton E w hc, substituteVars_itemWord_singleton E w hc'],
    fun c a s hc => by simp [itemWord_of_itemLetter_eq_inr E w hc]⟩

/-- The words of the items of `Solution.ofLetterWords` are given by `itemWord`. -/
@[simp]
theorem Solution.word_ofLetterWords (hw hw₀ hred heq) :
    (Solution.ofLetterWords E w hw hw₀ hred heq).word = itemWord E w :=
  (rfl)

end LetterWords

/-! ### Examples -/

section Examples

/-- The empty system has exactly one partition table, the empty one. -/
theorem cancellationFamily_nil {X A : Type*} [Finite A] :
    cancellationFamily ([] : List (List ((X ⊕ A) × Bool))) = {fun o => o.1.elim0} := by
  ext T
  rw [mem_cancellationFamily, Finset.mem_singleton]
  refine ⟨fun _ => funext fun o => o.1.elim0, ?_⟩
  rintro rfl
  exact ⟨fun o => o.1.elim0, fun i => i.elim0, fun o => o.1.elim0, fun o => o.1.elim0,
    fun o => o.1.elim0⟩

/-- The generalised equation of the table of the empty system is the empty generalised
equation. -/
theorem ofEntries_tableEntries_nil {X Z A : Type*}
    (T : Occurrence ([] : List (List ((X ⊕ A) × Bool))) → List ((Z ⊕ A) × Bool)) :
    ofEntries (tableEntries [] T) = empty :=
  eq_empty_of_numItems_eq_zero rfl

/-- The equation `x a⁻¹ = 1` over `F(a, b)`, with `x = 0` and `a = 0`. -/
private abbrev xEqA : List (List ((Fin 2 ⊕ Fin 2) × Bool)) :=
  [[(Sum.inl 0, true), (Sum.inr 0, false)]]

/-- The partition table `(a, a⁻¹)` of `x a⁻¹ = 1`. -/
private def xEqATable (o : Occurrence xEqA) : List ((Fin (systemSize xEqA) ⊕ Fin 2) × Bool) :=
  [(Sum.inr 0, decide (o.2.val = 0))]

/-- The equation `x = a` has a cancellation scheme with an item labelled `a` whose word is the
word map of `x`. -/
example : ∃ T ∈ cancellationFamily xEqA, ∃ k,
    (k, ((0 : Fin 2), true)) ∈ (ofEntries (tableEntries xEqA T)).constBases ∧
      wordMap (tableEntries xEqA T) 0 = [(Sum.inl k, true)] :=
  ⟨xEqATable, mem_cancellationFamily.2 ⟨fun _ => FreeGroup.IsReduced.singleton,
    by decide, by decide, by decide, by decide⟩, ⟨0, by decide⟩,
    (mem_constBases_ofEntries _).2 (by decide), by
      rw [wordMap_eq _ ⟨0, by decide⟩ (by decide) (by decide)]
      exact segment_succ _ ⟨0, by decide⟩ true⟩

/-- The equation `x² = a`, with `a` a letter of the basis, has no solution in `F(A)`, so no member
of its cancellation family has a solution. -/
example {X A : Type*} [Finite A] (x : X) (a : A)
    {T : Occurrence [[(Sum.inl x, true), (Sum.inl x, true), (Sum.inr a, false)]] →
      List ((Fin (systemSize [[(Sum.inl x, true), (Sum.inl x, true), (Sum.inr a, false)]]) ⊕
        A) × Bool)}
    (hT : T ∈ cancellationFamily [[(Sum.inl x, true), (Sum.inl x, true), (Sum.inr a, false)]]) :
    IsEmpty (ofEntries (tableEntries _ T)).Solution := by
  refine ⟨fun U => ?_⟩
  have h := (mem_cancellationFamily.1 hT).eval_substituteVars_eq_one U List.mem_cons_self
  -- The exponent sum of `x² a⁻¹` would vanish, but it is odd.
  have := congrArg (fun y => Multiplicative.toAdd
    (FreeGroup.lift (fun _ : A => Multiplicative.ofAdd (1 : ℤ)) y)) h
  simp [EqIneqSystem.eval_eq_lift, FreeGroup.lift_mk] at this
  lia

/-- The equation `x y b⁻¹ a⁻¹ = 1` over `F(a, b)`, with `x = 0`, `y = 1`, `a = 0` and `b = 1`. -/
private abbrev xyEqAB : List (List ((Fin 2 ⊕ Fin 2) × Bool)) :=
  [[(Sum.inl 0, true), (Sum.inl 1, true), (Sum.inr 1, false), (Sum.inr 0, false)]]

/-- The partition table `(a, b, b⁻¹, a⁻¹)` of `x y = a b`, without cancellation. -/
private def xyTable (o : Occurrence xyEqAB) : List ((Fin (systemSize xyEqAB) ⊕ Fin 2) × Bool) :=
  [[(Sum.inr 0, true)], [(Sum.inr 1, true)], [(Sum.inr 1, false)], [(Sum.inr 0, false)]].getD
    o.2.val []

/-- The partition table `(a z, z⁻¹ b, b⁻¹, a⁻¹)` of `x y = a b`, with a cancelling segment `z`. -/
private def xyCancelTable (o : Occurrence xyEqAB) :
    List ((Fin (systemSize xyEqAB) ⊕ Fin 2) × Bool) :=
  [[(Sum.inr 0, true), (Sum.inl ⟨0, by decide⟩, true)],
    [(Sum.inl ⟨0, by decide⟩, false), (Sum.inr 1, true)], [(Sum.inr 1, false)],
    [(Sum.inr 0, false)]].getD o.2.val []

/-- The solution `x = a`, `y = b` of `x y = a b` comes from the table without cancellation. -/
example : xyTable ∈ cancellationFamily xyEqAB ∧
    ∃ U : (ofEntries (tableEntries xyEqAB xyTable)).Solution,
      substituteVars U.word (wordMap (tableEntries xyEqAB xyTable) 0) = [(0, true)] ∧
        substituteVars U.word (wordMap (tableEntries xyEqAB xyTable) 1) = [(1, true)] := by
  have hp : ∀ p, ¬ IsVarPair (tableEntries xyEqAB xyTable) p := by decide
  refine ⟨mem_cancellationFamily.2 ⟨by unfold FreeGroup.IsReduced; decide, by decide, by decide,
    by decide, by decide⟩, Solution.ofLetterWords _ (fun _ => [(0, true)])
      (fun _ _ _ _ => .singleton) (by simp) (fun p h => (hp p h).elim) (fun p h => (hp p h).elim),
    ?_, ?_⟩
  · rw [Solution.word_ofLetterWords, wordMap_eq _ ⟨0, by decide⟩ (by decide) (by decide),
      substituteVars_itemWord_entry _ _ (Fin.isLt _)]
    decide
  · rw [Solution.word_ofLetterWords, wordMap_eq _ ⟨1, by decide⟩ (by decide) (by decide),
      substituteVars_itemWord_entry _ _ (Fin.isLt _)]
    decide

/-- Every solution `x = a c`, `y = c⁻¹ b` of `x y = a b`, for a nonempty reduced word `c`, comes
from the table with a cancelling segment, whose word maps preserve `c`. -/
example (c : List (Fin 2 × Bool)) (hc : FreeGroup.IsReduced c) (hc₀ : c ≠ []) :
    xyCancelTable ∈ cancellationFamily xyEqAB ∧
    ∃ U : (ofEntries (tableEntries xyEqAB xyCancelTable)).Solution,
      substituteVars U.word (wordMap (tableEntries xyEqAB xyCancelTable) 0) = (0, true) :: c ∧
      substituteVars U.word (wordMap (tableEntries xyEqAB xyCancelTable) 1) =
        FreeGroup.invRev c ++ [(1, true)] := by
  have hp : ∀ p, ¬ IsVarPair (tableEntries xyEqAB xyCancelTable) p := by decide
  have h₀ : (tableEntries xyEqAB xyCancelTable)[0] =
      ((Sum.inl 0, true), [(Sum.inr 0, true), (Sum.inl ⟨0, by decide⟩, true)]) := by decide
  have h₁ : (tableEntries xyEqAB xyCancelTable)[1] =
      ((Sum.inl 1, true), [(Sum.inl ⟨0, by decide⟩, false), (Sum.inr 1, true)]) := by decide
  refine ⟨mem_cancellationFamily.2 ⟨by unfold FreeGroup.IsReduced; decide, by decide, by decide,
    by decide, by decide⟩, Solution.ofLetterWords _ (fun _ => c) (fun _ _ _ _ => hc)
      (fun _ _ _ _ => hc₀) (fun p h => (hp p h).elim) (fun p h => (hp p h).elim), ?_, ?_⟩
  · rw [Solution.word_ofLetterWords, wordMap_eq _ ⟨0, by decide⟩ (by decide) (by decide),
      substituteVars_itemWord_entry _ _ (Fin.isLt _)]
    simp [h₀, FreeGroup.substituteVars]
  · rw [Solution.word_ofLetterWords, wordMap_eq _ ⟨1, by decide⟩ (by decide) (by decide),
      substituteVars_itemWord_entry _ _ (Fin.isLt _)]
    simp [h₁, FreeGroup.substituteVars]

end Examples

end GenEq

end TauCeti

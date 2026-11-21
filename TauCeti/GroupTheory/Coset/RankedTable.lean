/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.Table

/-!
# Ranked coset tables

A coset table (`TauCeti.CosetTable`) certifies an upper bound on the index of a subgroup once
every edge `g t • T.point g a i = T.point g a (T.act t i)` is known to hold in the group. The
deduction certificate of `TauCeti.CosetTable.check` establishes the edges by replaying the
deductions of a coset enumeration in order, carrying the list of edges known so far. That check
is one computation whose cost grows quadratically with the table, and it compares the words
naming the points letter by letter.

This file gives a certificate for the same statement in which every edge is checked on its own,
so that the check of a large table is a conjunction of independent finite computations and can be
split over as many `decide` calls as needed. A table `T : TauCeti.RankedCosetTable m k` consists
of

* the action `T.act t` of each generator on the `k` points, as for a coset table;
* a *forest*: a point `i` with `T.parent i < i` is named by the word of its parent `T.parent i`
  with the letter `T.letter i` put in front, and the other points, the roots, are named by the
  empty word, so that the words never have to be written down or compared;
* for each edge `(t, j)` a *rank* `T.rank t j` and the position `T.rel t j`, `T.rot t j` of a
  closed word in the lists of relators and subgroup generators.

An edge `(t, j)` passes `TauCeti.RankedCosetTable.checkEdge` if it is an edge of the forest, which
holds by the definition of the points, or if its closed word, a cyclic rotation of a relator, or a
subgroup generator at a root, has the form `t :: u` where `u` leads from `T.act t j` back to `j`
through edges of rank smaller than `T.rank t j`. Once the edges of smaller rank are known to hold,
the edge `(t, j)` is the only edge of the closed word that is not yet known, and the closed word
proves it. So passing the check does not make a single edge hold on its own: when every edge of
the table passes, induction on the rank shows that every edge holds in the group
(`TauCeti.RankedCosetTable.smul_point`). The ranks replace the order of the deductions of a
replay: no state is carried from one edge to the next.

The generators `g : Fin m → G` are an arbitrary family, so inverses of generators can be listed as
letters of their own; the relators then include the two-letter words `[t', t]` with
`g t' * g t = 1`, which deduce an edge from its reverse.

## Main definitions

* `TauCeti.RankedCosetTable`: the action, the forest, and the rank and closed word of each edge.
* `TauCeti.RankedCosetTable.toCosetTable`: the coset table it describes.
* `TauCeti.RankedCosetTable.checkEdge`: the Boolean check of one edge.
* `TauCeti.RankedCosetTable.checkRange`: the check of all edges at an interval of points.

## Main results

* `TauCeti.RankedCosetTable.smul_point`: if every edge passes the check, the table describes the
  action of the generators on the points it names.
* `TauCeti.RankedCosetTable.index_le` and `TauCeti.RankedCosetTable.finiteIndex`: a nonempty
  such table on `k` points for a subgroup `H` shows `H.index ≤ k`, and in particular that `H` has
  finite index.

## References

* J. A. Todd, H. S. M. Coxeter, *A practical method for enumerating cosets of a finite abstract
  group*, Proc. Edinburgh Math. Soc. 5 (1936), 26–34.
* D. F. Holt, B. Eick, E. A. O'Brien, *Handbook of Computational Group Theory*, Chapman &
  Hall/CRC, 2005, Chapter 5.
-/

public section

namespace TauCeti

/-- A ranked coset table on `k` points for `m` generators: the action of each generator on the
points, a forest naming the points, and for each edge `(t, j)` a rank and the position of a closed
word that deduces it from edges of smaller rank. -/
structure RankedCosetTable (m k : ℕ) where
  /-- The action of the generator `t` on the points. -/
  act : Fin m → Fin k → Fin k
  /-- The parent of a point in the forest. A point `i` with `parent i < i` is named by its parent
  moved by `letter i`; every other point is a root, named by the empty word. -/
  parent : Fin k → Fin k
  /-- The generator leading from the parent of a point to the point. -/
  letter : Fin k → Fin m
  /-- The rank of the edge `(t, j)`. -/
  rank : Fin m → Fin k → ℕ
  /-- The position of the closed word of the edge `(t, j)`: an index in the list of relators, or
  the length of that list plus an index in the list of subgroup generators. -/
  rel : Fin m → Fin k → ℕ
  /-- The cyclic rotation applied to the relator of the edge `(t, j)`. -/
  rot : Fin m → Fin k → ℕ

namespace RankedCosetTable

variable {m k : ℕ} (T : RankedCosetTable m k)

/-! ### The forest and the coset table -/

/-- The word naming the point `i`, read off the forest: the letters on the path from `i` to its
root, the letter of `i` first. -/
def word (i : Fin k) : List (Fin m) :=
  if _ : T.parent i < i then T.letter i :: word (T.parent i) else []
termination_by i.val
decreasing_by assumption

/-- The word of a point `i` is the word of its parent with the letter of `i` in front if
`T.parent i < i`, and is empty otherwise. -/
theorem word_def (i : Fin k) :
    T.word i = if T.parent i < i then T.letter i :: T.word (T.parent i) else [] := by
  rw [word, dite_eq_ite]

/-- The word of a point `i` with `T.parent i < i` is the word of its parent with the letter of
`i` in front. -/
theorem word_of_parent_lt {i : Fin k} (h : T.parent i < i) :
    T.word i = T.letter i :: T.word (T.parent i) := by
  rw [word_def, ite_eq_left h]

/-- The word of a root is empty. -/
theorem word_of_not_parent_lt {i : Fin k} (h : ¬ T.parent i < i) : T.word i = [] := by
  rw [word_def, ite_eq_right h]

/-- The point `0` is a root: its word is empty. -/
@[simp]
theorem word_zero [NeZero k] : T.word 0 = [] :=
  T.word_of_not_parent_lt (Fin.not_lt_zero _)

/-- The coset table described by a ranked coset table: the same action, with the points named by
the words of the forest. -/
def toCosetTable : CosetTable m k where
  act := T.act
  word := T.word

@[simp]
theorem toCosetTable_act : T.toCosetTable.act = T.act := (rfl)

@[simp]
theorem toCosetTable_word : T.toCosetTable.word = T.word := (rfl)

/-! ### The Boolean check

The bodies below are exposed because a certificate is checked by `decide`, which has to evaluate
them. -/

/-- The point reached from `i` along the word `u`, applying its letters from right to left, if
every edge on the way has rank less than `r`. -/
@[expose]
def scan (r : ℕ) (i : Fin k) : List (Fin m) → Option (Fin k)
  | [] => some i
  | t :: u => (scan r i u).bind fun j ↦ if T.rank t j < r then some (T.act t j) else none

/-- The edge `(t, j)` is an edge of the forest: the point `T.act t j` is not a root, its parent is
`j` and its letter is `t`. -/
@[expose]
def isForestEdge (t : Fin m) (j : Fin k) : Bool :=
  decide (j < T.act t j) && decide (T.parent (T.act t j) = j) && decide (T.letter (T.act t j) = t)

/-- The word `w` deduces the edge `(t, j)` when it is closed at the point `T.act t j`: it has the
form `t :: u`, where `u` leads from `T.act t j` to `j` through edges of rank less than
`T.rank t j`. -/
@[expose]
def closes (t : Fin m) (j : Fin k) : List (Fin m) → Bool
  | [] => false
  | t' :: u => decide (t' = t) && decide (T.scan (T.rank t j) (T.act t j) u = some j)

/-- The check of the edge `(t, j)` for the relators `rels` and the subgroup generators `stab`: it
is an edge of the forest, or the rotation by `T.rot t j` of the relator at the position
`T.rel t j` deduces it, or the position `T.rel t j` lies beyond the relators
(`rels.length ≤ T.rel t j`), `T.act t j` is a root and the subgroup generator at the position
`T.rel t j - rels.length` deduces it. -/
@[expose]
def checkEdge (rels stab : List (List (Fin m))) (t : Fin m) (j : Fin k) : Bool :=
  T.isForestEdge t j ||
    match rels[T.rel t j]? with
    | some w => T.closes t j (w.rotate (T.rot t j))
    | none =>
      !decide (T.parent (T.act t j) < T.act t j) &&
        (stab[T.rel t j - rels.length]?).any (T.closes t j)

/-- The check of every edge at the points `lo, …, lo + len - 1`. A large table is checked by
covering its points with several such intervals, each one a separate computation. -/
@[expose]
def checkRange (rels stab : List (List (Fin m))) (lo len : ℕ) : Bool :=
  (List.range' lo len).all fun n ↦
    if h : n < k then (List.finRange m).all fun t ↦ T.checkEdge rels stab t ⟨n, h⟩ else true

@[simp]
theorem scan_nil (r : ℕ) (i : Fin k) : T.scan r i [] = some i := (rfl)

@[simp]
theorem scan_cons (r : ℕ) (i : Fin k) (t : Fin m) (u : List (Fin m)) :
    T.scan r i (t :: u) =
      (T.scan r i u).bind fun j ↦ if T.rank t j < r then some (T.act t j) else none := (rfl)

/-- A scan succeeds exactly when every edge traversed by the word has rank less than the bound,
and then it returns the point the table reaches along the word. -/
theorem scan_eq_some_iff {r : ℕ} {i j : Fin k} {u : List (Fin m)} :
    T.scan r i u = some j ↔
      T.toCosetTable.trace u i = j ∧ ∀ e ∈ T.toCosetTable.edges u i, T.rank e.1 e.2 < r := by
  induction u generalizing j with
  | nil => simp [CosetTable.edges]
  | cons t u ih =>
    simp only [scan_cons, Option.bind_eq_some_iff, ih, CosetTable.trace_cons, toCosetTable_act,
      CosetTable.edges, List.forall_mem_cons]
    grind

/-- An edge passes `isForestEdge` exactly when the point it leads to lies above the point it
starts at and has that point as its parent and the generator of the edge as its letter. -/
@[simp]
theorem isForestEdge_eq_true_iff {t : Fin m} {j : Fin k} :
    T.isForestEdge t j = true ↔
      j < T.act t j ∧ T.parent (T.act t j) = j ∧ T.letter (T.act t j) = t := by
  simp only [isForestEdge, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

@[simp]
theorem closes_nil (t : Fin m) (j : Fin k) : T.closes t j [] = false := (rfl)

@[simp]
theorem closes_cons (t : Fin m) (j : Fin k) (t' : Fin m) (u : List (Fin m)) :
    T.closes t j (t' :: u) =
      (decide (t' = t) && decide (T.scan (T.rank t j) (T.act t j) u = some j)) := (rfl)

/-- A word deduces the edge `(t, j)` exactly when it has the form `t :: u`, where the table
carries `T.act t j` to `j` along `u` and every edge traversed on the way has rank less than
`T.rank t j`. -/
theorem closes_eq_true_iff {t : Fin m} {j : Fin k} {w : List (Fin m)} :
    T.closes t j w = true ↔
      ∃ u, w = t :: u ∧ T.toCosetTable.trace u (T.act t j) = j ∧
        ∀ e ∈ T.toCosetTable.edges u (T.act t j), T.rank e.1 e.2 < T.rank t j := by
  cases w with
  | nil => simp
  | cons t' u => simp [scan_eq_some_iff]

/-- An edge `(t, j)` passes `checkEdge` exactly when it is an edge of the forest, or the rotation
by `T.rot t j` of the relator at the position `T.rel t j` deduces it, or the position `T.rel t j`
lies beyond the relators, `T.act t j` is a root and the subgroup generator at the position
`T.rel t j - rels.length` deduces it. -/
theorem checkEdge_eq_true_iff {rels stab : List (List (Fin m))} {t : Fin m} {j : Fin k} :
    T.checkEdge rels stab t j = true ↔
      T.isForestEdge t j = true ∨
        (∃ w, rels[T.rel t j]? = some w ∧ T.closes t j (w.rotate (T.rot t j)) = true) ∨
        (rels.length ≤ T.rel t j ∧ ¬ T.parent (T.act t j) < T.act t j ∧
          ∃ w, stab[T.rel t j - rels.length]? = some w ∧ T.closes t j w = true) := by
  rw [checkEdge, Bool.or_eq_true]
  refine or_congr_right ?_
  cases h : rels[T.rel t j]? with
  | none => simp [List.getElem?_eq_none_iff.1 h, Option.any_eq_true]
  | some w => simp [(List.getElem?_eq_some_iff.1 h).1]

/-- An interval of points passes `checkRange` exactly when every edge at each of its points
passes `checkEdge`. -/
@[simp]
theorem checkRange_eq_true_iff {rels stab : List (List (Fin m))} {lo len : ℕ} :
    T.checkRange rels stab lo len = true ↔
      ∀ (t : Fin m) (j : Fin k), lo ≤ j → j < lo + len → T.checkEdge rels stab t j = true := by
  simp only [checkRange, List.all_eq_true, List.mem_range'_1, and_imp]
  refine ⟨fun h t j hlo hj ↦ ?_, fun h n hlo hn ↦ ?_⟩
  · have hj' := h j hlo hj
    simp only [j.isLt, ↓reduceDIte, Fin.eta, List.all_eq_true, List.mem_finRange,
      forall_const] at hj'
    exact hj' t
  · split
    · next hk => exact List.all_eq_true.2 fun t _ ↦ h t ⟨n, hk⟩ hlo hn
    · rfl

/-! ### Soundness -/

section Soundness

variable {T} {G α : Type*} [Group G] [MulAction G α] {g : Fin m → G} {a : α}

/-- An edge of the forest holds by the definition of the points. -/
private theorem smul_point_of_isForestEdge {t : Fin m} {j : Fin k}
    (h : T.isForestEdge t j = true) :
    g t • T.toCosetTable.point g a j = T.toCosetTable.point g a (T.act t j) := by
  obtain ⟨hlt, hparent, hletter⟩ := T.isForestEdge_eq_true_iff.1 h
  have hword : T.word (T.act t j) = t :: T.word j := by
    rw [T.word_of_parent_lt (hparent.symm ▸ hlt), hparent, hletter]
  rw [CosetTable.point_def, CosetTable.point_def, toCosetTable_word, hword, List.map_cons,
    List.prod_cons, mul_smul]

/-- A closed word deduces its first edge from the edges of smaller rank. -/
private theorem smul_point_of_closes {t : Fin m} {j : Fin k} {w : List (Fin m)}
    (h : T.closes t j w = true)
    (hw : (w.map g).prod • T.toCosetTable.point g a (T.act t j) =
      T.toCosetTable.point g a (T.act t j))
    (ih : ∀ t' j', T.rank t' j' < T.rank t j →
      g t' • T.toCosetTable.point g a j' = T.toCosetTable.point g a (T.act t' j')) :
    g t • T.toCosetTable.point g a j = T.toCosetTable.point g a (T.act t j) := by
  obtain ⟨u, rfl, htrace, hrank⟩ := T.closes_eq_true_iff.1 h
  have hu := CosetTable.prod_smul_point_of_edges (g := g) (a := a) (T.act t j) u
    fun e he ↦ ih e.1 e.2 (hrank e he)
  rwa [List.map_cons, List.prod_cons, mul_smul, hu, htrace] at hw

/-- **Soundness of a ranked coset table.** If the relators `rels` hold for the generators `g`,
the words `stab` fix the base point `a` and every edge passes the check, the table describes the
action of each generator on the points it names. The conclusion is the soundness of the edges of
`T.toCosetTable`, in the form the lemmas `TauCeti.CosetTable.prod_smul_point_of_edges` and
`TauCeti.CosetTable.smul_mem_range_point_of_edges` take as hypothesis. -/
theorem smul_point {rels stab : List (List (Fin m))}
    (hrels : ∀ r ∈ rels, (r.map g).prod = 1) (hstab : ∀ r ∈ stab, (r.map g).prod • a = a)
    (hT : ∀ t j, T.checkEdge rels stab t j = true) (t : Fin m) (j : Fin k) :
    g t • T.toCosetTable.point g a j = T.toCosetTable.point g a (T.toCosetTable.act t j) := by
  rw [toCosetTable_act]
  induction hr : T.rank t j using Nat.strong_induction_on generalizing t j with
  | _ r ih =>
    subst hr
    have ih' : ∀ t' j', T.rank t' j' < T.rank t j →
        g t' • T.toCosetTable.point g a j' = T.toCosetTable.point g a (T.act t' j') :=
      fun t' j' hlt ↦ ih _ hlt t' j' rfl
    rcases T.checkEdge_eq_true_iff.1 (hT t j) with h | ⟨w, hw, h⟩ | ⟨-, hroot, w, hw, h⟩
    · exact smul_point_of_isForestEdge h
    · refine smul_point_of_closes h ?_ ih'
      rw [List.map_rotate, List.prod_rotate_eq_one_of_prod_eq_one
        (hrels w (List.mem_of_getElem? hw)), one_smul]
    · refine smul_point_of_closes h ?_ ih'
      rw [CosetTable.point_def, toCosetTable_word, T.word_of_not_parent_lt hroot, List.map_nil,
        List.prod_nil, one_smul, hstab w (List.mem_of_getElem? hw)]

/-- The edges of a ranked coset table for a subgroup `H`, all of which pass the check, hold on
the cosets of `H`: if the relators `rels` hold for the generators `g` and the words `stab` lie in
`H`, the table describes the action of each generator on the cosets it names. The conclusion is
the hypothesis of the lemmas `TauCeti.CosetTable.surjective_point_of_edges`,
`TauCeti.CosetTable.index_le_of_edges` and `TauCeti.CosetTable.index_eq_iff_injective_of_edges`
for `T.toCosetTable`. -/
theorem smul_point_mk_one {H : Subgroup G} {rels stab : List (List (Fin m))}
    (hrels : ∀ r ∈ rels, (r.map g).prod = 1) (hstab : ∀ r ∈ stab, (r.map g).prod ∈ H)
    (hT : ∀ t j, T.checkEdge rels stab t j = true) (t : Fin m) (j : Fin k) :
    g t • T.toCosetTable.point g ((1 : G) : G ⧸ H) j =
      T.toCosetTable.point g ((1 : G) : G ⧸ H) (T.toCosetTable.act t j) :=
  smul_point hrels
    (fun r hr ↦ by simpa [MulAction.Quotient.smul_mk, QuotientGroup.eq] using hstab r hr) hT t j

/-- **A ranked coset table bounds the index.** If the generators `g` generate `G`, the relators
`rels` hold for them, the words `stab` lie in the subgroup `H` and every edge of a nonempty ranked
coset table on `k` points passes the check, then `H` has index at most `k`. -/
theorem index_le [NeZero k] {H : Subgroup G} {rels stab : List (List (Fin m))}
    (hg : Subgroup.closure (Set.range g) = ⊤) (hrels : ∀ r ∈ rels, (r.map g).prod = 1)
    (hstab : ∀ r ∈ stab, (r.map g).prod ∈ H) (hT : ∀ t j, T.checkEdge rels stab t j = true) :
    H.index ≤ k :=
  CosetTable.index_le_of_edges hg (smul_point_mk_one hrels hstab hT)

/-- A subgroup `H` has finite index if it admits a nonempty ranked coset table all of whose edges
pass the check, for generators `g` that generate `G`, relators `rels` that hold for them and words
`stab` that lie in `H`. -/
theorem finiteIndex [NeZero k] {H : Subgroup G} {rels stab : List (List (Fin m))}
    (hg : Subgroup.closure (Set.range g) = ⊤) (hrels : ∀ r ∈ rels, (r.map g).prod = 1)
    (hstab : ∀ r ∈ stab, (r.map g).prod ∈ H) (hT : ∀ t j, T.checkEdge rels stab t j = true) :
    H.FiniteIndex :=
  CosetTable.finiteIndex_of_edges hg (smul_point_mk_one hrels hstab hT)

end Soundness

end RankedCosetTable

end TauCeti

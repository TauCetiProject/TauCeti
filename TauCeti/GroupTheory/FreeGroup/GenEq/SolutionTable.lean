/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.PartitionTable
import TauCeti.GroupTheory.FreeGroup.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# The partition table of a solution

Let `r` be a finite system of equations over the free group `F(A)`, written as words in the
letters of `X^{±1} ∪ A^{±1}`, and let `W : X → F(A)` be a solution. Substituting `W` turns the
`i`-th equation into a product of reduced words `r_{i1}^W ⋯ r_{il_i}^W` which is trivial in
`F(A)`. Fixing a process of free reductions, each `r_{ij}^W` is graphically a product of the
maximal nonempty subwords that cancel against one other factor; naming these subwords by letters
`z` of a new alphabet `Z` writes `r_{ij}^W` as a word `V_{ij}` over `Z^{±1} ∪ A^{±1}`, and the
words `V_{ij}` form a partition table `T` of `r`. The subwords are a solution `U` of the
generalised equation `Ω_T`, and the word maps recover the solution: `P_x(U) = W(x)` graphically
for every variable `x` occurring in `r`.

This file introduces the tables with words for their letters which spell an assignment `W` in this
way, whether or not they come from a process of free reductions, and shows that they give
solutions of their generalised equations.

## Main definitions

* `TauCeti.GenEq.IsSolutionTable r W T u`: the table `T`, with the words `u z` for its letters,
  is a partition table of `r` spelling the assignment `W`.
* `TauCeti.GenEq.IsSolutionTable.solution`: the solution `U` of `Ω_T` given by the words of the
  letters of a table of `W`.

## Main results

* `TauCeti.GenEq.IsSolutionTable.map`: renaming the letters of a table gives a table of the same
  assignment.
* `TauCeti.GenEq.IsSolutionTable.exists_fin_systemSize`: at most `|S|` letters occur in a table,
  so the letters may be taken in `Fin |S|`.
* `TauCeti.GenEq.IsSolutionTable.substituteVars_wordMap`: the word maps `P_x(U)` of the solution
  spell the reduced word of `W x` for every variable `x` occurring in `r`.
* `TauCeti.GenEq.IsSolutionTable.eval_eq_one`: an assignment with a table is a solution.
* `TauCeti.GenEq.IsSolutionTable.exists_solution`: `Ω_T` has a solution `U` with `P_x(U) = W x`
  graphically for every variable `x` occurring in `r`.

## Implementation notes

A constant occurrence `r_{ij} = a` must have `V_{ij} = a`, so the subword cancelling against it,
which lies in the word of another occurrence, is the letter `a⁻¹` of `A^{±1}` and not a letter of
`Z`. A variable of the system that does not occur in `r` has the empty word map, so `P_x(U) = W(x)`
is asserted for the occurring variables only. Only the letters of `Z` occurring in the table are
required to have nonempty words: a variable sent to `1` has empty words, and the alphabet
`Fin |S|` has unused letters. The solution of `Ω_T` exists for every table spelling `W`; that the
table is a partition table is what makes `W` a solution of the system.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §4.2, Lemma 14 and its proof.
* G. S. Makanin, *Equations in a free group*, Izv. Akad. Nauk SSSR Ser. Mat. 46 (1982).
-/

public section

namespace TauCeti

namespace GenEq

open FreeGroup (substituteVars)

variable {X Z Z' A : Type*}

/-- The table `T`, with the words `u z` over `A^{±1}` for its letters `z`, is a *table of the
assignment* `W` for the system of words `r` (Kharlampovich–Myasnikov, §4.2, proof of Lemma 14):
`T` is a partition table of `r`, substituting the words `u z` into the word `T o` of an occurrence
gives, letter by letter and without free reduction, a reduced word representing the value of that
occurrence under `W`, and the letters occurring in `T` have nonempty words. -/
@[mk_iff]
structure IsSolutionTable (r : List (List ((X ⊕ A) × Bool))) (W : X → FreeGroup A)
    (T : Occurrence r → List ((Z ⊕ A) × Bool)) (u : Z → List (A × Bool)) : Prop where
  /-- The table is a partition table. -/
  isPartitionTable : IsPartitionTable r T
  /-- The word of each occurrence spells a reduced word. -/
  isReduced_substituteVars (o : Occurrence r) : FreeGroup.IsReduced (substituteVars u (T o))
  /-- The word of each occurrence spells the value of that occurrence. -/
  mk_substituteVars (o : Occurrence r) : FreeGroup.mk (substituteVars u (T o)) =
    EqIneqSystem.eval W FreeGroup.of (FreeGroup.mk [r[o.1][o.2]])
  /-- The letters occurring in the table have nonempty words. -/
  ne_nil_of_mem (o : Occurrence r) {z : Z} {b : Bool} (h : (Sum.inl z, b) ∈ T o) : u z ≠ []

variable {r : List (List ((X ⊕ A) × Bool))} {W : X → FreeGroup A}
  {T : Occurrence r → List ((Z ⊕ A) × Bool)} {u : Z → List (A × Bool)}

/-- The letters occurring in a table of an assignment have reduced words. -/
theorem IsSolutionTable.isReduced_of_mem (h : IsSolutionTable r W T u) (o : Occurrence r) {z : Z}
    {b : Bool} (hz : (Sum.inl z, b) ∈ T o) : FreeGroup.IsReduced (u z) :=
  (h.isReduced_substituteVars o).of_substituteVars_of_mem hz

/-- Renaming the letters of `Z` in a table of an assignment gives a table of the same assignment,
for any words of the new letters which agree with the words of the letters occurring in the
table. -/
theorem IsSolutionTable.map (h : IsSolutionTable r W T u) (f : Z → Z') {u' : Z' → List (A × Bool)}
    (hu : ∀ o z b, (Sum.inl z, b) ∈ T o → u' (f z) = u z) :
    IsSolutionTable r W (fun o => (T o).map (Prod.map (Sum.map f id) id)) u' := by
  have hsub (o : Occurrence r) :
      substituteVars u' ((T o).map (Prod.map (Sum.map f id) id)) = substituteVars u (T o) := by
    rw [FreeGroup.substituteVars_map_sumMap, FreeGroup.substituteVars_congr (U := u' ∘ f) (hu o)]
  have hne (o : Occurrence r) {z' : Z'} {b : Bool}
      (hz : (Sum.inl z', b) ∈ (T o).map (Prod.map (Sum.map f id) id)) : u' z' ≠ [] := by
    obtain ⟨⟨z | a, b'⟩, hy, heq⟩ := List.mem_map.1 hz
    · obtain ⟨rfl, rfl⟩ : f z = z' ∧ b' = b := by simpa using heq
      rw [hu o z b' hy]
      exact h.ne_nil_of_mem o hy
    · simp at heq
  have hred (o : Occurrence r) :
      FreeGroup.IsReduced (substituteVars u' ((T o).map (Prod.map (Sum.map f id) id))) := by
    rw [hsub o]
    exact h.isReduced_substituteVars o
  refine ⟨h.isPartitionTable.map f fun o => (hred o).of_substituteVars fun _ _ => hne o,
    hred, fun o => ?_, hne⟩
  rw [hsub o]
  exact h.mk_substituteVars o

/-- The table with empty words is a table of an assignment under which every letter of the system
has the value `1`, with any words for the letters of `Z`. -/
theorem IsSolutionTable.nil
    (h : ∀ o : Occurrence r, EqIneqSystem.eval W FreeGroup.of (FreeGroup.mk [r[o.1][o.2]]) = 1) :
    IsSolutionTable r W (fun _ => []) u where
  isPartitionTable := .nil fun o a ha => by
    obtain ⟨s, hs⟩ : ∃ s, r[o.1][o.2] = (Sum.inr a, s) := ⟨_, Prod.ext ha rfl⟩
    have := h o
    rw [hs, EqIneqSystem.eval_eq_lift, FreeGroup.lift_mk_singleton] at this
    cases s <;> simp at this
  isReduced_substituteVars _ := by simp
  mk_substituteVars o := by rw [h o, FreeGroup.substituteVars_nil, FreeGroup.one_eq_mk]
  ne_nil_of_mem _ _ _ hz := by simp at hz

/-- **Kharlampovich–Myasnikov, §4.2.** At most `|S|` letters occur in a partition table, so a table
of an assignment may be taken with its letters in `Fin |S|`. -/
theorem IsSolutionTable.exists_fin_systemSize (h : IsSolutionTable r W T u) :
    ∃ (T' : Occurrence r → List ((Fin (systemSize r) ⊕ A) × Bool))
      (u' : Fin (systemSize r) → List (A × Bool)), IsSolutionTable r W T' u' := by
  rcases Nat.eq_zero_or_pos (systemSize r) with hn | hn
  · refine ⟨fun _ => [], fun _ => [], .nil fun o => ?_⟩
    rw [← h.mk_substituteVars o, h.isPartitionTable.eq_nil_of_systemSize_eq_zero hn o,
      FreeGroup.substituteVars_nil, FreeGroup.one_eq_mk]
  · obtain ⟨f, hf⟩ := h.isPartitionTable.exists_injOn_fin hn
    refine ⟨_, Function.extend ({z | ∃ o b, (Sum.inl z, b) ∈ T o}.domRestrict f) (fun z => u z)
      fun _ => [], h.map f fun o z b hz => ?_⟩
    exact hf.injective.extend_apply _ _ ⟨z, o, b, hz⟩

/-- In a table of an assignment, the word of each occurrence spells the reduced word of the value
of that occurrence. -/
theorem IsSolutionTable.substituteVars_eq_toWord [DecidableEq A] (h : IsSolutionTable r W T u)
    (o : Occurrence r) : substituteVars u (T o) =
      (EqIneqSystem.eval W FreeGroup.of (FreeGroup.mk [r[o.1][o.2]])).toWord :=
  (h.isReduced_substituteVars o).eq_of_mk_eq FreeGroup.isReduced_toWord <| by
    rw [FreeGroup.mk_toWord, h.mk_substituteVars o]

/-- A table of an assignment is a partition table in which the word of each occurrence spells the
reduced word of the value of that occurrence, and the letters occurring have nonempty words. -/
theorem isSolutionTable_iff_toWord [DecidableEq A] : IsSolutionTable r W T u ↔
    IsPartitionTable r T ∧ (∀ o : Occurrence r, substituteVars u (T o) =
      (EqIneqSystem.eval W FreeGroup.of (FreeGroup.mk [r[o.1][o.2]])).toWord) ∧
    ∀ (o : Occurrence r) {z : Z} {b : Bool}, (Sum.inl z, b) ∈ T o → u z ≠ [] :=
  ⟨fun h => ⟨h.isPartitionTable, h.substituteVars_eq_toWord, h.ne_nil_of_mem⟩,
    fun ⟨hT, hu, hne⟩ => ⟨hT, fun o => hu o ▸ FreeGroup.isReduced_toWord,
      fun o => by rw [hu o, FreeGroup.mk_toWord], hne⟩⟩

/-- In a table of the assignment `W`, the word of an occurrence `x ^ s` of a variable, raised to
the sign `s`, spells the reduced word of `W x`. -/
theorem IsSolutionTable.substituteVars_cond [DecidableEq A] (h : IsSolutionTable r W T u)
    {o : Occurrence r} {x : X} {s : Bool} (hx : r[o.1][o.2] = (Sum.inl x, s)) :
    substituteVars u (cond s (T o) (FreeGroup.invRev (T o))) = (W x).toWord := by
  have hmk := h.mk_substituteVars o
  rw [hx, EqIneqSystem.eval_eq_lift, FreeGroup.lift_mk_singleton] at hmk
  refine FreeGroup.IsReduced.eq_of_mk_eq
    (FreeGroup.isReduced_substituteVars_cond u _ _ (h.isReduced_substituteVars o))
    FreeGroup.isReduced_toWord ?_
  rw [FreeGroup.mk_toWord]
  cases s
  · simpa [FreeGroup.substituteVars_invRev, ← FreeGroup.inv_mk, inv_eq_iff_eq_inv] using hmk
  · simpa using hmk

/-- `IsSolutionTable.substituteVars_cond` for an entry of the table. -/
private theorem IsSolutionTable.substituteVars_cond_of_mem [DecidableEq A]
    (h : IsSolutionTable r W T u) {e : ((X ⊕ A) × Bool) × List ((Z ⊕ A) × Bool)}
    (he : e ∈ tableEntries r T) {x : X} (hx : e.1.1 = Sum.inl x) :
    substituteVars u (cond e.1.2 e.2 (FreeGroup.invRev e.2)) = (W x).toWord := by
  obtain ⟨o, rfl⟩ := mem_tableEntries.1 he
  exact h.substituteVars_cond (Prod.ext hx rfl)

/-- A letter of `Z` carried by an item of the generalised equation of a table occurs in a word of
the table. -/
private theorem exists_mem_of_itemLetter_eq {c : Fin (ofEntries (tableEntries r T)).numItems}
    {z : Z} {s : Bool} (hc : itemLetter (tableEntries r T) c = (Sum.inl z, s)) :
    ∃ o, (Sum.inl z, s) ∈ T o := by
  have : (Sum.inl z, s) ∈ (tableEntries r T).flatMap Prod.snd := by
    rw [← hc, ← map_itemLetter_finRange]
    exact List.mem_map_of_mem (List.mem_finRange c)
  obtain ⟨e, he, hz⟩ := List.mem_flatMap.1 this
  obtain ⟨o, rfl⟩ := mem_tableEntries.1 he
  exact ⟨o, hz⟩

/-- **Kharlampovich–Myasnikov, §4.2, proof of Lemma 14.** The solution `U` of the generalised
equation `Ω_T` of a table `T` of an assignment, given by the words of the letters of the table:
an item carrying `z ^ ±1` gets `(u z) ^ ±1`, and an item carrying a letter of `A^{±1}` gets that
letter. -/
def IsSolutionTable.solution (h : IsSolutionTable r W T u) :
    (ofEntries (tableEntries r T)).Solution :=
  Solution.ofLetterWords (tableEntries r T) u
    (fun _ _ _ hc => (exists_mem_of_itemLetter_eq hc).elim fun o ho => h.isReduced_of_mem o ho)
    (fun _ _ _ hc => (exists_mem_of_itemLetter_eq hc).elim fun o ho => h.ne_nil_of_mem o ho)
    (fun p _ => by
      obtain ⟨o, ho⟩ := mem_tableEntries.1 (List.getElem_mem p.1.isLt)
      rw [Fin.getElem_fin, ← ho]
      exact h.isReduced_substituteVars o)
    (fun p hp => by
      classical
      obtain ⟨-, hl, heq, -⟩ := (isVarPair_iff _).1 hp
      obtain ⟨x, hx⟩ := Sum.isLeft_iff.1 hl
      simp only [Fin.getElem_fin] at hx heq ⊢
      rw [h.substituteVars_cond_of_mem (List.getElem_mem p.1.isLt) hx,
        h.substituteVars_cond_of_mem (List.getElem_mem p.2.isLt) (heq ▸ hx)])

/-- The words of the items of the solution of a table of an assignment are given by
`itemWord`. -/
@[simp]
theorem IsSolutionTable.word_solution (h : IsSolutionTable r W T u) :
    h.solution.word = itemWord (tableEntries r T) u :=
  Solution.word_ofLetterWords ..

/-- **Kharlampovich–Myasnikov, §4.2, proof of Lemma 14.** The word maps send the solution of a
table of the assignment `W` to `W`: `P_x(U)` is the reduced word of `W x` for every variable `x`
occurring in the system. -/
theorem IsSolutionTable.substituteVars_wordMap [DecidableEq A] (h : IsSolutionTable r W T u)
    {o : Occurrence r} {x : X} (hx : r[o.1][o.2].1 = Sum.inl x) :
    substituteVars h.solution.word (wordMap (tableEntries r T) x) = (W x).toWord := by
  obtain ⟨k, hk⟩ := exists_getElem_tableEntries T o
  obtain ⟨k₀, hk₀, hw⟩ := exists_wordMap_eq _ k ((congrArg (·.1.1) hk).trans hx)
  rw [hw, word_solution, substituteVars_itemWord_entry _ u k₀.isLt]
  exact h.substituteVars_cond_of_mem (List.getElem_mem k₀.isLt) hk₀

/-- Under the solution of a table of an assignment, every word map is reduced as written. -/
theorem IsSolutionTable.isReduced_substituteVars_wordMap (h : IsSolutionTable r W T u) (x : X) :
    FreeGroup.IsReduced (substituteVars h.solution.word (wordMap (tableEntries r T) x)) := by
  classical
  by_cases hx : ∀ k : Fin (tableEntries r T).length, (tableEntries r T)[k].1.1 ≠ Sum.inl x
  · rw [wordMap_eq_nil _ hx, FreeGroup.substituteVars_nil]
    exact .nil
  obtain ⟨k, hk⟩ := not_forall_not.1 hx
  obtain ⟨o, ho⟩ := mem_tableEntries.1 (List.getElem_mem k.isLt)
  rw [h.substituteVars_wordMap (o := o) ((congrArg (·.1.1) ho).trans hk)]
  exact FreeGroup.isReduced_toWord

/-- Under the solution of a table of the assignment `W`, the word map of a variable `x` occurring
in the system represents `W x`. -/
theorem IsSolutionTable.mk_substituteVars_wordMap (h : IsSolutionTable r W T u)
    {o : Occurrence r} {x : X} (hx : r[o.1][o.2].1 = Sum.inl x) :
    FreeGroup.mk (substituteVars h.solution.word (wordMap (tableEntries r T) x)) = W x := by
  classical
  rw [h.substituteVars_wordMap hx, FreeGroup.mk_toWord]

/-- An assignment with a table solves the system. -/
theorem IsSolutionTable.eval_eq_one (h : IsSolutionTable r W T u) {w : List ((X ⊕ A) × Bool)}
    (hw : w ∈ r) : EqIneqSystem.eval W FreeGroup.of (FreeGroup.mk w) = 1 := by
  refine (EqIneqSystem.eval_mk_congr FreeGroup.of fun x b hx => ?_).trans
    (h.isPartitionTable.eval_substituteVars_eq_one h.solution hw)
  obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx
  obtain ⟨o, ho⟩ := exists_occurrence_of_mem hw hj
  exact (h.mk_substituteVars_wordMap (o := o) (by rw [ho, hjx])).symm

/-- **Kharlampovich–Myasnikov, §4.2, proof of Lemma 14.** The words of the letters of a table of
the assignment `W` give a solution `U` of the generalised equation of the table, and the word
maps send `U` to `W`: `P_x(U)` is the reduced word of `W x` for every variable `x` occurring in
the system. -/
theorem IsSolutionTable.exists_solution [DecidableEq A] (h : IsSolutionTable r W T u) :
    ∃ U : (ofEntries (tableEntries r T)).Solution, ∀ (o : Occurrence r) (x : X),
      r[o.1][o.2].1 = Sum.inl x →
        substituteVars U.word (wordMap (tableEntries r T) x) = (W x).toWord :=
  ⟨h.solution, fun _ _ => h.substituteVars_wordMap⟩

/-! ### Examples -/

section Examples

/-- The solution `x ↦ 1` of the equation `x = 1` has the table with the empty word. -/
example {X A : Type*} (x : X) (W : X → FreeGroup A) (hW : W x = 1) :
    IsSolutionTable [[(Sum.inl x, true)]] W (fun _ => ([] : List ((Empty ⊕ A) × Bool)))
      Empty.elim :=
  .nil fun ⟨i, j⟩ => by
    fin_cases i
    fin_cases j
    simp [EqIneqSystem.eval_eq_lift, hW]

/-- The equation `x y b⁻¹ a⁻¹ = 1` over `F(a, b)`, with `x = 0`, `y = 1`, `a = 0` and `b = 1`. -/
private abbrev xyEqAB : List (List ((Fin 2 ⊕ Fin 2) × Bool)) :=
  [[(Sum.inl 0, true), (Sum.inl 1, true), (Sum.inr 1, false), (Sum.inr 0, false)]]

/-- The partition table `(a, b, b⁻¹, a⁻¹)` of `x y = a b`, without cancellation. -/
private def xyTable (o : Occurrence xyEqAB) : List ((Fin (systemSize xyEqAB) ⊕ Fin 2) × Bool) :=
  [[(Sum.inr 0, true)], [(Sum.inr 1, true)], [(Sum.inr 1, false)], [(Sum.inr 0, false)]].getD
    o.2.val []

/-- The solution `x = a`, `y = b` of `x y = a b` has the table without cancellation. -/
private theorem isSolutionTable_xyTable :
    IsSolutionTable xyEqAB ![FreeGroup.of 0, FreeGroup.of 1] xyTable fun _ => [] := by
  refine ⟨⟨by unfold FreeGroup.IsReduced; decide, by decide, by decide, by decide, by decide⟩,
    fun o => ?_, fun o => ?_, fun o _ _ hz => ?_⟩
  all_goals
    obtain ⟨i, j⟩ := o
    fin_cases i
    fin_cases j <;>
      simp_all [xyTable, FreeGroup.substituteVars, EqIneqSystem.eval_eq_lift, ← FreeGroup.inv_mk,
        FreeGroup.of]

/-- The solution `x = a`, `y = b` of `x y = a b` comes from the table without cancellation. -/
example : xyTable ∈ cancellationFamily xyEqAB ∧
    ∃ U : (ofEntries (tableEntries xyEqAB xyTable)).Solution,
      substituteVars U.word (wordMap (tableEntries xyEqAB xyTable) 0) = [(0, true)] ∧
        substituteVars U.word (wordMap (tableEntries xyEqAB xyTable) 1) = [(1, true)] := by
  obtain ⟨U, hU⟩ := isSolutionTable_xyTable.exists_solution
  exact ⟨mem_cancellationFamily.2 isSolutionTable_xyTable.isPartitionTable, U,
    by simpa using hU ⟨0, 0, by decide⟩ 0 rfl, by simpa using hU ⟨0, 1, by decide⟩ 1 rfl⟩

/-- The letter `z` of the cancelling segment, the first of the `|S| = 12` letters of a table of
`x y = a b`. -/
private def xyLetter : Fin (systemSize xyEqAB) :=
  ⟨0, by rw [← sum_occurrence_length_sub_one]; decide⟩

/-- The partition table `(a z, z⁻¹ b, b⁻¹, a⁻¹)` of `x y = a b`, with a cancelling segment `z`. -/
private def xyCancelTable (o : Occurrence xyEqAB) :
    List ((Fin (systemSize xyEqAB) ⊕ Fin 2) × Bool) :=
  [[(Sum.inr 0, true), (Sum.inl xyLetter, true)], [(Sum.inl xyLetter, false), (Sum.inr 1, true)],
    [(Sum.inr 1, false)], [(Sum.inr 0, false)]].getD o.2.val []

/-- Every solution `x = a c`, `y = c⁻¹ b` of `x y = a b`, for a nonempty word `c` such that `a c`
and `c⁻¹ b` are reduced, has the table `(a z, z⁻¹ b, b⁻¹, a⁻¹)` with the word `c` for the letter
`z`. -/
private theorem isSolutionTable_xyCancelTable (c : List (Fin 2 × Bool)) (hc₀ : c ≠ [])
    (hx : FreeGroup.IsReduced ((0, true) :: c))
    (hy : FreeGroup.IsReduced (FreeGroup.invRev c ++ [(1, true)])) :
    IsSolutionTable xyEqAB
      ![FreeGroup.mk ((0, true) :: c), FreeGroup.mk (FreeGroup.invRev c ++ [(1, true)])]
      xyCancelTable fun _ => c := by
  refine ⟨⟨by unfold FreeGroup.IsReduced; decide, by decide, by decide, by decide, by decide⟩,
    fun o => ?_, fun o => ?_, fun _ _ _ _ => hc₀⟩
  · obtain ⟨i, j⟩ := o
    fin_cases i
    fin_cases j <;> simp [xyCancelTable, FreeGroup.substituteVars, hx, hy]
  · obtain ⟨i, j⟩ := o
    fin_cases i
    fin_cases j <;>
      simp [xyCancelTable, FreeGroup.substituteVars, EqIneqSystem.eval_eq_lift,
        ← FreeGroup.inv_mk, FreeGroup.of]

/-- Such a solution `x = a c`, `y = c⁻¹ b` comes from the table with a cancelling segment, whose
word maps preserve `c`. -/
example (c : List (Fin 2 × Bool)) (hc₀ : c ≠ []) (hx : FreeGroup.IsReduced ((0, true) :: c))
    (hy : FreeGroup.IsReduced (FreeGroup.invRev c ++ [(1, true)])) :
    xyCancelTable ∈ cancellationFamily xyEqAB ∧
    ∃ U : (ofEntries (tableEntries xyEqAB xyCancelTable)).Solution,
      substituteVars U.word (wordMap (tableEntries xyEqAB xyCancelTable) 0) = (0, true) :: c ∧
      substituteVars U.word (wordMap (tableEntries xyEqAB xyCancelTable) 1) =
        FreeGroup.invRev c ++ [(1, true)] := by
  have h := isSolutionTable_xyCancelTable c hc₀ hx hy
  obtain ⟨U, hU⟩ := h.exists_solution
  refine ⟨mem_cancellationFamily.2 h.isPartitionTable, U, ?_, ?_⟩
  · simpa [FreeGroup.toWord_mk, hx.reduce_eq] using hU ⟨0, 0, by decide⟩ 0 rfl
  · simpa [FreeGroup.toWord_mk, hy.reduce_eq] using hU ⟨0, 1, by decide⟩ 1 rfl

end Examples

end GenEq

end TauCeti

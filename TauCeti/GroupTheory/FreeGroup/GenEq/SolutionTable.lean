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

## Main results

* `TauCeti.GenEq.IsSolutionTable.eval_eq_one`: an assignment with a table is a solution.
* `TauCeti.GenEq.IsSolutionTable.exists_fin_systemSize`: at most `|S|` letters occur in a table,
  so the letters may be taken in `Fin |S|`.
* `TauCeti.GenEq.IsSolutionTable.exists_solution`: the words of the letters give a solution `U`
  of `Ω_T` whose word maps `P_x(U)` spell the reduced word of `W x` for every variable `x`
  occurring in `r`.

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
  (h.isReduced_substituteVars o).of_substituteVars hz

/-- Renaming the letters of `Z` in a table of an assignment, by a map which is injective on the
letters occurring in each word of the table, gives a table of the same assignment, for any words
of the new letters which agree with the words of the letters occurring in the table. -/
private theorem IsSolutionTable.map (h : IsSolutionTable r W T u) (f : Z → Z')
    (hf : ∀ o, Set.InjOn f {z | ∃ b, (Sum.inl z, b) ∈ T o}) {u' : Z' → List (A × Bool)}
    (hu : ∀ o z b, (Sum.inl z, b) ∈ T o → u' (f z) = u z) :
    IsSolutionTable r W (fun o => (T o).map (Prod.map (Sum.map f id) id)) u' where
  isPartitionTable := h.isPartitionTable.map f hf
  isReduced_substituteVars o := by
    rw [FreeGroup.substituteVars_map_sumMap (hu o)]
    exact h.isReduced_substituteVars o
  mk_substituteVars o := by
    rw [FreeGroup.substituteVars_map_sumMap (hu o)]
    exact h.mk_substituteVars o
  ne_nil_of_mem o z' b hz := by
    obtain ⟨⟨z | a, b'⟩, hy, heq⟩ := List.mem_map.1 hz
    · obtain ⟨rfl, rfl⟩ : f z = z' ∧ b' = b := by simpa using heq
      rw [hu o z b' hy]
      exact h.ne_nil_of_mem o hy
    · simp at heq

/-- If words over `A^{±1}` spell the values of the letters of a word in the variables and
constants, their concatenation spells the value of the word. -/
private theorem eval_mk_map_fst (R : List (((X ⊕ A) × Bool) × List ((Z ⊕ A) × Bool)))
    (hR : ∀ e ∈ R, FreeGroup.mk (substituteVars u e.2) =
      EqIneqSystem.eval W FreeGroup.of (FreeGroup.mk [e.1])) :
    EqIneqSystem.eval W FreeGroup.of (FreeGroup.mk (R.map Prod.fst)) =
      FreeGroup.mk (substituteVars u (R.flatMap Prod.snd)) := by
  induction R with
  | nil => simp [← FreeGroup.one_eq_mk]
  | cons e R ih =>
    have hmk : FreeGroup.mk (e.1 :: R.map Prod.fst) =
        FreeGroup.mk [e.1] * FreeGroup.mk (R.map Prod.fst) := by
      rw [FreeGroup.mul_mk, List.singleton_append]
    simp [hmk, ← FreeGroup.mul_mk, hR e List.mem_cons_self,
      ih fun e he => hR e (List.mem_cons_of_mem _ he)]

/-- An assignment with a table solves the system. -/
theorem IsSolutionTable.eval_eq_one (h : IsSolutionTable r W T u) {w : List ((X ⊕ A) × Bool)}
    (hw : w ∈ r) : EqIneqSystem.eval W FreeGroup.of (FreeGroup.mk w) = 1 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
  set R := (List.finRange r[(⟨i, hi⟩ : Fin r.length)].length).map fun j =>
    (r[(⟨i, hi⟩ : Fin r.length)][j], T ⟨⟨i, hi⟩, j⟩) with hR
  have := eval_mk_map_fst (W := W) (u := u) R fun e he => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 he
    exact h.mk_substituteVars ⟨⟨i, hi⟩, j⟩
  have hfst : R.map Prod.fst = r[i] := by
    simp [hR, Function.comp_def, List.map_getElem_finRange]
  have hsnd : FreeGroup.mk (R.flatMap Prod.snd) = 1 := by
    simpa [hR, List.flatMap_map] using h.isPartitionTable.mk_flatMap_eq_one ⟨i, hi⟩
  rwa [hfst, FreeGroup.mk_substituteVars, hsnd, map_one] at this

/-- A table of an assignment all of whose words are empty stays one with any alphabet of letters
and any words for them. -/
private theorem IsSolutionTable.of_forall_eq_nil (h : IsSolutionTable r W T u) (hT : ∀ o, T o = [])
    (u' : Z' → List (A × Bool)) :
    IsSolutionTable r W (fun _ => ([] : List ((Z' ⊕ A) × Bool))) u' where
  isPartitionTable :=
    { isReduced _ := .nil
      mk_flatMap_eq_one i := by rw [List.flatMap_eq_nil_iff.2 fun _ _ => rfl, FreeGroup.one_eq_mk]
      length_le _ := by simp
      eq_of_eq_inr o a ha := by simpa [hT o] using h.isPartitionTable.eq_of_eq_inr o ha
      eq_nil_iff _ _ _ := Iff.rfl }
  isReduced_substituteVars _ := by simp
  mk_substituteVars o := by simpa [hT o] using h.mk_substituteVars o
  ne_nil_of_mem _ _ _ hz := by simp at hz

/-- **Kharlampovich–Myasnikov, §4.2.** At most `|S|` letters occur in a partition table, so a table
of an assignment may be taken with its letters in `Fin |S|`. -/
theorem IsSolutionTable.exists_fin_systemSize (h : IsSolutionTable r W T u) :
    ∃ (T' : Occurrence r → List ((Fin (systemSize r) ⊕ A) × Bool))
      (u' : Fin (systemSize r) → List (A × Bool)), IsSolutionTable r W T' u' := by
  rcases Nat.eq_zero_or_pos (systemSize r) with hn | hn
  · exact ⟨fun _ => [], fun _ => [],
      h.of_forall_eq_nil (h.isPartitionTable.eq_nil_of_systemSize_eq_zero hn) _⟩
  · obtain ⟨f, hf⟩ := h.isPartitionTable.exists_injOn_fin hn
    have hf' (o : Occurrence r) : Set.InjOn f {z | ∃ b, (Sum.inl z, b) ∈ T o} :=
      fun _ hz _ hz' hzz' => hf ⟨o, hz⟩ ⟨o, hz'⟩ hzz'
    refine ⟨_, Function.extend ({z | ∃ o b, (Sum.inl z, b) ∈ T o}.domRestrict f) (fun z => u z)
      fun _ => [], h.map f hf' fun o z b hz => ?_⟩
    exact hf.injective.extend_apply _ _ ⟨z, o, b, hz⟩

variable [DecidableEq A]

/-- In a table of the assignment `W`, the word of an occurrence of the variable `x`, raised to the
sign of the occurrence, spells the reduced word of `W x`. -/
private theorem IsSolutionTable.substituteVars_cond (h : IsSolutionTable r W T u)
    {e : ((X ⊕ A) × Bool) × List ((Z ⊕ A) × Bool)} (he : e ∈ tableEntries r T) {x : X}
    (hx : e.1.1 = Sum.inl x) :
    substituteVars u (cond e.1.2 e.2 (FreeGroup.invRev e.2)) = (W x).toWord := by
  obtain ⟨o, rfl⟩ := mem_tableEntries.1 he
  obtain ⟨s, hs⟩ : ∃ s, r[o.1][o.2] = (Sum.inl x, s) := ⟨_, Prod.ext hx rfl⟩
  have hmk := h.mk_substituteVars o
  rw [hs, EqIneqSystem.eval_eq_lift, FreeGroup.lift_mk_singleton] at hmk
  refine FreeGroup.IsReduced.eq_of_mk_eq
    (FreeGroup.isReduced_substituteVars_cond u _ _ (h.isReduced_substituteVars o))
    FreeGroup.isReduced_toWord ?_
  rw [FreeGroup.mk_toWord, hs]
  cases s
  · simpa [FreeGroup.substituteVars_invRev, ← FreeGroup.inv_mk, inv_eq_iff_eq_inv] using hmk
  · simpa using hmk

/-- **Kharlampovich–Myasnikov, §4.2, proof of Lemma 14.** The words of the letters of a table of
the assignment `W` give a solution `U` of the generalised equation of the table, and the word
maps send `U` to `W`: `P_x(U)` is the reduced word of `W x` for every variable `x` occurring in
the system. -/
theorem IsSolutionTable.exists_solution (h : IsSolutionTable r W T u) :
    ∃ U : (ofEntries (tableEntries r T)).Solution, ∀ (o : Occurrence r) (x : X),
      r[o.1][o.2].1 = Sum.inl x →
        substituteVars U.word (wordMap (tableEntries r T) x) = (W x).toWord := by
  have hmem : ∀ c z s, itemLetter (tableEntries r T) c = (Sum.inl z, s) →
      ∃ o, (Sum.inl z, s) ∈ T o := by
    intro c z s hc
    have : (Sum.inl z, s) ∈ (tableEntries r T).flatMap Prod.snd := by
      rw [← hc, ← map_itemLetter_finRange]
      exact List.mem_map_of_mem (List.mem_finRange c)
    obtain ⟨e, he, hz⟩ := List.mem_flatMap.1 this
    obtain ⟨o, rfl⟩ := mem_tableEntries.1 he
    exact ⟨o, hz⟩
  refine ⟨Solution.ofLetterWords (tableEntries r T) u
    (fun c z s hc => (hmem c z s hc).elim fun o ho => h.isReduced_of_mem o ho)
    (fun c z s hc => (hmem c z s hc).elim fun o ho => h.ne_nil_of_mem o ho)
    (fun p _ => ?_) (fun p hp => ?_), fun o x hx => ?_⟩
  · obtain ⟨o, ho⟩ := mem_tableEntries.1 (List.getElem_mem p.1.isLt)
    rw [Fin.getElem_fin, ← ho]
    exact h.isReduced_substituteVars o
  · obtain ⟨-, hl, heq, -⟩ := (isVarPair_iff _).1 hp
    obtain ⟨x, hx⟩ := Sum.isLeft_iff.1 hl
    simp only [Fin.getElem_fin] at hx heq ⊢
    rw [h.substituteVars_cond (List.getElem_mem p.1.isLt) hx,
      h.substituteVars_cond (List.getElem_mem p.2.isLt) (heq ▸ hx)]
  · obtain ⟨k, hk⟩ := exists_getElem_tableEntries T o
    obtain ⟨k₀, hk₀, hw⟩ := exists_wordMap_eq _ k ((congrArg (·.1.1) hk).trans hx)
    rw [hw, Solution.word_ofLetterWords, substituteVars_itemWord_entry _ u k₀.isLt]
    exact h.substituteVars_cond (List.getElem_mem k₀.isLt) hk₀

/-! ### Examples -/

section Examples

/-- The solution `x ↦ 1` of the equation `x = 1` has the table with the empty word. -/
example {X A : Type*} (x : X) (W : X → FreeGroup A) (hW : W x = 1) :
    IsSolutionTable [[(Sum.inl x, true)]] W (fun _ => ([] : List ((Empty ⊕ A) × Bool)))
      Empty.elim := by
  refine ⟨⟨fun _ => .nil, fun i => ?_, fun _ => by simp, fun o a ha => ?_, fun _ _ _ => Iff.rfl⟩,
    fun _ => by simp, fun o => ?_, fun _ _ _ hz => by simp at hz⟩
  · rw [List.flatMap_eq_nil_iff.2 fun _ _ => rfl, FreeGroup.one_eq_mk]
  · obtain ⟨i, j⟩ := o
    fin_cases i
    fin_cases j
    simp at ha
  · obtain ⟨i, j⟩ := o
    fin_cases i
    fin_cases j
    simp [EqIneqSystem.eval_eq_lift, hW, FreeGroup.one_eq_mk]

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

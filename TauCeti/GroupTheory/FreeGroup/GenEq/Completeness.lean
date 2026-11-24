/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.SolutionTable
import Mathlib.Algebra.BigOperators.Fin
import TauCeti.GroupTheory.FreeGroup.Cancellation

/-!
# Every solution comes from the cancellation family

Let `r` be a finite system of equations over the free group `F(A)`, written as words
`r_{i1} ⋯ r_{il_i}` in the letters of `X^{±1} ∪ A^{±1}`, and let `W : X → F(A)` be a solution.
Substituting the reduced words of the values of `W` turns the `i`-th equation into a product of
reduced blocks `r_{i1}^W ⋯ r_{il_i}^W` which is trivial in `F(A)`. Fixing a process of free
reductions, each block is graphically a product of the maximal nonempty subwords that cancel
against a single other block of the same equation (`TauCeti.exists_cancellationPieces`). Naming
these pieces by new letters, equation by equation, writes the blocks as the words `V_{ij}` of a
table of the assignment `W` (`TauCeti.GenEq.IsSolutionTable`).

Hence the reduction of a system of equations to generalised equations is complete: every solution
`W` is `P(U)`, graphically, for a solution `U` of the generalised equation `Ω_T` of a partition
table `T` with its letters in `Fin |S|` (Kharlampovich–Myasnikov, Lemma 14(3)), and a system with
an empty cancellation family has no solution in `F(A)` (Lemma 14(1)).

## Main results

* `TauCeti.GenEq.exists_isSolutionTable`: every solution of a system of equations has a table.
* `TauCeti.GenEq.exists_solution_wordMap_eq`: **Lemma 14(3)**, every solution `W` is `P(U)` for
  a partition table `T` with letters in `Fin |S|` and a solution `U` of `Ω_T`.
* `TauCeti.GenEq.exists_eval_ne_one_of_cancellationFamily_eq_empty`: **Lemma 14(1)**, a system
  with an empty cancellation family has no solution.

## Implementation notes

A constant occurrence `r_{ij} = a` has the one-letter block `a`, which is a single piece; a
partition table must have `V_{ij} = a`, so this piece is written as the letter `a` of `A^{±1}`
at both of its occurrences, keeping the product of the words of each equation trivial. Here
every piece which is a single letter of `A^{±1}` is written as that letter.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §4.2, Lemma 14 and its proof.
* G. S. Makanin, *Equations in a free group*, Izv. Akad. Nauk SSSR Ser. Mat. 46 (1982).
-/

public section

namespace TauCeti

namespace GenEq

open FreeGroup (substituteLetter substituteVars)

variable {X Z Z' A : Type*}

/-! ### Tables spelling the reduced words of a solution -/

section Spelling

variable [DecidableEq A] {r : List (List ((X ⊕ A) × Bool))} {W : X → FreeGroup A}
  {T : Occurrence r → List ((Z ⊕ A) × Bool)} {u : Z → List (A × Bool)}

/-- The blocks `r_{i1}^W, …, r_{il}^W` of a word `r_{i1} ⋯ r_{il}` under the assignment `W`: the
reduced words of the values of its letters. -/
private def blocks (W : X → FreeGroup A) (w : List ((X ⊕ A) × Bool)) : List (List (A × Bool)) :=
  w.map fun y => substituteVars (fun x => (W x).toWord) [y]

@[simp]
private theorem length_blocks (w : List ((X ⊕ A) × Bool)) : (blocks W w).length = w.length :=
  List.length_map _

private theorem getElem_blocks (w : List ((X ⊕ A) × Bool)) {j : ℕ} (hj : j < (blocks W w).length) :
    (blocks W w)[j] = substituteVars (fun x => (W x).toWord) [w[j]'(by simpa using hj)] :=
  List.getElem_map _

/-- The product of the blocks of a word under `W` is the value of the word at `W`. -/
private theorem mk_flatten_blocks (w : List ((X ⊕ A) × Bool)) :
    FreeGroup.mk (blocks W w).flatten = EqIneqSystem.eval W FreeGroup.of (FreeGroup.mk w) := by
  simpa [blocks, FreeGroup.substituteVars, List.flatMap_def, FreeGroup.mk_toWord] using
    (EqIneqSystem.eval_mk_eq_mk_substituteVars (fun x => (W x).toWord) w).symm

/-- The blocks of a word are reduced. -/
private theorem isReduced_of_mem_blocks {w : List ((X ⊕ A) × Bool)} {b : List (A × Bool)}
    (hb : b ∈ blocks W w) : FreeGroup.IsReduced b := by
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hb
  exact FreeGroup.isReduced_substituteVars_singleton fun _ _ => FreeGroup.isReduced_toWord

/-- A table spelling, letter by letter, the blocks of the occurrences under `W`, with nonempty
words for its letters, whose equations have trivial products, whose words are short and which keeps
the constant occurrences, is a table of the assignment `W`. -/
private theorem isSolutionTable_of_substituteVars_eq (hu : ∀ z, u z ≠ [])
    (hmk : ∀ i : Fin r.length,
      FreeGroup.mk ((List.finRange r[i].length).flatMap fun j => T ⟨i, j⟩) = 1)
    (hlen : ∀ o, (T o).length ≤ r[o.1].length - 1)
    (hinr : ∀ (o : Occurrence r) (a : A) (s : Bool), r[o.1][o.2] = (Sum.inr a, s) →
      T o = [(Sum.inr a, s)])
    (hsub : ∀ o, substituteVars u (T o) = substituteVars (fun x => (W x).toWord) [r[o.1][o.2]]) :
    IsSolutionTable r W T u := by
  -- The letters of `Z` and of `A^{±1}` are all replaced by nonempty words.
  have hf (o : Occurrence r) : ∀ y ∈ T o, Sum.elim u (fun a => [(a, true)]) y.1 ≠ [] := by
    rintro ⟨z | a, b⟩ - <;> simp [hu]
  have hred o : FreeGroup.IsReduced (substituteVars u (T o)) :=
    hsub o ▸ FreeGroup.isReduced_substituteVars_singleton fun _ _ => FreeGroup.isReduced_toWord
  have hnil (o : Occurrence r) :
      T o = [] ↔ Sum.elim (fun x => (W x).toWord) (fun a => [(a, true)]) r[o.1][o.2].1 = [] := by
    rw [← FreeGroup.flatMap_substituteLetter_eq_nil_iff (hf o), ← substituteVars, hsub,
      substituteVars, List.flatMap_singleton, FreeGroup.substituteLetter]
    cases r[o.1][o.2].2 <;> simp [FreeGroup.invRev]
  refine ⟨⟨fun o => (hred o).of_flatMap_substituteLetter (hf o),
    hmk, hlen, fun o a h => hinr o a _ (Prod.ext h rfl), fun o o' h => by rw [hnil, hnil, h]⟩, hred,
    fun o => by
      rw [hsub, ← EqIneqSystem.eval_mk_eq_mk_substituteVars]
      simp only [FreeGroup.mk_toWord],
    fun _ z _ _ => hu z⟩

end Spelling

/-! ### Naming the cancellation pieces -/

section Pieces

/-- The one-letter word naming the piece `z` in a table: the letter `a ^ s` of `A^{±1}` if the
piece is that single letter, and the letter `e z` otherwise. -/
private def pieceLetter (piece : Z → List (A × Bool)) (e : Z → Z') (z : Z) :
    List ((Z' ⊕ A) × Bool) :=
  match piece z with
  | [a] => [(Sum.inr a.1, a.2)]
  | _ => [(Sum.inl (e z), true)]

variable {piece : Z → List (A × Bool)} {e : Z → Z'}

/-- Each letter of a word over `Z^{±1}` is named by one letter. -/
private theorem length_substituteLetter_pieceLetter (y : Z × Bool) :
    (substituteLetter (pieceLetter piece e) y).length = 1 := by
  obtain ⟨z, _ | _⟩ := y <;> simp only [FreeGroup.substituteLetter_true,
    FreeGroup.substituteLetter_false, FreeGroup.invRev_length] <;> unfold pieceLetter <;> split <;>
    rfl

/-- Naming the pieces and substituting their words spells the substitution of the pieces. -/
private theorem substituteVars_flatMap_pieceLetter {u : Z' → List (A × Bool)}
    (hu : ∀ z, u (e z) = piece z) (V : List (Z × Bool)) :
    substituteVars u (V.flatMap (substituteLetter (pieceLetter piece e))) =
      V.flatMap (substituteLetter piece) := by
  have h₁ (z : Z) : substituteVars u (pieceLetter piece e z) = piece z := by
    unfold pieceLetter
    split <;> simp_all
  simp only [substituteVars] at h₁ ⊢
  rw [List.flatMap_assoc]
  refine List.flatMap_congr fun ⟨z, b⟩ _ => ?_
  cases b <;> simp [FreeGroup.flatMap_substituteLetter_invRev, h₁]

/-- A word over `Z^{±1}` spelling a single letter of `A^{±1}` is named by that letter. -/
private theorem flatMap_pieceLetter_eq_singleton (hpiece : ∀ z, piece z ≠ []) {V : List (Z × Bool)}
    {a : A} {s : Bool} (h : V.flatMap (substituteLetter piece) = [(a, s)]) :
    V.flatMap (substituteLetter (pieceLetter piece e)) = [(Sum.inr a, s)] := by
  have hne (y : Z × Bool) : substituteLetter piece y ≠ [] := by
    obtain ⟨z, _ | _⟩ := y <;> simp [FreeGroup.invRev, hpiece]
  obtain _ | ⟨⟨z, b⟩, V⟩ := V
  · simp at h
  rw [List.flatMap_cons, List.append_eq_singleton_iff] at h
  rcases h with ⟨h₁, -⟩ | ⟨h₁, h₂⟩
  · exact absurd h₁ (hne _)
  obtain rfl : V = [] := (FreeGroup.flatMap_substituteLetter_eq_nil_iff fun y _ => hpiece y.1).1 h₂
  obtain ⟨c, hc⟩ : ∃ c, piece z = [c] := List.length_eq_one_iff.1 (by
    have := congrArg List.length h₁
    cases b <;> simpa [FreeGroup.invRev_length] using this)
  have hρ : pieceLetter piece e z = [(Sum.inr c.1, c.2)] := by simp [pieceLetter, hc]
  cases b <;> simp_all [FreeGroup.invRev]

variable [DecidableEq A] {r : List (List ((X ⊕ A) × Bool))} {W : X → FreeGroup A}
  {Y : Fin r.length → Type*}

/-- **Kharlampovich–Myasnikov, §4.2, proof of Lemma 14.** Cancellation pieces of the blocks of
each equation under `W`, named by `e` and written as letters of `A^{±1}` when they are single
letters, give a table of the assignment `W`. -/
private theorem isSolutionTable_flatMap_pieceLetter
    (P : ∀ i, CancellationPieces (blocks W r[i]) (Y i)) (e : (Σ i, Y i) → Z')
    {u : Z' → List (A × Bool)} (hu : ∀ i y, u (e ⟨i, y⟩) = (P i).piece y) (hu₀ : ∀ z, u z ≠ []) :
    IsSolutionTable r W (fun o => ((P o.1).patterns[(o.2 : ℕ)]'(by simp)).flatMap
      (substituteLetter (pieceLetter (P o.1).piece fun y => e ⟨o.1, y⟩))) u := by
  have hblock (o : Occurrence r) : ((P o.1).patterns[(o.2 : ℕ)]'(by simp)).flatMap
      (substituteLetter (P o.1).piece) = substituteVars (fun x => (W x).toWord) [r[o.1][o.2]] := by
    simp [getElem_blocks]
  refine isSolutionTable_of_substituteVars_eq hu₀ (fun i => ?_) (fun o => ?_) (fun o a s ha => ?_)
    (fun o => by rw [substituteVars_flatMap_pieceLetter (hu o.1), hblock])
  · -- The words of an equation are those of its cancellation pieces, renamed letter by letter.
    have hrow : (List.finRange r[i].length).flatMap
        (fun j : Fin r[i].length => (P i).patterns[(j : ℕ)]'(by simp)) =
        (P i).patterns.flatten := by
      rw [List.flatMap_def]
      congr 1
      exact List.ext_getElem (by simp) fun n _ _ => by simp
    have := congrArg (fun L => FreeGroup.mk
      (L.flatMap (substituteLetter (pieceLetter (P i).piece fun y => e ⟨i, y⟩)))) hrow
    simpa only [List.flatMap_assoc, FreeGroup.mk_flatMap_substituteLetter,
      (P i).mk_flatten_patterns, map_one] using this
  · simpa [List.length_flatMap, length_substituteLetter_pieceLetter] using
      (P o.1).length_le_of_mem_patterns (List.getElem_mem _)
  · refine flatMap_pieceLetter_eq_singleton (P o.1).piece_ne_nil ?_
    rw [hblock, ha, FreeGroup.substituteVars_singleton_inr]

end Pieces

/-! ### Completeness -/

/-- **Kharlampovich–Myasnikov, §4.2, proof of Lemma 14.** Every solution `W` of a system of
equations `r` over `F(A)` has a table: a partition table `T` of `r` with letters in some `Fin p`,
and words `u` for its letters, such that substituting `u` into the word of each occurrence spells,
without free reduction, the reduced word of the value of that occurrence under `W`. -/
theorem exists_isSolutionTable {r : List (List ((X ⊕ A) × Bool))} {W : X → FreeGroup A}
    (h : ∀ w ∈ r, EqIneqSystem.eval W FreeGroup.of (FreeGroup.mk w) = 1) :
    ∃ (p : ℕ) (T : Occurrence r → List ((Fin p ⊕ A) × Bool)) (u : Fin p → List (A × Bool)),
      IsSolutionTable r W T u := by
  classical
  -- Fix cancellation pieces of the blocks of each equation, and name all of them by the letters
  -- of one alphabet.
  choose p hp using fun i : Fin r.length => exists_cancellationPieces
    (fun _ => isReduced_of_mem_blocks) ((mk_flatten_blocks r[i]).trans (h _ (List.getElem_mem _)))
  obtain ⟨P⟩ : Nonempty (∀ i, CancellationPieces (blocks W r[i]) (Fin (p i))) :=
    ⟨fun i => (hp i).some⟩
  obtain ⟨σ⟩ : Nonempty ((Σ i, Fin (p i)) ≃ Fin (∑ i, p i)) := ⟨finSigmaFinEquiv⟩
  let piece (q : Σ i, Fin (p i)) : List (A × Bool) := (P q.1).piece q.2
  exact ⟨_, _, _, isSolutionTable_flatMap_pieceLetter P σ (u := piece ∘ σ.symm)
    (fun i y => congrArg piece (σ.symm_apply_apply ⟨i, y⟩)) fun _ => (P _).piece_ne_nil _⟩

/-- **Kharlampovich–Myasnikov, Lemma 14(3).** For every solution `W` of a system of equations `r`
over `F(A)` there are a partition table `T` of `r` with its letters in `Fin |S|` (a member of the
cancellation family when `A` is finite) and a solution `U` of its generalised equation such that
`W = P(U)`, graphically: `P_x(U)` is the reduced word of `W x` for every variable `x` occurring in
`r`. -/
theorem exists_solution_wordMap_eq [DecidableEq A] {r : List (List ((X ⊕ A) × Bool))}
    {W : X → FreeGroup A} (h : ∀ w ∈ r, EqIneqSystem.eval W FreeGroup.of (FreeGroup.mk w) = 1) :
    ∃ T : Occurrence r → List ((Fin (systemSize r) ⊕ A) × Bool), IsPartitionTable r T ∧
      ∃ U : (ofEntries (tableEntries r T)).Solution, ∀ (o : Occurrence r) (x : X),
        r[o.1][o.2].1 = Sum.inl x →
          substituteVars U.word (wordMap (tableEntries r T) x) = (W x).toWord := by
  obtain ⟨p, T, u, hT⟩ := exists_isSolutionTable h
  obtain ⟨T', u', hT'⟩ := hT.exists_fin_systemSize
  exact ⟨T', hT'.isPartitionTable, hT'.solution, fun _ _ => hT'.substituteVars_wordMap⟩

/-- **Kharlampovich–Myasnikov, Lemma 14(1).** A system of equations over `F(A)` whose cancellation
family is empty has no solution in `F(A)`: every assignment violates one of its equations. -/
theorem exists_eval_ne_one_of_cancellationFamily_eq_empty [Finite A]
    {r : List (List ((X ⊕ A) × Bool))} (h : cancellationFamily r = ∅) (W : X → FreeGroup A) :
    ∃ w ∈ r, EqIneqSystem.eval W FreeGroup.of (FreeGroup.mk w) ≠ 1 := by
  classical
  by_contra! hW
  obtain ⟨T, hT, -⟩ := exists_solution_wordMap_eq hW
  simpa [h] using mem_cancellationFamily.2 hT

/-! ### Examples -/

section Examples

/-- The constant equation `a = 1` has no partition table, hence an empty cancellation family: the
word of the occurrence of `a` would have length at most `0`. -/
private theorem cancellationFamily_singleton_inr {X A : Type*} [Finite A] (a : A) :
    cancellationFamily ([[(Sum.inr a, true)]] : List (List ((X ⊕ A) × Bool))) = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun T hT => ?_
  have hT := mem_cancellationFamily.1 hT
  have := hT.length_le ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩
  rw [hT.eq_of_eq_inr _ rfl] at this
  simp at this

/-- The equation `a = 1` has no solution, by Lemma 14(1). -/
example {X A : Type*} [Finite A] (a : A) (W : X → FreeGroup A) :
    ∃ w ∈ ([[(Sum.inr a, true)]] : List (List ((X ⊕ A) × Bool))),
      EqIneqSystem.eval W FreeGroup.of (FreeGroup.mk w) ≠ 1 :=
  exists_eval_ne_one_of_cancellationFamily_eq_empty (cancellationFamily_singleton_inr a) W

end Examples

end GenEq

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.GroupTheory.FreeGroup.Substitution
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import TauCeti.GroupTheory.FreeGroup.Reduce

/-!
# Cancellation pieces of a trivial product of reduced words

Let `w₀, …, w_{l-1}` be reduced words over `α^{±1}` whose product is trivial in `FreeGroup α`.
Fixing a process of free reductions of `w₀ ⋯ w_{l-1}` to the empty word, every `wⱼ` cancels
completely, and it is graphically a product of the maximal nonempty subwords that cancel against a
single other block. Naming these subwords by fresh letters `z ∈ Z` writes each `wⱼ` as a word
`Vⱼ` over `Z^{±1}` (`TauCeti.CancellationPieces`):

* `wⱼ` is the substitution of the pieces into `Vⱼ`, letter by letter and without free
  reduction;
* every signed letter of `Z^{±1}` occurs exactly once in `V₀ ⋯ V_{l-1}`, and no letter of `Z`
  occurs twice in one `Vⱼ` (a block does not cancel with itself);
* the product `V₀ ⋯ V_{l-1}` is trivial in `FreeGroup Z`;
* two distinct blocks exchange at most one piece.

Consequently each `Vⱼ` is reduced and has length at most `l - 1`, and there are at most
`l (l - 1) / 2` pieces. This is the combinatorial core of Makanin's reduction of equations over
free groups to generalised equations: the words `Vⱼ` of one equation form a row of a partition
table, and the pieces are a solution of the associated generalised equation.

The pieces are built along the reduction process: the first free reduction of the product cancels
the last letter of a block against the first letter of the next nonempty block; it either
lengthens the piece already exchanged between these two blocks or starts a new one. That a new
piece never joins two blocks that already exchange one is the non-crossing property of free
reductions (`FreeGroup.mk_eq_one_of_mk_append_cons_append_cons_eq_one`).

## Main definitions and results

* `TauCeti.CancellationPieces ws Z`: pieces indexed by `Z` and the words `Vⱼ` for the list
  `ws` of blocks.
* `TauCeti.exists_cancellationPieces`: a list of reduced words with trivial product has
  cancellation pieces indexed by some `Fin p`.
* `TauCeti.CancellationPieces.length_le_of_mem_patterns`: `|Vⱼ| ≤ l - 1`.
* `TauCeti.CancellationPieces.card_le`: at most `l (l - 1) / 2` pieces.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §4.2, proof of Lemma 14 and the definition of partition tables.
* G. S. Makanin, *Equations in a free group*, Izv. Akad. Nauk SSSR Ser. Mat. 46 (1982).
-/

public section

namespace FreeGroup

variable {α : Type*}

/-- **Non-crossing of free reductions.** If the generator `x` occurs in the trivial word
`P (x, b) M (x, !b) Q` only at the two displayed positions, then the subword `M` between them is
trivial. -/
theorem mk_eq_one_of_mk_append_cons_append_cons_eq_one {P M Q : List (α × Bool)} {x : α} {b : Bool}
    (hP : x ∉ P.map Prod.fst) (hM : x ∉ M.map Prod.fst) (hQ : x ∉ Q.map Prod.fst)
    (h : mk (P ++ (x, b) :: (M ++ (x, !b) :: Q)) = 1) : mk M = 1 := by
  classical
  by_contra hM₁
  -- Otherwise the reduced word `(x, b) R (x, !b)` of `x^b M x^-b`, with `R` the reduced word of
  -- `M`, would be the reduced word of `P⁻¹ Q⁻¹`, which does not contain `x`.
  set R := (mk M).toWord with hR
  have hRM : R.Sublist M := by rw [hR, toWord_mk]; exact reduce.red.sublist
  have hR₀ : R ≠ [] := fun h₀ => hM₁ (by rw [← mk_toWord (x := mk M), ← hR, h₀, one_eq_mk])
  have hxR : x ∉ R.map Prod.fst := fun hx => hM ((hRM.map _).subset hx)
  have hmk : mk ([(x, b)] ++ R ++ invRev [(x, b)]) = mk (invRev P ++ invRev Q) := by
    have hC : mk ([(x, b)] ++ R ++ invRev [(x, b)]) = mk ([(x, b)] ++ M ++ [(x, !b)]) := by
      rw [← mul_mk, ← mul_mk, ← mul_mk, ← mul_mk, hR, mk_toWord]
      simp [invRev]
    have h' : mk P * mk ([(x, b)] ++ R ++ invRev [(x, b)]) * mk Q = 1 := by
      rw [hC, ← h]
      simp
    have hPQ : (mk P)⁻¹ * (mk Q)⁻¹ = mk (invRev P ++ invRev Q) := by
      rw [inv_mk, inv_mk, mul_mk]
    rw [← hPQ]
    exact eq_inv_mul_of_mul_eq (eq_inv_of_mul_eq_one_left h')
  have hsub := (reduce.red (L := invRev P ++ invRev Q)).sublist
  rw [← reduce.sound hmk, (isReduced_toWord.singleton_append_append_invRev hR₀ hxR).reduce_eq]
    at hsub
  have hmem := hsub.subset (List.mem_append_left _ (List.mem_append_left _
    (List.mem_singleton_self (x, b))))
  simp only [invRev, List.mem_append, List.mem_reverse, List.mem_map, Prod.mk.injEq] at hmem
  rcases hmem with ⟨a, ha, rfl, -⟩ | ⟨a, ha, rfl, -⟩
  exacts [hP (List.mem_map_of_mem ha), hQ (List.mem_map_of_mem ha)]

/-- In a list of reduced words whose concatenation contains a letter followed by its inverse,
the letter ends one of the words and its inverse begins the next nonempty word. -/
theorem exists_eq_append_cons_append_cons_of_flatten_eq {ws : List (List (α × Bool))}
    (hws : ∀ w ∈ ws, IsReduced w) {L₁ L₂ : List (α × Bool)} {x : α} {b : Bool}
    (h : ws.flatten = L₁ ++ (x, b) :: (x, !b) :: L₂) :
    ∃ pre w₁ mid w₂ post, ws = pre ++ (w₁ ++ [(x, b)]) :: (mid ++ ((x, !b) :: w₂) :: post) ∧
      ∀ w ∈ mid, w = [] := by
  induction ws generalizing L₁ with
  | nil => simp at h
  | cons w ws ih =>
    have hws' : ∀ w ∈ ws, IsReduced w := fun w hw => hws w (List.mem_cons_of_mem _ hw)
    rw [List.flatten_cons, List.append_eq_append_iff] at h
    rcases h with ⟨as, rfl, h⟩ | ⟨bs, rfl, h⟩
    · obtain ⟨pre, w₁, mid, w₂, post, rfl, hmid⟩ := ih hws' h
      exact ⟨w :: pre, w₁, mid, w₂, post, rfl, hmid⟩
    · rcases bs with _ | ⟨c, _ | ⟨d, bs⟩⟩
      · -- The pair lies in the later words.
        obtain ⟨pre, w₁, mid, w₂, post, rfl, hmid⟩ := ih (L₁ := []) hws' (by simpa using h.symm)
        exact ⟨(L₁ ++ []) :: pre, w₁, mid, w₂, post, rfl, hmid⟩
      · -- The letter ends `w`; its inverse begins the next nonempty word.
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
        obtain ⟨rfl, h⟩ := h
        obtain ⟨mid, w₂, post, rfl, hmid, -⟩ := List.flatten_eq_cons_iff.1 h.symm
        exact ⟨[], L₁, mid, w₂, post, rfl, hmid⟩
      · -- The pair would lie inside the reduced word `w`.
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        have hw := (hws _ List.mem_cons_self).infix (L₁ := [(x, b), (x, !b)]) ⟨L₁, bs, by simp⟩
        simp [isReduced_cons_cons] at hw

end FreeGroup

namespace TauCeti

open FreeGroup

variable {α Z Z' : Type*}

/-- **Cancellation pieces** of a list `ws = [w₀, …, w_{l-1}]` of words over `α^{±1}`
(Makanin; Kharlampovich–Myasnikov, §4.2): nonempty words `piece z` over `α^{±1}` indexed by `Z`,
and words `patterns = [V₀, …, V_{l-1}]` over `Z^{±1}`, such that each `wⱼ` is the substitution of
the pieces into `Vⱼ` without free reduction, every signed letter of `Z^{±1}` occurs exactly once in
`V₀ ⋯ V_{l-1}`, no letter of `Z` occurs twice in one `Vⱼ`, the product `V₀ ⋯ V_{l-1}` is trivial
in `FreeGroup Z`, and two distinct `Vⱼ` share at most one letter of `Z`. -/
structure CancellationPieces (ws : List (List (α × Bool))) (Z : Type*) where
  /-- The word over `α^{±1}` named by a letter of `Z`. -/
  piece : Z → List (α × Bool)
  /-- The words `V₀, …, V_{l-1}` over `Z^{±1}`, spelling out the blocks in pieces. -/
  patterns : List (List (Z × Bool))
  /-- Every piece is nonempty. -/
  piece_ne_nil (z : Z) : piece z ≠ []
  /-- Each block is graphically the substitution of the pieces into its word over `Z^{±1}`. -/
  map_flatMap_patterns : patterns.map (fun v => v.flatMap (substituteLetter piece)) = ws
  /-- No signed letter of `Z^{±1}` occurs twice in `V₀ ⋯ V_{l-1}`. -/
  nodup_flatten_patterns : patterns.flatten.Nodup
  /-- Every signed letter of `Z^{±1}` occurs in `V₀ ⋯ V_{l-1}`. -/
  mem_flatten_patterns (z : Z) (b : Bool) : (z, b) ∈ patterns.flatten
  /-- No letter of `Z` occurs twice in one word `Vⱼ`. -/
  nodup_map_fst (v : List (Z × Bool)) : v ∈ patterns → (v.map Prod.fst).Nodup
  /-- The product `V₀ ⋯ V_{l-1}` is trivial in `FreeGroup Z`. -/
  mk_flatten_patterns : mk patterns.flatten = 1
  /-- Two distinct words `Vⱼ` share at most one letter of `Z`. -/
  pairwise_subsingleton : patterns.Pairwise fun v v' =>
    {z | z ∈ v.map Prod.fst ∧ z ∈ v'.map Prod.fst}.Subsingleton

namespace CancellationPieces

variable {ws : List (List (α × Bool))} (P : CancellationPieces ws Z)

/-- There is one word over `Z^{±1}` for each block. -/
@[simp]
theorem length_patterns : P.patterns.length = ws.length := by
  simpa using congrArg List.length P.map_flatMap_patterns

/-- The `j`-th block is the substitution of the pieces into the `j`-th word over `Z^{±1}`. -/
theorem flatMap_getElem_patterns {j : ℕ} (hj : j < P.patterns.length) :
    P.patterns[j].flatMap (substituteLetter P.piece) = ws[j]'(P.length_patterns ▸ hj) := by
  have h : j < (P.patterns.map fun v => v.flatMap (substituteLetter P.piece)).length := by
    simpa using hj
  exact (List.getElem_map _ (h := h)).symm.trans (List.getElem_of_eq P.map_flatMap_patterns h)

/-- Each word over `Z^{±1}` is reduced. -/
theorem isReduced_of_mem_patterns {v : List (Z × Bool)} (hv : v ∈ P.patterns) : IsReduced v :=
  isReduced_of_nodup_map_fst (P.nodup_map_fst v hv)

/-- Every signed letter of `Z^{±1}` occurs exactly once in `V₀ ⋯ V_{l-1}`. -/
theorem count_flatten_patterns [DecidableEq Z] (z : Z) (b : Bool) :
    P.patterns.flatten.count (z, b) = 1 :=
  List.count_eq_one_of_mem P.nodup_flatten_patterns (P.mem_flatten_patterns z b)

/-- The pieces of a list of reduced words are reduced. -/
theorem isReduced_piece (hws : ∀ w ∈ ws, IsReduced w) (z : Z) : IsReduced (P.piece z) := by
  obtain ⟨v, hv, hzv⟩ := List.mem_flatten.1 (P.mem_flatten_patterns z true)
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hzv
  exact (hws _ (P.map_flatMap_patterns ▸ List.mem_map_of_mem hv)).infix
    ⟨A.flatMap (substituteLetter P.piece), B.flatMap (substituteLetter P.piece), by simp⟩

/-- Only finitely many pieces occur. -/
theorem finite (P : CancellationPieces ws Z) : Finite Z := by
  have := (List.finite_toSet P.patterns.flatten).to_subtype
  exact Finite.of_injective
    (fun z => (⟨(z, true), P.mem_flatten_patterns z true⟩ : {a | a ∈ P.patterns.flatten}))
    fun z z' h => by simpa using congrArg Subtype.val h

/-- Two distinct words over `Z^{±1}` share at most one letter of `Z`. -/
theorem subsingleton_of_ne {i k : ℕ} (hi : i < P.patterns.length) (hk : k < P.patterns.length)
    (hik : i ≠ k) :
    {z | z ∈ P.patterns[i].map Prod.fst ∧ z ∈ P.patterns[k].map Prod.fst}.Subsingleton := by
  have h := List.pairwise_iff_getElem.1 P.pairwise_subsingleton
  rcases lt_or_gt_of_ne hik with hlt | hlt
  · exact h i k hi hk hlt
  · simpa only [and_comm] using h k i hk hi hlt

/-- **Kharlampovich–Myasnikov, §4.2.** Each word over `Z^{±1}` has length at most `l - 1`: a
block exchanges at most one piece with each other block, and none with itself. -/
theorem length_le_of_mem_patterns {v : List (Z × Bool)} (hv : v ∈ P.patterns) :
    v.length ≤ ws.length - 1 := by
  classical
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  have hnd := P.nodup_map_fst _ hv
  rw [← List.toFinset_card_of_nodup (hnd.of_map _), ← P.length_patterns]
  -- Each letter `a` of `Vᵢ` is sent to the other block containing its inverse.
  refine (Finset.card_le_card_of_forall_subsingleton
    (t := (Finset.univ : Finset (Fin P.patterns.length)).erase ⟨i, hi⟩)
    (fun a k => (a.1, !a.2) ∈ P.patterns[k]) ?_ ?_).trans (by simp)
  · intro a ha
    rw [List.mem_toFinset] at ha
    obtain ⟨v', hv', ha'⟩ := List.mem_flatten.1 (P.mem_flatten_patterns a.1 (!a.2))
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv'
    refine ⟨⟨k, hk⟩, Finset.mem_erase.2 ⟨fun hki => ?_, Finset.mem_univ _⟩, ha'⟩
    simp only [Fin.mk.injEq] at hki
    subst hki
    have := List.inj_on_of_nodup_map hnd ha ha' rfl
    obtain ⟨_, _ | _⟩ := a <;> simp at this
  · intro k hk a ha a' ha'
    simp only [Set.mem_ofPred_eq, List.mem_toFinset] at ha ha'
    have hki : i ≠ k := fun h => (Finset.mem_erase.1 hk).1 (Fin.ext h.symm)
    have h₁ : a.1 = a'.1 := P.subsingleton_of_ne hi k.2 hki
      ⟨List.mem_map_of_mem ha.1, List.mem_map.2 ⟨_, ha.2, rfl⟩⟩
      ⟨List.mem_map_of_mem ha'.1, List.mem_map.2 ⟨_, ha'.2, rfl⟩⟩
    exact List.inj_on_of_nodup_map hnd ha.1 ha'.1 h₁

/-- **Kharlampovich–Myasnikov, §4.2.** There are at most `l (l - 1) / 2` pieces. -/
theorem card_le (P : CancellationPieces ws Z) : Nat.card Z ≤ ws.length * (ws.length - 1) / 2 := by
  classical
  have := P.finite
  have : Fintype Z := Fintype.ofFinite Z
  have huniv : P.patterns.flatten.toFinset = Finset.univ := by
    ext ⟨z, b⟩
    simp [P.mem_flatten_patterns]
  rw [Nat.card_eq_fintype_card, Nat.le_div_iff_mul_le two_pos]
  calc Fintype.card Z * 2 = Fintype.card (Z × Bool) := by simp
    _ = P.patterns.flatten.length := by
      rw [← List.toFinset_card_of_nodup P.nodup_flatten_patterns, huniv, Finset.card_univ]
    _ = (P.patterns.map List.length).sum := List.length_flatten
    _ ≤ (P.patterns.map List.length).length • (ws.length - 1) :=
      List.sum_le_length_nsmul _ _ (by simpa using fun v hv => P.length_le_of_mem_patterns hv)
    _ = ws.length * (ws.length - 1) := by simp

end CancellationPieces

/-! ### Building the pieces along a reduction process -/

section Construction

/-- If the signed letters `(y, c)` and `(y, !c)` occur in a list without repetitions at the
displayed positions, then `y` occurs nowhere else. -/
private theorem not_mem_map_fst_of_nodup {L₁ L₂ L₃ : List (Z × Bool)} {y : Z} {c : Bool}
    (h : (L₁ ++ (y, c) :: (L₂ ++ (y, !c) :: L₃)).Nodup) : y ∉ (L₁ ++ L₂ ++ L₃).map Prod.fst := by
  have hp : (L₁ ++ (y, c) :: (L₂ ++ (y, !c) :: L₃)).Perm
      ((y, c) :: (y, !c) :: (L₁ ++ L₂ ++ L₃)) :=
    List.perm_middle.trans (.cons _ (by rw [← List.append_assoc]; exact List.perm_middle))
  have h' := hp.nodup_iff.1 h
  rw [List.nodup_cons, List.nodup_cons, List.mem_cons, not_or] at h'
  intro hy
  obtain ⟨⟨_, d⟩, hd, rfl⟩ := List.mem_map.1 hy
  cases d <;> cases c <;> simp_all

/-- A list of empty words has cancellation pieces with no pieces. -/
private theorem nonempty_of_forall_eq_nil {ws : List (List (α × Bool))} (hws : ∀ w ∈ ws, w = []) :
    Nonempty (CancellationPieces ws (Fin 0)) := by
  refine ⟨{
    piece := Fin.elim0
    patterns := ws.map fun _ => []
    piece_ne_nil := fun z => z.elim0
    map_flatMap_patterns := ?_
    nodup_flatten_patterns := by simp
    mem_flatten_patterns := fun z => z.elim0
    nodup_map_fst := by simp
    mk_flatten_patterns := by simp [← one_eq_mk]
    pairwise_subsingleton := List.pairwise_map.2 (List.pairwise_of_forall fun _ _ => by simp) }⟩
  rw [List.map_map]
  conv_rhs => rw [← List.map_id ws]
  exact List.map_congr_left fun w hw => by simp [hws w hw]

/-- Changing the piece of a letter `y` that occurs only in a block ending with `(y, c)` and a later
block beginning with `(y, !c)` changes only the substitutions into these two blocks. -/
private theorem map_flatMap_update [DecidableEq Z] {Vpre Vmid Vpost : List (List (Z × Bool))}
    {A C : List (Z × Bool)} {y : Z} {c : Bool}
    (hnd : (Vpre ++ (A ++ [(y, c)]) :: (Vmid ++ ((y, !c) :: C) :: Vpost)).flatten.Nodup)
    (u : Z → List (α × Bool)) (s : List (α × Bool)) :
    (Vpre ++ (A ++ [(y, c)]) :: (Vmid ++ ((y, !c) :: C) :: Vpost)).map
        (·.flatMap (substituteLetter (Function.update u y s))) =
      Vpre.map (·.flatMap (substituteLetter u)) ++
        (A.flatMap (substituteLetter u) ++ substituteLetter (Function.update u y s) (y, c)) ::
        (Vmid.map (·.flatMap (substituteLetter u)) ++
          (substituteLetter (Function.update u y s) (y, !c) ++ C.flatMap (substituteLetter u)) ::
          Vpost.map (·.flatMap (substituteLetter u))) := by
  have hy : ∀ a ∈ Vpre.flatten ++ A ++ Vmid.flatten ++ C ++ Vpost.flatten, a.1 ≠ y := by
    have := not_mem_map_fst_of_nodup (L₁ := Vpre.flatten ++ A) (L₂ := Vmid.flatten)
      (L₃ := C ++ Vpost.flatten) (y := y) (c := c) (by simpa using hnd)
    exact fun a ha hay => this (List.mem_map.2 ⟨a, by simpa using ha, hay⟩)
  simp only [List.mem_append] at hy
  have hF : ∀ v : List (Z × Bool), (∀ a ∈ v, a.1 ≠ y) →
      v.flatMap (substituteLetter (Function.update u y s)) = v.flatMap (substituteLetter u) :=
    fun v hv => flatMap_substituteLetter_congr fun a ha => Function.update_of_ne (hv a ha) _ _
  have hFs : ∀ V : List (List (Z × Bool)), (∀ a ∈ V.flatten, a.1 ≠ y) →
      V.map (·.flatMap (substituteLetter (Function.update u y s))) =
        V.map (·.flatMap (substituteLetter u)) :=
    fun V hV => List.map_congr_left fun v hv =>
      hF v fun a ha => hV a (List.mem_flatten.2 ⟨v, hv, ha⟩)
  simp [hFs Vpre fun a ha => hy a (by simp [ha]), hFs Vmid fun a ha => hy a (by simp [ha]),
    hFs Vpost fun a ha => hy a (by simp [ha]), hF A fun a ha => hy a (by simp [ha]),
    hF C fun a ha => hy a (by simp [ha])]

/-- **Lengthening a piece.** Suppose the patterns of `P` contain a block ending with `(y, c)`
followed (after empty blocks) by a block beginning with `(y, !c)`. Appending a letter `(x, e)` to
the first of the corresponding words and prepending `(x, !e)` to the second gives a list of words
with cancellation pieces over the same patterns: the piece `y` absorbs the new letter. -/
private theorem nonempty_of_continue {ws : List (List (α × Bool))} (P : CancellationPieces ws Z)
    {Vpre Vmid Vpost : List (List (Z × Bool))} {A C : List (Z × Bool)} {y : Z} {c : Bool}
    (hP : P.patterns = Vpre ++ (A ++ [(y, c)]) :: (Vmid ++ ((y, !c) :: C) :: Vpost)) (x : α)
    (e : Bool) : Nonempty (CancellationPieces
      (Vpre.map (·.flatMap (substituteLetter P.piece)) ++
        ((A ++ [(y, c)]).flatMap (substituteLetter P.piece) ++ [(x, e)]) ::
        (Vmid.map (·.flatMap (substituteLetter P.piece)) ++
          ((x, !e) :: ((y, !c) :: C).flatMap (substituteLetter P.piece)) ::
          Vpost.map (·.flatMap (substituteLetter P.piece)))) Z) := by
  classical
  -- The piece `y` becomes `t = y (x, e)` read in the first block.
  set t := substituteLetter P.piece (y, c) ++ [(x, e)] with ht
  set u := Function.update P.piece y (bif c then t else invRev t) with hu
  have hx : invRev [(x, e)] = [(x, !e)] := by simp [invRev]
  have hc : substituteLetter u (y, c) = t := by cases c <;> simp [substituteLetter, hu]
  have hnc : substituteLetter u (y, !c) = (x, !e) :: substituteLetter P.piece (y, !c) := by
    cases c <;> simp [substituteLetter, hu, ht, hx]
  refine ⟨{
    piece := u
    patterns := P.patterns
    piece_ne_nil := fun z => ?_
    map_flatMap_patterns := ?_
    nodup_flatten_patterns := P.nodup_flatten_patterns
    mem_flatten_patterns := P.mem_flatten_patterns
    nodup_map_fst := P.nodup_map_fst
    mk_flatten_patterns := P.mk_flatten_patterns
    pairwise_subsingleton := P.pairwise_subsingleton }⟩
  · by_cases hz : z = y
    · subst hz
      cases c <;> simp [hu, ht, hx]
    · simpa [hu, Function.update_of_ne hz] using P.piece_ne_nil z
  · rw [hP, hu, map_flatMap_update (hP ▸ P.nodup_flatten_patterns), ← hu, hc, hnc]
    simp [ht]

/-- If the patterns of `P` contain a block `A (z, c) B` followed (after empty blocks) by a block
`C (z, !c) D`, then the word `B C` between the two occurrences of `z` is trivial. -/
private theorem mk_append_eq_one_of_patterns_eq {ws : List (List (α × Bool))}
    (P : CancellationPieces ws Z) {Vpre Vmid Vpost : List (List (Z × Bool))}
    {A B C D : List (Z × Bool)} {z : Z} {c : Bool}
    (hP : P.patterns = Vpre ++ (A ++ (z, c) :: B) :: (Vmid ++ (C ++ (z, !c) :: D) :: Vpost))
    (hmid : ∀ v ∈ Vmid, v = []) : mk (B ++ C) = 1 := by
  have hflat : P.patterns.flatten =
      (Vpre.flatten ++ A) ++ (z, c) :: ((B ++ C) ++ (z, !c) :: (D ++ Vpost.flatten)) := by
    simp [hP, List.flatten_eq_nil_iff.2 hmid]
  have hz := not_mem_map_fst_of_nodup (hflat ▸ P.nodup_flatten_patterns)
  simp only [List.map_append, List.mem_append, not_or] at hz
  refine mk_eq_one_of_mk_append_cons_append_cons_eq_one ?_ ?_ ?_
    (hflat ▸ P.mk_flatten_patterns) <;>
    simp only [List.map_append, List.mem_append, not_or] <;> tauto

/-- **Non-crossing.** If the patterns of `P` contain a block `v₁` followed (after empty blocks) by
a block `v₂`, and `v₁` does not end with a letter whose inverse begins `v₂`, then `v₁` and `v₂`
share no letter of `Z`. -/
private theorem disjoint_of_not_continue {ws : List (List (α × Bool))} (P : CancellationPieces ws Z)
    {Vpre Vmid Vpost : List (List (Z × Bool))} {v₁ v₂ : List (Z × Bool)}
    (hP : P.patterns = Vpre ++ v₁ :: (Vmid ++ v₂ :: Vpost)) (hmid : ∀ v ∈ Vmid, v = [])
    (hne : ¬∃ A C y c, v₁ = A ++ [(y, c)] ∧ v₂ = (y, !c) :: C) {z : Z} (hz₁ : z ∈ v₁.map Prod.fst)
    (hz₂ : z ∈ v₂.map Prod.fst) : False := by
  have hnd : (Vpre.flatten ++ (v₁ ++ v₂) ++ Vpost.flatten).Nodup := by
    simpa [hP, List.flatten_eq_nil_iff.2 hmid] using P.nodup_flatten_patterns
  obtain ⟨⟨z, c⟩, hc, rfl⟩ := List.mem_map.1 hz₁
  obtain ⟨⟨z', c'⟩, hc', hz'⟩ := List.mem_map.1 hz₂
  simp only at hz'
  subst z'
  obtain rfl : c' = !c := by
    have hdisj := List.disjoint_of_nodup_append (hnd.sublist (List.infix_append _ _ _).sublist)
    cases c <;> cases c' <;> first | rfl | exact (hdisj hc hc').elim
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hc
  obtain ⟨C, D, rfl⟩ := List.append_of_mem hc'
  -- The word `B C` between the two occurrences of `z` is trivial, hence `C = B⁻¹`.
  have hCB := ((P.isReduced_of_mem_patterns (v := A ++ (z, c) :: B) (by simp [hP])).infix
    ⟨A ++ [(z, c)], [], by simp⟩).eq_invRev_of_mk_append_eq_one
    ((P.isReduced_of_mem_patterns (v := C ++ (z, !c) :: D) (by simp [hP])).infix
      ⟨[], [(z, !c)] ++ D, by simp⟩) (mk_append_eq_one_of_patterns_eq P hP hmid)
  subst hCB
  -- Either `B = C = []`, or `B` ends with a letter whose inverse begins `C`.
  rcases List.eq_nil_or_concat' B with rfl | ⟨B', a, rfl⟩
  · exact hne ⟨A, D, z, c, by simp, by simp⟩
  · exact hne ⟨A ++ (z, c) :: B', invRev B' ++ (z, !c) :: D, a.1, a.2, by simp,
      by simp [invRev]⟩

/-- The patterns after starting a new piece `n` exchanged between the blocks `v₁` and `v₂`, the
old letters being renamed along `f`. -/
private def insertPiece (f : Z → Z') (n : Z') (Vpre Vmid Vpost : List (List (Z × Bool)))
    (v₁ v₂ : List (Z × Bool)) : List (List (Z' × Bool)) :=
  Vpre.map (List.map (Prod.map f id)) ++ (v₁.map (Prod.map f id) ++ [(n, true)]) ::
    (Vmid.map (List.map (Prod.map f id)) ++ ((n, false) :: v₂.map (Prod.map f id)) ::
      Vpost.map (List.map (Prod.map f id)))

/-- The letters of the patterns after starting a new piece: the renamed old letters, with the
cancelling pair `(n, true) (n, false)` inserted. -/
private theorem flatten_insertPiece (f : Z → Z') (n : Z') (Vpre : List (List (Z × Bool)))
    {Vmid : List (List (Z × Bool))} (Vpost : List (List (Z × Bool))) (v₁ v₂ : List (Z × Bool))
    (hmid : ∀ v ∈ Vmid, v = []) :
    (insertPiece f n Vpre Vmid Vpost v₁ v₂).flatten = (Vpre.flatten ++ v₁).map (Prod.map f id) ++
      (n, true) :: (n, false) :: (v₂ ++ Vpost.flatten).map (Prod.map f id) := by
  simp [insertPiece, ← List.map_flatten, List.flatten_eq_nil_iff.2 hmid]

/-- Renaming the letters along an injective map and inserting the cancelling pair `n n⁻¹` of a
fresh letter keeps a word without repeated signed letters. -/
private theorem nodup_map_append_cons_cons {f : Z → Z'} (hf : f.Injective) {n : Z'}
    (hn : ∀ z, f z ≠ n) {X Y : List (Z × Bool)} (h : (X ++ Y).Nodup) :
    (X.map (Prod.map f id) ++ (n, true) :: (n, false) :: Y.map (Prod.map f id)).Nodup := by
  refine (List.perm_middle.trans (.cons _ List.perm_middle)).nodup_iff.2 ?_
  have h' := h.map (hf.prodMap Function.injective_id)
  rw [List.map_append] at h'
  simp [h', hn]

/-- Renaming the letters and inserting a cancelling pair does not change the element of the free
group represented, up to renaming. -/
private theorem mk_map_append_cons_cons (f : Z → Z') (n : Z') (X Y : List (Z × Bool)) :
    mk (X.map (Prod.map f id) ++ (n, true) :: (n, false) :: Y.map (Prod.map f id)) =
      FreeGroup.map f (mk (X ++ Y)) := by
  have h := (Red.Step.not (L₁ := X.map (Prod.map f id)) (L₂ := Y.map (Prod.map f id)) (x := n)
    (b := true)).mk_eq
  rw [Bool.not_true] at h
  rw [h, map.mk, ← List.map_append, Prod.map_def]
  rfl

/-- After starting a new piece, no letter occurs twice in one pattern. -/
private theorem nodup_map_fst_insertPiece {f : Z → Z'} (hf : f.Injective) {n : Z'}
    (hn : ∀ z, f z ≠ n) {Vpre Vmid Vpost : List (List (Z × Bool))} {v₁ v₂ : List (Z × Bool)}
    (h : ∀ v ∈ Vpre ++ v₁ :: (Vmid ++ v₂ :: Vpost), (v.map Prod.fst).Nodup) :
    ∀ v ∈ insertPiece f n Vpre Vmid Vpost v₁ v₂, (v.map Prod.fst).Nodup := by
  have hold : ∀ w ∈ Vpre ++ v₁ :: (Vmid ++ v₂ :: Vpost),
      ((w.map (Prod.map f id)).map Prod.fst).Nodup := fun w hw => by
    simpa [List.map_map, Function.comp_def] using (h w hw).map hf
  have hn' : ∀ w : List (Z × Bool), n ∉ (w.map (Prod.map f id)).map Prod.fst := by simp [hn]
  intro v hv
  simp only [insertPiece, List.mem_append, List.mem_cons, List.mem_map] at hv
  rcases hv with ⟨w, hw, rfl⟩ | rfl | ⟨w, hw, rfl⟩ | rfl | ⟨w, hw, rfl⟩
  · exact hold w (by simp [hw])
  · rw [List.map_append, List.nodup_append]
    refine ⟨hold v₁ (by simp), List.nodup_singleton _, fun a ha b hb hab => ?_⟩
    rw [List.mem_singleton.1 hb] at hab
    subst hab
    exact hn' v₁ ha
  · exact hold w (by simp [hw])
  · rw [List.map_cons, List.nodup_cons]
    exact ⟨hn' v₂, hold v₂ (by simp)⟩
  · exact hold w (by simp [hw])

/-- Pairwise relations survive replacing two entries `a`, `b` of a list by `a'`, `b'` and the
others by their images under `g`, provided the relations transfer. -/
private theorem pairwise_map_append_cons_append_cons {β γ : Type*} {R : β → β → Prop}
    {S : γ → γ → Prop} {g : β → γ} {l₁ l₂ l₃ : List β} {a b : β} {a' b' : γ}
    (h : (l₁ ++ a :: (l₂ ++ b :: l₃)).Pairwise R) (hg : ∀ x y, R x y → S (g x) (g y))
    (ha : ∀ x, (R a x → S a' (g x)) ∧ (R x a → S (g x) a'))
    (hb : ∀ x, (R b x → S b' (g x)) ∧ (R x b → S (g x) b')) (hab : S a' b') :
    (l₁.map g ++ a' :: (l₂.map g ++ b' :: l₃.map g)).Pairwise S := by
  simp only [List.pairwise_append, List.pairwise_cons, List.pairwise_map, List.mem_append,
    List.mem_cons, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h ⊢
  obtain ⟨h₁, ⟨h₂, h₃, ⟨h₄, h₅⟩, h₆⟩, h₇⟩ := h
  refine ⟨h₁.imp (hg _ _), ⟨?_, h₃.imp (hg _ _), ⟨fun x hx => (hb x).1 (h₄ x hx),
    h₅.imp (hg _ _)⟩, ?_⟩, ?_⟩
  · rintro _ (⟨x, hx, rfl⟩ | rfl | ⟨x, hx, rfl⟩)
    · exact (ha x).1 (h₂ x (Or.inl hx))
    · exact hab
    · exact (ha x).1 (h₂ x (Or.inr (Or.inr hx)))
  · rintro x hx _ (rfl | ⟨y, hy, rfl⟩)
    · exact (hb x).2 (h₆ x hx b (Or.inl rfl))
    · exact hg _ _ (h₆ x hx y (Or.inr hy))
  · rintro x hx _ (rfl | ⟨y, hy, rfl⟩ | rfl | ⟨y, hy, rfl⟩)
    · exact (ha x).2 (h₇ x hx a (Or.inl rfl))
    · exact hg _ _ (h₇ x hx y (Or.inr (Or.inl hy)))
    · exact (hb x).2 (h₇ x hx b (Or.inr (Or.inr (Or.inl rfl))))
    · exact hg _ _ (h₇ x hx y (Or.inr (Or.inr (Or.inr hy))))

/-- If every letter shared by `V` and `W` is the image under `f` of a letter shared by `v` and
`w`, and `v`, `w` share at most one letter, then so do `V` and `W`. -/
private theorem subsingleton_of_forall_shared {Y Y' : Type*} (f : Y → Y') {v w : List (Y × Bool)}
    {V W : List (Y' × Bool)} (h : {z | z ∈ v.map Prod.fst ∧ z ∈ w.map Prod.fst}.Subsingleton)
    (hVW : ∀ z ∈ V.map Prod.fst, z ∈ W.map Prod.fst →
      ∃ z₀ ∈ v.map Prod.fst, z₀ ∈ w.map Prod.fst ∧ f z₀ = z) :
    {z | z ∈ V.map Prod.fst ∧ z ∈ W.map Prod.fst}.Subsingleton :=
  (h.image f).anti fun z hz => by
    obtain ⟨z₀, h₁, h₂, rfl⟩ := hVW z hz.1 hz.2
    exact ⟨z₀, ⟨h₁, h₂⟩, rfl⟩

/-- A letter shared by two words renamed along an injective map is the image of a shared
letter. -/
private theorem exists_mem_of_mem_map_prodMap {f : Z → Z'} (hf : f.Injective)
    {v w : List (Z × Bool)} {z : Z'} (hv : z ∈ (v.map (Prod.map f id)).map Prod.fst)
    (hw : z ∈ (w.map (Prod.map f id)).map Prod.fst) :
    ∃ z₀ ∈ v.map Prod.fst, z₀ ∈ w.map Prod.fst ∧ f z₀ = z := by
  simp only [List.map_map, Function.comp_def, Prod.map_fst, List.mem_map] at hv hw
  obtain ⟨a, ha, rfl⟩ := hv
  obtain ⟨b, hb, hab⟩ := hw
  exact ⟨a.1, List.mem_map_of_mem ha, hf hab ▸ List.mem_map_of_mem hb, rfl⟩

/-- A letter of a word extended by `(n, c)` at either end is `n` or a letter of the word. -/
private theorem mem_map_fst_or_eq {v : List (Z' × Bool)} {z n : Z'} {c : Bool}
    (h : z ∈ (v ++ [(n, c)]).map Prod.fst ∨ z ∈ ((n, c) :: v).map Prod.fst) :
    z ∈ v.map Prod.fst ∨ z = n := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at h
  tauto

/-- After starting a new piece between two blocks sharing no letter, two distinct patterns share
at most one letter. -/
private theorem pairwise_insertPiece {f : Z → Z'} (hf : f.Injective) {n : Z'} (hn : ∀ z, f z ≠ n)
    {Vpre Vmid Vpost : List (List (Z × Bool))} {v₁ v₂ : List (Z × Bool)}
    (h : (Vpre ++ v₁ :: (Vmid ++ v₂ :: Vpost)).Pairwise fun v w =>
      {z | z ∈ v.map Prod.fst ∧ z ∈ w.map Prod.fst}.Subsingleton)
    (hdisj : ∀ z ∈ v₁.map Prod.fst, z ∉ v₂.map Prod.fst) :
    (insertPiece f n Vpre Vmid Vpost v₁ v₂).Pairwise fun v w =>
      {z | z ∈ v.map Prod.fst ∧ z ∈ w.map Prod.fst}.Subsingleton := by
  have key := @exists_mem_of_mem_map_prodMap _ _ _ hf
  have hext := @mem_map_fst_or_eq Z'
  have hn' : ∀ w : List (Z × Bool), n ∉ (w.map (Prod.map f id)).map Prod.fst := by simp [hn]
  refine pairwise_map_append_cons_append_cons h
    (fun v w h => subsingleton_of_forall_shared f h fun z hv hw => key hv hw)
    (fun w => ⟨fun h => subsingleton_of_forall_shared f h fun z hv hw => ?_,
      fun h => subsingleton_of_forall_shared f h fun z hv hw => ?_⟩)
    (fun w => ⟨fun h => subsingleton_of_forall_shared f h fun z hv hw => ?_,
      fun h => subsingleton_of_forall_shared f h fun z hv hw => ?_⟩) ?_
  · rcases hext (Or.inl hv) with hv | rfl
    exacts [key hv hw, absurd hw (hn' w)]
  · rcases hext (Or.inl hw) with hw | rfl
    exacts [key hv hw, absurd hv (hn' w)]
  · rcases hext (Or.inr hv) with hv | rfl
    exacts [key hv hw, absurd hw (hn' w)]
  · rcases hext (Or.inr hw) with hw | rfl
    exacts [key hv hw, absurd hv (hn' w)]
  · -- The two blocks of the new piece share only the new letter.
    refine (Set.subsingleton_singleton (a := n)).anti fun z hz => ?_
    rcases hext (Or.inl hz.1) with h₁ | rfl
    · rcases hext (Or.inr hz.2) with h₂ | rfl
      · obtain ⟨z₀, h₀, h₀', -⟩ := key h₁ h₂
        exact (hdisj z₀ h₀ h₀').elim
      · rfl
    · rfl

/-- Substituting into the patterns after starting a new piece `n` with piece `[(x, e)]`: the
blocks of `v₁` and `v₂` gain the letters `(x, e)` and `(x, !e)`. -/
private theorem map_flatMap_insertPiece {f : Z → Z'} {n : Z'} {u : Z → List (α × Bool)}
    {u' : Z' → List (α × Bool)} (hu : u' ∘ f = u) {x : α} {e : Bool} (hn : u' n = [(x, e)])
    (Vpre Vmid Vpost : List (List (Z × Bool))) (v₁ v₂ : List (Z × Bool)) :
    (insertPiece f n Vpre Vmid Vpost v₁ v₂).map (·.flatMap (substituteLetter u')) =
      Vpre.map (·.flatMap (substituteLetter u)) ++
        (v₁.flatMap (substituteLetter u) ++ [(x, e)]) ::
        (Vmid.map (·.flatMap (substituteLetter u)) ++
          ((x, !e) :: v₂.flatMap (substituteLetter u)) ::
          Vpost.map (·.flatMap (substituteLetter u))) := by
  have hx : invRev [(x, e)] = [(x, !e)] := by simp [invRev]
  subst hu
  simp [insertPiece, Function.comp_def, flatMap_substituteLetter_map, hn, hx]

/-- After starting a new piece `Fin.last p`, every signed letter of `Fin (p + 1)` occurs in the
patterns if every signed letter of `Fin p` occurred before. -/
private theorem mem_flatten_insertPiece {p : ℕ} {Vpre Vmid Vpost : List (List (Fin p × Bool))}
    {v₁ v₂ : List (Fin p × Bool)} (hmid : ∀ v ∈ Vmid, v = [])
    (h : ∀ z b, (z, b) ∈ (Vpre.flatten ++ v₁) ++ (v₂ ++ Vpost.flatten)) (z : Fin (p + 1))
    (b : Bool) :
    (z, b) ∈ (insertPiece Fin.castSucc (Fin.last p) Vpre Vmid Vpost v₁ v₂).flatten := by
  rw [flatten_insertPiece _ _ _ _ _ _ hmid]
  induction z using Fin.lastCases with
  | last => cases b <;> simp
  | cast z =>
    have h' := List.mem_map_of_mem (f := Prod.map Fin.castSucc id) (h z b)
    rw [List.map_append, List.mem_append] at h'
    rcases h' with h' | h'
    · exact List.mem_append_left _ h'
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h'))

/-- **A new piece.** Suppose the patterns of `P` contain a block `v₁` followed (after empty
blocks) by a block `v₂` sharing no letter with it. Appending `(x, e)` to the word of `v₁` and
prepending `(x, !e)` to the word of `v₂` gives a list of words with cancellation pieces with one
more piece, `[(x, e)]`, exchanged between these two blocks. -/
private theorem nonempty_of_new {p : ℕ} {ws : List (List (α × Bool))}
    (P : CancellationPieces ws (Fin p)) {Vpre Vmid Vpost : List (List (Fin p × Bool))}
    {v₁ v₂ : List (Fin p × Bool)} (hP : P.patterns = Vpre ++ v₁ :: (Vmid ++ v₂ :: Vpost))
    (hmid : ∀ v ∈ Vmid, v = []) (hdisj : ∀ z ∈ v₁.map Prod.fst, z ∉ v₂.map Prod.fst) (x : α)
    (e : Bool) : Nonempty (CancellationPieces
      (Vpre.map (·.flatMap (substituteLetter P.piece)) ++
        (v₁.flatMap (substituteLetter P.piece) ++ [(x, e)]) ::
        (Vmid.map (·.flatMap (substituteLetter P.piece)) ++
          ((x, !e) :: v₂.flatMap (substituteLetter P.piece)) ::
          Vpost.map (·.flatMap (substituteLetter P.piece)))) (Fin (p + 1))) := by
  have hflat : P.patterns.flatten = (Vpre.flatten ++ v₁) ++ (v₂ ++ Vpost.flatten) := by
    simp [hP, List.flatten_eq_nil_iff.2 hmid]
  have hnew := flatten_insertPiece Fin.castSucc (Fin.last p) Vpre Vpost v₁ v₂ hmid
  set u := Fin.snoc (α := fun _ => List (α × Bool)) P.piece [(x, e)] with hu
  refine ⟨{
    piece := u
    patterns := insertPiece Fin.castSucc (Fin.last p) Vpre Vmid Vpost v₁ v₂
    piece_ne_nil := fun z => ?_
    map_flatMap_patterns := map_flatMap_insertPiece (Fin.snoc_comp_castSucc ..) (Fin.snoc_last ..)
      Vpre Vmid Vpost v₁ v₂
    nodup_flatten_patterns := hnew ▸ nodup_map_append_cons_cons (Fin.castSucc_injective p)
      Fin.castSucc_ne_last (hflat ▸ P.nodup_flatten_patterns)
    mem_flatten_patterns := mem_flatten_insertPiece hmid (hflat ▸ P.mem_flatten_patterns)
    nodup_map_fst := nodup_map_fst_insertPiece (Fin.castSucc_injective p) Fin.castSucc_ne_last
      (hP ▸ P.nodup_map_fst)
    mk_flatten_patterns := by
      rw [hnew, mk_map_append_cons_cons, ← hflat, P.mk_flatten_patterns, _root_.map_one]
    pairwise_subsingleton := pairwise_insertPiece (Fin.castSucc_injective p)
      Fin.castSucc_ne_last (hP ▸ P.pairwise_subsingleton) hdisj }⟩
  · induction z using Fin.lastCases with
    | last => simp [hu]
    | cast z => simpa [hu] using P.piece_ne_nil z

/-- **One step of the reduction process.** Cancelling the last letter of a block against the
first letter of the next nonempty block either lengthens a piece or starts a new one. -/
private theorem exists_of_cancel {pre mid post : List (List (α × Bool))} {w₁ w₂ : List (α × Bool)}
    (hmid : ∀ w ∈ mid, w = []) {p : ℕ}
    (P : CancellationPieces (pre ++ w₁ :: (mid ++ w₂ :: post)) (Fin p)) (x : α) (e : Bool) :
    ∃ p', Nonempty (CancellationPieces
      (pre ++ (w₁ ++ [(x, e)]) :: (mid ++ ((x, !e) :: w₂) :: post)) (Fin p')) := by
  obtain ⟨Vpre, Vrest, hP, hpre, hrest⟩ := List.map_eq_append_iff.1 P.map_flatMap_patterns
  obtain ⟨v₁, Vrest, rfl, hv₁, hrest⟩ := List.map_eq_cons_iff.1 hrest
  obtain ⟨Vmid, Vrest, rfl, hVmid, hrest⟩ := List.map_eq_append_iff.1 hrest
  obtain ⟨v₂, Vpost, rfl, hv₂, hpost⟩ := List.map_eq_cons_iff.1 hrest
  have hws : Vpre.map (·.flatMap (substituteLetter P.piece)) ++
      (v₁.flatMap (substituteLetter P.piece) ++ [(x, e)]) ::
      (Vmid.map (·.flatMap (substituteLetter P.piece)) ++
        ((x, !e) :: v₂.flatMap (substituteLetter P.piece)) ::
        Vpost.map (·.flatMap (substituteLetter P.piece))) =
      pre ++ (w₁ ++ [(x, e)]) :: (mid ++ ((x, !e) :: w₂) :: post) := by
    rw [hpre, hv₁, hVmid, hv₂, hpost]
  rw [← hws]
  -- The empty blocks have empty patterns, since the pieces are nonempty.
  replace hVmid : ∀ v ∈ Vmid, v = [] := fun v hv => by
    have := hmid _ (hVmid ▸ List.mem_map_of_mem hv)
    rw [List.flatMap_eq_nil_iff] at this
    exact List.eq_nil_iff_forall_not_mem.2 fun a ha => by
      obtain ⟨z, _ | _⟩ := a <;> simpa [invRev, P.piece_ne_nil] using this _ ha
  by_cases hcont : ∃ A C y c, v₁ = A ++ [(y, c)] ∧ v₂ = (y, !c) :: C
  · obtain ⟨A, C, y, c, rfl, rfl⟩ := hcont
    exact ⟨p, nonempty_of_continue P hP x e⟩
  · exact ⟨p + 1, nonempty_of_new P hP hVmid
      (fun z hz₁ hz₂ => disjoint_of_not_continue P hP hVmid hcont hz₁ hz₂) x e⟩

end Construction

/-- **Makanin; Kharlampovich–Myasnikov, §4.2, proof of Lemma 14.** A list of reduced words whose
product is trivial in the free group has cancellation pieces, indexed by `Fin p` for some `p`. -/
theorem exists_cancellationPieces {ws : List (List (α × Bool))} (hws : ∀ w ∈ ws, IsReduced w)
    (h : mk ws.flatten = 1) : ∃ p, Nonempty (CancellationPieces ws (Fin p)) := by
  induction hn : ws.flatten.length using Nat.strong_induction_on generalizing ws with
  | _ n ih =>
  by_cases hred : IsReduced ws.flatten
  · exact ⟨0, nonempty_of_forall_eq_nil
      (List.flatten_eq_nil_iff.1 (hred.eq_nil_of_mk_eq_one h))⟩
  -- The first free reduction cancels the end of a block against the start of the next
  -- nonempty block; the rest of the reduction process reduces the shorter list.
  obtain ⟨L₁, L₂, x, e, hL⟩ := exists_eq_append_cons_cons_of_not_isReduced hred
  obtain ⟨pre, w₁, mid, w₂, post, rfl, hmid⟩ :=
    exists_eq_append_cons_append_cons_of_flatten_eq hws hL
  have hflat : (pre ++ (w₁ ++ [(x, e)]) :: (mid ++ ((x, !e) :: w₂) :: post)).flatten =
      (pre.flatten ++ w₁) ++ (x, e) :: (x, !e) :: (w₂ ++ post.flatten) := by
    simp [List.flatten_eq_nil_iff.2 hmid]
  have hflat' : (pre ++ w₁ :: (mid ++ w₂ :: post)).flatten =
      (pre.flatten ++ w₁) ++ (w₂ ++ post.flatten) := by
    simp [List.flatten_eq_nil_iff.2 hmid]
  obtain ⟨p, ⟨P⟩⟩ := ih _ (by rw [← hn, hflat, hflat']; simp)
    (ws := pre ++ w₁ :: (mid ++ w₂ :: post)) (fun w hw => by
      simp only [List.mem_append, List.mem_cons] at hw
      rcases hw with hw | rfl | hw | rfl | hw
      · exact hws w (by simp [hw])
      · exact (hws (w ++ [(x, e)]) (by simp)).infix ⟨[], [(x, e)], by simp⟩
      · exact hws w (by simp [hw])
      · exact (hws ((x, !e) :: w) (by simp)).infix ⟨[(x, !e)], [], by simp⟩
      · exact hws w (by simp [hw]))
    (by rw [hflat', ← (Red.Step.not (x := x) (b := e)).mk_eq, ← hflat, h]) rfl
  exact exists_of_cancel hmid P x e

section Examples

/-- With no blocks there are no pieces. -/
example (P : CancellationPieces ([] : List (List (α × Bool))) Z) : IsEmpty Z :=
  (Nat.card_eq_zero.1 (by simpa using P.card_le)).resolve_right
    (not_infinite_iff_finite.2 P.finite)

/-- A single block with cancellation pieces is empty: `l = 1` forces `w₀ = []`. -/
example {w : List (α × Bool)} (P : CancellationPieces [w] Z) : w = [] := by
  obtain ⟨v, hv⟩ : ∃ v, P.patterns = [v] := List.length_eq_one_iff.1 (by simp)
  have hv₀ : v = [] :=
    List.eq_nil_of_length_eq_zero <| by
      simpa using P.length_le_of_mem_patterns (v := v) (by simp [hv])
  simpa [hv, hv₀] using P.map_flatMap_patterns.symm

/-- Two blocks exchange at most one piece. -/
example {w₀ w₁ : List (α × Bool)} (P : CancellationPieces [w₀, w₁] Z) : Nat.card Z ≤ 1 := by
  simpa using P.card_le

/-- A nonempty word `w` followed by its formal inverse is a single piece. -/
example {w : List (α × Bool)} (hw : w ≠ []) :
    Nonempty (CancellationPieces [w, invRev w] (Fin 1)) :=
  ⟨{
    piece := fun _ => w
    patterns := [[(0, true)], [(0, false)]]
    piece_ne_nil := fun _ => hw
    map_flatMap_patterns := by simp [substituteLetter]
    nodup_flatten_patterns := by decide
    mem_flatten_patterns := by decide
    nodup_map_fst := by decide
    mk_flatten_patterns := by
      simpa [← one_eq_mk] using (Red.Step.not (L₁ := []) (L₂ := []) (x := (0 : Fin 1))
        (b := true)).mk_eq
    pairwise_subsingleton := by simp [Set.subsingleton_of_subsingleton] }⟩

/-- The trivial product `(a c) (c⁻¹ b) (b⁻¹ a⁻¹)` (with `a = 0`, `c = 1`, `b = 2`) has the three
one-letter pieces `a`, `c`, `b`, one for each pair of blocks: every `Vⱼ` has the maximal length
`l - 1 = 2`, and there are `l (l - 1) / 2 = 3` pieces. -/
example : ∃ P : CancellationPieces ([[(0, true), (1, true)], [(1, false), (2, true)],
    [(2, false), (0, false)]] : List (List (Fin 3 × Bool))) (Fin 3),
    ∀ v ∈ P.patterns, v.length = 2 :=
  ⟨{
    piece := fun z => [(z, true)]
    patterns := [[(0, true), (1, true)], [(1, false), (2, true)], [(2, false), (0, false)]]
    piece_ne_nil := by decide
    map_flatMap_patterns := by decide
    nodup_flatten_patterns := by decide
    mem_flatten_patterns := by decide
    nodup_map_fst := by decide
    mk_flatten_patterns := by decide
    pairwise_subsingleton := by
      simp only [Set.Subsingleton, Set.mem_ofPred_eq]
      decide }, by decide⟩

end Examples

end TauCeti

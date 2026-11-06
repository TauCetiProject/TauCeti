/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.GroupTheory.Coxeter.Bipartite

import TauCeti.Combinatorics.SimpleGraph.Acyclic
import TauCeti.GroupTheory.Coxeter.Basic

/-!
# Conjugacy of Coxeter elements on a forest

Let `cs` be a Coxeter system with Coxeter matrix `M`. A *Coxeter element* is a product of all the
simple reflections, each exactly once, in some order. Different orders usually give different
elements, but two moves on the word preserve the conjugacy class of the product:

* moving the first letter to the end conjugates the product by that simple reflection, and more
  generally rotating a word `l₁ ++ l₂` to `l₂ ++ l₁` conjugates the product
  (`CoxeterSystem.isConj_wordProd_append`);
* exchanging two adjacent letters that are not joined in the Coxeter graph does not change the
  product, since the corresponding simple reflections commute.

When the Coxeter graph is a forest, as it is for every finite Weyl group, these two moves connect
any two orderings of the simple reflections. Peel off a vertex `s` with at most one neighbour `t`
among the remaining letters, rotate `s` to the front of both words, and connect the rest by
induction. A move on the rest lifts to the word with `s` in front: an exchange lifts directly, and
the rotation of a first letter `a` lifts either through an exchange of `s` with `a`, when they are
not joined, or, when `a = t`, through a double rotation followed by moving `s`, which commutes with
every other letter, back to the front. Hence **all Coxeter elements of a Coxeter system whose
Coxeter graph is a forest are conjugate** (`CoxeterSystem.isConj_wordProd_of_perm`), and each of
them is conjugate to the bipartite Coxeter element of any two-colouring of the Coxeter graph
(`CoxeterSystem.isConj_wordProd_bipartiteCoxeterElement`). So the order of a Coxeter element and
its eigenvalues in any linear representation depend only on the Coxeter system. The statement only
uses the graph induced on the letters of the word, so it also applies to the products of the simple
reflections of any subset of the indices on which the Coxeter graph is a forest.

The hypothesis on the graph cannot simply be dropped: for the affine Coxeter system of type
`Ã₂`, whose Coxeter graph is a triangle, the Coxeter elements `s₁ s₂ s₃` and `s₁ s₃ s₂` are not
conjugate.

## Main results

* `CoxeterSystem.isConj_wordProd_of_perm`: if the Coxeter graph induced on the letters of a word
  without repeated letters is a forest, every rearrangement of the word spells a conjugate element.
* `CoxeterSystem.isConj_wordProd_bipartiteCoxeterElement`: on a forest, every Coxeter element is
  conjugate to the bipartite Coxeter element.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 1, Lemma 1.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  § 3.16.
-/

public section

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- The two moves on words: rotating the first letter to the end, and exchanging two adjacent
letters that are not joined in the Coxeter graph. -/
private inductive Move (M : CoxeterMatrix B) : List B → List B → Prop
  | rotate (a : B) (l : List B) : Move M (a :: l) (l ++ [a])
  | swap (l₁ l₂ : List B) {a a' : B} (h : ¬M.graph.Adj a a') :
      Move M (l₁ ++ a :: a' :: l₂) (l₁ ++ a' :: a :: l₂)

/-- Words connected by moves are rearrangements of each other. -/
private theorem perm_of_eqvGen_move {l l' : List B} (h : Relation.EqvGen (Move M) l l') :
    l.Perm l' := by
  induction h with
  | rel _ _ h =>
    cases h with
    | rotate a l => exact (List.perm_append_singleton a l).symm
    | swap l₁ l₂ _ => exact (List.Perm.swap _ _ _).append_left l₁
  | refl => exact .refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Words connected by moves spell conjugate elements. -/
private theorem isConj_of_eqvGen_move {l l' : List B} (h : Relation.EqvGen (Move M) l l') :
    IsConj (cs.wordProd l) (cs.wordProd l') := by
  induction h with
  | rel _ _ h =>
    cases h with
    | rotate a l => exact cs.isConj_wordProd_append [a] l
    | swap l₁ l₂ h =>
      rw [wordProd_append, wordProd_append, wordProd_cons, wordProd_cons, wordProd_cons,
        wordProd_cons, (cs.commute_simple_of_not_adj h).left_comm]
  | refl => exact .refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Rotating `l₁ ++ l₂` to `l₂ ++ l₁` is a sequence of moves. -/
private theorem eqvGen_move_append_comm (l₁ l₂ : List B) :
    Relation.EqvGen (Move M) (l₁ ++ l₂) (l₂ ++ l₁) := by
  induction l₁ generalizing l₂ with
  | nil => simpa using .refl _
  | cons a l₁ ih =>
    refine .trans _ _ _ (.rel _ _ (Move.rotate a (l₁ ++ l₂))) ?_
    simpa using ih (l₂ ++ [a])

/-- A letter `a` not joined to any letter of `l` moves past `l` by exchanges. -/
private theorem eqvGen_move_cons_append (a : B) {l : List B} (h : ∀ x ∈ l, ¬M.graph.Adj a x)
    (l₁ l₂ : List B) :
    Relation.EqvGen (Move M) (l₁ ++ a :: (l ++ l₂)) (l₁ ++ l ++ a :: l₂) := by
  induction l generalizing l₁ with
  | nil => simpa using .refl _
  | cons x l ih =>
    refine .trans _ _ _ (.rel _ _ (Move.swap l₁ (l ++ l₂) (h x (by simp)))) ?_
    simpa using ih (fun y hy ↦ h y (by simp [hy])) (l₁ ++ [x])

/-- A single move on a word lifts to the word with an extra first letter `s` that is joined to at
most one letter of it. -/
private theorem eqvGen_move_cons_of_move (s : B) {u u' : List B} (hu : u.Nodup)
    (hs : ∀ x ∈ u, ∀ y ∈ u, M.graph.Adj s x → M.graph.Adj s y → x = y) (h : Move M u u') :
    Relation.EqvGen (Move M) (s :: u) (s :: u') := by
  cases h with
  | swap l₁ l₂ h => exact .rel _ _ (Move.swap (s :: l₁) l₂ h)
  | rotate a l =>
    by_cases hsa : M.graph.Adj s a
    · -- `a` is the only letter joined to `s`, so `s` commutes with every letter of `l`: rotate
      -- `s a` to the end and move `s` back to the front.
      have hl : ∀ x ∈ l, ¬M.graph.Adj s x := fun x hx hsx ↦
        (List.nodup_cons.mp hu).1 (hs x (by simp [hx]) a (by simp) hsx hsa ▸ hx)
      refine .trans _ _ _ (eqvGen_move_append_comm [s, a] l) (.symm _ _ ?_)
      simpa using eqvGen_move_cons_append s hl [] [a]
    · exact .trans _ _ _ (.rel _ _ (Move.swap [] l hsa)) (.rel _ _ (Move.rotate a (s :: l)))

/-- A sequence of moves on a word without repeated letters lifts to the word with an extra first
letter `s` that is joined to at most one of its letters. -/
private theorem eqvGen_move_cons (s : B) {u u' : List B} (hu : u.Nodup)
    (hs : ∀ x ∈ u, ∀ y ∈ u, M.graph.Adj s x → M.graph.Adj s y → x = y)
    (h : Relation.EqvGen (Move M) u u') :
    Relation.EqvGen (Move M) (s :: u) (s :: u') := by
  induction h with
  | rel _ _ h => exact eqvGen_move_cons_of_move s hu hs h
  | refl => exact .refl _
  | symm _ _ h ih =>
    have hp := perm_of_eqvGen_move h
    exact (ih (hp.nodup_iff.mpr hu) fun x hx y hy ↦ hs x (hp.mem_iff.mp hx) y
      (hp.mem_iff.mp hy)).symm
  | trans _ _ _ h₁ _ ih₁ ih₂ =>
    have hp := perm_of_eqvGen_move h₁
    exact .trans _ _ _ (ih₁ hu hs) (ih₂ (hp.nodup_iff.mp hu) fun x hx y hy ↦
      hs x (hp.mem_iff.mpr hx) y (hp.mem_iff.mpr hy))

/-- If the Coxeter graph induces a forest on the letters of a word without repeated letters, the
moves connect the word to each of its rearrangements. -/
private theorem eqvGen_move_of_perm :
    ∀ (n : ℕ) {l l' : List B}, l.length = n → l.Nodup →
      (M.graph.induce {i | i ∈ l}).IsAcyclic → l.Perm l' → Relation.EqvGen (Move M) l l'
  | 0, l, l', hn, _, _, hp => by
    obtain rfl := List.length_eq_zero_iff.mp hn
    obtain rfl := List.nil_perm.mp hp
    exact .refl _
  | n + 1, l, l', hn, hl, hM, hp => by
    classical
    -- The induced forest is finite and nonempty, so some letter `s` is joined to at most one
    -- letter of `l`.
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil l (List.ne_nil_of_length_eq_add_one hn)
    have : Nonempty {i | i ∈ l} := ⟨⟨a, ha⟩⟩
    have : Fintype {i | i ∈ l} := Set.Finite.fintype (List.finite_toSet l)
    obtain ⟨⟨s, hs⟩, hdeg⟩ := hM.exists_degree_le_one
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdeg
    have hleaf : ∀ x ∈ l, ∀ y ∈ l, M.graph.Adj s x → M.graph.Adj s y → x = y :=
      fun x hx y hy hsx hsy ↦ congrArg Subtype.val <| Finset.card_le_one.mp hdeg ⟨x, hx⟩
        (by simpa using hsx) ⟨y, hy⟩ (by simpa using hsy)
    -- Rotate `s` to the front of both words, and connect the remaining letters by induction.
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hs
    obtain ⟨l₁', l₂', rfl⟩ := List.append_of_mem (hp.mem_iff.mp hs)
    have hu : (l₁ ++ s :: l₂).Perm (s :: (l₂ ++ l₁)) := List.perm_append_comm
    have hu' : (l₁' ++ s :: l₂').Perm (s :: (l₂' ++ l₁')) := List.perm_append_comm
    have hnd := List.nodup_cons.mp (hu.nodup_iff.mp hl)
    have hsub : {i | i ∈ l₂ ++ l₁} ≤ {i | i ∈ l₁ ++ s :: l₂} := fun i hi ↦
      hu.mem_iff.mpr (List.mem_cons_of_mem s hi)
    have ih := eqvGen_move_of_perm n (by simpa [hn] using hu.length_eq.symm) hnd.2
      (hM.embedding (M.graph.induceHomOfLE hsub)) ((hu.symm.trans hp).trans hu').cons_inv
    refine .trans _ _ _ (eqvGen_move_append_comm l₁ (s :: l₂)) (.trans _ _ _ ?_
      (eqvGen_move_append_comm l₁' (s :: l₂')).symm)
    exact eqvGen_move_cons s hnd.2 (fun x hx y hy ↦ hleaf x (hsub hx) y (hsub hy)) ih

/-- **Coxeter elements on a forest are conjugate.** If the Coxeter graph induces a forest on the
letters of a word with no repeated letter, then every rearrangement of the word spells an element
conjugate to the one it spells. In particular, when the Coxeter graph is a forest, all Coxeter
elements, the products of all the simple reflections each taken once, are conjugate. -/
theorem isConj_wordProd_of_perm {l l' : List B} (hl : l.Nodup)
    (hM : (M.graph.induce {i | i ∈ l}).IsAcyclic) (h : l.Perm l') :
    IsConj (cs.wordProd l) (cs.wordProd l') :=
  cs.isConj_of_eqvGen_move (eqvGen_move_of_perm _ rfl hl hM h)

/-- **On a forest, every Coxeter element is conjugate to the bipartite Coxeter element.** If the
Coxeter graph is a forest, the product of all the simple reflections, each exactly once and in any
order, is conjugate to the bipartite Coxeter element of any two-colouring of the Coxeter graph. -/
theorem isConj_wordProd_bipartiteCoxeterElement [Fintype B] (hM : M.graph.IsAcyclic)
    (c : M.graph.Coloring Bool) {l : List B} (hl : l.Nodup) (hl' : ∀ i, i ∈ l) :
    IsConj (cs.wordProd l) (cs.bipartiteCoxeterElement c) := by
  obtain ⟨l₁, l₂, -, -, hnd, hmem, heq⟩ := cs.exists_wordProd_eq_bipartiteCoxeterElement c
  rw [← heq]
  exact cs.isConj_wordProd_of_perm hl (hM.induce _)
    ((List.perm_ext_iff_of_nodup hl hnd).mpr fun i ↦ iff_of_true (hl' i) (hmem i))

end CoxeterSystem

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Basic
public import TauCeti.Combinatorics.Graph.Serre.Path.Basic
public import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Folded labelled graphs

A labelled graph is folded when the label and initial vertex determine a dart. This makes
the word and endpoints determine a path and ensures that a reduced path has a freely reduced
label. These are the local facts behind the Stallings subgroup criterion.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*, Section 3.
-/

public section

namespace TauCeti
namespace StallingsGraph

variable {α : Type*} (S : StallingsGraph α)

/-- Outgoing darts with the same label coincide. -/
def IsFolded : Prop :=
  ∀ e f : S.graph.E, S.graph.src e = S.graph.src f → S.label e = S.label f → e = f

/-- Foldedness is uniqueness of an outgoing dart with a given label. -/
theorem isFolded_def : S.IsFolded ↔
    ∀ e f : S.graph.E, S.graph.src e = S.graph.src f → S.label e = S.label f → e = f :=
  Iff.rfl

/-- In a folded graph, the target and label also determine a dart. -/
theorem IsFolded.eq_of_tgt_label (hS : S.IsFolded) {e f : S.graph.E}
    (ht : S.graph.tgt e = S.graph.tgt f) (hl : S.label e = S.label f) : e = f := by
  apply S.graph.rev_injective
  apply hS (S.graph.rev e) (S.graph.rev f)
  · simpa only [S.graph.src_rev] using ht
  · simpa only [S.label_rev] using congrArg (fun x : α × Bool => (x.1, !x.2)) hl

/-- The rose is folded: each signed generator specifies its unique outgoing dart. -/
theorem rose_isFolded (α : Type*) : (rose α).IsFolded := by
  intro e f _ h
  exact h

/-- Two consecutive darts of a reduced path cannot carry inverse labels in a folded graph. -/
theorem IsFolded.labels_not_inverse (hS : S.IsFolded) {e f : S.graph.E}
    (hsrc : S.graph.src f = S.graph.tgt e) (hne : f ≠ S.graph.rev e) :
    S.label f ≠ ((S.label e).1, !(S.label e).2) := by
  intro h
  have hfr : f = S.graph.rev e := hS f (S.graph.rev e)
    (hsrc.trans (S.graph.src_rev e).symm) (by simpa only [S.label_rev] using h)
  exact hne hfr

/-- A reduced path in a folded graph reads a freely reduced word. -/
theorem IsFolded.isReduced_word (hS : S.IsFolded) {a b : S.graph.V}
    (p : S.graph.Path a b) (hp : SerreGraph.Path.IsReduced S.graph p) :
    FreeGroup.IsReduced (S.word p) := by
  induction p with
  | nil => simpa only [word_nil] using (FreeGroup.IsReduced.nil : FreeGroup.IsReduced [])
  | cons p e ih =>
    cases p with
    | nil => simpa only [word_cons, word_nil, List.nil_append] using
        (FreeGroup.IsReduced.singleton (a := S.label e.1))
    | cons p f =>
      obtain ⟨hprev, hne⟩ := (SerreGraph.Path.isReduced_cons_cons S.graph p f e).mp hp
      have hword := ih hprev
      have hlocal : (S.label f.1).1 = (S.label e.1).1 →
          (S.label f.1).2 = (S.label e.1).2 := by
        intro ha
        by_contra hb
        apply IsFolded.labels_not_inverse S hS (e.2.1.trans f.2.2.symm) hne
        apply Prod.ext
        · exact ha.symm
        · cases he : (S.label e.1).2 <;> cases hf : (S.label f.1).2 <;>
            simp_all
      simp only [word_cons, List.append_assoc, List.singleton_append,
        FreeGroup.IsReduced, List.isChain_append_cons_cons, List.isChain_singleton,
        and_true] at hword ⊢
      exact ⟨hword, hlocal⟩

/-- In a folded graph, endpoints and the label word determine a path. -/
theorem IsFolded.path_eq_of_word_eq (hS : S.IsFolded) {a b : S.graph.V}
    (p q : S.graph.Path a b) (h : S.word p = S.word q) : p = q := by
  induction p with
  | nil =>
    cases q with
    | nil => rfl
    | cons q f => simp at h
  | cons p e ih =>
    cases q with
    | nil => simp at h
    | cons q f =>
      simp only [word_cons] at h
      obtain ⟨hword, hlabel⟩ := List.append_inj' h (by simp)
      simp only [List.singleton_inj] at hlabel
      have he : e.1 = f.1 := IsFolded.eq_of_tgt_label S hS
        (e.2.2.trans f.2.2.symm) hlabel
      have hsrc : _ := congrArg S.graph.src he
      simp only [e.2.1, f.2.1] at hsrc
      cases hsrc
      have hef : e = f := Subtype.ext he
      cases hef
      congr 1
      exact ih q hword

/-- The reduced word of a reduced path's reading is its actual label word. -/
@[simp] theorem IsFolded.toWord_read_eq_word [DecidableEq α] (hS : S.IsFolded)
    {a b : S.graph.V} (p : S.graph.Path a b)
    (hp : SerreGraph.Path.IsReduced S.graph p) :
    (S.read p).toWord = S.word p := by
  rw [S.read_eq_mk_word, FreeGroup.toWord_mk]
  exact (IsFolded.isReduced_word S hS p hp).reduce_eq

/-- A folded graph's reduced paths with fixed endpoints have distinct free-group readings. -/
theorem IsFolded.path_eq_of_read_eq (hS : S.IsFolded)
    {a b : S.graph.V} (p q : S.graph.Path a b)
    (hp : SerreGraph.Path.IsReduced S.graph p)
    (hq : SerreGraph.Path.IsReduced S.graph q)
    (h : S.read p = S.read q) : p = q := by
  classical
  apply IsFolded.path_eq_of_word_eq S hS p q
  simpa only [IsFolded.toWord_read_eq_word S hS p hp,
    IsFolded.toWord_read_eq_word S hS q hq] using
    congrArg FreeGroup.toWord h

end StallingsGraph
end TauCeti

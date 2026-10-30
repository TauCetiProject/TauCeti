/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Fold.Subgroup
public import TauCeti.Combinatorics.Graph.Stallings.Folded
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite Stallings folding

A fold of two distinct equally labelled darts strictly decreases the number of darts.
Consequently a finite labelled graph admits a finite sequence of folds ending in a folded
graph. Every step preserves the subgroup read at the base vertex. This is the termination
step in the construction of a finite folded graph from a flower of generating words.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 3, Proposition 3.8.
-/

public section

namespace TauCeti.StallingsGraph

universe u v w

variable {α : Type u}

/-- A single fold of distinct equally labelled darts with the same source. -/
def FoldStep (S T : StallingsGraph.{u, v, w} α) : Prop :=
  ∃ e f, ∃ hsrc : S.graph.src e = S.graph.src f,
    ∃ hlabel : S.label e = S.label f, e ≠ f ∧ T = S.foldAt e f hsrc hlabel

/-- Characterize a fold step by its two distinct darts and the resulting quotient. -/
theorem foldStep_iff (S T : StallingsGraph.{u, v, w} α) :
    FoldStep S T ↔
      ∃ e f, ∃ hsrc : S.graph.src e = S.graph.src f,
        ∃ hlabel : S.label e = S.label f, e ≠ f ∧ T = S.foldAt e f hsrc hlabel :=
  Iff.rfl

/-- A finite sequence of Stallings folds, including the empty sequence. -/
abbrev FoldSequence (S T : StallingsGraph.{u, v, w} α) : Prop :=
  Relation.ReflTransGen FoldStep S T

/-- A finite fold sequence preserves the subgroup accepted at the base vertex. -/
theorem FoldSequence.subgroup_base {S T : StallingsGraph.{u, v, w} α}
    (h : FoldSequence S T) : T.subgroup T.base = S.subgroup S.base := by
  induction h with
  | refl => rfl
  | tail h hstep ih =>
    obtain ⟨e, f, hsrc, hlabel, _, rfl⟩ := hstep
    exact (foldAt_subgroup_base _ e f hsrc hlabel).trans ih

/-- A finite fold sequence preserves finiteness of vertices. -/
theorem FoldSequence.finite_V {S T : StallingsGraph.{u, v, w} α}
    (h : FoldSequence S T) [Finite S.graph.V] : Finite T.graph.V := by
  induction h with
  | refl => infer_instance
  | tail h hstep ih =>
    obtain ⟨e, f, hsrc, hlabel, _, rfl⟩ := hstep
    let _ := ih
    infer_instance

/-- A finite fold sequence preserves finiteness of darts. -/
theorem FoldSequence.finite_E {S T : StallingsGraph.{u, v, w} α}
    (h : FoldSequence S T) [Finite S.graph.E] : Finite T.graph.E := by
  induction h with
  | refl => infer_instance
  | tail h hstep ih =>
    obtain ⟨e, f, hsrc, hlabel, _, rfl⟩ := hstep
    let _ := ih
    infer_instance

/-- A finite fold sequence preserves connectedness. -/
theorem FoldSequence.connected {S T : StallingsGraph.{u, v, w} α}
    (h : FoldSequence S T) (hS : S.graph.Connected) : T.graph.Connected := by
  induction h with
  | refl => exact hS
  | tail h hstep ih =>
    obtain ⟨e, f, hsrc, hlabel, _, rfl⟩ := hstep
    exact connected_foldAt _ e f hsrc hlabel ih

/-- Folding distinct darts strictly decreases the number of darts. -/
theorem card_foldAt_lt (S : StallingsGraph.{u, v, w} α) [Finite S.graph.E]
    (e f : S.graph.E) (hne : e ≠ f)
    (hsrc : S.graph.src e = S.graph.src f)
    (hlabel : S.label e = S.label f) :
    Nat.card (S.foldAt e f hsrc hlabel).graph.E < Nat.card S.graph.E := by
  classical
  let _ := Fintype.ofFinite S.graph.E
  let _ := Fintype.ofFinite (S.foldAt e f hsrc hlabel).graph.E
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  apply Fintype.card_lt_of_surjective_not_injective
    (S.foldHom e f hsrc hlabel).graphHom.mapE
    (S.foldHom_mapE_surjective e f hsrc hlabel)
  intro hinj
  exact hne (hinj (S.foldHom_mapE_eq e f hsrc hlabel))

/-- A finite labelled graph can be folded by a finite sequence of quotients. -/
theorem exists_foldSequence_isFolded (S : StallingsGraph.{u, v, w} α)
    [Finite S.graph.E] :
    ∃ T : StallingsGraph.{u, v, w} α, FoldSequence S T ∧ T.IsFolded := by
  classical
  have aux : ∀ n : ℕ, ∀ (R : StallingsGraph.{u, v, w} α),
      [Finite R.graph.E] →
      Nat.card R.graph.E = n →
      ∃ T : StallingsGraph.{u, v, w} α, FoldSequence R T ∧ T.IsFolded := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro R _ hn
      by_cases hR : R.IsFolded
      · exact ⟨R, .refl, hR⟩
      · rw [R.isFolded_def] at hR
        push Not at hR
        obtain ⟨e, f, hsrc, hlabel, hne⟩ := hR
        let Q := R.foldAt e f hsrc hlabel
        have hlt : Nat.card Q.graph.E < n := by
          exact hn ▸ R.card_foldAt_lt e f hne hsrc hlabel
        obtain ⟨T, hchain, hfolded⟩ := ih _ hlt Q rfl
        have hstep : FoldSequence R Q :=
          Relation.ReflTransGen.single ⟨e, f, hsrc, hlabel, hne, rfl⟩
        exact ⟨T, hstep.trans hchain, hfolded⟩
  exact aux (Nat.card S.graph.E) S rfl

end TauCeti.StallingsGraph

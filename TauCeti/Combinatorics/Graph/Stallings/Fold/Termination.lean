/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Fold.Subgroup
public import TauCeti.Combinatorics.Graph.Stallings.Folded
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Set.Card

/-!
# Finite Stallings folding

A fold of two distinct equally labelled darts removes exactly one pair of mutually reverse
darts, and removes one vertex exactly when the termini of the two darts differ.
Consequently a finite labelled graph admits a finite sequence of folds ending in a folded
graph. Every step preserves the subgroup read at the base vertex. This is the termination
step in the construction of a finite folded graph from a flower of generating words.
The fold sequence yields a surjective quotient morphism to the folded graph.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 2, Lemma 2.5 and Section 3, Proposition 3.8.
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

/-- A sequence of folds has a quotient morphism surjective on vertices and darts. -/
theorem FoldSequence.exists_surjective_hom {S T : StallingsGraph.{u, v, w} α}
    (h : FoldSequence S T) :
    ∃ f : S.Hom T, Function.Surjective f.graphHom.mapV ∧
      Function.Surjective f.graphHom.mapE := by
  induction h with
  | refl =>
    refine ⟨Hom.id _, ?_, ?_⟩
    · simpa only [Hom.id_graphHom, SerreGraph.Hom.id_mapV] using
        (Function.surjective_id : Function.Surjective (id : S.graph.V → S.graph.V))
    · simpa only [Hom.id_graphHom, SerreGraph.Hom.id_mapE] using
        (Function.surjective_id : Function.Surjective (id : S.graph.E → S.graph.E))
  | tail h hstep ih =>
    obtain ⟨e, f, hsrc, hlabel, _, rfl⟩ := hstep
    obtain ⟨g, hgv, hge⟩ := ih
    refine ⟨Hom.comp (foldHom _ e f hsrc hlabel) g, ?_, ?_⟩
    · simpa only [Hom.comp_graphHom, SerreGraph.Hom.comp_mapV] using
        (foldHom_mapV_surjective _ e f hsrc hlabel).comp hgv
    · simpa only [Hom.comp_graphHom, SerreGraph.Hom.comp_mapE] using
        (foldHom_mapE_surjective _ e f hsrc hlabel).comp hge

/-- Folding two distinct darts removes exactly one pair of mutually reverse darts. -/
theorem card_foldAt_E_add_two (S : StallingsGraph.{u, v, w} α) [Finite S.graph.E]
    (e f : S.graph.E) (hne : e ≠ f) (hsrc : S.graph.src e = S.graph.src f)
    (hlabel : S.label e = S.label f) :
    Nat.card (S.foldAt e f hsrc hlabel).graph.E + 2 = Nat.card S.graph.E := by
  have hrev : e ≠ S.graph.rev f := fun h => by
    have hl := S.label_rev f
    rw [← h, hlabel] at hl
    simpa using congrArg Prod.snd hl
  have hbij : Function.Bijective fun d : ({f, S.graph.rev f}ᶜ : Set S.graph.E) =>
      (S.foldHom e f hsrc hlabel).graphHom.mapE d := by
    refine ⟨fun x y h => Subtype.ext ?_, fun q => ?_⟩
    · have hx := x.2
      have hy := y.2
      rw [foldHom_mapE_eq_iff_eq_or] at h
      grind
    · obtain ⟨d, rfl⟩ := S.foldHom_mapE_surjective e f hsrc hlabel q
      by_cases hd : d = f
      · subst hd
        exact ⟨⟨e, by simp [hne, hrev]⟩, S.foldHom_mapE_eq e d hsrc hlabel⟩
      by_cases hd' : d = S.graph.rev f
      · have hrev' : S.graph.rev e ≠ f := fun h => hrev (by rw [← h, S.graph.rev_rev])
        exact ⟨⟨S.graph.rev e, by simp [hrev', S.graph.rev_injective.ne hne]⟩, by
          simp only [hd', SerreGraph.Hom.map_rev, S.foldHom_mapE_eq e f hsrc hlabel]⟩
      · exact ⟨⟨d, by simp [hd, hd']⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_coe_set_eq,
    ← Set.ncard_add_ncard_compl {f, S.graph.rev f}, Set.ncard_pair (S.graph.rev_ne f).symm,
    add_comm]

/-- Folding distinct darts strictly decreases the number of darts. -/
theorem card_foldAt_lt (S : StallingsGraph.{u, v, w} α) [Finite S.graph.E]
    (e f : S.graph.E) (hne : e ≠ f)
    (hsrc : S.graph.src e = S.graph.src f)
    (hlabel : S.label e = S.label f) :
    Nat.card (S.foldAt e f hsrc hlabel).graph.E < Nat.card S.graph.E := by
  have := S.card_foldAt_E_add_two e f hne hsrc hlabel
  omega

/-- Folding two darts with distinct termini removes exactly one vertex. -/
theorem card_foldAt_V_add_one (S : StallingsGraph.{u, v, w} α) [Finite S.graph.V]
    (e f : S.graph.E) (hsrc : S.graph.src e = S.graph.src f) (hlabel : S.label e = S.label f)
    (htgt : S.graph.tgt e ≠ S.graph.tgt f) :
    Nat.card (S.foldAt e f hsrc hlabel).graph.V + 1 = Nat.card S.graph.V := by
  have hbij : Function.Bijective fun x : ({S.graph.tgt f}ᶜ : Set S.graph.V) =>
      (S.foldHom e f hsrc hlabel).graphHom.mapV x := by
    refine ⟨fun x y h => Subtype.ext ?_, fun q => ?_⟩
    · have hx := x.2
      have hy := y.2
      rw [foldHom_mapV_eq_iff_eq_or] at h
      grind
    · obtain ⟨x, rfl⟩ := S.foldHom_mapV_surjective e f hsrc hlabel q
      by_cases hx : x = S.graph.tgt f
      · subst hx
        exact ⟨⟨S.graph.tgt e, htgt⟩, S.foldHom_mapV_tgt_eq e f hsrc hlabel⟩
      · exact ⟨⟨x, hx⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_coe_set_eq,
    ← Set.ncard_add_ncard_compl {S.graph.tgt f}, Set.ncard_singleton, add_comm]

/-- Folding two darts with a common terminus keeps the number of vertices. -/
theorem card_foldAt_V_of_tgt_eq (S : StallingsGraph.{u, v, w} α)
    (e f : S.graph.E) (hsrc : S.graph.src e = S.graph.src f) (hlabel : S.label e = S.label f)
    (htgt : S.graph.tgt e = S.graph.tgt f) :
    Nat.card (S.foldAt e f hsrc hlabel).graph.V = Nat.card S.graph.V :=
  (Nat.card_eq_of_bijective _ ⟨S.foldHom_mapV_injective e f hsrc hlabel htgt,
    S.foldHom_mapV_surjective e f hsrc hlabel⟩).symm

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
    | ind n ih =>
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

/-- Every finite labelled graph has a finite folded quotient with the same accepted subgroup.
The quotient map is surjective on vertices and darts, so connected input remains connected. -/
theorem exists_folded_quotient (S : StallingsGraph.{u, v, w} α)
    [Finite S.graph.V] [Finite S.graph.E] :
    ∃ (T : StallingsGraph.{u, v, w} α),
      Finite T.graph.V ∧ Finite T.graph.E ∧
        ∃ f : S.Hom T, T.IsFolded ∧
          Function.Surjective f.graphHom.mapV ∧
          Function.Surjective f.graphHom.mapE ∧
          T.subgroup T.base = S.subgroup S.base ∧
          (S.graph.Connected → T.graph.Connected) := by
  obtain ⟨T, hseq, hfold⟩ := S.exists_foldSequence_isFolded
  obtain ⟨f, hfv, hfe⟩ := hseq.exists_surjective_hom
  exact ⟨T, hseq.finite_V, hseq.finite_E, f, hfold, hfv, hfe,
    hseq.subgroup_base, hseq.connected⟩

end TauCeti.StallingsGraph

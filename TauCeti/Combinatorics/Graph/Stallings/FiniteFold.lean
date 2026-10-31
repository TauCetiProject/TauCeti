/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Fold
public import TauCeti.Combinatorics.Graph.Stallings.Folded
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Finite folding of labelled graphs

Every finite labelled graph has a folded quotient. Repeatedly identifying two outgoing darts
with the same label terminates because each nontrivial fold strictly decreases the number of
darts. The quotient morphism remains surjective on vertices and darts.

The folding construction follows I. Kapovich and A. Myasnikov, *Stallings foldings and
subgroups of free groups*, §2, Definition 2.4 and Lemma 2.5.
-/

public section

namespace TauCeti.StallingsGraph

universe u v w

/-- A morphism obtained by composing finitely many single-fold quotient morphisms. -/
inductive IsFoldSequence {α : Type u} :
    {S T : StallingsGraph.{u, v, w} α} → S.Hom T → Prop
  | id (S : StallingsGraph.{u, v, w} α) : IsFoldSequence (Hom.id S)
  | fold {S T : StallingsGraph.{u, v, w} α}
      (e f : S.graph.E) (hs : S.graph.src e = S.graph.src f)
      (hl : S.label e = S.label f) (g : (S.foldAt e f hs hl).Hom T)
      (hg : IsFoldSequence g) :
      IsFoldSequence (Hom.comp g (S.foldHom e f hs hl))

private theorem exists_folded_quotient_aux {α : Type u} (n : ℕ) :
    ∀ (S : StallingsGraph.{u, v, w} α),
      [Finite S.graph.V] → [Finite S.graph.E] → Nat.card S.graph.E = n →
      ∃ T : StallingsGraph.{u, v, w} α,
        ∃ _ : Finite T.graph.V, ∃ _ : Finite T.graph.E,
          T.IsFolded ∧ ∃ f : S.Hom T,
            Function.Surjective f.graphHom.mapV ∧
              Function.Surjective f.graphHom.mapE ∧ IsFoldSequence f := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S instV instE hn
    by_cases hfold : S.IsFolded
    · refine ⟨S, instV, instE, hfold, Hom.id S, ?_, ?_, IsFoldSequence.id S⟩
      · intro x
        exact ⟨x, by simp⟩
      · intro x
        exact ⟨x, by simp⟩
    · have hbad : ∃ e f : S.graph.E,
          S.graph.src e = S.graph.src f ∧ S.label e = S.label f ∧ e ≠ f := by
        have hnot : ¬ ∀ e f : S.graph.E,
            S.graph.src e = S.graph.src f → S.label e = S.label f → e = f :=
          fun h => hfold (S.isFolded_def.mpr h)
        push Not at hnot
        obtain ⟨e, f, hs, hl, hne⟩ := hnot
        exact ⟨e, f, hs, hl, hne⟩
      obtain ⟨e, f, hs, hl, hne⟩ := hbad
      let U := S.foldAt e f hs hl
      have hsmall : Nat.card U.graph.E < n := by
        have hc := @Fintype.card_lt_of_surjective_not_injective
          S.graph.E U.graph.E (Fintype.ofFinite _) (Fintype.ofFinite _)
          (S.foldHom e f hs hl).graphHom.mapE
          (S.foldHom_mapE_surjective e f hs hl)
          (fun hinj => hne (hinj (S.foldHom_mapE_eq e f hs hl)))
        simpa only [Fintype.card_eq_nat_card, hn] using hc
      obtain ⟨T, hTV, hTE, hT, g, hgV, hgE, hgSeq⟩ :=
        ih (Nat.card U.graph.E) hsmall U rfl
      let q := S.foldHom e f hs hl
      let h := Hom.comp g q
      refine ⟨T, hTV, hTE, hT, h, ?_, ?_, IsFoldSequence.fold e f hs hl g hgSeq⟩
      · simpa only [h, q, Hom.comp_graphHom, SerreGraph.Hom.comp_mapV] using
          hgV.comp (S.foldHom_mapV_surjective e f hs hl)
      · simpa only [h, q, Hom.comp_graphHom, SerreGraph.Hom.comp_mapE] using
          hgE.comp (S.foldHom_mapE_surjective e f hs hl)

/-- A finite labelled graph has a folded quotient, reached by a finite sequence of folds.
The resulting based label-preserving morphism is surjective on vertices and darts. -/
theorem exists_folded_quotient {α : Type u} (S : StallingsGraph.{u, v, w} α)
    [Finite S.graph.V] [Finite S.graph.E] :
    ∃ T : StallingsGraph.{u, v, w} α,
      ∃ _ : Finite T.graph.V, ∃ _ : Finite T.graph.E,
        T.IsFolded ∧ ∃ f : S.Hom T,
          Function.Surjective f.graphHom.mapV ∧
            Function.Surjective f.graphHom.mapE ∧ IsFoldSequence f :=
  exists_folded_quotient_aux (Nat.card S.graph.E) S rfl

end TauCeti.StallingsGraph

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Fold.Basic
public import Mathlib.Data.Set.Card

/-!
# Counting vertices and darts of a Stallings fold

A fold of two distinct equally labelled darts with a common source removes exactly one pair of
mutually reverse darts, so it strictly decreases the number of darts. It removes exactly one
vertex when the termini of the two darts differ, and keeps the number of vertices when they
coincide.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 2, Lemma 2.5.
-/

public section

namespace TauCeti.StallingsGraph

universe u v w

variable {α : Type u}

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
      rw [foldHom_mapE_eq_iff] at h
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
      rw [foldHom_mapV_eq_iff] at h
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

end TauCeti.StallingsGraph

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Colored.Counting
public import TauCeti.Combinatorics.Hypergraph.Colored.EditDiscrepancy
public import TauCeti.Data.Fintype.EmbeddingFiber

import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Stability of induced colored counts under edits

Changing one unordered triple can affect an induced labeled copy only if one of its pattern
triples maps onto that triple. A union bound over the pattern triples therefore controls the
change in induced counts by the edit discrepancy, with coefficient `k.choose 3` and scale
`|V|^k`. The estimate includes nonedges because they are palette values, and requires no
regularity or finite palette.

This is the elementary edit-transfer step in induced counting; see Rödl–Schacht,
*Regular Partitions of Hypergraphs: Counting Lemmas* (2007). The normalization of edit
discrepancy counts six orderings of every edited unordered triple.
-/

public section

open Finset

namespace TauCeti
namespace Colored3Graph

variable {κ V : Type*} [Fintype V]

/-- The number of injections whose restricted colorings disagree is bounded by a union over
source triples and edited host triples. -/
theorem card_comap_ne_le (H H' : Colored3Graph κ V) {W : Type*} [Fintype W] :
    Nat.card {f : W ↪ V // H.comap f ≠ H'.comap f} ≤
      (Fintype.card W).choose 3 *
        (6 * {t | H.color t ≠ H'.color t}.ncard *
          Fintype.card V ^ (Fintype.card W - 3)) := by
  classical
  let edits : Finset (Set.powersetCard V 3) :=
    univ.filter fun t ↦ H.color t ≠ H'.color t
  let bad (s : Set.powersetCard W 3) : Finset (W ↪ V) :=
    univ.filter fun f ↦ Set.powersetCard.map 3 f s ∈ edits
  -- Fixing a source triple leaves six orderings of an edited host triple.
  have hbad (s : Set.powersetCard W 3) :
      #(bad s) ≤ #edits * (6 * Fintype.card V ^ (Fintype.card W - 3)) := by
    rw [card_eq_sum_card_fiberwise (f := fun f ↦ Set.powersetCard.map 3 f s)
      (t := edits) (by intro f hf; exact (mem_filter.mp hf).2)]
    calc
      _ ≤ ∑ t ∈ edits, 6 * Fintype.card V ^ (Fintype.card W - 3) := by
        apply sum_le_sum
        intro t ht
        calc
          _ ≤ #{f : W ↪ V | Set.powersetCard.map 3 f s = t} :=
            card_le_card (by
              intro f hf
              exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hf).2⟩)
          _ ≤ _ := by
            simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype,
              Nat.factorial_succ, Nat.factorial_zero] using
              (card_embedding_map_eq_le (s := s) (t := t))
      _ = _ := by simp
  -- Every changed restriction contains a source triple witnessing the change.
  have hcover :
      univ.filter (fun f : W ↪ V ↦ H.comap f ≠ H'.comap f) ⊆ univ.biUnion bad := by
    intro f hf
    have hne := (mem_filter.mp hf).2
    have hex : ∃ s, H.color (Set.powersetCard.map 3 f s) ≠
        H'.color (Set.powersetCard.map 3 f s) := by
      by_contra! heq
      exact hne (Colored3Graph.ext (funext (by simpa only [color_comap] using heq)))
    obtain ⟨s, hs⟩ := hex
    exact mem_biUnion.mpr ⟨s, mem_univ _, by simp [bad, edits, hs]⟩
  calc
    _ = #(univ.filter (fun f : W ↪ V ↦ H.comap f ≠ H'.comap f)) := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ #(univ.biUnion bad) := card_le_card hcover
    _ ≤ ∑ s, #(bad s) := card_biUnion_le
    _ ≤ ∑ _ : Set.powersetCard W 3,
        #edits * (6 * Fintype.card V ^ (Fintype.card W - 3)) := sum_le_sum fun s _ ↦ hbad s
    _ = _ := by
      have he : #edits = {t | H.color t ≠ H'.color t}.ncard := by
        simp [edits, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_subtype]
      have hc : Fintype.card (Set.powersetCard W 3) = (Fintype.card W).choose 3 := by
        simpa only [Nat.card_eq_fintype_card] using Set.powersetCard.card W 3
      simp [he, hc, mul_assoc, mul_left_comm, mul_comm]

private theorem abs_inducedCopyCount_sub_le_edits (H H' : Colored3Graph κ V)
    (F : FiniteColored3Pattern κ) :
    |(H.inducedCopyCount F : ℝ) - H'.inducedCopyCount F| ≤
      (F.k.choose 3 : ℝ) *
        (6 * {t | H.color t ≠ H'.color t}.ncard *
          (Fintype.card V : ℝ) ^ (F.k - 3)) := by
  classical
  let bad : Finset (Fin F.k ↪ V) := univ.filter fun f ↦ H.comap f ≠ H'.comap f
  have hmem (f : Fin F.k ↪ V) (h : H.comap f = H'.comap f) :
      f ∈ H.inducedCopies F ↔ f ∈ H'.inducedCopies F := by
    simp only [mem_inducedCopies, isInducedCopy_iff, ← color_comap, h]
  have h₁ : H.inducedCopies F ⊆ H'.inducedCopies F ∪ bad := by
    intro f hf
    by_cases h : H.comap f = H'.comap f
    · exact mem_union_left _ ((hmem f h).mp hf)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h⟩)
  have h₂ : H'.inducedCopies F ⊆ H.inducedCopies F ∪ bad := by
    intro f hf
    by_cases h : H.comap f = H'.comap f
    · exact mem_union_left _ ((hmem f h).mpr hf)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h⟩)
  have hc₁ := (card_le_card h₁).trans (card_union_le _ _)
  have hc₂ := (card_le_card h₂).trans (card_union_le _ _)
  have hb : #bad ≤ F.k.choose 3 *
      (6 * {t | H.color t ≠ H'.color t}.ncard * Fintype.card V ^ (F.k - 3)) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_fin]
      using (H.card_comap_ne_le H' (W := Fin F.k))
  rw [inducedCopyCount_def, inducedCopyCount_def]
  have hc₁' : ((H.inducedCopies F).card : ℝ) ≤ (H'.inducedCopies F).card + (#bad : ℝ) :=
    by exact_mod_cast hc₁
  have hc₂' : ((H'.inducedCopies F).card : ℝ) ≤ (H.inducedCopies F).card + (#bad : ℝ) :=
    by exact_mod_cast hc₂
  have hb' : (#bad : ℝ) ≤ (F.k.choose 3 : ℝ) *
      (6 * {t | H.color t ≠ H'.color t}.ncard *
        (Fintype.card V : ℝ) ^ (F.k - 3)) := by exact_mod_cast hb
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Editing a fraction `δ` of ordered host triples changes the induced count by at most
`k.choose 3 * δ * |V|^k`. This includes empty hosts and patterns with fewer than three vertices. -/
theorem inducedCopyCount_edit_transfer (H H' : Colored3Graph κ V)
    (F : FiniteColored3Pattern κ) :
    |(H.inducedCopyCount F : ℝ) - H'.inducedCopyCount F| ≤
      (F.k.choose 3 : ℝ) * (H.editDiscrepancy3 H' : ℝ) * (Fintype.card V : ℝ) ^ F.k := by
  by_cases hk : F.k < 3
  · simp [inducedCopyCount_of_lt_three _ _ hk, Nat.choose_eq_zero_of_lt hk]
  by_cases hn : Fintype.card V = 0
  · have hk₀ : 0 < F.k := by omega
    simp [inducedCopyCount_eq_zero_of_card_lt _ _ (by omega : Fintype.card V < F.k),
      hn, hk₀.ne']
  have hn' : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hn
  convert H.abs_inducedCopyCount_sub_le_edits H' F using 1
  rw [editDiscrepancy3_def]
  push_cast
  rw [Nat.card_eq_fintype_card]
  have hpow : (Fintype.card V : ℝ) ^ F.k =
      (Fintype.card V : ℝ) ^ (F.k - 3) * (Fintype.card V : ℝ) ^ 3 := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : 3 ≤ F.k)]
  rw [hpow]
  field_simp
  norm_cast

/-- An edit approximation controls every induced colored pattern count, independently of the
regularity properties of the approximating coloring. -/
theorem Approximates3.inducedCopyCount_sub_le {H H' : Colored3Graph κ V} {δ : ℝ}
    (h : H.Approximates3 H' δ) (F : FiniteColored3Pattern κ) :
    |(H.inducedCopyCount F : ℝ) - H'.inducedCopyCount F| ≤
      (F.k.choose 3 : ℝ) * δ * (Fintype.card V : ℝ) ^ F.k := by
  apply (H.inducedCopyCount_edit_transfer H' F).trans
  gcongr
  exact (approximates3_iff _ _ _).mp h

end Colored3Graph
end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.TopRegular
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Stability of top regularity under small changes of the support

Recoloring the pairs of a lower skeleton moves triples between polyads. A polyad `P'` of the new
skeleton then has a counterpart `P` of the old one, for instance the polyad with the same cells
and colors, whose support differs from that of `P'` only in the moved triples. If the moved
triples are at most an `η`-fraction of both supports, top regularity of a coloring over `P`
passes to `P'` at a parameter `ε` with `δ + 2η + η / ε ≤ ε`, at the same rank.

The two polyads may live over different skeletons, and neither pair graph need lie in the other,
so neither the slicing lemma nor density inheritance applies. Instead, every subpolyad of `P'`
is restricted to `P` (`Subpolyad3.restrict`), and the densities over the two supports are both
compared with the density over their intersection. All supports count role-ordered injective
triples.

## Main results

* `TauCeti.Colored3Graph.IsTopRegularOverPolyad.of_card_sdiff_support_le`: top regularity
  over `P` passes to every polyad `P'` whose support differs from that of `P` in a small
  fraction of each.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset

namespace TauCeti.Colored3Graph

open Subpolyad3

variable {κ κ₂ κ₂' V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]
  {S : PairSkeleton3 κ₂ V} {S' : PairSkeleton3 κ₂' V} {P : Polyad3 S} {P' : Polyad3 S'}
  {H : Colored3Graph κ V} {δ ε η : ℝ} {r : ℕ}

/-- **Top regularity under a change of support.** If `H` is `(δ, r)`-top-regular over `P`, and
the supports of `P` and `P'` each have at most an `η`-fraction of their triples outside the
other, then `H` is `(ε, r)`-top-regular over `P'` whenever `δ + 2η + η / ε ≤ ε`. The polyads may
live over different skeletons. -/
theorem IsTopRegularOverPolyad.of_card_sdiff_support_le (h : H.IsTopRegularOverPolyad P δ r)
    (hε : 0 < ε) (hη : 0 ≤ η) (hbudget : δ + 2 * η + η / ε ≤ ε)
    (h₁ : (#(P'.support \ P.support) : ℝ) ≤ η * #P'.support)
    (h₂ : (#(P.support \ P'.support) : ℝ) ≤ η * #P.support) :
    H.IsTopRegularOverPolyad P' ε r := by
  obtain hε₁ | hε₁ := le_or_gt 1 ε
  · exact isTopRegularOverPolyad_of_one_le (H := H) (P := P') (r := r) hε₁
  rw [isTopRegularOverPolyad_iff]
  intro c Q hQ
  have hδ : 0 ≤ δ := haveI : Nonempty κ := ⟨c⟩; h.nonneg
  have hηε : 0 ≤ η / ε := div_nonneg hη hε.le
  -- The test is restricted to `P`; the restriction loses only triples outside `P`.
  have hU := unionSupport_restrict Q P
  have hUsub : unionSupport (fun i ↦ (Q i).restrict P) ⊆ unionSupport Q :=
    hU ▸ inter_subset_left
  have hUsdiff : unionSupport Q \ unionSupport (fun i ↦ (Q i).restrict P) ⊆
      P'.support \ P.support := by
    intro x hx
    rw [hU, mem_sdiff, mem_inter, not_and] at hx
    exact mem_sdiff.2 ⟨unionSupport_subset Q hx.1, hx.2 hx.1⟩
  have hcardU : (#(unionSupport Q \ unionSupport fun i ↦ (Q i).restrict P) : ℝ) ≤
      η * #P'.support := (Nat.cast_le.2 (card_le_card hUsdiff)).trans h₁
  -- The restricted test passes the size threshold over `P`.
  have hPP' : (1 - η) * #P.support ≤ #P'.support := by
    have h := card_le_card_sdiff_add_card (s := P.support) (t := P'.support)
    have : (#P.support : ℝ) ≤ #(P.support \ P'.support) + #P'.support := by exact_mod_cast h
    linarith
  have hsize : δ * #P.support ≤ #(unionSupport fun i ↦ (Q i).restrict P) := by
    have h := card_sdiff_add_card_eq_card hUsub
    have hU' : (#(unionSupport Q \ unionSupport fun i ↦ (Q i).restrict P) : ℝ) +
        #(unionSupport fun i ↦ (Q i).restrict P) = #(unionSupport Q) := by exact_mod_cast h
    have hP₀ : (0 : ℝ) ≤ #P.support := Nat.cast_nonneg _
    have hεη : 0 ≤ ε - η := by linarith
    calc δ * #P.support ≤ (ε - η) * (1 - η) * #P.support := by
          gcongr
          nlinarith
      _ ≤ (ε - η) * #P'.support := by rw [mul_assoc]; gcongr
      _ ≤ _ := by linarith
  -- Compare the four densities.
  have d₁ := H.abs_relDensityOn_sub_le_div_of_card_sdiff_le c hUsub hε hη hQ hcardU
  have d₂ := isTopRegularOverPolyad_iff.1 h c (fun i ↦ (Q i).restrict P) hsize
  have d₃ := H.abs_relDensityOn_sub_le_div_of_card_sdiff_le c (N := #P.support)
    (inter_subset_left (s₁ := P.support) (s₂ := P'.support)) one_pos hη (by rw [one_mul])
    (by rwa [sdiff_inter_self_left])
  have d₄ := H.abs_relDensityOn_sub_le_div_of_card_sdiff_le c (N := #P'.support)
    (inter_subset_right (s₁ := P.support) (s₂ := P'.support)) one_pos hη (by rw [one_mul])
    (by rwa [sdiff_inter_self_right])
  rw [div_one] at d₃ d₄
  rw [relativeDensity_def] at d₂ ⊢
  calc _ ≤ |(H.relDensityOn c (unionSupport Q) : ℝ) -
          H.relDensityOn c (unionSupport fun i ↦ (Q i).restrict P)| +
        |(H.relDensityOn c (unionSupport fun i ↦ (Q i).restrict P) : ℝ) -
          H.relDensityOn c P.support| +
        |(H.relDensityOn c P.support : ℝ) - H.relDensityOn c (P.support ∩ P'.support)| +
        |(H.relDensityOn c P'.support : ℝ) - H.relDensityOn c (P.support ∩ P'.support)| := by
        have := abs_sub_le (H.relDensityOn c (unionSupport Q) : ℝ)
          (H.relDensityOn c (unionSupport fun i ↦ (Q i).restrict P))
          (H.relDensityOn c P'.support)
        have := abs_sub_le (H.relDensityOn c (unionSupport fun i ↦ (Q i).restrict P) : ℝ)
          (H.relDensityOn c P.support) (H.relDensityOn c P'.support)
        have := abs_sub_le (H.relDensityOn c P.support : ℝ)
          (H.relDensityOn c (P.support ∩ P'.support)) (H.relDensityOn c P'.support)
        rw [abs_sub_comm (H.relDensityOn c (P.support ∩ P'.support) : ℝ)] at this
        linarith
    _ ≤ η / ε + δ + η + η := by linarith
    _ ≤ ε := by linarith

end TauCeti.Colored3Graph

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Colored.EditDiscrepancy
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith

/-!
# Relative color densities and their stability under edits

For a coloring `H` of the unordered triples of `V`, the relative density `H.relDensityOn c supp`
of a color `c` over a finite support of injective triples is the fraction of the supported
triples whose underlying unordered triple has color `c`. Colors are read through the underlying
unordered triple, while the normalization counts the supported ordered injections, so a triple
contributes once for each of its supported orderings, both to the count and to the normalization.
The relative density is `0` on the empty support.

Relative densities lie between `0` and `1`, and on a nonempty support the densities of all colors
sum to one. Splitting a color by a labelling of the triples splits its density: the densities of
the split colors `(c, i)` sum to the density of `c`, and each lies within `b` of a `1 / |ι|` share
of it once the count discrepancy `splitDiscrepancy` is at most `b` times the support size.
Recoloring changes `relDensityOn`,
multiplied by the support size, by at most the number of supported edited triples `editedOn`,
defined in `TauCeti.Combinatorics.Hypergraph.Colored.EditDiscrepancy`.

## Main definitions

* `TauCeti.Colored3Graph.relDensityOn`: the relative density of a color over a support.
* `TauCeti.Colored3Graph.splitDiscrepancy`: the count of a split color on a support minus a
  `1 / |ι|` share of the count of its parent color.

## Main results

* `TauCeti.Colored3Graph.sum_relDensityOn`: on a nonempty support the densities sum to one.
* `TauCeti.Colored3Graph.sum_relDensityOn_split`: the split densities of a color sum to its
  density.
* `TauCeti.Colored3Graph.abs_relDensityOn_split_sub_le`: a small count discrepancy of a split
  color gives a small density discrepancy.
* `TauCeti.Colored3Graph.abs_relDensityOn_sub_mul_card_le_card_editedOn`: the count-scaled
  density change is bounded by the supported edit count.
* `TauCeti.Colored3Graph.abs_relDensityOn_sub_le_div_of_card_editedOn_le`: an `η`-fraction
  of edits on a support changes density on an `ε`-fraction subsupport by at most `η / ε`.
* `TauCeti.Colored3Graph.abs_relDensityOn_sub_le_div_of_card_sdiff_le`: removing few triples
  from a support changes the density of every color by little.
-/

public section

open Finset

namespace TauCeti

namespace Colored3Graph

variable {κ V : Type*} [DecidableEq κ]

/-- The relative density of the color `c` over a finite support of injective triples: the fraction
of supported triples whose underlying unordered triple has color `c`. It is `0` on the empty
support. -/
def relDensityOn (H : Colored3Graph κ V) (c : κ)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) : ℚ :=
  #{x ∈ supp | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c} / #supp

/-- The relative density counts supported triples whose underlying triple has color `c`. -/
theorem relDensityOn_def (H : Colored3Graph κ V) (c : κ)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) :
    H.relDensityOn c supp =
      #{x ∈ supp | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c} / #supp :=
  (rfl)

/-- Multiplying a relative density by the support size recovers the color count, including
when the support is empty. -/
theorem relDensityOn_mul_card (H : Colored3Graph κ V) (c : κ)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) :
    H.relDensityOn c supp * #supp =
      (#{x ∈ supp | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c} : ℚ) := by
  obtain rfl | hs := supp.eq_empty_or_nonempty
  · simp
  · rw [relDensityOn_def, div_mul_cancel₀ _ (by exact_mod_cast hs.card_pos.ne')]

/-- Recoloring changes a color count by at most the number of edited supported triples.
The count-scaled form includes empty supports and does not require a finite palette. -/
theorem abs_relDensityOn_sub_mul_card_le_card_editedOn (H H' : Colored3Graph κ V) (c : κ)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) :
    |H.relDensityOn c supp - H'.relDensityOn c supp| * #supp ≤
      (#(H.editedOn H' supp) : ℚ) := by
  rw [editedOn_def]
  rw [← abs_of_nonneg (Nat.cast_nonneg (α := ℚ) #supp), ← abs_mul, sub_mul,
    relDensityOn_mul_card, relDensityOn_mul_card]
  simp only [← sum_boole]
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ ↦ ?_)
  by_cases h : H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) =
      H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩)
  · simp [h]
  · split_ifs <;> simp

/-- Recoloring at most an `η`-fraction of `B` changes the density on any subsupport `A`
carrying at least an `ε`-fraction of `B` by at most `η / ε`. Empty supports are allowed. -/
theorem abs_relDensityOn_sub_le_div_of_card_editedOn_le (H H' : Colored3Graph κ V) (c : κ)
    {A B : Finset {x : Fin 3 → V // Function.Injective x}} {ε η : ℝ}
    (hAB : A ⊆ B) (hε : 0 < ε) (hη : 0 ≤ η) (hsize : ε * #B ≤ #A)
    (hedit : (#(H.editedOn H' B) : ℝ) ≤ η * #B) :
    |(H.relDensityOn c A : ℝ) - H'.relDensityOn c A| ≤ η / ε := by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · have hA := subset_empty.1 hAB
    simp [hA, relDensityOn_def, div_nonneg hη hε.le]
  have hBpos : (0 : ℝ) < #B := Nat.cast_pos.2 hB.card_pos
  have hd : |(H.relDensityOn c A : ℝ) - H'.relDensityOn c A| * #A ≤
      (#(H.editedOn H' A) : ℝ) := by
    exact_mod_cast H.abs_relDensityOn_sub_mul_card_le_card_editedOn H' c A
  have hmono : (#(H.editedOn H' A) : ℝ) ≤ #(H.editedOn H' B) := by
    exact_mod_cast card_le_card (H.editedOn_mono H' hAB)
  apply (le_div_iff₀ hε).2
  apply (mul_le_mul_iff_left₀ hBpos).1
  calc
    _ = |(H.relDensityOn c A : ℝ) - H'.relDensityOn c A| * (ε * #B) := by ac_rfl
    _ ≤ |(H.relDensityOn c A : ℝ) - H'.relDensityOn c A| * #A :=
      mul_le_mul_of_nonneg_left hsize (abs_nonneg _)
    _ ≤ η * #B := hd.trans (hmono.trans hedit)

/-- Relative densities are nonnegative. -/
theorem relDensityOn_nonneg (H : Colored3Graph κ V) (c : κ)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) : 0 ≤ H.relDensityOn c supp := by
  rw [relDensityOn_def]
  positivity

/-- Relative densities are at most one. -/
theorem relDensityOn_le_one (H : Colored3Graph κ V) (c : κ)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) : H.relDensityOn c supp ≤ 1 := by
  rw [relDensityOn_def]
  exact div_le_one_of_le₀ (mod_cast card_filter_le _ _) (by positivity)

section Subset

variable [DecidableEq V]

/-- Shrinking a support to a subsupport changes the count-scaled density by at most the number
of removed triples. Empty supports are allowed. -/
theorem abs_relDensityOn_sub_mul_card_le_card_sdiff (H : Colored3Graph κ V) (c : κ)
    {A B : Finset {x : Fin 3 → V // Function.Injective x}} (hAB : A ⊆ B) :
    |H.relDensityOn c B - H.relDensityOn c A| * #B ≤ (#(B \ A) : ℚ) := by
  have hB := H.relDensityOn_mul_card c B
  have hA := H.relDensityOn_mul_card c A
  have hcard : (#(B \ A) : ℚ) + #A = #B := by exact_mod_cast card_sdiff_add_card_eq_card hAB
  -- The colored triples of `B` are those of `A` together with at most the removed ones.
  have hlow := card_le_card (filter_subset_filter
    (fun x ↦ H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c) hAB)
  have hsub : {x ∈ B | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c} ⊆
      {x ∈ A | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c} ∪ (B \ A) := by
    intro x hx
    obtain ⟨hxB, hx⟩ := mem_filter.1 hx
    by_cases hxA : x ∈ A
    · exact mem_union_left _ (mem_filter.2 ⟨hxA, hx⟩)
    · exact mem_union_right _ (mem_sdiff.2 ⟨hxB, hxA⟩)
  have hhigh := (card_le_card hsub).trans (card_union_le _ _)
  have h₀ := H.relDensityOn_nonneg c A
  have h₁ := H.relDensityOn_le_one c A
  rw [← abs_of_nonneg (Nat.cast_nonneg (α := ℚ) #B), ← abs_mul, sub_mul, hB, ← hcard, mul_add,
    hA, abs_le]
  have hlow' : (_ : ℚ) ≤ _ := Nat.cast_le.2 hlow
  have hhigh' : (_ : ℚ) ≤ _ := Nat.cast_le.2 hhigh
  push_cast at hlow' hhigh'
  constructor <;> nlinarith

/-- If at most `η N` triples are removed from a support `B` with `ε N ≤ #B`, the density of every
color changes by at most `η / ε`. Empty supports are allowed. -/
theorem abs_relDensityOn_sub_le_div_of_card_sdiff_le (H : Colored3Graph κ V) (c : κ)
    {A B : Finset {x : Fin 3 → V // Function.Injective x}} {N ε η : ℝ} (hAB : A ⊆ B)
    (hε : 0 < ε) (hη : 0 ≤ η) (hsize : ε * N ≤ #B) (hsdiff : (#(B \ A) : ℝ) ≤ η * N) :
    |(H.relDensityOn c B : ℝ) - H.relDensityOn c A| ≤ η / ε := by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · simp [subset_empty.1 hAB, div_nonneg hη hε.le]
  have hBpos : (0 : ℝ) < #B := Nat.cast_pos.2 hB.card_pos
  have hd : |(H.relDensityOn c B : ℝ) - H.relDensityOn c A| * #B ≤ #(B \ A) := by
    exact_mod_cast H.abs_relDensityOn_sub_mul_card_le_card_sdiff c hAB
  have hN : η * N ≤ η / ε * #B := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hε, mul_assoc]
    exact mul_le_mul_of_nonneg_left (by linarith) hη
  exact le_of_mul_le_mul_right (hd.trans (hsdiff.trans hN)) hBpos

end Subset

/-- Every relative density over the empty support is `0`. -/
@[simp]
theorem relDensityOn_empty (H : Colored3Graph κ V) (c : κ) : H.relDensityOn c ∅ = 0 := by
  simp [relDensityOn_def]

/-- The relative density of the color of a constant coloring is one on a nonempty support. -/
theorem relDensityOn_const_self {c : κ} {supp : Finset {x : Fin 3 → V // Function.Injective x}}
    (h : supp.Nonempty) : (const c : Colored3Graph κ V).relDensityOn c supp = 1 := by
  rw [relDensityOn_def, div_eq_one_iff_eq (by exact_mod_cast h.card_pos.ne')]
  simp

/-- The relative density of any other color of a constant coloring is zero. -/
@[simp]
theorem relDensityOn_const_of_ne {c₀ c : κ} (h : c₀ ≠ c)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) :
    (const c₀ : Colored3Graph κ V).relDensityOn c supp = 0 := by
  simp [relDensityOn_def, h]

/-- **The relative densities of all colors sum to one** on a nonempty support. -/
theorem sum_relDensityOn [Fintype κ] (H : Colored3Graph κ V)
    {supp : Finset {x : Fin 3 → V // Function.Injective x}} (h : supp.Nonempty) :
    ∑ c, H.relDensityOn c supp = 1 := by
  simp only [relDensityOn_def, ← sum_div]
  rw [div_eq_one_iff_eq (by exact_mod_cast h.card_pos.ne')]
  -- Every supported triple has exactly one color.
  exact_mod_cast (card_eq_sum_card_fiberwise fun _ _ => mem_univ _).symm

/-- Merging the split colors `(c, i)` over all labels `i` recovers the relative density of `c`. -/
theorem sum_relDensityOn_split {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Colored3Graph κ V)
    (f : Set.powersetCard V 3 → ι) (c : κ)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) :
    ∑ i, (H.split f).relDensityOn (c, i) supp = H.relDensityOn c supp := by
  simp only [relDensityOn_def, ← sum_div, color_split, Prod.mk.injEq]
  congr 1
  rw [card_eq_sum_card_fiberwise
    (f := fun x ↦ f (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩))
    (t := univ) fun _ _ ↦ mem_univ _]
  simp [filter_filter]

section Split

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The count discrepancy of the split color `(c, i)` on a set `s` of injective triples: the
number of triples of `s` of split color `(c, i)` minus a `1 / |ι|` share of the number of triples
of color `c`. -/
noncomputable def splitDiscrepancy (H : Colored3Graph κ V) (f : Set.powersetCard V 3 → ι) (c : κ)
    (i : ι) (s : Finset {x : Fin 3 → V // Function.Injective x}) : ℝ :=
  #{x ∈ s | (H.split f).color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = (c, i)} -
    (#{x ∈ s | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c} : ℝ) /
      Fintype.card ι

theorem splitDiscrepancy_def (H : Colored3Graph κ V) (f : Set.powersetCard V 3 → ι) (c : κ)
    (i : ι) (s : Finset {x : Fin 3 → V // Function.Injective x}) :
    H.splitDiscrepancy f c i s =
      #{x ∈ s | (H.split f).color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = (c, i)} -
        (#{x ∈ s | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c} : ℝ) /
          Fintype.card ι :=
  (rfl)

/-- The density discrepancy of a split color, multiplied by the support size, is its count
discrepancy. -/
theorem relDensityOn_split_sub_mul_card (H : Colored3Graph κ V) (f : Set.powersetCard V 3 → ι)
    (c : κ) (i : ι) (s : Finset {x : Fin 3 → V // Function.Injective x}) :
    (((H.split f).relDensityOn (c, i) s : ℝ) - H.relDensityOn c s / Fintype.card ι) * #s =
      H.splitDiscrepancy f c i s := by
  have h₁ := congrArg (fun q : ℚ ↦ (q : ℝ)) ((H.split f).relDensityOn_mul_card (c, i) s)
  have h₂ := congrArg (fun q : ℚ ↦ (q : ℝ)) (H.relDensityOn_mul_card c s)
  push_cast at h₁ h₂
  rw [sub_mul, div_mul_eq_mul_div, h₁, h₂, splitDiscrepancy_def]

/-- A bound on the count discrepancy of a split color, relative to the size of a set of
injective triples, bounds its density discrepancy. -/
theorem abs_relDensityOn_split_sub_le (H : Colored3Graph κ V) (f : Set.powersetCard V 3 → ι)
    (c : κ) (i : ι) (s : Finset {x : Fin 3 → V // Function.Injective x}) {b : ℝ} (hb : 0 ≤ b)
    (h : |H.splitDiscrepancy f c i s| ≤ b * #s) :
    |((H.split f).relDensityOn (c, i) s : ℝ) - H.relDensityOn c s / Fintype.card ι| ≤ b := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simpa using hb
  have hs' : (0 : ℝ) < #s := by exact_mod_cast hs.card_pos
  rw [← mul_le_mul_iff_of_pos_right hs', ← abs_of_pos hs', ← abs_mul,
    relDensityOn_split_sub_mul_card, abs_of_pos hs']
  exact h

end Split

end Colored3Graph

end TauCeti

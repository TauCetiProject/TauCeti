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
import Mathlib.Tactic.Ring

/-!
# Relative color densities and their stability under edits

For a coloring `H` of the unordered triples of `V`, the relative density `H.relDensityOn c supp`
of a color `c` over a finite support of injective triples is the fraction of the supported
triples whose underlying unordered triple has color `c`. Colors are read through the underlying
unordered triple, while the normalization counts the supported ordered injections, so a triple
contributes once for each of its supported orderings, both to the count and to the normalization.
The relative density is `0` on the empty support.

Relative densities lie between `0` and `1`, and on a nonempty support the densities of all colors
sum to one. Recoloring changes `relDensityOn`, multiplied by the support size, by at most
the number of supported edited triples `editedOn`, defined in
`TauCeti.Combinatorics.Hypergraph.Colored.EditDiscrepancy`.

## Main definitions

* `TauCeti.Colored3Graph.relDensityOn`: the relative density of a color over a support.

## Main results

* `TauCeti.Colored3Graph.sum_relDensityOn`: on a nonempty support the densities sum to one.
* `TauCeti.Colored3Graph.abs_relDensityOn_sub_mul_card_le_card_editedOn`: the count-scaled
  density change is bounded by the supported edit count.
* `TauCeti.Colored3Graph.abs_relDensityOn_sub_le_div_of_card_editedOn_le`: an `η`-fraction
  of edits on a support changes density on an `ε`-fraction subsupport by at most `η / ε`.
* `TauCeti.Colored3Graph.abs_relDensityOn_sub_le_div_of_card_sdiff_le`: removing few triples
  from a support changes the density of every color by little.
* `TauCeti.Colored3Graph.abs_relDensityOn_sub_mul_card_le` and
  `TauCeti.Colored3Graph.sum_abs_relDensityOn_sub_mul_card_le`: count-scaled single-color and
  palette-summed density bounds between any two supports, independent of the palette size.
* `TauCeti.Colored3Graph.sum_card_mul_sq_relDensityOn_sub_le`: palette-independent perturbation
  bound for support-weighted sums of squared relative densities.
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
  #{x ∈ supp | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} / #supp

/-- The relative density counts supported triples whose underlying triple has color `c`. -/
theorem relDensityOn_def (H : Colored3Graph κ V) (c : κ)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) :
    H.relDensityOn c supp =
      #{x ∈ supp | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} / #supp :=
  (rfl)

/-- Multiplying a relative density by the support size recovers the color count, including
when the support is empty. -/
theorem relDensityOn_mul_card (H : Colored3Graph κ V) (c : κ)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) :
    H.relDensityOn c supp * #supp =
      (#{x ∈ supp | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℚ) := by
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
  by_cases h : H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) =
      H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)
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
    (fun x ↦ H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c) hAB)
  have hsub : {x ∈ B | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} ⊆
      {x ∈ A | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} ∪ (B \ A) := by
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

/-- The relative densities of all colors sum to at most one on every support, including the empty
support where they vanish. -/
theorem sum_relDensityOn_le_one [Fintype κ] (H : Colored3Graph κ V)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) :
    ∑ c, H.relDensityOn c supp ≤ 1 := by
  obtain rfl | hs := supp.eq_empty_or_nonempty
  · simp
  · exact (H.sum_relDensityOn hs).le

section Perturbation

variable [DecidableEq V]

/-- Decompose the count-scaled difference of a color density between any two supports into the
triples added to `W \ U` and those removed from `U \ W`, valid also on empty supports. -/
private theorem relDensityOn_sub_mul_card_eq_sdiff (H : Colored3Graph κ V) (c : κ)
    (W U : Finset {x : Fin 3 → V // Function.Injective x}) :
    (H.relDensityOn c W - H.relDensityOn c U) * #W =
      ((#{x ∈ W \ U | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℚ) -
        H.relDensityOn c U * #(W \ U)) +
      (H.relDensityOn c U * #(U \ W) -
        #{x ∈ U \ W | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c}) := by
  let P : {x : Fin 3 → V // Function.Injective x} → Prop :=
    fun x ↦ H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c
  have hW := H.relDensityOn_mul_card c W
  have hU := H.relDensityOn_mul_card c U
  have hcard : (#W : ℚ) + #(U \ W) = #(W \ U) + #U := by
    have h₁ := card_sdiff_add_card_inter W U
    have h₂ := card_sdiff_add_card_inter U W
    rw [inter_comm U W] at h₂
    exact_mod_cast (by omega : #W + #(U \ W) = #(W \ U) + #U)
  have hsdiff (A B : Finset {x : Fin 3 → V // Function.Injective x}) :
      A.filter P \ B.filter P = (A \ B).filter P := by
    ext x
    simp only [mem_sdiff, mem_filter]
    tauto
  have hcol : (#(W.filter P) : ℚ) + #((U \ W).filter P) =
      #((W \ U).filter P) + #(U.filter P) := by
    have h₁ := card_sdiff_add_card_inter (W.filter P) (U.filter P)
    have h₂ := card_sdiff_add_card_inter (U.filter P) (W.filter P)
    rw [inter_comm (U.filter P) (W.filter P), hsdiff] at h₂
    rw [hsdiff] at h₁
    exact_mod_cast (by omega : #(W.filter P) + #((U \ W).filter P) =
      #((W \ U).filter P) + #(U.filter P))
  have hmul := congrArg (H.relDensityOn c U * ·) hcard
  dsimp only [P] at hcol
  linarith

/-- For any two supports `W` and `U`, the count-scaled density difference on `W` is bounded by
`#(W \ U) + #(U \ W)`. Empty supports are allowed, and no containment or finite palette is
required. -/
theorem abs_relDensityOn_sub_mul_card_le (H : Colored3Graph κ V) (c : κ)
    (W U : Finset {x : Fin 3 → V // Function.Injective x}) :
    |H.relDensityOn c W - H.relDensityOn c U| * #W ≤ (#(W \ U) + #(U \ W) : ℚ) := by
  have h₀ := H.relDensityOn_nonneg c U
  have h₁ := H.relDensityOn_le_one c U
  have hc₁ : (#{x ∈ W \ U | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℚ) ≤
      #(W \ U) := mod_cast card_filter_le _ _
  have hc₂ : (#{x ∈ U \ W | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℚ) ≤
      #(U \ W) := mod_cast card_filter_le _ _
  have hd₁ : H.relDensityOn c U * #(W \ U) ≤ #(W \ U) :=
    mul_le_of_le_one_left (Nat.cast_nonneg _) h₁
  have hd₂ : H.relDensityOn c U * #(U \ W) ≤ #(U \ W) :=
    mul_le_of_le_one_left (Nat.cast_nonneg _) h₁
  have hn₁ : 0 ≤ H.relDensityOn c U * #(W \ U) := mul_nonneg h₀ (Nat.cast_nonneg _)
  have hn₂ : 0 ≤ H.relDensityOn c U * #(U \ W) := mul_nonneg h₀ (Nat.cast_nonneg _)
  rw [← abs_of_nonneg (Nat.cast_nonneg (α := ℚ) #W), ← abs_mul,
    H.relDensityOn_sub_mul_card_eq_sdiff c W U, abs_le]
  constructor <;>
    linarith [Nat.cast_nonneg (α := ℚ)
      #{x ∈ W \ U | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c},
      Nat.cast_nonneg (α := ℚ)
      #{x ∈ U \ W | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c}]

/-- **Total-variation support stability.** Summing the count-scaled density differences between
`W` and `U` over all colors gives at most `2 (#(W \ U) + #(U \ W))`, with no factor depending on
the size of the palette. -/
theorem sum_abs_relDensityOn_sub_mul_card_le [Fintype κ] (H : Colored3Graph κ V)
    (W U : Finset {x : Fin 3 → V // Function.Injective x}) :
    (∑ c, |H.relDensityOn c W - H.relDensityOn c U|) * #W ≤
      2 * (#(W \ U) + #(U \ W) : ℚ) := by
  have hloc (c : κ) : |H.relDensityOn c W - H.relDensityOn c U| * #W ≤
      (#{x ∈ W \ U | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℚ) +
        H.relDensityOn c U * #(W \ U) + H.relDensityOn c U * #(U \ W) +
        #{x ∈ U \ W | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} := by
    have h₀ := H.relDensityOn_nonneg c U
    have hn₁ : 0 ≤ H.relDensityOn c U * #(W \ U) := mul_nonneg h₀ (Nat.cast_nonneg _)
    have hn₂ : 0 ≤ H.relDensityOn c U * #(U \ W) := mul_nonneg h₀ (Nat.cast_nonneg _)
    rw [← abs_of_nonneg (Nat.cast_nonneg (α := ℚ) #W), ← abs_mul,
      H.relDensityOn_sub_mul_card_eq_sdiff c W U, abs_le]
    constructor <;>
      linarith [Nat.cast_nonneg (α := ℚ)
        #{x ∈ W \ U | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c},
        Nat.cast_nonneg (α := ℚ)
        #{x ∈ U \ W | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c}]
  have hfib (X : Finset {x : Fin 3 → V // Function.Injective x}) :
      ∑ c : κ, (#{x ∈ X | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℚ) = #X := by
    exact_mod_cast (card_eq_sum_card_fiberwise (s := X) fun _ _ ↦ mem_univ _).symm
  have hd₁ : (∑ c, H.relDensityOn c U) * #(W \ U) ≤ #(W \ U) :=
    mul_le_of_le_one_left (Nat.cast_nonneg _) (H.sum_relDensityOn_le_one U)
  have hd₂ : (∑ c, H.relDensityOn c U) * #(U \ W) ≤ #(U \ W) :=
    mul_le_of_le_one_left (Nat.cast_nonneg _) (H.sum_relDensityOn_le_one U)
  have hsum := sum_le_sum fun c (_ : c ∈ univ) ↦ hloc c
  simp only [sum_add_distrib, ← sum_mul, hfib] at hsum
  linarith

/-- Algebraic identity comparing the support-weighted squared density on `U` with that on a subset
`I ⊆ U`, valid also when either set is empty. -/
private theorem card_mul_sq_relDensityOn_sub_of_subset (H : Colored3Graph κ V) (c : κ)
    {I U : Finset {x : Fin 3 → V // Function.Injective x}} (hIU : I ⊆ U) :
    (#U : ℚ) * H.relDensityOn c U ^ 2 - #I * H.relDensityOn c I ^ 2 =
      (H.relDensityOn c U + H.relDensityOn c I) *
        #{x ∈ U \ I | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} -
      #(U \ I) * H.relDensityOn c U * H.relDensityOn c I := by
  let P : {x : Fin 3 → V // Function.Injective x} → Prop :=
    fun x ↦ H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c
  set p := H.relDensityOn c U
  set q := H.relDensityOn c I
  let nI : ℚ := (#{x ∈ I | P x} : ℚ)
  let nD : ℚ := (#{x ∈ U \ I | P x} : ℚ)
  have hI : q * #I = nI := H.relDensityOn_mul_card c I
  have hU : p * #U = nD + nI := by
    rw [H.relDensityOn_mul_card c U]
    have hunion : U.filter P = (U \ I).filter P ∪ I.filter P := by
      rw [← filter_union, sdiff_union_of_subset hIU]
    have hdisj : Disjoint ((U \ I).filter P) (I.filter P) :=
      sdiff_disjoint.mono (filter_subset _ _) (filter_subset _ _)
    dsimp only [nD, nI, P]
    exact_mod_cast congrArg card hunion |>.trans (card_union_of_disjoint hdisj)
  have hcard : (#U : ℚ) = #(U \ I) + #I := by
    exact_mod_cast (card_sdiff_add_card_eq_card hIU).symm
  calc (#U : ℚ) * p ^ 2 - #I * q ^ 2
      = (p + q) * nD - #(U \ I) * p * q +
          (p + q) * (p * #U - (nD + nI)) - (p + q) * (q * #I - nI) -
          p * q * (#U - (#(U \ I) + #I)) := by ring
    _ = (p + q) * nD - #(U \ I) * p * q := by rw [hU, hI, hcard]; ring

/-- Shrinking a support `U` to `I ⊆ U` increases the sum over colors of `#I * d(c | I)²` beyond
`#U * d(c | U)²` by at most `#(U \ I)`. -/
theorem neg_card_sdiff_le_sum_card_mul_sq_relDensityOn_sub [Fintype κ] (H : Colored3Graph κ V)
    {I U : Finset {x : Fin 3 → V // Function.Injective x}} (hIU : I ⊆ U) :
    -(#(U \ I) : ℚ) ≤
      ∑ c, (#U : ℚ) * H.relDensityOn c U ^ 2 - ∑ c, (#I : ℚ) * H.relDensityOn c I ^ 2 := by
  rw [← sum_sub_distrib]
  have hloc (c : κ) : -(#(U \ I) * H.relDensityOn c U) ≤
      (#U : ℚ) * H.relDensityOn c U ^ 2 - #I * H.relDensityOn c I ^ 2 := by
    rw [H.card_mul_sq_relDensityOn_sub_of_subset c hIU]
    have h₁ : 0 ≤ (H.relDensityOn c U + H.relDensityOn c I) *
        (#{x ∈ U \ I | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℚ) :=
      mul_nonneg (add_nonneg (H.relDensityOn_nonneg c U) (H.relDensityOn_nonneg c I))
        (Nat.cast_nonneg _)
    have h₂ : #(U \ I) * H.relDensityOn c U * H.relDensityOn c I ≤ #(U \ I) * H.relDensityOn c U :=
      mul_le_of_le_one_right (mul_nonneg (Nat.cast_nonneg _) (H.relDensityOn_nonneg c U))
        (H.relDensityOn_le_one c I)
    linarith
  have hsum := sum_le_sum fun c (_ : c ∈ univ) ↦ hloc c
  rw [sum_neg_distrib, ← mul_sum] at hsum
  have hd : #(U \ I) * ∑ c, H.relDensityOn c U ≤ #(U \ I) :=
    mul_le_of_le_one_right (Nat.cast_nonneg _) (H.sum_relDensityOn_le_one U)
  linarith

/-- Shrinking a support `U` to `I ⊆ U` decreases the sum over colors of `#U * d(c | U)²` by at
most `2 #(U \ I)`, independently of the palette size. -/
theorem sum_card_mul_sq_relDensityOn_sub_le_two_mul_card_sdiff [Fintype κ] (H : Colored3Graph κ V)
    {I U : Finset {x : Fin 3 → V // Function.Injective x}} (hIU : I ⊆ U) :
    ∑ c, (#U : ℚ) * H.relDensityOn c U ^ 2 - ∑ c, (#I : ℚ) * H.relDensityOn c I ^ 2 ≤
      2 * (#(U \ I) : ℚ) := by
  rw [← sum_sub_distrib]
  have hloc (c : κ) : (#U : ℚ) * H.relDensityOn c U ^ 2 - #I * H.relDensityOn c I ^ 2 ≤
      2 * (#{x ∈ U \ I | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℚ) := by
    rw [H.card_mul_sq_relDensityOn_sub_of_subset c hIU]
    have h₁ : (H.relDensityOn c U + H.relDensityOn c I) *
        (#{x ∈ U \ I | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℚ) ≤
        2 * #{x ∈ U \ I | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} :=
      mul_le_mul_of_nonneg_right
        (by linarith [H.relDensityOn_le_one c U, H.relDensityOn_le_one c I]) (Nat.cast_nonneg _)
    have h₂ : 0 ≤ #(U \ I) * H.relDensityOn c U * H.relDensityOn c I :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (H.relDensityOn_nonneg c U))
        (H.relDensityOn_nonneg c I)
    linarith
  have hfib : ∑ c : κ,
      (#{x ∈ U \ I | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℚ) = #(U \ I) := by
    exact_mod_cast (card_eq_sum_card_fiberwise (s := U \ I) fun _ _ ↦ mem_univ _).symm
  have hsum := sum_le_sum fun c (_ : c ∈ univ) ↦ hloc c
  rw [← mul_sum, hfib] at hsum
  exact hsum

/-- **Squared-density support perturbation.** Between any two supports `W` and `U`, the difference
of the support-weighted sums of squared color densities is bounded by `2 #(W \ U) + #(U \ W)`,
with no factor depending on the size of the palette. Swapping `W` and `U` gives the corresponding
lower bound. -/
theorem sum_card_mul_sq_relDensityOn_sub_le [Fintype κ] (H : Colored3Graph κ V)
    (W U : Finset {x : Fin 3 → V // Function.Injective x}) :
    ∑ c, (#W : ℚ) * H.relDensityOn c W ^ 2 - ∑ c, (#U : ℚ) * H.relDensityOn c U ^ 2 ≤
      2 * (#(W \ U) : ℚ) + #(U \ W) := by
  have h₁ := H.sum_card_mul_sq_relDensityOn_sub_le_two_mul_card_sdiff
    (inter_subset_left (s₁ := W) (s₂ := U))
  have h₂ := H.neg_card_sdiff_le_sum_card_mul_sq_relDensityOn_sub
    (inter_subset_right (s₁ := W) (s₂ := U))
  rw [sdiff_inter_self_left] at h₁
  rw [sdiff_inter_self_right] at h₂
  linarith

end Perturbation

end Colored3Graph

end TauCeti

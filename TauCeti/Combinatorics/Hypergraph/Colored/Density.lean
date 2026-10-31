/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Colored.EditDiscrepancy
import TauCeti.Data.Fintype.EmbeddingFiber
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Relative color densities over supports of injective triples

For a coloring `H` of the unordered triples of `V`, the relative density `H.relDensityOn c supp`
of a color `c` over a finite support of injective triples is the fraction of the supported
triples whose underlying unordered triple has color `c`. Colors are read through the underlying
unordered triple, while the normalization counts the supported ordered injections, so a triple
contributes once for each of its supported orderings, both to the count and to the normalization.
The relative density is `0` on the empty support.

Relative densities lie between `0` and `1`, and on a nonempty support the densities of all colors
sum to one.

## Main definitions

* `TauCeti.Colored3Graph.relDensityOn`: the relative density of a color over a support.
* `TauCeti.Colored3Graph.editedOn`: the supported injective triples whose colors differ.

## Main results

* `TauCeti.Colored3Graph.sum_relDensityOn`: on a nonempty support the densities sum to one.
-/

public section

open Finset

namespace TauCeti

namespace Colored3Graph

variable {κ V : Type*} [DecidableEq κ]

/-- The supported injective triples whose underlying unordered triple has different colors
in `H` and `H'`. Each supported ordering is counted separately. -/
def editedOn (H H' : Colored3Graph κ V)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) :
    Finset {x : Fin 3 → V // Function.Injective x} :=
  supp.filter fun x ↦ H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
    H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)

/-- Edited triples are obtained by filtering the support for unequal colors. -/
theorem editedOn_def (H H' : Colored3Graph κ V)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) :
    H.editedOn H' supp = supp.filter fun x ↦
      H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
        H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) :=
  (rfl)

/-- Membership means being supported and having different colors. -/
@[simp]
theorem mem_editedOn_iff (H H' : Colored3Graph κ V)
    (supp : Finset {x : Fin 3 → V // Function.Injective x})
    (x : {x : Fin 3 → V // Function.Injective x}) :
    x ∈ H.editedOn H' supp ↔ x ∈ supp ∧
      H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
        H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) := by
  simp [editedOn_def]

/-- Every edited triple belongs to the given support. -/
theorem editedOn_subset (H H' : Colored3Graph κ V)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) :
    H.editedOn H' supp ⊆ supp := by
  rw [editedOn_def]
  exact filter_subset _ _

/-- Enlarging the support can only enlarge the set of edited triples. -/
theorem editedOn_mono (H H' : Colored3Graph κ V)
    {A B : Finset {x : Fin 3 → V // Function.Injective x}} (h : A ⊆ B) :
    H.editedOn H' A ⊆ H.editedOn H' B := by
  simp only [editedOn_def]
  exact filter_subset_filter _ h

/-- The edited support is independent of the direction of recoloring. -/
theorem editedOn_comm (H H' : Colored3Graph κ V)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) :
    H.editedOn H' supp = H'.editedOn H supp := by
  simp only [editedOn_def, ne_comm]

/-- A coloring has no edits relative to itself. -/
@[simp]
theorem editedOn_self (H : Colored3Graph κ V)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) : H.editedOn H supp = ∅ := by
  simp [editedOn_def]

/-- There are no edited triples on the empty support. -/
@[simp]
theorem editedOn_empty (H H' : Colored3Graph κ V) : H.editedOn H' ∅ = ∅ := by
  simp [editedOn_def]

/-- The edit count is additive over a finite family of pairwise disjoint supports. -/
theorem card_editedOn_biUnion {ι : Type*} [DecidableEq V]
    (H H' : Colored3Graph κ V) (s : Finset ι)
    (supp : ι → Finset {x : Fin 3 → V // Function.Injective x})
    (h : (s : Set ι).PairwiseDisjoint supp) :
    #(H.editedOn H' (s.biUnion supp)) = ∑ i ∈ s, #(H.editedOn H' (supp i)) := by
  classical
  simp only [editedOn_def, filter_biUnion]
  exact card_biUnion fun i hi j hj hij ↦ (h hi hj hij).mono
    (filter_subset _ _) (filter_subset _ _)

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

/-- The edited triples in any support are bounded by the global edit discrepancy times
`|V|³`. This converts unordered edits to ordered injective triples, including empty hosts. -/
theorem card_editedOn_le_editDiscrepancy3 [Fintype V] (H H' : Colored3Graph κ V)
    (supp : Finset {x : Fin 3 → V // Function.Injective x}) :
    (#(H.editedOn H' supp) : ℝ) ≤
      (H.editDiscrepancy3 H' : ℝ) * (Fintype.card V : ℝ) ^ 3 := by
  classical
  rw [editedOn_def]
  let edits : Finset (Set.powersetCard V 3) := univ.filter fun t ↦ H.color t ≠ H'.color t
  let triple (x : {x : Fin 3 → V // Function.Injective x}) :=
    Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩
  have hfiber (t : Set.powersetCard V 3) : #{x ∈ supp | triple x = t} ≤ 6 := by
    let s : Set.powersetCard (Fin 3) 3 := ⟨univ, by simp⟩
    have hm (f : Fin 3 ↪ V) : Set.powersetCard.map 3 f s =
        Set.powersetCard.ofFinEmb 3 V f := Subtype.ext (by simp [s])
    have hc : Nat.card {f : Fin 3 ↪ V // Set.powersetCard.ofFinEmb 3 V f = t} ≤ 6 := by
      simpa only [Fintype.card_fin, hm, Nat.sub_self, pow_zero, mul_one,
        Nat.factorial_succ, Nat.factorial_zero] using
        (card_embedding_map_eq_le (s := s) (t := t))
    have he := Fintype.card_congr (Equiv.subtypeEquiv
      (p := fun x ↦ triple x = t) (q := fun f ↦ Set.powersetCard.ofFinEmb 3 V f = t)
      (Equiv.subtypeInjectiveEquivEmbedding (Fin 3) V) (fun _ ↦ Iff.rfl))
    have hle : #{x | triple x = t} ≤ 6 := by
      simpa only [Nat.card_eq_fintype_card, ← he, Fintype.card_subtype,
        Fintype.card_fin, Nat.sub_self, pow_zero, mul_one] using hc
    exact (card_le_card (filter_subset_filter _ (subset_univ supp))).trans hle
  have hcount : #{x ∈ supp | H.color (triple x) ≠ H'.color (triple x)} ≤
      6 * {t | H.color t ≠ H'.color t}.ncard := by
    rw [card_eq_sum_card_fiberwise (f := triple) (t := edits)
      (by intro x hx; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩)]
    calc
      _ ≤ ∑ _t ∈ edits, 6 := sum_le_sum fun t _ ↦
        (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans (hfiber t)
      _ = _ := by
        simp [edits, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
          Fintype.card_subtype, mul_comm]
  by_cases hn : Fintype.card V = 0
  · have : IsEmpty V := Fintype.card_eq_zero_iff.1 hn
    simp
  have hn' : (Fintype.card V : ℝ) ^ 3 ≠ 0 := by exact_mod_cast pow_ne_zero 3 hn
  rw [editDiscrepancy3_def]
  rw [Nat.card_eq_fintype_card]
  push_cast
  rw [div_mul_cancel₀ _ hn']
  exact_mod_cast hcount

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

end Colored3Graph

end TauCeti

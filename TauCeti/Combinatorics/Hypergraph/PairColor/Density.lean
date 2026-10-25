/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Positivity

/-!
# Densities of coherent pair colors

`pairColorDensity S c s t` is the proportion of ordered distinct pairs in `s ×ˢ t` with
color `c`. The denominator excludes the diagonal even when the cells overlap. An empty
support has density zero; consequently the palette densities sum to one only when there
is at least one distinct pair. Reversing the cells reverses the palette color.

These densities supply the pair factors in predictions for colored hypergraph counts.
-/

public section

open Finset

namespace TauCeti

variable {κ V : Type*}

/-- The density of a color among the ordered distinct pairs in two finite vertex sets.
It is zero when no distinct pair exists. -/
noncomputable def pairColorDensity (S : PairColorSystem κ V) (c : κ) (s t : Finset V) : ℚ := by
  classical
  exact (#((s ×ˢ t).filter fun p => S.colorOfPair p.1 p.2 = some c) : ℚ) /
    #((s ×ˢ t).filter fun p => p.1 ≠ p.2)

/-- Pair-color density is the color count divided by the distinct-pair count. -/
theorem pairColorDensity_def [DecidableEq κ] [DecidableEq V]
    (S : PairColorSystem κ V) (c : κ) (s t : Finset V) :
    pairColorDensity S c s t =
      (#((s ×ˢ t).filter fun p => S.colorOfPair p.1 p.2 = some c) : ℚ) /
        #((s ×ˢ t).filter fun p => p.1 ≠ p.2) := by
  unfold pairColorDensity
  congr

/-- Multiplying density by the size of its distinct-pair support recovers the color count.
This also holds for empty support, when both sides vanish. -/
theorem pairColorDensity_mul_card_support [DecidableEq κ] [DecidableEq V]
    (S : PairColorSystem κ V) (c : κ) (s t : Finset V) :
    pairColorDensity S c s t * #((s ×ˢ t).filter fun p => p.1 ≠ p.2) =
      (#((s ×ˢ t).filter fun p => S.colorOfPair p.1 p.2 = some c) : ℚ) := by
  have hsub : (s ×ˢ t).filter (fun p => S.colorOfPair p.1 p.2 = some c) ⊆
      (s ×ˢ t).filter (fun p => p.1 ≠ p.2) := by
    intro p hp
    obtain ⟨hp, hc⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hp, (S.colorOfPair_eq_some_iff _ _ _).mp hc |>.choose⟩
  by_cases h : #((s ×ˢ t).filter fun p => p.1 ≠ p.2) = 0
  · have hc : #((s ×ˢ t).filter fun p => S.colorOfPair p.1 p.2 = some c) = 0 :=
      Nat.eq_zero_of_le_zero (h ▸ card_le_card hsub)
    simp [pairColorDensity_def, h, hc]
  · rw [pairColorDensity_def, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr h)]

/-- Pair-color densities are nonnegative. -/
theorem pairColorDensity_nonneg (S : PairColorSystem κ V) (c : κ) (s t : Finset V) :
    0 ≤ pairColorDensity S c s t := by
  classical
  rw [pairColorDensity_def]
  positivity

/-- A color occupies at most the whole distinct-pair support. -/
theorem pairColorDensity_le_one (S : PairColorSystem κ V) (c : κ) (s t : Finset V) :
    pairColorDensity S c s t ≤ 1 := by
  classical
  rw [pairColorDensity_def]
  apply div_le_one_of_le₀ _ (by positivity)
  have hsub : (s ×ˢ t).filter (fun p => S.colorOfPair p.1 p.2 = some c) ⊆
      (s ×ˢ t).filter (fun p => p.1 ≠ p.2) := by
    intro p hp
    obtain ⟨hp, hc⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hp, (S.colorOfPair_eq_some_iff _ _ _).mp hc |>.choose⟩
  exact_mod_cast card_le_card hsub

/-- With no distinct pairs, every color has density zero. -/
theorem pairColorDensity_eq_zero_of_support_eq_empty [DecidableEq V]
    (S : PairColorSystem κ V) (c : κ) (s t : Finset V)
    (h : (s ×ˢ t).filter (fun p => p.1 ≠ p.2) = ∅) :
    pairColorDensity S c s t = 0 := by
  classical
  simp [pairColorDensity_def, h]

@[simp]
theorem pairColorDensity_empty_left (S : PairColorSystem κ V) (c : κ) (t : Finset V) :
    pairColorDensity S c ∅ t = 0 := by
  classical
  simp [pairColorDensity_def]

@[simp]
theorem pairColorDensity_empty_right (S : PairColorSystem κ V) (c : κ) (s : Finset V) :
    pairColorDensity S c s ∅ = 0 := by
  classical
  simp [pairColorDensity_def]

@[simp]
theorem pairColorDensity_singleton_self (S : PairColorSystem κ V) (c : κ) (v : V) :
    pairColorDensity S c {v} {v} = 0 := by
  classical
  simp [pairColorDensity_def]

/-- Palette densities sum to one on nonempty distinct-pair support.
Nonempty cells alone do not suffice, as the coincident-singleton case shows. -/
theorem sum_pairColorDensity [Fintype κ] [DecidableEq V]
    (S : PairColorSystem κ V) (s t : Finset V)
    (h : ((s ×ˢ t).filter fun p => p.1 ≠ p.2).Nonempty) :
    ∑ c, pairColorDensity S c s t = 1 := by
  classical
  have hmem (p : V × V) :
      S.colorOfPair p.1 p.2 ∈ (univ : Finset κ).image some ↔ p.1 ≠ p.2 := by
    by_cases hp : p.1 ≠ p.2
    · simp [hp]
    · have heq := not_ne_iff.mp hp
      simp [heq]
  have hcount := sum_card_fiberwise_eq_card_filter (s ×ˢ t)
    ((univ : Finset κ).image some) (fun p => S.colorOfPair p.1 p.2)
  rw [sum_image (fun _ _ _ _ h => Option.some_injective _ h)] at hcount
  simp only [hmem] at hcount
  simp_rw [pairColorDensity_def]
  rw [← sum_div, ← Nat.cast_sum, hcount]
  exact div_self (Nat.cast_ne_zero.mpr h.card_pos.ne')

/-- Reversing both the ordered cells and the palette color preserves density. -/
theorem pairColorDensity_swap (S : PairColorSystem κ V) (c : κ) (s t : Finset V) :
    pairColorDensity S (S.rev c) t s = pairColorDensity S c s t := by
  classical
  have hcolor : #((t ×ˢ s).filter fun p => S.colorOfPair p.1 p.2 = some (S.rev c)) =
      #((s ×ˢ t).filter fun p => S.colorOfPair p.1 p.2 = some c) := by
    apply card_equiv (Equiv.prodComm V V)
    intro p
    simp [and_comm, ← S.colorOfPair_swap_eq_some_iff p.2 p.1 c]
  have hsupport : #((t ×ˢ s).filter fun p => p.1 ≠ p.2) =
      #((s ×ˢ t).filter fun p => p.1 ≠ p.2) := by
    apply card_equiv (Equiv.prodComm V V)
    simp [and_comm, ne_comm]
  simp only [pairColorDensity_def, hcolor, hsupport]

end TauCeti

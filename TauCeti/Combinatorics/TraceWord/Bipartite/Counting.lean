/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import TauCeti.Data.Fintype.SmallRange

/-!
# Counting bipartite trace words with few vertices

A rectangular trace always starts with a row vertex. For words of half-length `k > 0`
with at most `k` vertices, counting row and column labels separately retains a factor of the
row dimension, even when that dimension is small compared to the number of columns.
This factor cancels the normalized trace's row denominator in moment estimates.
-/

public section

open Finset

namespace TauCeti

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

private theorem card_filter_bipartiteWord_le {k r : ℕ} (hr : r < k)
    (S : Finset ((Fin k → α) × (Fin k → β)))
    (hS : ∀ w ∈ S, #(univ.image w.1) + #(univ.image w.2) ≤ k) :
    #{w ∈ S | #(univ.image w.1) - 1 = r} ≤
      Fintype.card α * max (Fintype.card α) (Fintype.card β) ^ (k - 1) * k ^ (2 * k) := by
  rcases isEmpty_or_nonempty α with hα | hα
  · have : Nonempty (Fin k) := ⟨⟨r, hr⟩⟩
    simp [Finset.eq_empty_of_isEmpty S]
  rcases isEmpty_or_nonempty β with hβ | hβ
  · have : Nonempty (Fin k) := ⟨⟨r, hr⟩⟩
    simp [Finset.eq_empty_of_isEmpty S]
  let rows : Finset (Fin k → α) := {u : Fin k → α | #(univ.image u) ≤ r + 1}
  let cols : Finset (Fin k → β) := {v : Fin k → β | #(univ.image v) ≤ k - (r + 1)}
  have hle : #{w ∈ S | #(univ.image w.1) - 1 = r} ≤ #(rows ×ˢ cols) := by
    apply card_le_card
    intro w hw
    obtain ⟨hwS, hw⟩ := mem_filter.mp hw
    have hrow : 0 < #(univ.image w.1) :=
      card_pos.mpr ⟨_, mem_image_of_mem w.1 (mem_univ ⟨r, hr⟩)⟩
    have hcount := hS w hwS
    simp only [rows, cols, mem_product, mem_filter, mem_univ, true_and]
    omega
  have hrows : #rows ≤ Fintype.card α ^ (r + 1) * (r + 1) ^ k := by
    simpa only [Fintype.card_fin] using card_filter_card_image_le (α := Fin k) (β := α) (r + 1)
  have hcols : #cols ≤ Fintype.card β ^ (k - (r + 1)) * (k - (r + 1)) ^ k := by
    simpa only [Fintype.card_fin] using
      card_filter_card_image_le (α := Fin k) (β := β) (k - (r + 1))
  set N := max (Fintype.card α) (Fintype.card β)
  calc
    _ ≤ #rows * #cols := hle.trans_eq (card_product _ _)
    _ ≤ _ := Nat.mul_le_mul hrows hcols
    _ ≤ (Fintype.card α * N ^ r * k ^ k) * (N ^ (k - (r + 1)) * k ^ k) := by
      rw [pow_succ']
      gcongr
      · exact le_max_left _ _
      · omega
      · exact le_max_right _ _
      · omega
    _ = _ := by
      have hexp : k - 1 = r + (k - (r + 1)) := by omega
      rw [hexp, pow_add N, Nat.two_mul, pow_add k]
      ac_rfl

/-- A collection of bipartite words of half-length `k > 0` with at most `k` visited vertices
has at most `p · max(p,n)^(k-1) · k^(2k+1)` elements, where `p` and `n` are the dimensions. -/
theorem card_bipartiteWord_le {k : ℕ} (hk : k ≠ 0)
    (S : Finset ((Fin k → α) × (Fin k → β)))
    (hS : ∀ w ∈ S, #(univ.image w.1) + #(univ.image w.2) ≤ k) :
    #S ≤ Fintype.card α * max (Fintype.card α) (Fintype.card β) ^ (k - 1) * k ^ (2 * k + 1) := by
  have hmaps (w) (hw : w ∈ S) : #(univ.image w.1) - 1 ∈ range k := by
    have hrow : 0 < #(univ.image w.1) :=
      card_pos.mpr ⟨_, mem_image_of_mem w.1 (mem_univ ⟨0, Nat.pos_of_ne_zero hk⟩)⟩
    have := hS w hw
    rw [mem_range]
    omega
  rw [card_eq_sum_card_fiberwise hmaps]
  refine (sum_le_sum fun r hr ↦ card_filter_bipartiteWord_le (mem_range.mp hr) S hS).trans_eq ?_
  simp only [sum_const, card_range, Nat.nsmul_eq_mul, pow_succ]
  ac_rfl

end TauCeti

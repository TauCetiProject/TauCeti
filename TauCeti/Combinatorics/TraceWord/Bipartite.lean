/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Vertex and edge counts of bipartite trace words

The trace of `(X Xᴴ) ^ k` for a rectangular matrix `X` expands over the closed words

`u 0, v 0, u 1, v 1, …, u (k - 1), v (k - 1), u 0`

alternating between row indices `u : Fin k → α` and column indices `v : Fin k → β`
(`Matrix.trace_mul_conjTranspose_pow_eq_sum_prod`). Such a word has `2 * k` steps. The step
from `u t` to `v t` reads the entry of `X` at `(u t, v t)`, and the step from `v t` back to
`u (t + 1)` reads the entry at `(u (t + 1), v t)`; `TauCeti.bipartiteEdge u v` records these
positions, which are the edges of the bipartite graph traversed by the word.

A connected graph has at most one more vertex than edges, so a bipartite word visits at most
one more row and column index than it reads positions. When no position is read exactly once,
the word reads at most `k` positions, and hence visits at most `k + 1` row and column indices in
total. In the moment method for sample covariance matrices these are the words left in the
expected trace expansion of a matrix with independent centred entries, and the bound controls
the number of their labellings by `p` row and `n` column indices.

## Main declarations

* `TauCeti.bipartiteEdge`: the positions read by the steps of a bipartite word.
* `TauCeti.card_image_add_card_image_le_card_image_bipartiteEdge_add_one`: a bipartite word
  visits at most one more row and column index than it reads positions.
* `TauCeti.card_image_bipartiteEdge_le_of_no_singleton_edge`: a bipartite word of half-length
  `k` reading no position exactly once reads at most `k` positions.
* `TauCeti.card_image_add_card_image_le_add_one_of_no_singleton_edge`: such a word visits at
  most `k + 1` row and column indices.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a
  review*, Statistica Sinica 9 (1999), §2.2.1, the moment method for sample covariance matrices.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, the counting argument for the moment method.
-/

public section

open Finset

namespace TauCeti

variable {α β : Type*} {k : ℕ}

/-- The positions read by the steps of the closed bipartite word
`u 0, v 0, u 1, v 1, …, v (k - 1), u 0`: the step `inl t` from `u t` to `v t` reads `(u t, v t)`
and the step `inr t` from `v t` to `u (t + 1)` reads `(u (t + 1), v t)`, the row indices being
read cyclically. -/
def bipartiteEdge (u : Fin k → α) (v : Fin k → β) : Fin k ⊕ Fin k → α × β :=
  Sum.elim (fun t ↦ (u t, v t)) fun t ↦ (u (finRotate k t), v t)

@[simp]
theorem bipartiteEdge_inl (u : Fin k → α) (v : Fin k → β) (t : Fin k) :
    bipartiteEdge u v (.inl t) = (u t, v t) := by
  simp [bipartiteEdge]

@[simp]
theorem bipartiteEdge_inr (u : Fin k → α) (v : Fin k → β) (t : Fin k) :
    bipartiteEdge u v (.inr t) = (u (finRotate k t), v t) := by
  simp [bipartiteEdge]

variable [DecidableEq α] [DecidableEq β]

/-- A bipartite word visits at most one more row and column index than it reads positions.
The word may revisit indices and positions. -/
theorem card_image_add_card_image_le_card_image_bipartiteEdge_add_one (u : Fin k → α)
    (v : Fin k → β) :
    #(univ.image u) + #(univ.image v) ≤ #(univ.image (bipartiteEdge u v)) + 1 := by
  cases k with
  | zero => simp
  | succ m =>
  -- Every row index other than `u 0` is entered for the first time along a step `inr s`, and
  -- every column index along a step `inl t`; these steps read distinct positions.
  let fu : α → Fin (m + 1) := fun a ↦ if h : ∃ t, u t = a then Fin.find (u · = a) h else 0
  let fv : β → Fin (m + 1) := fun b ↦ if h : ∃ t, v t = b then Fin.find (v · = b) h else 0
  have hfu {a : α} (ha : a ∈ univ.image u) :
      u (fu a) = a ∧ ∀ t, u t = a → fu a ≤ t := by
    obtain ⟨t, -, rfl⟩ := mem_image.1 ha
    have h : ∃ t', u t' = u t := ⟨t, rfl⟩
    simp only [fu, h, ↓reduceDIte]
    exact ⟨Fin.find_spec h, fun t' ht' ↦ Fin.find_le_of_pos h ht'⟩
  have hfv {b : β} (hb : b ∈ univ.image v) :
      v (fv b) = b ∧ ∀ t, v t = b → fv b ≤ t := by
    obtain ⟨t, -, rfl⟩ := mem_image.1 hb
    have h : ∃ t', v t' = v t := ⟨t, rfl⟩
    simp only [fv, h, ↓reduceDIte]
    exact ⟨Fin.find_spec h, fun t' ht' ↦ Fin.find_le_of_pos h ht'⟩
  let f : α ⊕ β → α × β :=
    Sum.elim (fun a ↦ (a, v ((finRotate (m + 1)).symm (fu a)))) fun b ↦ (u (fv b), b)
  have hmaps : ∀ x ∈ ((univ.image u).erase (u 0)).disjSum (univ.image v),
      f x ∈ univ.image (bipartiteEdge u v) := by
    rintro (a | b) hx <;> simp only [inl_mem_disjSum, inr_mem_disjSum] at hx
    · have ha := hfu (mem_of_mem_erase hx)
      refine mem_image.2 ⟨.inr ((finRotate (m + 1)).symm (fu a)), mem_univ _, ?_⟩
      simp [f, ha.1]
    · have hb := hfv hx
      exact mem_image.2 ⟨.inl (fv b), mem_univ _, by simp [f, hb.1]⟩
  -- The first visit `fu a` of a row index `a ≠ u 0` is entered along the step `inr s` reading
  -- `f (inl a)`, with `s` just before `fu a`. If this position is also `f (inr b)`, then the
  -- first visit `fv b` of `b` lies between `fu a` and `s`, which is impossible.
  have hmix {a : α} {b : β} (ha : a ∈ (univ.image u).erase (u 0)) (hb : b ∈ univ.image v) :
      f (.inl a) ≠ f (.inr b) := by
    intro hab
    have ha' := hfu (mem_of_mem_erase ha)
    have hb' := hfv hb
    set s := (finRotate (m + 1)).symm (fu a) with hs
    simp only [f, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at hab
    have h1 : fu a ≤ fv b := ha'.2 _ hab.1.symm
    have h2 : fv b ≤ s := hb'.2 _ hab.2
    have hrot : finRotate (m + 1) s = fu a := by simp [hs]
    have hlast : s ≠ Fin.last m := by
      rintro hsl
      rw [hsl, finRotate_last] at hrot
      exact ne_of_mem_erase ha (by rw [← ha'.1, ← hrot])
    have hval := coe_finRotate_of_ne_last hlast
    rw [hrot] at hval
    rw [Fin.le_def] at h1 h2
    omega
  have hinj : Set.InjOn f ↑(((univ.image u).erase (u 0)).disjSum (univ.image v)) := by
    rintro (a | b) hx (a' | b') hy hxy <;>
      simp only [mem_coe, inl_mem_disjSum, inr_mem_disjSum] at hx hy
    · simp only [f, Sum.elim_inl, Prod.mk.injEq] at hxy
      rw [hxy.1]
    · exact absurd hxy (hmix hx hy)
    · exact absurd hxy.symm (hmix hy hx)
    · simp only [f, Sum.elim_inr, Prod.mk.injEq] at hxy
      rw [hxy.2]
  have hcard := card_le_card_of_injOn f hmaps hinj
  rw [card_disjSum, card_erase_of_mem (mem_image_of_mem u (mem_univ 0))] at hcard
  have hpos : 0 < #(univ.image u) := card_pos.2 (univ_nonempty.image u)
  omega

/-- A bipartite word of half-length `k` that reads no position exactly once reads at most `k`
distinct positions. -/
theorem card_image_bipartiteEdge_le_of_no_singleton_edge {u : Fin k → α} {v : Fin k → β}
    (h : ∀ a, ∃ b ≠ a, bipartiteEdge u v b = bipartiteEdge u v a) :
    #(univ.image (bipartiteEdge u v)) ≤ k := by
  have hfiber : ∀ e ∈ univ.image (bipartiteEdge u v),
      2 ≤ #{a | bipartiteEdge u v a = e} := by
    intro e he
    obtain ⟨a, -, rfl⟩ := mem_image.1 he
    obtain ⟨b, hba, hb⟩ := h a
    exact one_lt_card.2 ⟨a, by simp, b, mem_filter.2 ⟨mem_univ _, hb⟩, hba.symm⟩
  have := mul_card_image_le_card univ 2 hfiber
  simp only [card_univ, Fintype.card_sum, Fintype.card_fin] at this
  omega

/-- A bipartite word of half-length `k` that reads no position exactly once visits at most
`k + 1` row and column indices in total. -/
theorem card_image_add_card_image_le_add_one_of_no_singleton_edge {u : Fin k → α}
    {v : Fin k → β} (h : ∀ a, ∃ b ≠ a, bipartiteEdge u v b = bipartiteEdge u v a) :
    #(univ.image u) + #(univ.image v) ≤ k + 1 :=
  (card_image_add_card_image_le_card_image_bipartiteEdge_add_one u v).trans
    (Nat.add_le_add_right (card_image_bipartiteEdge_le_of_no_singleton_edge h) 1)

end TauCeti

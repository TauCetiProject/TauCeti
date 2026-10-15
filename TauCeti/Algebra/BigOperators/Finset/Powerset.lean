/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset

/-!
# Splitting a sum over the subsets of a finite set

A sum over all subsets of a finite set `s` with at least two elements splits into four parts:
the empty set, the singletons, the subsets with at least two elements other than `s`, and `s`
itself. This is the bookkeeping behind expansions of the form
`∏_{i ∈ s} (1 + x_i) = ∑_{S ⊆ s} ∏_{i ∈ S} x_i`, where the four parts are the constant term, the
linear terms, the mixed terms, and the top-degree term.

## Main results

* `TauCeti.sum_powerset_eq_add_sum_singleton_add_sum_filter_add`: the four-part splitting.
-/

public section

namespace TauCeti

open Finset

/-- **A sum over the subsets of a finite set `s` with at least two elements splits into four
parts**: the empty set, the singletons, the subsets with at least two elements other than `s`, and
`s` itself. -/
theorem sum_powerset_eq_add_sum_singleton_add_sum_filter_add {α M : Type*} [DecidableEq α]
    [AddCommMonoid M] {s : Finset α} (hs : 1 < s.card) (f : Finset α → M) :
    ∑ S ∈ s.powerset, f S = f ∅ + ∑ a ∈ s, f {a} +
      ∑ S ∈ s.powerset.filter (fun S : Finset α ↦ 1 < S.card ∧ S ≠ s), f S + f s := by
  rw [← add_sum_erase _ _ (mem_powerset.2 (empty_subset s)),
    ← add_sum_erase (s.powerset.erase ∅) _
      (mem_erase.2 ⟨(card_pos.1 (by omega)).ne_empty, mem_powerset_self s⟩),
    ← sum_filter_add_sum_filter_not ((s.powerset.erase ∅).erase s) fun S ↦ S.card = 1]
  -- The subsets of cardinality one are the singletons of elements of `s`.
  have hsing : ((s.powerset.erase ∅).erase s).filter (fun S : Finset α ↦ S.card = 1) =
      s.image fun a : α ↦ ({a} : Finset α) := by
    ext S
    simp only [mem_filter, mem_erase, mem_powerset, mem_image, card_eq_one]
    constructor
    · rintro ⟨⟨-, -, hS⟩, a, rfl⟩
      exact ⟨a, singleton_subset_iff.1 hS, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨⟨fun h ↦ ?_, singleton_ne_empty a, singleton_subset_iff.2 ha⟩, a, rfl⟩
      have hcard := congrArg Finset.card h
      rw [card_singleton] at hcard
      omega
  -- The remaining nonempty proper subsets are those with at least two elements.
  have hbig : ((s.powerset.erase ∅).erase s).filter (fun S : Finset α ↦ ¬ S.card = 1) =
      s.powerset.filter fun S : Finset α ↦ 1 < S.card ∧ S ≠ s := by
    ext S
    simp only [mem_filter, mem_erase, mem_powerset, ← nonempty_iff_ne_empty, ← card_pos]
    constructor
    · rintro ⟨⟨hs, hpos, hsub⟩, h1⟩
      exact ⟨hsub, by omega, hs⟩
    · rintro ⟨hsub, h1, hs⟩
      exact ⟨⟨hs, by omega, hsub⟩, by omega⟩
  rw [hsing, hbig, sum_image fun _ _ _ _ h ↦ singleton_inj.1 h]
  ac_rfl

end TauCeti

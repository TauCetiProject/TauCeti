/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Card
import Mathlib.Order.Preorder.Finite

/-!
# The strict rank of an element of a finite preorder

In a finite preorder `I`, the number `#{k | k < i}` of elements strictly below `i` is a rank
function: it strictly increases along `<` (`TauCeti.card_filter_lt_lt_card_filter_lt`) and is
smaller than the cardinality of `I` (`TauCeti.card_filter_lt_lt_card`). Hence every strictly
increasing chain of `I` has fewer than `Fintype.card I` steps.

A nonzero function on a finite preorder has a maximal point of its support: an index `a` with
`v a ≠ 0` past which `v` vanishes (`TauCeti.exists_ne_zero_forall_gt_eq_zero`).
-/

public section

open Finset

namespace TauCeti

variable {I : Type*} [Preorder I] [Fintype I] [DecidableRel ((· < ·) : I → I → Prop)]

/-- The rank `#{k | k < i}` strictly increases along `<`. -/
theorem card_filter_lt_lt_card_filter_lt {i j : I} (h : i < j) :
    #{k | k < i} < #{k | k < j} := by
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun k hk ↦ ?_).2 ⟨i, ?_, ?_⟩)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hk.trans h
  · simpa using h
  · simp

/-- The rank `#{k | k < i}` is smaller than the cardinality of `I`. -/
theorem card_filter_lt_lt_card (i : I) : #{k | k < i} < Fintype.card I := by
  rw [← Finset.card_univ]
  exact Finset.card_lt_card (Finset.filter_ssubset.2 ⟨i, Finset.mem_univ _, lt_irrefl i⟩)

/-- A nonzero function on a finite preorder has a maximal point of its support: some `a` with
`v a ≠ 0` and `v b = 0` for every `b > a`. -/
theorem exists_ne_zero_forall_gt_eq_zero {ι S : Type*} [Preorder ι] [Finite ι] [Zero S]
    (v : ι → S) (hv : v ≠ 0) : ∃ a, v a ≠ 0 ∧ ∀ b, a < b → v b = 0 := by
  have hs : {a | v a ≠ 0}.Nonempty := by
    simpa only [Set.nonempty_def, Set.mem_ofPred_eq, ne_eq, funext_iff, Pi.zero_apply,
      not_forall] using hv
  obtain ⟨a, ha, hmax⟩ := (Set.toFinite {a | v a ≠ 0}).exists_maximal hs
  exact ⟨a, ha, fun b hab ↦ by
    by_contra hb
    exact hab.not_ge (hmax hb hab.le)⟩

end TauCeti

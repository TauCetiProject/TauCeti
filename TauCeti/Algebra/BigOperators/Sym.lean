/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Sym.Sym2
import Mathlib.Algebra.BigOperators.Sym
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.BigOperators

/-!
# Counting unordered pairs by their increasing representatives

Over a finite linear order, a finset of unordered pairs with no diagonal pair `s(a, a)` has one
element for each increasing pair `a < b` with `s(a, b)` in it
(`Finset.card_eq_sum_sum_ite_lt_of_forall_mk_notMem`). This is the cardinality form of Mathlib's
`Finset.sum_sym2_filter_not_isDiag`, written as a double sum over the whole type so that it can be
compared term by term with other double sums over `a < b`.
-/

public section

open Finset

namespace Finset

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- A finset of unordered pairs without diagonal pairs is counted over the increasing pairs
`a < b`. -/
theorem card_eq_sum_sum_ite_lt_of_forall_mk_notMem (F : Finset (Sym2 α))
    (hF : ∀ a, s(a, a) ∉ F) :
    #F = ∑ a : α, ∑ b : α, if a < b ∧ s(a, b) ∈ F then 1 else 0 := by
  have hdiag : ∀ e ∈ F, ¬ e.IsDiag := fun e he hd => by
    induction e using Sym2.ind with
    | _ a b =>
      rw [Sym2.mk_isDiag_iff] at hd
      exact hF a (hd ▸ he)
  calc #F = ∑ e ∈ (univ : Finset α).sym2 with ¬ e.IsDiag, if e ∈ F then 1 else 0 := by
        rw [← card_filter]
        congr 1
        ext e
        simp only [mem_filter, mem_sym2_iff, mem_univ, implies_true, true_and]
        exact ⟨fun he => ⟨hdiag e he, he⟩, fun h => h.2⟩
    _ = ∑ p ∈ (univ : Finset α).offDiag with p.1 < p.2, if s(p.1, p.2) ∈ F then 1 else 0 :=
        sum_sym2_filter_not_isDiag _ _
    _ = ∑ p ∈ (univ : Finset (α × α)) with p.1 < p.2, if s(p.1, p.2) ∈ F then 1 else 0 := by
        congr 1
        ext p
        simp only [mem_filter, mem_offDiag, mem_univ, true_and, and_iff_right_iff_imp]
        exact fun h => h.ne
    _ = ∑ a : α, ∑ b : α, if a < b ∧ s(a, b) ∈ F then 1 else 0 := by
        rw [sum_filter, ← Fintype.sum_prod_type']
        simp only [ite_and]

end Finset

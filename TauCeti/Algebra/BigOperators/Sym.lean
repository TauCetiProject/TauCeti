/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Sym
import Mathlib.Algebra.BigOperators.Sym
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.BigOperators

/-!
# Sums over unordered pairs by their increasing representatives

Over a linear order, a finset `F` of unordered pairs from `s` with no diagonal pair `s(a, a)` has
one element for each increasing pair `a < b` of `s` with `s(a, b) ∈ F`. Summing a function over
`F` is therefore a double sum over `s` restricted to `a < b`
(`Finset.sum_eq_sum_sum_ite_lt_of_subset_sym2`); this is Mathlib's
`Finset.sum_sym2_filter_not_isDiag` restricted to `F`, written as a double sum so that it can be
compared term by term with other double sums over `a < b`. Over a finite type the cardinality form
is `Finset.card_eq_sum_sum_ite_lt_of_forall_mk_notMem`.
-/

public section

open Finset

namespace Finset

variable {α : Type*} [LinearOrder α]

/-- A sum over a finset `F ⊆ s.sym2` of unordered pairs without diagonal pairs is a double sum over
the increasing pairs `a < b` of `s`. -/
theorem sum_eq_sum_sum_ite_lt_of_subset_sym2 {M : Type*} [AddCommMonoid M] {s : Finset α}
    {F : Finset (Sym2 α)} (hFs : F ⊆ s.sym2) (hF : ∀ a ∈ s, s(a, a) ∉ F) (f : Sym2 α → M) :
    ∑ e ∈ F, f e = ∑ a ∈ s, ∑ b ∈ s, if a < b ∧ s(a, b) ∈ F then f s(a, b) else 0 := by
  have hdiag : ∀ e ∈ F, ¬ e.IsDiag := fun e he hd => by
    induction e using Sym2.ind with
    | _ a b =>
      rw [Sym2.mk_isDiag_iff] at hd
      subst hd
      exact hF a (mem_sym2_iff.mp (hFs he) a (Sym2.mem_mk_left a a)) he
  calc ∑ e ∈ F, f e = ∑ e ∈ s.sym2 with ¬ e.IsDiag, if e ∈ F then f e else 0 := by
        rw [sum_ite_mem, inter_eq_right.mpr fun e he => mem_filter.mpr ⟨hFs he, hdiag e he⟩]
    _ = ∑ p ∈ s.offDiag with p.1 < p.2, if s(p.1, p.2) ∈ F then f s(p.1, p.2) else 0 :=
        sum_sym2_filter_not_isDiag _ _
    _ = ∑ p ∈ s ×ˢ s with p.1 < p.2, if s(p.1, p.2) ∈ F then f s(p.1, p.2) else 0 := by
        congr 1
        ext p
        simp only [mem_filter, mem_offDiag, mem_product]
        exact ⟨fun h => ⟨⟨h.1.1, h.1.2.1⟩, h.2⟩, fun h => ⟨⟨h.1.1, h.1.2, h.2.ne⟩, h.2⟩⟩
    _ = ∑ a ∈ s, ∑ b ∈ s, if a < b ∧ s(a, b) ∈ F then f s(a, b) else 0 := by
        rw [sum_filter, sum_product]
        simp only [ite_and]

/-- Over a finite linear order, a finset of unordered pairs without diagonal pairs is counted over
the increasing pairs `a < b`. -/
theorem card_eq_sum_sum_ite_lt_of_forall_mk_notMem [Fintype α] (F : Finset (Sym2 α))
    (hF : ∀ a, s(a, a) ∉ F) :
    #F = ∑ a : α, ∑ b : α, if a < b ∧ s(a, b) ∈ F then 1 else 0 := by
  rw [card_eq_sum_ones]
  exact sum_eq_sum_sum_ite_lt_of_subset_sym2 (fun e _ => by simp)
    (fun a _ => hF a) _

end Finset

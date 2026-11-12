/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Set.Card

/-!
# Counting tuples of natural numbers with bounded sum

The tuples `c : A → ℕ` over a finite type `A` with `∑ a, c a ≤ N` are finitely many, and there
are exactly `(N + card A).choose (card A)` of them. Adding one coordinate for the slack
`N - ∑ a, c a` identifies them with the tuples on `Option A` that sum to exactly `N`, which
Mathlib counts as `Finset.card_finsuppAntidiag_nat_eq_choose`.

For `0 < N`, these tuples label the cells of side `1 / N` of the unit cube that meet the standard
simplex, which is how the count enters Mahler's reduction in Diophantine approximation.

## Main results

* `TauCeti.finite_setOf_sum_le`: the tuples with `∑ a, c a ≤ N` form a finite set.
* `TauCeti.ncard_setOf_sum_le`: there are `(N + card A).choose (card A)` of them.
-/

public section

open Finset

namespace TauCeti

/-- The tuples `c : A → ℕ` with `∑ a, c a ≤ N` form a finite set. -/
theorem finite_setOf_sum_le (A : Type*) [Fintype A] (N : ℕ) :
    {c : A → ℕ | ∑ a, c a ≤ N}.Finite := by
  classical
  refine (Fintype.piFinset fun _ : A ↦ Finset.range (N + 1)).finite_toSet.subset fun c hc ↦ ?_
  simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
  exact fun a ↦ Nat.lt_succ_of_le
    ((Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)).trans hc)

/-- There are `(N + card A).choose (card A)` tuples `c : A → ℕ` with `∑ a, c a ≤ N`: the slack
`N - ∑ a, c a` as an extra coordinate makes them the tuples on `Option A` summing to `N`. -/
theorem ncard_setOf_sum_le (A : Type*) [Fintype A] (N : ℕ) :
    {c : A → ℕ | ∑ a, c a ≤ N}.ncard = (N + Fintype.card A).choose (Fintype.card A) := by
  classical
  have hfin := finite_setOf_sum_le A N
  have hbij : hfin.toFinset.card = #((Finset.univ : Finset (Option A)).finsuppAntidiag N) := by
    refine card_nbij' (fun c ↦ Finsupp.equivFunOnFinite.symm fun o ↦ o.elim (N - ∑ a, c a) c)
      (fun F a ↦ F (some a)) (fun c hc ↦ ?_) (fun F hF ↦ ?_) (fun c _ ↦ rfl) fun F hF ↦ ?_
    · have hc' : ∑ a, c a ≤ N := by simpa using hc
      simpa [mem_finsuppAntidiag, Fintype.sum_option] using Nat.sub_add_cancel hc'
    · have hF' : F none + ∑ a, F (some a) = N := by
        simpa [mem_finsuppAntidiag, Fintype.sum_option] using hF
      simpa using hF' ▸ Nat.le_add_left _ _
    · have hF' : F none + ∑ a, F (some a) = N := by
        simpa [mem_finsuppAntidiag, Fintype.sum_option] using hF
      ext (_ | a)
      · simp [← hF']
      · simp
  have hcount : #((Finset.univ : Finset (Option A)).finsuppAntidiag N) =
      (Fintype.card A + 1 + N - 1).choose N := by
    simp [card_finsuppAntidiag_nat_eq_choose]
  have harith : Fintype.card A + 1 + N - 1 = N + Fintype.card A := by omega
  rw [Set.ncard_eq_toFinset_card _ hfin, hbij, hcount, harith, Nat.choose_symm_add]

end TauCeti

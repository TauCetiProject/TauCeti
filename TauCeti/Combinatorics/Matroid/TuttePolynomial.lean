/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import TauCeti.Combinatorics.Matroid.Minor.Rank
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.Matroid.Minor.Finite
import TauCeti.Combinatorics.Matroid.Rank.ENat

/-!
# The Tutte polynomial of a finite matroid

The Tutte polynomial of a finite matroid `M` with ground set `E` and rank function `r` is the
rank generating function
`T_M(x, y) = ∑_{A ⊆ E} (x - 1) ^ (r(E) - r(A)) * (y - 1) ^ (|A| - r(A))`,
a polynomial in two variables with integer coefficients. We realise it in
`MvPolynomial (Fin 2) ℤ`, with `X 0` standing for `x` and `X 1` for `y`, and with the natural
number `(M.eRk A).toNat` as the rank of a set `A`.

The Tutte polynomial satisfies the deletion–contraction recursion proved here: if `e` is neither
a loop nor a coloop then `T_M = T_(M ＼ e) + T_(M ／ e)`, while a loop contributes a factor `y`
and a coloop a factor `x`. The matroid with empty ground set has Tutte polynomial `1`.

## Main declarations

* `Matroid.tuttePolynomial`: the Tutte polynomial of a finite matroid.
* `Matroid.tuttePolynomial_eq_delete_add_contract`: deletion–contraction for an element that is
  neither a loop nor a coloop.
* `Matroid.tuttePolynomial_eq_X_one_mul_of_isLoop`,
  `Matroid.tuttePolynomial_eq_X_zero_mul_of_isColoop`: the recursions at a loop and at a coloop.

## References

* F. Ardila, *Algebraic and geometric methods in enumerative combinatorics*, arXiv:1409.2562,
  §7.6, equation (25) and Theorem 7.6.1.
* J. A. Ellis-Monaghan and C. Merino, *Graph polynomials and their applications I: the Tutte
  polynomial*, arXiv:0803.3079, Definitions 2 and 3.
-/

public section

open Finset MvPolynomial

namespace Matroid

variable {α : Type*} (M : Matroid α) [M.Finite] {e : α}

/-- The Tutte polynomial `T_M(x, y) = ∑_{A ⊆ E} (x - 1) ^ (r(E) - r(A)) * (y - 1) ^ (|A| - r(A))`
of a finite matroid `M` with ground set `E` and rank function `r`, where `X 0` is the variable
`x` and `X 1` the variable `y`. -/
noncomputable def tuttePolynomial : MvPolynomial (Fin 2) ℤ :=
  ∑ A ∈ M.ground_finite.toFinset.powerset,
    (X 0 - 1) ^ (M.eRank.toNat - (M.eRk A).toNat) * (X 1 - 1) ^ (#A - (M.eRk A).toNat)

/-- The Tutte polynomial as a sum over the subsets of the ground set. -/
theorem tuttePolynomial_eq_sum : M.tuttePolynomial = ∑ A ∈ M.ground_finite.toFinset.powerset,
    (X 0 - 1) ^ (M.eRank.toNat - (M.eRk A).toNat) * (X 1 - 1) ^ (#A - (M.eRk A).toNat) :=
  (rfl)

/-- The summand of the Tutte polynomial indexed by a set `A`. -/
private noncomputable def term (A : Finset α) : MvPolynomial (Fin 2) ℤ :=
  (X 0 - 1) ^ (M.eRank.toNat - (M.eRk A).toNat) * (X 1 - 1) ^ (#A - (M.eRk A).toNat)

private lemma tuttePolynomial_eq_sum_term {s : Finset α} (hs : M.ground_finite.toFinset = s) :
    M.tuttePolynomial = ∑ A ∈ s.powerset, term M A := by
  subst hs
  rfl

/-- Split the sum defining the Tutte polynomial according to whether a set contains `e`. -/
private lemma tuttePolynomial_eq_sum_add_sum [DecidableEq α] (he : e ∈ M.E) :
    M.tuttePolynomial = ∑ A ∈ (M.ground_finite.toFinset.erase e).powerset, term M A +
      ∑ A ∈ (M.ground_finite.toFinset.erase e).powerset, term M (insert e A) := by
  rw [← sum_powerset_insert (notMem_erase e _), insert_erase (by simpa)]
  rfl

omit [M.Finite] in
/-- Away from a non-coloop `e`, the summands for `M` and `M ＼ {e}` agree. -/
private lemma term_deleteElem (he : ¬ M.IsColoop e) {A : Finset α} (heA : e ∉ A) :
    term (M ＼ {e}) A = term M A := by
  rw [term, term, eRank_deleteElem_of_not_isColoop he, delete_eRk_eq,
    Set.sdiff_singleton_eq_self (by simpa)]

/-- For a nonloop `e`, the summand for `M` at `insert e A` is the summand for `M ／ {e}` at `A`. -/
private lemma term_insert_of_isNonloop [DecidableEq α] (he : M.IsNonloop e) {A : Finset α}
    (heA : e ∉ A) : term M (insert e A) = term (M ／ {e}) A := by
  rw [term, term, coe_insert, he.toNat_eRk_insert, he.toNat_eRank,
    card_insert_of_notMem heA, Nat.add_sub_add_right, Nat.add_sub_add_right]

omit [M.Finite] in
/-- For a loop `e`, adding `e` to `A` multiplies the summand by `y - 1`. -/
private lemma term_insert_of_isLoop [DecidableEq α] (he : M.IsLoop e) {A : Finset α}
    (heA : e ∉ A) : term M (insert e A) = (X 1 - 1) * term M A := by
  have hr : M.eRk (insert e (A : Set α)) = M.eRk A := by
    rw [← Set.union_singleton, eRk_eq_eRk_union_eRk_le_zero _ he.eRk_eq.le]
  rw [term, term, coe_insert, hr, card_insert_of_notMem heA,
    Nat.sub_add_comm (toNat_eRk_le_card M A), pow_succ]
  ring

/-- For a coloop `e` outside `A`, the summand for `M` at `A` is `x - 1` times the summand for
`M ／ {e}` at `A`. -/
private lemma term_of_isColoop (he : M.IsColoop e) {A : Finset α} (heA : e ∉ A) :
    term M A = (X 0 - 1) * term (M ／ {e}) A := by
  have hr : (M ／ {e}).eRk A = M.eRk A := by
    rw [contract_eq_delete_of_subset_coloops (Set.singleton_subset_iff.2 he), delete_eRk_eq,
      Set.sdiff_singleton_eq_self (by simpa)]
  rw [term, term, he.isNonloop.toNat_eRank, hr, ← hr,
    Nat.sub_add_comm (toNat_eRk_le_toNat_eRank _ _), pow_succ]
  ring

/-- **Deletion–contraction**: if `e ∈ E` is neither a loop nor a coloop, then
`T_M = T_(M ＼ {e}) + T_(M ／ {e})`. -/
theorem tuttePolynomial_eq_delete_add_contract (he : e ∈ M.E) (hl : ¬ M.IsLoop e)
    (hc : ¬ M.IsColoop e) :
    M.tuttePolynomial = (M ＼ {e}).tuttePolynomial + (M ／ {e}).tuttePolynomial := by
  classical
  have hn : M.IsNonloop e := (M.isLoop_or_isNonloop e he).resolve_left hl
  rw [tuttePolynomial_eq_sum_add_sum M he,
    tuttePolynomial_eq_sum_term _ (toFinset_ground_deleteElem M),
    tuttePolynomial_eq_sum_term _ (toFinset_ground_contractElem M)]
  congr 1 <;> refine sum_congr rfl fun A hA ↦ ?_
  · exact (term_deleteElem M hc fun h ↦ notMem_erase e _ (mem_powerset.1 hA h)).symm
  · exact term_insert_of_isNonloop M hn fun h ↦ notMem_erase e _ (mem_powerset.1 hA h)

/-- If `e` is a loop, then `T_M = y * T_(M ＼ {e})`. -/
theorem tuttePolynomial_eq_X_one_mul_of_isLoop (he : M.IsLoop e) :
    M.tuttePolynomial = X 1 * (M ＼ {e}).tuttePolynomial := by
  classical
  rw [tuttePolynomial_eq_sum_add_sum M he.mem_ground,
    tuttePolynomial_eq_sum_term _ (toFinset_ground_deleteElem M), mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun A hA ↦ ?_
  have heA : e ∉ A := fun h ↦ notMem_erase e _ (mem_powerset.1 hA h)
  rw [term_insert_of_isLoop M he heA, term_deleteElem M he.not_isColoop heA]
  ring

/-- If `e` is a coloop, then `T_M = x * T_(M ／ {e})`. -/
theorem tuttePolynomial_eq_X_zero_mul_of_isColoop (he : M.IsColoop e) :
    M.tuttePolynomial = X 0 * (M ／ {e}).tuttePolynomial := by
  classical
  rw [tuttePolynomial_eq_sum_add_sum M he.mem_ground,
    tuttePolynomial_eq_sum_term _ (toFinset_ground_contractElem M), mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun A hA ↦ ?_
  have heA : e ∉ A := fun h ↦ notMem_erase e _ (mem_powerset.1 hA h)
  rw [term_insert_of_isNonloop M he.isNonloop heA, term_of_isColoop M he heA]
  ring

/-- A finite matroid with empty ground set has Tutte polynomial `1`. -/
theorem tuttePolynomial_eq_one_of_ground_eq_empty (h : M.E = ∅) : M.tuttePolynomial = 1 := by
  rw [tuttePolynomial_eq_sum_term M (s := ∅) (by simpa using h), powerset_empty, sum_singleton,
    term, ← eRk_ground, h]
  simp

/-- The empty matroid has Tutte polynomial `1`. -/
@[simp]
theorem tuttePolynomial_emptyOn : (emptyOn α).tuttePolynomial = 1 :=
  tuttePolynomial_eq_one_of_ground_eq_empty _ rfl

/-- A matroid whose ground set is a single loop has Tutte polynomial `y`. -/
theorem tuttePolynomial_eq_X_one_of_ground_eq_singleton (hE : M.E = {e}) (he : M.IsLoop e) :
    M.tuttePolynomial = X 1 := by
  rw [tuttePolynomial_eq_X_one_mul_of_isLoop M he,
    tuttePolynomial_eq_one_of_ground_eq_empty _ (by simp [hE]), mul_one]

/-- A matroid whose ground set is a single coloop has Tutte polynomial `x`. -/
theorem tuttePolynomial_eq_X_zero_of_ground_eq_singleton (hE : M.E = {e})
    (he : M.IsColoop e) : M.tuttePolynomial = X 0 := by
  rw [tuttePolynomial_eq_X_zero_mul_of_isColoop M he,
    tuttePolynomial_eq_one_of_ground_eq_empty _ (by simp [hE]), mul_one]

end Matroid

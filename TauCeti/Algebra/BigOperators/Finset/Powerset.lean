/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Finset.NoncommProd
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import TauCeti.Algebra.GroupWithZero.Indicator

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum

/-!
# Splitting products and sums over the subsets of a finite set

A product (or sum) over all subsets of a finite set `s` with at least two elements splits into four
parts: the empty set, the singletons, the subsets with at least two elements other than `s`, and
`s` itself. This is the bookkeeping behind expansions of the form
`∏_{i ∈ s} (1 + x_i) = ∑_{S ⊆ s} ∏_{i ∈ S} x_i`, where the four parts are the constant term, the
linear terms, the mixed terms, and the top-degree term.

A product over the `n + 1`-element subsets of `insert a s`, with `a ∉ s`, splits into the
product over the `n + 1`-element subsets of `s` and the product over the sets `insert a t` with `t`
an `n`-element subset of `s`. This is the inductive step for elementary symmetric sums.

For a family commuting pairwise only on `s`, a sum of noncommutative products over the
`n`-element subsets of `u ⊆ s` can be rewritten with the family extended by zero outside `s`,
which commutes pairwise everywhere.

## Main results

* `TauCeti.prod_powerset_eq_mul_prod_singleton_mul_prod_filter_mul`,
  `TauCeti.sum_powerset_eq_add_sum_singleton_add_sum_filter_add`: the four-part splitting.
* `Finset.prod_powersetCard_succ_insert`, `Finset.sum_powersetCard_succ_insert`: splitting over
  the `n + 1`-element subsets of `insert a s`.
* `Finset.sum_noncommProd_powersetCard_eq_indicator`: sums of noncommutative products over
  `n`-element subsets, rewritten with the family extended by zero.
* `Finset.sum_noncommProd_powersetCard_succ_insert`: the recursion for the sum of the products
  over the `n + 1`-element subsets when an index is added to `s`, and
  `Finset.sum_noncommProd_powersetCard_succ_insert_of_pairwise_commute`, the same recursion as
  sums over `powersetCard` for a family commuting pairwise everywhere.
* `TauCeti.exists_minimal_vanishing_subsum`: a vanishing sum with a nonzero term has a minimal
  vanishing subsum with at least two terms.
* `TauCeti.sum_filter_two_le_card`: a sum over the subsets with at least two elements of a finite
  type, of a function of the cardinality, grouped by cardinality.
-/

public section

open scoped Function

namespace Finset

variable {α β : Type*} [CommMonoid β]

/-- A product over the `n + 1`-element subsets of `insert a s`, with `a ∉ s`, is the product over
the `n + 1`-element subsets of `s` times the product over the sets `insert a t` with `t` an
`n`-element subset of `s`. -/
@[to_additive /-- A sum over the `n + 1`-element subsets of `insert a s`, with `a ∉ s`, is the sum
over the `n + 1`-element subsets of `s` plus the sum over the sets `insert a t` with `t` an
`n`-element subset of `s`. -/]
theorem prod_powersetCard_succ_insert [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (n : ℕ) (f : Finset α → β) :
    ∏ t ∈ (insert a s).powersetCard (n + 1), f t =
      (∏ t ∈ s.powersetCard (n + 1), f t) * ∏ t ∈ s.powersetCard n, f (insert a t) := by
  rw [powersetCard_succ_insert ha, prod_union, prod_image]
  · exact insert_erase_invOn.2.injOn.mono fun t ht ↦
      notMem_mono (mem_powersetCard.1 ht).1 ha
  · aesop (add simp [disjoint_left, insert_subset_iff, mem_powersetCard])

/-- For `u ⊆ s` and a family commuting pairwise on `s`, the sum of the products over the
`n`-element subsets of `u` is the corresponding sum for the family extended by zero outside `s`. -/
theorem sum_noncommProd_powersetCard_eq_indicator {ι R : Type*} [Semiring R] {s u : Finset ι}
    (hu : u ⊆ s) (x : ι → R) (hc : (s : Set ι).Pairwise (Commute on x)) (n : ℕ) :
    ∑ t : u.powersetCard n,
        t.1.noncommProd x (hc.mono (coe_subset.2 ((mem_powersetCard.1 t.2).1.trans hu))) =
      ∑ t ∈ u.powersetCard n,
        t.noncommProd ((s : Set ι).indicator x) (hc.pairwise_commute_indicator.set_pairwise _) := by
  rw [← sum_coe_sort (u.powersetCard n)]
  exact sum_congr rfl fun (t : u.powersetCard n) _ ↦ noncommProd_congr rfl (fun i hi ↦
    (Set.indicator_of_mem (mem_coe.2 ((mem_powersetCard.1 t.2).1.trans hu hi)) x).symm) _

/-- With `a ∉ s`, the sum of the products over the `n + 1`-element subsets of `insert a s` of a
family commuting pairwise everywhere is the corresponding sum over `s` plus `x a` times the sum of
the products over the `n`-element subsets of `s`. -/
theorem sum_noncommProd_powersetCard_succ_insert_of_pairwise_commute {ι R : Type*} [Semiring R]
    [DecidableEq ι] {s : Finset ι} {a : ι} (ha : a ∉ s) (x : ι → R) (hc : Pairwise (Commute on x))
    (n : ℕ) :
    ∑ t ∈ (insert a s).powersetCard (n + 1), t.noncommProd x (hc.set_pairwise _) =
      ∑ t ∈ s.powersetCard (n + 1), t.noncommProd x (hc.set_pairwise _) +
        x a * ∑ t ∈ s.powersetCard n, t.noncommProd x (hc.set_pairwise _) := by
  rw [sum_powersetCard_succ_insert ha, mul_sum]
  exact congrArg _ (sum_congr rfl fun t ht ↦
    noncommProd_insert_of_notMem _ _ _ _ fun h ↦ ha ((mem_powersetCard.1 ht).1 h))

/-- With `a ∉ s`, the sum of the products over the `n + 1`-element subsets of `insert a s` of a
family commuting pairwise on `insert a s` is the corresponding sum over `s` plus `x a` times the
sum of the products over the `n`-element subsets of `s`. -/
theorem sum_noncommProd_powersetCard_succ_insert {ι R : Type*} [Semiring R] [DecidableEq ι]
    {s : Finset ι} {a : ι} (ha : a ∉ s) (x : ι → R)
    (hc : ((insert a s : Finset ι) : Set ι).Pairwise (Commute on x)) (n : ℕ) :
    ∑ t : (insert a s).powersetCard (n + 1),
        t.1.noncommProd x (hc.mono (coe_subset.2 (mem_powersetCard.1 t.2).1)) =
      ∑ t : s.powersetCard (n + 1), t.1.noncommProd x
          (hc.mono (coe_subset.2 ((mem_powersetCard.1 t.2).1.trans (subset_insert a s)))) +
        x a * ∑ t : s.powersetCard n, t.1.noncommProd x
          (hc.mono (coe_subset.2 ((mem_powersetCard.1 t.2).1.trans (subset_insert a s)))) := by
  rw [sum_noncommProd_powersetCard_eq_indicator subset_rfl x hc,
    sum_noncommProd_powersetCard_eq_indicator (subset_insert a s) x hc,
    sum_noncommProd_powersetCard_eq_indicator (subset_insert a s) x hc,
    ← Set.indicator_of_mem (mem_coe.2 (mem_insert_self a s)) x]
  exact sum_noncommProd_powersetCard_succ_insert_of_pairwise_commute ha _
    hc.pairwise_commute_indicator n

end Finset

namespace TauCeti

open Finset
open scoped Finset

/-- **A product over the subsets of a finite set `s` with at least two elements splits into four
parts**: the empty set, the singletons, the subsets with at least two elements other than `s`, and
`s` itself. -/
@[to_additive /-- **A sum over the subsets of a finite set `s` with at least two elements splits
into four parts**: the empty set, the singletons, the subsets with at least two elements other than
`s`, and `s` itself. -/]
theorem prod_powerset_eq_mul_prod_singleton_mul_prod_filter_mul {α M : Type*} [DecidableEq α]
    [CommMonoid M] {s : Finset α} (hs : 1 < s.card) (f : Finset α → M) :
    ∏ S ∈ s.powerset, f S = f ∅ * (∏ a ∈ s, f {a}) *
      (∏ S ∈ s.powerset.filter (fun S : Finset α ↦ 1 < S.card ∧ S ≠ s), f S) * f s := by
  rw [← mul_prod_erase _ _ (mem_powerset.2 (empty_subset s)),
    ← mul_prod_erase (s.powerset.erase ∅) _
      (mem_erase.2 ⟨(card_pos.1 (by omega)).ne_empty, mem_powerset_self s⟩),
    ← prod_filter_mul_prod_filter_not ((s.powerset.erase ∅).erase s) fun S ↦ S.card = 1]
  -- The subsets of cardinality one are the singletons of elements of `s`.
  have hsing : ((s.powerset.erase ∅).erase s).filter (fun S : Finset α ↦ S.card = 1) =
      s.image fun a : α ↦ ({a} : Finset α) := by
    ext S
    simp only [mem_filter, mem_erase, mem_powerset, mem_image, card_eq_one]
    grind
  -- The remaining nonempty proper subsets are those with at least two elements.
  have hbig : ((s.powerset.erase ∅).erase s).filter (fun S : Finset α ↦ ¬ S.card = 1) =
      s.powerset.filter fun S : Finset α ↦ 1 < S.card ∧ S ≠ s := by
    ext S
    simp only [mem_filter, mem_erase, mem_powerset, ← nonempty_iff_ne_empty, ← card_pos]
    grind
  rw [hsing, hbig, prod_image fun _ _ _ _ h ↦ singleton_inj.1 h]
  ac_rfl

/-- A vanishing sum `∑ fᵢ = 0` with a nonzero term has a minimal vanishing subsum with at least two
terms: an index set `I` with `∑ i ∈ I, fᵢ = 0` such that no nonempty proper subset of `I` has
vanishing sum. Applied to a linear relation `∑ cᵢxᵢ = 0` among the unknowns of a unit equation,
it yields a nondegenerate homogeneous solution in fewer unknowns. -/
theorem exists_minimal_vanishing_subsum {ι M : Type*} [Fintype ι] [AddCommMonoid M] {f : ι → M}
    (h : ∑ i, f i = 0) (hf : f ≠ 0) :
    ∃ I : Finset ι, 2 ≤ #I ∧ ∑ i ∈ I, f i = 0 ∧ ∀ J ⊂ I, J.Nonempty → ∑ i ∈ J, f i ≠ 0 := by
  classical
  -- Choose `I` of least cardinality among the nonempty vanishing subsums of nonzero terms.
  let s := univ.filter (f · ≠ 0)
  let F := s.powerset.filter fun J ↦ J.Nonempty ∧ ∑ i ∈ J, f i = 0
  have hsF : s ∈ F := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hf
    exact mem_filter.mpr ⟨mem_powerset_self s, ⟨i, by simpa [s] using hi⟩,
      by rw [sum_filter_ne_zero, h]⟩
  obtain ⟨I, hIF, hImin⟩ := F.exists_min_image card ⟨s, hsF⟩
  obtain ⟨hIs, hIne, hI0⟩ : I ⊆ s ∧ I.Nonempty ∧ ∑ i ∈ I, f i = 0 := by simpa [F] using hIF
  refine ⟨I, ?_, hI0, fun J hJI hJ hJ0 ↦ ?_⟩
  · by_contra! hI
    obtain ⟨i, rfl⟩ := card_eq_one.mp (le_antisymm (Nat.lt_succ_iff.mp hI) hIne.card_pos)
    exact (by simpa [s] using hIs (mem_singleton_self i) : f i ≠ 0) (by simpa using hI0)
  · exact (card_lt_card hJI).not_ge (hImin J (by simpa [F, hJ, hJ0] using hJI.subset.trans hIs))


/-- A sum over the subsets with at least two elements of an `(n + 2)`-element type, of a function
of the cardinality, grouped by cardinality. -/
theorem sum_filter_two_le_card {ι M : Type*} [Fintype ι] [AddCommMonoid M] {n : ℕ}
    (hn : Fintype.card ι = n + 2) (g : ℕ → M) :
    ∑ I ∈ (univ : Finset (Finset ι)).filter (2 ≤ #·), g #I =
      ∑ k : Fin (n + 1), (n + 2).choose (k + 2) • g (k + 2) := by
  classical
  rw [sum_filter, ← powerset_univ, sum_powerset_apply_card (fun m ↦ if 2 ≤ m then g m else 0),
    card_univ, hn, Fin.sum_univ_eq_sum_range (fun k ↦ (n + 2).choose (k + 2) • g (k + 2)),
    sum_range_succ', sum_range_succ']
  simp only [zero_add, Nat.not_ofNat_le_one, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero, ite_false,
    le_add_iff_nonneg_left, zero_le, ite_true, nsmul_zero, add_zero]

end TauCeti

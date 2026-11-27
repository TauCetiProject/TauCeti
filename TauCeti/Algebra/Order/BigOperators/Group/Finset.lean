/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi
import TauCeti.Algebra.Order.BigOperators.Group.Multiset

/-!
# Order bounds for finset sums and products

In a lattice-ordered additive commutative group, a sum of `#s` terms, each bounded by `B` in
absolute value, is bounded by `#s • B` in absolute value. This is the crude estimate used when a
bound on each term of a finite average or a counting sum is summed over the index set.

In a linearly ordered commutative monoid, a finite product of nonempty finite maxima is the
maximum, over all choices of one index from each family, of the corresponding products. This is
the order analogue of `Finset.prod_univ_sum`, which expands a product of sums as a sum over the
same choices. Additively, a sum of row maxima is bounded by `b` exactly when every choice of one
row per component has sum at most `b`.

## Main results

* `Finset.abs_sum_le_card_nsmul`: `|∑ i ∈ s, f i| ≤ #s • B` when `|f i| ≤ B` for every `i ∈ s`.
* `Finset.card_nsmul_le_sum_sum_of_exists_le`: the total of a finite family of nonnegative
  weights bounds the cardinality of a subset times the threshold reached at each of its points.
* `Finset.prod_univ_sup'`, `Finset.sum_univ_sup'`: `∏ i, (t i).sup' (f i)` is the maximum of
  `∏ i, f i (x i)` over `x ∈ Fintype.piFinset t`, and likewise for sums.
-/

public section

open Fintype

namespace Finset

section AbsSum

variable {ι R : Type*} [AddCommGroup R] [Lattice R] [IsOrderedAddMonoid R]

/-- A sum of terms with absolute value at most `B` has absolute value at most `#s • B`. -/
theorem abs_sum_le_card_nsmul {s : Finset ι} {f : ι → R} {B : R} (h : ∀ i ∈ s, |f i| ≤ B) :
    |∑ i ∈ s, f i| ≤ #s • B :=
  Multiset.abs_sum_map_le_card_nsmul s.val f h

end AbsSum

/-- A counting form of Markov's inequality for a finite family of weight functions. Each term
counted by `s` reaches the common threshold `r` in at least one of the weights indexed by `I`. -/
theorem card_nsmul_le_sum_sum_of_exists_le {α ι R : Type*} [AddCommMonoid R] [Preorder R]
    [IsOrderedAddMonoid R] (s : Finset α) {t : Finset α} (hst : s ⊆ t) (I : Finset ι)
    (w : ι → α → R) {r : R} (hw : ∀ i ∈ I, ∀ x ∈ t, 0 ≤ w i x)
    (hr : ∀ x ∈ s, ∃ i ∈ I, r ≤ w i x) : s.card • r ≤ ∑ i ∈ I, ∑ x ∈ t, w i x := by
  calc
    _ ≤ ∑ x ∈ s, ∑ i ∈ I, w i x := s.card_nsmul_le_sum _ _ fun x hx ↦ by
      obtain ⟨i, hi, hrx⟩ := hr x hx
      exact hrx.trans (single_le_sum (fun j hj ↦ hw j hj x (hst hx)) hi)
    _ ≤ ∑ x ∈ t, ∑ i ∈ I, w i x :=
      sum_le_sum_of_subset_of_nonneg hst fun x hx _ ↦ sum_nonneg fun i hi ↦ hw i hi x hx
    _ = _ := sum_comm

section ProdSup

variable {ι M : Type*} {κ : ι → Type*} [Fintype ι] [DecidableEq ι]
  [CommMonoid M] [LinearOrder M] [IsOrderedMonoid M]

/-- A product of nonempty finite maxima is the maximum of the products over all choices of one
index from each family. -/
@[to_additive /-- A sum of nonempty finite maxima is the maximum of the sums over all choices of
one index from each family. -/]
theorem prod_univ_sup' (t : ∀ i, Finset (κ i)) (ht : ∀ i, (t i).Nonempty) (f : ∀ i, κ i → M) :
    ∏ i, (t i).sup' (ht i) (f i) =
      (piFinset t).sup' (piFinset_nonempty.2 ht) fun x => ∏ i, f i (x i) := by
  refine le_antisymm ?_ <| sup'_le _ _ fun x hx =>
    prod_le_prod fun i _ => le_sup' (f i) (mem_piFinset.1 hx i)
  choose x hx hxf using fun i => exists_mem_eq_sup' (ht i) (f i)
  calc ∏ i, (t i).sup' (ht i) (f i) = ∏ i, f i (x i) := prod_congr rfl fun i _ => hxf i
    _ ≤ _ := le_sup' (fun x => ∏ i, f i (x i)) (mem_piFinset.2 hx)

end ProdSup

end Finset

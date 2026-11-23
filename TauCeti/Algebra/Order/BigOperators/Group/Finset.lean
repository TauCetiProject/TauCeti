/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi

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
  -- the triangle inequality `|∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i|`, valid in any lattice-ordered group
  (le_sum_of_subadditive _ abs_zero.le abs_add_le s f).trans <| sum_le_card_nsmul s _ B h

end AbsSum

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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Products and sums over subtypes

Mathlib's `tprod_subtype` rewrites a product over a subtype `{b // p b}` as a product over the
whole type of the multiplicative indicator. Two products over different subtypes therefore agree
as soon as the two indicators agree pointwise, which reduces such comparisons to a case split on
the defining predicates.

## Main results

* `tprod_subtype_eq_of_mulIndicator_eq`, `tsum_subtype_eq_of_indicator_eq`: products (sums)
  over two subtypes agree when the factors (summands), extended by one (zero), agree.
* `hasProd_map_ite_mem`, `hasSum_map_ite_mem`: a family supported in a finite set `s` and given
  there by a homomorphism `φ` applied to `f m` has product (sum) `φ (∏ m ∈ s, f m)`
  (`φ (∑ m ∈ s, f m)`).
-/

public section

namespace TauCeti

/-- Two products over subtypes agree when their factors, extended by one, agree. -/
@[to_additive /-- Two sums over subtypes agree when their summands, extended by zero, agree. -/]
theorem tprod_subtype_eq_of_mulIndicator_eq {α β : Type*} [CommMonoid α] [TopologicalSpace α]
    {p q : β → Prop} {g g' : β → α}
    (h : ∀ b, {b | p b}.mulIndicator g b = {b | q b}.mulIndicator g' b) :
    ∏' b : {b // p b}, g b = ∏' b : {b // q b}, g' b :=
  (tprod_subtype {b | p b} g).trans <| (tprod_congr h).trans (tprod_subtype {b | q b} g').symm

/-- A family supported in a finite set `s` and given there by `φ (f m)` has product
`φ (∏ m ∈ s, f m)` for any monoid homomorphism `φ`. -/
@[to_additive /-- A family supported in a finite set `s` and given there by `φ (f m)` sums to
`φ (∑ m ∈ s, f m)` for any additive monoid homomorphism `φ`. -/]
theorem hasProd_map_ite_mem {ι α β F : Type*} [CommMonoid α] [CommMonoid β]
    [TopologicalSpace β] [FunLike F α β] [MonoidHomClass F α β] [DecidableEq ι]
    (φ : F) (s : Finset ι) (f : ι → α)
    (L : SummationFilter ι := SummationFilter.unconditional ι) [L.LeAtTop] :
    HasProd (fun m ↦ φ (if m ∈ s then f m else 1)) (φ (∏ m ∈ s, f m)) L := by
  have h : HasProd (fun m ↦ φ (if m ∈ s then f m else 1))
      (∏ m ∈ s, φ (if m ∈ s then f m else 1)) L :=
    hasProd_prod_of_ne_finset_one fun m hm ↦ by simp [hm]
  rwa [← map_prod, Finset.prod_ite_mem, Finset.inter_self] at h

end TauCeti

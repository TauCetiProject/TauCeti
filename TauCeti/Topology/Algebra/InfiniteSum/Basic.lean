/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Products and sums over subtypes and over disjoint indicators

Mathlib's `tprod_subtype` rewrites a product over a subtype `{b // p b}` as a product over the
whole type of the multiplicative indicator. Two products over different subtypes therefore agree
as soon as the two indicators agree pointwise, which reduces such comparisons to a case split on
the defining predicates.

## Main results

* `tprod_subtype_eq_of_mulIndicator_eq`, `tsum_subtype_eq_of_indicator_eq`: products (sums)
  over two subtypes agree when the factors (summands), extended by one (zero), agree.
* `hasProd_mulIndicator_apply_of_mem`, `tprod_mulIndicator_apply_of_mem` (additive:
  `hasSum_indicator_apply_of_mem`, `tsum_indicator_apply_of_mem`): over a pairwise disjoint family
  of sets, at a point of the `i`-th set, the product of the multiplicative indicators (the sum of
  the indicators) reduces to the `i`-th factor (summand). This evaluates countably-valued
  functions written as `∑ₙ 𝟙_{Aₙ} cₙ` with disjoint `Aₙ`.
-/

public section

open Function

namespace TauCeti

/-- Two products over subtypes agree when their factors, extended by one, agree. -/
@[to_additive /-- Two sums over subtypes agree when their summands, extended by zero, agree. -/]
theorem tprod_subtype_eq_of_mulIndicator_eq {α β : Type*} [CommMonoid α] [TopologicalSpace α]
    {p q : β → Prop} {g g' : β → α}
    (h : ∀ b, {b | p b}.mulIndicator g b = {b | q b}.mulIndicator g' b) :
    ∏' b : {b // p b}, g b = ∏' b : {b // q b}, g' b :=
  (tprod_subtype {b | p b} g).trans <| (tprod_congr h).trans (tprod_subtype {b | q b} g').symm

/-- At a point of the `i`-th set of a pairwise disjoint family, the product of the multiplicative
indicators has the `i`-th factor as its value. -/
@[to_additive /-- At a point of the `i`-th set of a pairwise disjoint family, the sum of the
indicators has the `i`-th summand as its value. -/]
theorem hasProd_mulIndicator_apply_of_mem {ι α β : Type*} [CommMonoid α] [TopologicalSpace α]
    {s : ι → Set β} (hs : Pairwise (Disjoint on s)) (f : ι → β → α) {i : ι} {x : β}
    (hx : x ∈ s i) : HasProd (fun j ↦ (s j).mulIndicator (f j) x) (f i x) := by
  convert hasProd_single i fun j hj ↦
    Set.mulIndicator_of_notMem (fun hxj ↦ Set.disjoint_left.1 (hs hj) hxj hx) (f j)
  exact (Set.mulIndicator_of_mem hx (f i)).symm

/-- At a point of the `i`-th set of a pairwise disjoint family, the product of the multiplicative
indicators is the `i`-th factor. -/
@[to_additive /-- At a point of the `i`-th set of a pairwise disjoint family, the sum of the
indicators is the `i`-th summand. -/]
theorem tprod_mulIndicator_apply_of_mem {ι α β : Type*} [CommMonoid α] [TopologicalSpace α]
    [T2Space α] {s : ι → Set β} (hs : Pairwise (Disjoint on s)) (f : ι → β → α) {i : ι} {x : β}
    (hx : x ∈ s i) : ∏' j, (s j).mulIndicator (f j) x = f i x :=
  (hasProd_mulIndicator_apply_of_mem hs f hx).tprod_eq

end TauCeti

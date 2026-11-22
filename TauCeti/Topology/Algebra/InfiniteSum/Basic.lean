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

end TauCeti

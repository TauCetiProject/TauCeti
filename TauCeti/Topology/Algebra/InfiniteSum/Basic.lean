/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Conditional infinite products and sums over predicate subtypes

Mathlib's `tprod_subtype` and `tsum_subtype` express an infinite product or sum over a set
coercion `s : Set α` in terms of `Set.mulIndicator` and `Set.indicator`. When filtering an ambient
index type by a decidable predicate `P : α → Prop`, rewriting directly between the subtype
`{x : α // P x}` and a pointwise `if P x then f x else 1` (resp. `0`) avoids repeated indicator
case splits and `Set.Elem`/`Subtype` reindexing at call sites.

## Main results

* `TauCeti.tprod_subtype_eq_tprod_ite`, `TauCeti.tsum_subtype_eq_tsum_ite`: an infinite product
  (sum) over `{x : α // P x}` equals the infinite product (sum) of `if P x then f x else 1`
  (resp. `0`) over `α`.
-/

public section

namespace TauCeti

/-- An infinite product over a subtype `{x : α // P x}` equals the infinite product over `α` of the
conditional factor `if P x then f x else 1`. -/
@[to_additive /-- An infinite sum over a subtype `{x : α // P x}` equals the infinite sum over `α`
of the conditional summand `if P x then f x else 0`. -/]
theorem tprod_subtype_eq_tprod_ite {α β : Type*} [CommMonoid β] [TopologicalSpace β]
    (P : α → Prop) [DecidablePred P] (f : α → β) :
    (∏' x : {x : α // P x}, f x.1) = ∏' x : α, if P x then f x else 1 :=
  ((Equiv.subtypeEquivRight fun _ ↦ Set.mem_ofPred.symm).tprod_eq fun x ↦ f x.1).symm.trans <|
    (tprod_subtype {x : α | P x} f).trans <|
      tprod_congr fun x ↦ by simp [Set.mulIndicator_apply, Set.mem_ofPred_eq]

end TauCeti

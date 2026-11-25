/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Chain
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability of reachability in a family of relations

Let `R : α → V → V → Prop` be a family of relations on `V`, parametrised by a measurable space
`α`, such that each instance `{x | R x a b}` is measurable. Being a chain along a fixed finite
list is then measurable, and, when `V` is countable, so is reachability along `R x`: it is a
countable union over the finite paths.

## Main results

* `TauCeti.measurableSet_setOf_isChain`: being a chain along a fixed list is measurable.
* `TauCeti.measurableSet_setOf_reflTransGen`: reachability along a measurable family of relations
  on a countable type is measurable.
-/

public section

open Set

namespace TauCeti

variable {α V : Type*} [MeasurableSpace α] {R : α → V → V → Prop}

/-- Being a chain along a fixed finite list is measurable in a measurable family of relations. -/
theorem measurableSet_setOf_isChain (hR : ∀ a b, MeasurableSet {x | R x a b}) :
    ∀ l : List V, MeasurableSet {x | List.IsChain (R x) l}
  | [] => by simp
  | [_] => by simp
  | a :: b :: l => by
    simp only [List.isChain_cons_cons, ofPred_and]
    exact (hR a b).inter (measurableSet_setOf_isChain hR (b :: l))

/-- **Reachability is measurable.** For a family of relations on a countable type, each of whose
instances is a measurable condition, reachability along the relation is measurable: it is a
countable union over the finite paths. -/
theorem measurableSet_setOf_reflTransGen [Countable V] (hR : ∀ a b, MeasurableSet {x | R x a b})
    (u v : V) : MeasurableSet {x | Relation.ReflTransGen (R x) u v} := by
  have h : {x | Relation.ReflTransGen (R x) u v} = ⋃ l : List V,
      {x | List.IsChain (R x) (u :: l)} ∩ {_x | (u :: l).getLast (List.cons_ne_nil _ _) = v} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    exact ⟨List.exists_isChain_cons_of_relationReflTransGen,
      fun ⟨l, hl, hv⟩ ↦ List.relationReflTransGen_of_exists_isChain_cons l hl hv⟩
  rw [h]
  exact MeasurableSet.iUnion fun l ↦
    (measurableSet_setOf_isChain hR _).inter (MeasurableSet.const _)

end TauCeti

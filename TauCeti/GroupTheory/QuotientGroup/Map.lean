/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The quotient homomorphism between two quotients of a group

For normal subgroups `V ≤ U` of a group `G`, the class of `g` modulo `V` determines its class
modulo `U`, so there is a homomorphism `G ⧸ V →* G ⧸ U`. It is Mathlib's `QuotientGroup.map` at
the identity of `G`, the map `ProfiniteGrp.toFiniteQuotientFunctor` sends `V ≤ U` to, and it is
the transition map of every system indexed by the normal subgroups of `G` ordered by inclusion.

`QuotientGroup.map` asks for `V ≤ Subgroup.comap (MonoidHom.id G) U` rather than `V ≤ U`, and the
two are equal only up to unfolding; naming the specialization keeps the systems built on it
rewritable. The name records the systems it serves, whose quotients are the finite ones, by open
normal subgroups; nothing here assumes either subgroup has finite index.

## Main definitions

* `TauCeti.finiteQuotientMap hVU`: the quotient homomorphism `G ⧸ V →* G ⧸ U` for `V ≤ U`.

## Main statements

* `TauCeti.finiteQuotientMap_mk`: the map sends the class of `g` to the class of `g`, which is
  what characterizes it.
* `TauCeti.finiteQuotientMap_refl` and `TauCeti.finiteQuotientMap_comp`: the two functor laws.
* `TauCeti.finiteQuotientMap_surjective`: the map is surjective.

## Implementation notes

`finiteQuotientMap` keeps its body sealed: it is characterized by the lemmas above, and those are
proved as `(rfl)`, so no consumer unfolds a body. Surjectivity is stated here, beside the
definition, for the same reason: it is Mathlib's
`QuotientGroup.map_surjective_of_surjective` read across the sealed body, and this is the one
module in which the two maps are still definitionally equal.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] {U V W : Subgroup G}

/-- The quotient homomorphism `G ⧸ V →* G ⧸ U` for normal subgroups `V ≤ U`. This is Mathlib's
`QuotientGroup.map` at the identity of `G`, the map `ProfiniteGrp.toFiniteQuotientFunctor` sends
`V ≤ U` to. -/
def finiteQuotientMap [U.Normal] [V.Normal] (hVU : V ≤ U) : G ⧸ V →* G ⧸ U :=
  QuotientGroup.map V U (.id G) fun _ hv => hVU hv

@[simp]
theorem finiteQuotientMap_mk [U.Normal] [V.Normal] (hVU : V ≤ U) (g : G) :
    finiteQuotientMap hVU (g : G ⧸ V) = (g : G ⧸ U) :=
  (rfl)

@[simp]
theorem finiteQuotientMap_refl [U.Normal] :
    finiteQuotientMap (le_refl U) = MonoidHom.id (G ⧸ U) :=
  QuotientGroup.map_id U _

@[simp]
theorem finiteQuotientMap_comp [U.Normal] [V.Normal] [W.Normal] (hWV : W ≤ V) (hVU : V ≤ U) :
    (finiteQuotientMap hVU).comp (finiteQuotientMap hWV) = finiteQuotientMap (hWV.trans hVU) :=
  QuotientGroup.map_comp_map W V U (.id G) (.id G) _ _ _

/-- The quotient homomorphism `G ⧸ V →* G ⧸ U` is surjective. -/
theorem finiteQuotientMap_surjective [U.Normal] [V.Normal] (hVU : V ≤ U) :
    Function.Surjective (finiteQuotientMap hVU) :=
  QuotientGroup.map_surjective_of_surjective V U (.id G) QuotientGroup.mk_surjective _

end TauCeti

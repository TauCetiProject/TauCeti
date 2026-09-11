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
modulo `U`, so there is a homomorphism `G ⧸ V →* G ⧸ U`: the homomorphism underlying Mathlib's
`Subgroup.quotientMapOfLE`. It is Mathlib's `QuotientGroup.map` at the identity of `G`, the map
`ProfiniteGrp.toFiniteQuotientFunctor` sends `V ≤ U` to, and it is the transition map of every
system indexed by the normal subgroups of `G` ordered by inclusion.

`QuotientGroup.map` asks for `V ≤ Subgroup.comap (MonoidHom.id G) U` rather than `V ≤ U`, and the
two are equal only up to unfolding; naming the specialization keeps the systems built on it
rewritable.

## Main definitions

* `TauCeti.QuotientGroup.mapOfLE hVU`: the quotient homomorphism `G ⧸ V →* G ⧸ U` for `V ≤ U`.

## Main statements

* `TauCeti.QuotientGroup.mapOfLE_mk`: the map sends the class of `g` to the class of `g`, which
  is what characterizes it.
* `TauCeti.QuotientGroup.mapOfLE_refl` and `TauCeti.QuotientGroup.mapOfLE_comp`: the two functor
  laws.
* `TauCeti.QuotientGroup.mapOfLE_surjective`: the map is surjective.

## Usage

Work with `mapOfLE` through the four lemmas above: `mapOfLE_mk` evaluates it on classes,
`mapOfLE_refl` and `mapOfLE_comp` simplify identities and composites, and `mapOfLE_surjective`
feeds constructions that need a surjection, such as `Sylow.mapSurjective`. To identify
`mapOfLE hVU` with another homomorphism out of `G ⧸ V`, compare the two on classes with
`QuotientGroup.induction_on` and `mapOfLE_mk`.
-/

public section

namespace TauCeti

namespace QuotientGroup

variable {G : Type*} [Group G] {U V W : Subgroup G}

/-- The quotient homomorphism `G ⧸ V →* G ⧸ U` for normal subgroups `V ≤ U`. This is Mathlib's
`QuotientGroup.map` at the identity of `G`, the map `ProfiniteGrp.toFiniteQuotientFunctor` sends
`V ≤ U` to. -/
def mapOfLE [U.Normal] [V.Normal] (hVU : V ≤ U) : G ⧸ V →* G ⧸ U :=
  _root_.QuotientGroup.map V U (.id G) fun _ hv => hVU hv

/-- The quotient homomorphism sends the class of `g` modulo `V` to the class of `g` modulo
`U`. -/
@[simp]
theorem mapOfLE_mk [U.Normal] [V.Normal] (hVU : V ≤ U) (g : G) :
    mapOfLE hVU (g : G ⧸ V) = (g : G ⧸ U) :=
  (rfl)

/-- The quotient homomorphism for `U ≤ U` is the identity of `G ⧸ U`. -/
@[simp]
theorem mapOfLE_refl [U.Normal] :
    mapOfLE (le_refl U) = MonoidHom.id (G ⧸ U) :=
  _root_.QuotientGroup.map_id U _

/-- The quotient homomorphisms compose: `G ⧸ W → G ⧸ V → G ⧸ U` is the quotient homomorphism
for `W ≤ U`. -/
@[simp]
theorem mapOfLE_comp [U.Normal] [V.Normal] [W.Normal] (hWV : W ≤ V) (hVU : V ≤ U) :
    (mapOfLE hVU).comp (mapOfLE hWV) = mapOfLE (hWV.trans hVU) :=
  _root_.QuotientGroup.map_comp_map W V U (.id G) (.id G) _ _ _

/-- The quotient homomorphism `G ⧸ V →* G ⧸ U` is surjective. -/
theorem mapOfLE_surjective [U.Normal] [V.Normal] (hVU : V ≤ U) :
    Function.Surjective (mapOfLE hVU) :=
  _root_.QuotientGroup.map_surjective_of_surjective V U (.id G)
    _root_.QuotientGroup.mk_surjective _

end QuotientGroup

end TauCeti

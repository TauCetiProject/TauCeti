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
`ProfiniteGrp.toFiniteQuotientFunctor` sends `V ≤ U` to, and it is the canonical transition map
of the system of quotient groups of `G` indexed by its normal subgroups ordered by inclusion, and
of the systems built from those quotients.

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
* `TauCeti.QuotientGroup.mapOfLE_comp_mk'`: composing it with the quotient map of `G` modulo
  `V` gives the quotient map of `G` modulo `U`.
* `TauCeti.QuotientGroup.map_comp_mapOfLE` and `TauCeti.QuotientGroup.mapOfLE_comp_map`: it
  commutes with the homomorphisms `QuotientGroup.map` induced by a homomorphism `G →* H` on the
  quotients.
* `TauCeti.QuotientGroup.mapOfLE_surjective`: the map is surjective.

## Usage

Work with `mapOfLE` through the lemmas above: `mapOfLE_mk` evaluates it on classes,
`mapOfLE_refl`, `mapOfLE_comp`, `mapOfLE_comp_mk'`, `map_comp_mapOfLE` and `mapOfLE_comp_map`
simplify identities and composites, and `mapOfLE_surjective` feeds constructions that need a
surjection, such as `Sylow.mapSurjective`.
To identify `mapOfLE hVU` with another homomorphism out of `G ⧸ V`, compare the two on classes with
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

/-- The quotient homomorphism `G ⧸ V →* G ⧸ U` is the quotient map of `G` modulo `U`, read
through the quotient map of `G` modulo `V`. -/
@[simp]
theorem mapOfLE_comp_mk' [U.Normal] [V.Normal] (hVU : V ≤ U) :
    (mapOfLE hVU).comp (_root_.QuotientGroup.mk' V) = _root_.QuotientGroup.mk' U :=
  MonoidHom.ext fun g ↦ mapOfLE_mk hVU g

/-- The homomorphism `G ⧸ U →* H ⧸ N` induced by `f` composed with the quotient homomorphism
`G ⧸ V →* G ⧸ U` is the homomorphism `G ⧸ V →* H ⧸ N` induced by `f`. -/
@[simp]
theorem map_comp_mapOfLE {H : Type*} [Group H] {N : Subgroup H} [N.Normal] [U.Normal] [V.Normal]
    (hVU : V ≤ U) (f : G →* H) (h : U ≤ N.comap f) :
    (_root_.QuotientGroup.map U N f h).comp (mapOfLE hVU) =
      _root_.QuotientGroup.map V N f (hVU.trans h) :=
  _root_.QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun g ↦ by simp)

/-- The quotient homomorphism `H ⧸ M →* H ⧸ N` composed with the homomorphism `G ⧸ U →* H ⧸ M`
induced by `f` is the homomorphism `G ⧸ U →* H ⧸ N` induced by `f`. -/
@[simp]
theorem mapOfLE_comp_map {H : Type*} [Group H] {M N : Subgroup H} [M.Normal] [N.Normal]
    [U.Normal] (hMN : M ≤ N) (f : G →* H) (h : U ≤ M.comap f) :
    (mapOfLE hMN).comp (_root_.QuotientGroup.map U M f h) =
      _root_.QuotientGroup.map U N f (h.trans (Subgroup.comap_mono hMN)) :=
  _root_.QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun g ↦ by simp)

/-- The quotient homomorphism `G ⧸ V →* G ⧸ U` is surjective. -/
theorem mapOfLE_surjective [U.Normal] [V.Normal] (hVU : V ≤ U) :
    Function.Surjective (mapOfLE hVU) :=
  _root_.QuotientGroup.map_surjective_of_surjective V U (.id G)
    _root_.QuotientGroup.mk_surjective _

end QuotientGroup

end TauCeti

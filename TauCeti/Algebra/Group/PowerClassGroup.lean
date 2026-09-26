/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.PowMonoidHom

/-!
# The group of `n`th power classes `G ⧸ Gⁿ`

For a commutative group `G` the subgroup `Gⁿ` of `n`th powers is the range of `powMonoidHom n`,
and this file names it together with the quotient `G ⧸ Gⁿ` and the class of an element. At `n = 2`
the subgroup is Mathlib's `Subgroup.square G`, by `TauCeti.square_eq_powMonoidHom_two_range`.

## Main definitions

* `TauCeti.powerSubgroup`: the subgroup `Gⁿ ≤ G`, whose elements are characterised as the `n`th
  powers by `TauCeti.mem_powerSubgroup_iff`.
* `TauCeti.powerClassQuotient`, `TauCeti.powerClassHom`: the quotient `G ⧸ Gⁿ` and the map taking
  an element to its power class. It is surjective (`TauCeti.powerClassHom_surjective`) with kernel
  `Gⁿ` (`TauCeti.ker_powerClassHom`), so it presents `G ⧸ Gⁿ` as the quotient of `G` by the `n`th
  powers.
* `TauCeti.powerClassMap`: the map `G ⧸ Gⁿ → H ⧸ Hⁿ` induced by a homomorphism `G →* H`, which
  carries `n`th powers to `n`th powers. It is functorial (`TauCeti.powerClassMap_id`,
  `TauCeti.powerClassMap_comp`); for a field extension `L/K` and `f` the map `Kˣ →* Lˣ` it is the
  map of power classes along which Kummer theory is natural in the field.
-/

public section

namespace TauCeti

variable (G : Type*) [CommGroup G] (n : ℕ)

/-- **The subgroup of `n`th powers** `Gⁿ ≤ G`. -/
def powerSubgroup : Subgroup G :=
  (powMonoidHom n : G →* G).range

/-- **The group of `n`th power classes** `G ⧸ Gⁿ`. -/
abbrev powerClassQuotient : Type _ :=
  G ⧸ powerSubgroup G n

/-- The quotient homomorphism `G → G ⧸ Gⁿ`. -/
def powerClassHom : G →* powerClassQuotient G n :=
  QuotientGroup.mk' (powerSubgroup G n)

/-- The kernel of the power-class homomorphism is the subgroup `Gⁿ` of `n`th powers. -/
@[simp]
theorem ker_powerClassHom : (powerClassHom G n).ker = powerSubgroup G n :=
  QuotientGroup.ker_mk' (powerSubgroup G n)

/-- Every power class is the class of an element: `powerClassHom` is surjective. -/
theorem powerClassHom_surjective : Function.Surjective (powerClassHom G n) :=
  QuotientGroup.mk'_surjective (powerSubgroup G n)

variable {G}

/-- The power-class homomorphism sends `g` to its quotient class. -/
@[simp]
theorem powerClassHom_apply (g : G) : powerClassHom G n g = QuotientGroup.mk g := by
  exact QuotientGroup.mk'_apply (powerSubgroup G n) g

/-- An element belongs to `Gⁿ` exactly when it is an `n`th power. -/
@[simp]
theorem mem_powerSubgroup_iff {g : G} : g ∈ powerSubgroup G n ↔ ∃ h : G, h ^ n = g := by
  rw [powerSubgroup, MonoidHom.mem_range]
  exact exists_congr fun h => by rw [powMonoidHom_apply]

/-! ### Functoriality -/

variable {H : Type*} [CommGroup H]

/-- A homomorphism carries `n`th powers to `n`th powers: `Gⁿ` lies in the preimage of `Hⁿ`. -/
theorem powerSubgroup_le_comap (f : G →* H) :
    powerSubgroup G n ≤ (powerSubgroup H n).comap f := by
  rintro _ ⟨g, rfl⟩
  exact ⟨f g, (map_pow f g n).symm⟩

/-- **The map of power classes** `G ⧸ Gⁿ → H ⧸ Hⁿ` induced by a homomorphism `f : G →* H`, the
class of `g` going to the class of `f g`. -/
def powerClassMap (f : G →* H) : powerClassQuotient G n →* powerClassQuotient H n :=
  QuotientGroup.map (powerSubgroup G n) (powerSubgroup H n) f (powerSubgroup_le_comap n f)

/-- `powerClassMap` sends the class of `g` to the class of `f g`. -/
@[simp]
theorem powerClassMap_mk (f : G →* H) (g : G) :
    powerClassMap n f (QuotientGroup.mk g) = QuotientGroup.mk (f g) :=
  QuotientGroup.map_mk _ _ _ _ g

/-- `powerClassMap` is the map of power classes compatible with `powerClassHom`:
`powerClassMap n f ∘ powerClassHom G n = powerClassHom H n ∘ f`. -/
theorem powerClassMap_comp_powerClassHom (f : G →* H) :
    (powerClassMap n f).comp (powerClassHom G n) = (powerClassHom H n).comp f := by
  ext g
  simp

/-- The identity induces the identity on power classes. -/
@[simp]
theorem powerClassMap_id : powerClassMap n (MonoidHom.id G) = MonoidHom.id _ := by
  ext g
  simp

/-- The map of power classes of a composite is the composite of the maps of power classes. -/
theorem powerClassMap_comp {P : Type*} [CommGroup P] (f : G →* H) (f' : H →* P) :
    powerClassMap n (f'.comp f) = (powerClassMap n f').comp (powerClassMap n f) := by
  ext g
  simp

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.RepresentationTheory.Rep.Res

/-!
# The units along a tower of Galois extensions

Let `K ⊆ L ⊆ M` be a tower of fields with `L/K` normal. Restriction `Gal(M/K) → Gal(L/K)` and the
inclusion `Lˣ → Mˣ` are compatible: `σ(ι(a)) = ι(σ|_L(a))` for `σ ∈ Gal(M/K)` and `a ∈ Lˣ`. This
file records the inclusion as a morphism `unitsInflationHom K L M` from the restriction of the
`Gal(L/K)`-representation `Lˣ` to the `Gal(M/K)`-representation `Mˣ`. Through
`groupCohomology.map (AlgEquiv.restrictNormalHom L)` it induces the inflation maps

`Hⁿ(Gal(L/K), Lˣ) → Hⁿ(Gal(M/K), Mˣ)`,

in particular the inflation of relative Brauer groups `H²(Gal(L/K), Lˣ) → H²(Gal(M/K), Mˣ)` along
which local invariants are compared.

## Main definitions

* `TauCeti.unitsInflationHom`: the inclusion `Lˣ → Mˣ` as a morphism of `Gal(M/K)`-representations
  from the restriction of `Lˣ` along `Gal(M/K) → Gal(L/K)`.
-/

public section

namespace TauCeti

universe u

variable (K L M : Type u) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M] [Algebra L M]
  [IsScalarTower K L M] [Normal K L]

/-- **The units along a tower of Galois extensions**: for `K ⊆ L ⊆ M` with `L/K` normal, the
inclusion `Lˣ → Mˣ` is a morphism of `Gal(M/K)`-representations from `Lˣ`, on which `Gal(M/K)` acts
through restriction to `L`, to `Mˣ`. It is the coefficient map of inflation
`Hⁿ(Gal(L/K), Lˣ) → Hⁿ(Gal(M/K), Mˣ)`. -/
noncomputable def unitsInflationHom :
    Rep.res (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K))
        (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) ⟶
      Rep.ofMulDistribMulAction Gal(M/K) Mˣ :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (Units.map (algebraMap L M : L →* M)).toAdditive.toIntLinearMap fun σ a =>
      Additive.toMul.injective <| Units.ext <|
        AlgEquiv.restrictNormal_commutes σ L (Rep.toAdditive a).toMul

/-- `unitsInflationHom K L M` is the inclusion `Lˣ → Mˣ`. -/
@[simp]
theorem unitsInflationHom_apply (a : Lˣ) :
    (unitsInflationHom K L M).hom
        ((Rep.toAdditive (M := Gal(L/K)) (G := Lˣ)).symm (Additive.ofMul a)) =
      (Rep.toAdditive (M := Gal(M/K)) (G := Mˣ)).symm
        (Additive.ofMul (Units.map (algebraMap L M : L →* M) a)) :=
  (rfl)

end TauCeti

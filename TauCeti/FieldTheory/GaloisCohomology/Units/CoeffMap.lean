/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Extension
public import TauCeti.FieldTheory.GaloisCohomology.Coefficients

/-!
# Unit coefficients along an embedding of fields

For a `K`-embedding `σ : L →ₐ[K] Kˢ`, the chosen identification of separable closures
`separableClosureRingEquiv K L σ : Lˢ ≃+* Kˢ` carries the units of `Lˢ` to the units of `Kˢ` and
back. These are the coefficient legs, with unit coefficients, of corestriction and restriction
along `L/K`; they involve no exponent, Kummer map or Hilbert 90, so they live here rather than in
`TauCeti.FieldTheory.GaloisCohomology.Kummer`, which uses them for the Kummer sequence.

## Main definitions

* `TauCeti.unitsCoeffMapSymm`: the units of `Lˢ` as units of `Kˢ`.
* `TauCeti.unitsCoeffMap`: the units of `Kˢ` as units of `Lˢ`, its inverse.

## Main results

* `TauCeti.unitsCoeffMapSymm_smul`, `TauCeti.unitsCoeffMap_smul`: both are equivariant along
  `G_L ≃ₜ* Gal(Kˢ/σ(L))`; `TauCeti.unitsCoeffMap_coe_smul` is the second with `G_L` acting
  through `G_K`.
* `TauCeti.unitsCoeffMapSymm_unitsCoeffMap`, `TauCeti.unitsCoeffMap_unitsCoeffMapSymm`: they are
  inverse to each other, also as additive maps (`TauCeti.unitsCoeffMapSymm_comp_unitsCoeffMap`,
  `TauCeti.unitsCoeffMap_comp_unitsCoeffMapSymm`).
* `TauCeti.unitsCoeffMapSymm_unitsCoeffPow`, `TauCeti.unitsCoeffMap_unitsCoeffPow`: both commute
  with the `n`th power map `TauCeti.unitsCoeffPow`.
* `TauCeti.unitsCoeffMapSymm_coe_baseUnitsEquivInvariants`,
  `TauCeti.unitsCoeffMap_coe_embeddedUnitsInvariants`,
  `TauCeti.unitsCoeffMap_coe_baseUnitsEquivInvariants`: their effect on the invariants attached to
  units of `L` and of `K`.
-/

public section

noncomputable section

namespace TauCeti

variable (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K)

/-- **The units of `Lˢ` as units of `Kˢ`**, along the identification of separable closures. It is
the ambient coefficient map of the Kummer sequence for which `TauCeti.kummerCoeffMapSymm` is the
map of `n`th roots of unity. -/
def unitsCoeffMapSymm : UnitsCoeff L →+ UnitsCoeff K :=
  MonoidHom.toAdditive (Units.map (separableClosureRingEquiv K L σ).toMonoidHom)

/-- `unitsCoeffMapSymm` applies the identification of separable closures to a unit. -/
@[simp]
theorem toMul_unitsCoeffMapSymm (y : UnitsCoeff L) :
    (unitsCoeffMapSymm K L σ y).toMul =
      Units.map (separableClosureRingEquiv K L σ).toMonoidHom y.toMul :=
  (rfl)

/-- **`unitsCoeffMapSymm` is equivariant** along the inverse of `G_L ≃ₜ* Gal(Kˢ/σ(L))`. -/
@[simp]
theorem unitsCoeffMapSymm_smul (h : ↥σ.fieldRange.fixingSubgroup) (y : UnitsCoeff L) :
    unitsCoeffMapSymm K L σ ((absoluteGaloisGroupEquivFixingSubgroup K L σ).symm h • y) =
      h • unitsCoeffMapSymm K L σ y := by
  refine Additive.toMul.injective ?_
  rw [Subgroup.smul_def (α := UnitsCoeff K), toMul_unitsCoeffMapSymm, Additive.toMul_smul,
    Additive.toMul_smul, toMul_unitsCoeffMapSymm]
  exact Units.ext (by simp [absoluteGaloisGroupEquivFixingSubgroup_symm_apply])

/-- **The units of `Kˢ` as units of `Lˢ`**, along the inverse of the identification of separable
closures: the inverse of `TauCeti.unitsCoeffMapSymm` (`unitsCoeffMapSymm_unitsCoeffMap`), and the
coefficient leg of restriction with unit coefficients, as `TauCeti.kummerCoeffMap` is for the
roots of unity. -/
def unitsCoeffMap : UnitsCoeff K →+ UnitsCoeff L :=
  MonoidHom.toAdditive (Units.map (separableClosureRingEquiv K L σ).symm.toMonoidHom)

/-- `unitsCoeffMap` applies the inverse identification of separable closures to a unit. -/
@[simp]
theorem toMul_unitsCoeffMap (x : UnitsCoeff K) :
    (unitsCoeffMap K L σ x).toMul =
      Units.map (separableClosureRingEquiv K L σ).symm.toMonoidHom x.toMul :=
  (rfl)

/-- **`unitsCoeffMap` is equivariant** along `G_L ≃ₜ* Gal(Kˢ/σ(L))`: an automorphism `g` of `Lˢ`
over `L` acts on `(Kˢ)ˣ` through its image in the subgroup of `G_K` fixing `σ(L)`. -/
@[simp]
theorem unitsCoeffMap_smul (g : AbsoluteGaloisGroup L) (x : UnitsCoeff K) :
    unitsCoeffMap K L σ (absoluteGaloisGroupEquivFixingSubgroup K L σ g • x) =
      g • unitsCoeffMap K L σ x := by
  refine Additive.toMul.injective ?_
  rw [Subgroup.smul_def (α := UnitsCoeff K), toMul_unitsCoeffMap, Additive.toMul_smul,
    Additive.toMul_smul, toMul_unitsCoeffMap]
  exact Units.ext (by simp [absoluteGaloisGroupEquivFixingSubgroup_apply])

/-- `TauCeti.unitsCoeffMap_smul` with `g` acting on `(Kˢ)ˣ` through its image in `G_K`, the form
the compatible pair of `TauCeti.galoisResUnits` takes once the inclusion of the subgroup fixing
`σ(L)` is unfolded. -/
@[simp]
theorem unitsCoeffMap_coe_smul (g : AbsoluteGaloisGroup L) (x : UnitsCoeff K) :
    unitsCoeffMap K L σ
        ((absoluteGaloisGroupEquivFixingSubgroup K L σ g : AbsoluteGaloisGroup K) • x) =
      g • unitsCoeffMap K L σ x :=
  unitsCoeffMap_smul K L σ g x

/-- The two coefficient identifications of the units are inverse to each other. -/
@[simp]
theorem unitsCoeffMapSymm_unitsCoeffMap (x : UnitsCoeff K) :
    unitsCoeffMapSymm K L σ (unitsCoeffMap K L σ x) = x :=
  Additive.toMul.injective <| Units.ext <| by simp

/-- The two coefficient identifications of the units are inverse to each other. -/
@[simp]
theorem unitsCoeffMap_unitsCoeffMapSymm (y : UnitsCoeff L) :
    unitsCoeffMap K L σ (unitsCoeffMapSymm K L σ y) = y :=
  Additive.toMul.injective <| Units.ext <| by simp

/-- `TauCeti.unitsCoeffMapSymm_unitsCoeffMap` as an equality of additive maps. -/
@[simp]
theorem unitsCoeffMapSymm_comp_unitsCoeffMap :
    (unitsCoeffMapSymm K L σ).comp (unitsCoeffMap K L σ) = AddMonoidHom.id (UnitsCoeff K) :=
  AddMonoidHom.ext (unitsCoeffMapSymm_unitsCoeffMap K L σ)

/-- `TauCeti.unitsCoeffMap_unitsCoeffMapSymm` as an equality of additive maps. -/
@[simp]
theorem unitsCoeffMap_comp_unitsCoeffMapSymm :
    (unitsCoeffMap K L σ).comp (unitsCoeffMapSymm K L σ) = AddMonoidHom.id (UnitsCoeff L) :=
  AddMonoidHom.ext (unitsCoeffMap_unitsCoeffMapSymm K L σ)

/-! ### Interaction with the coefficient operations -/

/-- `unitsCoeffMapSymm` commutes with the `n`th power map of the Kummer sequence. -/
@[simp]
theorem unitsCoeffMapSymm_unitsCoeffPow (n : ℕ) (y : UnitsCoeff L) :
    unitsCoeffMapSymm K L σ (unitsCoeffPow L n y) = unitsCoeffPow K n (unitsCoeffMapSymm K L σ y) :=
  Additive.toMul.injective <| Units.ext <| by simp

/-- `unitsCoeffMap` commutes with the `n`th power map of the Kummer sequence. -/
@[simp]
theorem unitsCoeffMap_unitsCoeffPow (n : ℕ) (x : UnitsCoeff K) :
    unitsCoeffMap K L σ (unitsCoeffPow K n x) = unitsCoeffPow L n (unitsCoeffMap K L σ x) :=
  Additive.toMul.injective <| Units.ext <| by simp

/-- `unitsCoeffMapSymm` carries the invariant of `G_L` attached to `b ∈ Lˣ` to the invariant of
`Gal(Kˢ/σ(L))` attached to `b`. -/
@[simp]
theorem unitsCoeffMapSymm_coe_baseUnitsEquivInvariants (b : Additive Lˣ) :
    unitsCoeffMapSymm K L σ (baseUnitsEquivInvariants L b) =
      embeddedUnitsInvariants K L σ b.toMul :=
  Additive.toMul.injective <| Units.ext <| by simp [separableClosureRingEquiv_algebraMap]

/-- `unitsCoeffMap` carries the invariant of `Gal(Kˢ/σ(L))` attached to `b ∈ Lˣ` to the invariant
of `G_L` attached to `b`, inverting `TauCeti.unitsCoeffMapSymm_coe_baseUnitsEquivInvariants`. -/
@[simp]
theorem unitsCoeffMap_coe_embeddedUnitsInvariants (b : Lˣ) :
    unitsCoeffMap K L σ (embeddedUnitsInvariants K L σ b) =
      baseUnitsEquivInvariants L (Additive.ofMul b) :=
  (congrArg (unitsCoeffMap K L σ)
    (unitsCoeffMapSymm_coe_baseUnitsEquivInvariants K L σ (.ofMul b))).symm.trans
    (unitsCoeffMap_unitsCoeffMapSymm K L σ _)

/-- `unitsCoeffMap` carries the invariant of `G_K` attached to `a ∈ Kˣ` to the invariant of `G_L`
attached to the image of `a` in `Lˣ`. -/
@[simp]
theorem unitsCoeffMap_coe_baseUnitsEquivInvariants (a : Additive Kˣ) :
    unitsCoeffMap K L σ (baseUnitsEquivInvariants K a) =
      baseUnitsEquivInvariants L (Additive.ofMul (Units.map (algebraMap K L : K →* L) a.toMul)) :=
  Additive.toMul.injective <| Units.ext <| by
    simp [IsScalarTower.algebraMap_apply K L (SeparableClosure L)]

end TauCeti

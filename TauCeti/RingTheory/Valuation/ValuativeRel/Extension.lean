/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

/-!
# Valuation extensions from valuative relations

Mathlib has two compatible notions of one valuation extending another. `ValuativeExtension A B`
states the relation intrinsically, without choosing value groups, while
`Valuation.HasExtension vA vB` states that the pullback of `vB` is equivalent to `vA`.

This file supplies the canonical bridge for the valuations attached to valuative relations. It
allows Mathlib's valuation-extension API, including its algebra maps between valuation rings and
residue fields, to be used directly from a `ValuativeExtension` hypothesis.

## Main results

* `ValuativeExtension.valuationHasExtension`: the canonical valuation on `B` extends the
  canonical valuation on `A`.
* `TauCeti.integerRingAlgebra`: the induced algebra structure on the valuation rings.
* `TauCeti.residueFieldAlgebra`: the induced algebra structure on the residue fields.
-/

public section

open ValuativeRel

namespace ValuativeExtension

variable {A B : Type*} [CommRing A] [Ring B] [ValuativeRel A] [ValuativeRel B]
  [Algebra A B] [ValuativeExtension A B]

/-- A compatible extension of valuative relations makes the canonical valuation on the larger
ring an extension, in Mathlib's valuation-level sense, of the canonical valuation on the base.
-/
instance valuationHasExtension :
    Valuation.HasExtension (valuation A) (valuation B) where
  val_isEquiv_comap :=
    (ValuativeRel.isEquiv ((valuation B).comap (algebraMap A B)) (valuation A)).symm

end ValuativeExtension

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

local notation "𝒪ᵥ[" K "]" => Valuation.integer (valuation K)
local notation "𝓀ᵥ[" K "]" => IsLocalRing.ResidueField ↥𝒪ᵥ[K]

/-- The structure map of a compatible extension restricts to its rings of integers. -/
noncomputable instance integerRingAlgebra : Algebra 𝒪ᵥ[K] 𝒪ᵥ[L] :=
  Valuation.HasExtension.instAlgebra_valuationSubring (valuation K) (valuation L)

/-- The local map on rings of integers induces the residue-field extension. -/
noncomputable instance residueFieldAlgebra : Algebra 𝓀ᵥ[K] 𝓀ᵥ[L] :=
  IsLocalRing.ResidueField.instAlgebra

/-- Coercing the integer-ring structure map to `L` gives the field structure map. -/
theorem coe_algebraMap_integerRing (x : 𝒪ᵥ[K]) :
    ((algebraMap 𝒪ᵥ[K] 𝒪ᵥ[L] x : 𝒪ᵥ[L]) : L) = algebraMap K L (x : K) :=
  Valuation.HasExtension.coe_algebraMap_valuationSubring_eq (valuation K) (valuation L) x

/-- Reduction commutes with the structure map between the rings of integers. -/
@[simp]
theorem algebraMap_residueField_residue (x : 𝒪ᵥ[K]) :
    algebraMap 𝓀ᵥ[K] 𝓀ᵥ[L] (IsLocalRing.residue 𝒪ᵥ[K] x) =
      IsLocalRing.residue 𝒪ᵥ[L] (algebraMap 𝒪ᵥ[K] 𝒪ᵥ[L] x) :=
  Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap (valuation K) (valuation L) x

end TauCeti

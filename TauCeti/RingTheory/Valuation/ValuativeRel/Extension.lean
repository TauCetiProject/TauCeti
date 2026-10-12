/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Valuation.Integral

/-!
# Valuation extensions from valuative relations

Mathlib has two compatible notions of one valuation extending another. `ValuativeExtension A B`
states the relation intrinsically, without choosing value groups, while
`Valuation.HasExtension vA vB` states that the pullback of `vB` is equivalent to `vA`.

This file supplies the canonical bridge for the valuations attached to valuative relations. It
allows Mathlib's valuation-extension API, including its algebra maps between valuation rings and
residue fields, to be used directly from a `ValuativeExtension` hypothesis.

In an algebraic field extension, the nonzero values of the base field are coinitial among the
nonzero values of the extension. This provides the small base-field elements needed to compare
the two valuative topologies.

## Main results

* `TauCeti.ValuativeExtension.trans`: compatibility of valuative relations in an algebra tower.
* `ValuativeExtension.valuationHasExtension`: the canonical valuation on `B` extends the
  canonical valuation on `A`.
* `TauCeti.integerRingAlgebra`: the induced algebra structure on the valuation rings.
* `TauCeti.residueFieldAlgebra`: the induced algebra structure on the residue fields.
* `IsAlgebraic.exists_ne_zero_vle`: a nonzero algebraic element has value at least that of some
  nonzero base-field element.
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

/-- Compatibility of valuative relations composes along an algebra tower. -/
theorem ValuativeExtension.trans (A B C : Type*) [CommSemiring A] [CommSemiring B] [Semiring C]
    [ValuativeRel A] [ValuativeRel B] [ValuativeRel C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [ValuativeExtension A B] [ValuativeExtension B C] : ValuativeExtension A C where
  vle_iff_vle a b := by
    simp only [IsScalarTower.algebraMap_apply A B C, ValuativeExtension.vle_iff_vle]

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

end TauCeti

variable {K L : Type*} [Field K] [Field L] [ValuativeRel L] [Algebra K L]

/-- In a valued field extension, every nonzero algebraic element has value at least
that of some nonzero base-field element. -/
theorem IsAlgebraic.exists_ne_zero_vle {y : L} (halg : IsAlgebraic K y) (hy : y ≠ 0) :
    ∃ x : K, x ≠ 0 ∧ algebraMap K L x ≤ᵥ y := by
  -- Clear denominators over the base valuation ring, then use integrally closedness of the
  -- target valuation ring to bound the resulting multiple of `y⁻¹`.
  let v := (valuation L).comap (algebraMap K L)
  have : Valuation.HasExtension v (valuation L) := ⟨.refl⟩
  obtain ⟨a, ha⟩ := halg.inv.isIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors v.integer) y⁻¹
  have hai : IsIntegral (valuation L).integer (a • y⁻¹) := ha.tower_top
  have hav : valuation L (a • y⁻¹) ≤ 1 :=
    (Valuation.integer.integers (valuation L)).isIntegral_iff_v_le_one.mp hai
  have hyv : 0 < valuation L y := zero_lt_iff.mpr (by simpa using hy)
  refine ⟨a, ?_, ?_⟩
  · exact_mod_cast (nonZeroDivisors.ne_zero a.property)
  · rw [(valuation L).vle_iff_le]
    simpa [Submonoid.smul_def, Algebra.smul_def,
      IsScalarTower.algebraMap_apply v.integer K L,
      Algebra.algebraMap_ofSubring, mul_inv_le_iff₀ hyv] using hav

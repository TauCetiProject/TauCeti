/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import TauCeti.RingTheory.Valuation.ValuativeRel.Extension
import TauCeti.FieldTheory.FunctionField.Place.OfValuationSubring
import TauCeti.NumberTheory.LocalField.NatCastValuation

/-!
# The maximal ideal of a local field as a height-one prime

Let `L` be a nonarchimedean local field. Its valuation ring `𝒪[L]`, packaged as the valuation
subring of `L`, is a discrete valuation ring, so its maximal ideal is a height-one prime
`TauCeti.maximalPrime L` of a Dedekind domain with fraction field `L`. Statements about the
fraction field of a Dedekind domain at a height-one prime `u`, phrased with the adic valuation of
`u`, therefore apply to `L` at `maximalPrime L`. This file records the facts needed to read them
back in terms of the valuation of `L`: the adic valuation of `maximalPrime L` is equivalent to the
valuation of `L` and has valuation ring `𝒪[L]` again, the valuation ring of `K` maps into it for an
extension `L/K`, and an integer that is nonzero in the residue field of `K` lies outside
`maximalPrime L`.

## Main definitions

* `TauCeti.maximalPrime L`: the maximal ideal of `𝒪[L]`, as a height-one prime.
* `TauCeti.algebraValuationSubringMaximalPrime`: the map from `𝒪[K]` to the valuation ring of the
  adic valuation of `maximalPrime L`, a local homomorphism
  (`TauCeti.isLocalHom_algebraMap_valuationSubringMaximalPrime`) compatible with `K → L`
  (`TauCeti.coe_algebraMap_valuationSubringMaximalPrime`).

## Main results

* `TauCeti.valuationSubring_valuation_maximalPrime`: the valuation ring of the adic valuation of
  `maximalPrime L` is `𝒪[L]`.
* `TauCeti.isEquiv_valuation_maximalPrime`: that adic valuation is equivalent to the valuation of
  `L`.
* `TauCeti.natCast_notMem_maximalPrime`: an integer nonzero in the residue field of `K` lies
  outside `maximalPrime L`.
-/

public section

open ValuativeRel

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- `𝒪[L]`, packaged as a valuation subring, is a discrete valuation ring. -/
instance isDiscreteValuationRing_valuationSubring :
    IsDiscreteValuationRing (valuation L).valuationSubring :=
  inferInstanceAs (IsDiscreteValuationRing 𝒪[L])

variable (L) in
/-- The maximal ideal of `𝒪[L]`, as a height-one prime. -/
noncomputable abbrev maximalPrime :
    IsDedekindDomain.HeightOneSpectrum (valuation L).valuationSubring :=
  IsDiscreteValuationRing.maximalIdeal _

variable (L) in
/-- The valuation ring of the adic valuation of the maximal ideal of `𝒪[L]` is `𝒪[L]`. -/
theorem valuationSubring_valuation_maximalPrime :
    ((maximalPrime L).valuation L).valuationSubring = (valuation L).valuationSubring :=
  Place.valuationSubring_valuation_maximalIdeal _

variable (L) in
/-- The adic valuation of the maximal ideal of `𝒪[L]` is equivalent to the valuation of `L`. -/
theorem isEquiv_valuation_maximalPrime :
    ((maximalPrime L).valuation L).IsEquiv (valuation L) :=
  (Valuation.isEquiv_iff_valuationSubring _ _).2 (valuationSubring_valuation_maximalPrime L)

variable [Algebra K L] [ValuativeExtension K L]

variable (K L) in
/-- `𝒪[K]` maps into the valuation ring of the adic valuation of the maximal ideal of `𝒪[L]`,
which is `𝒪[L]`. -/
noncomputable instance algebraValuationSubringMaximalPrime :
    Algebra 𝒪[K] ((maximalPrime L).valuation L).valuationSubring :=
  (((algebraMap K L).comp (algebraMap 𝒪[K] K)).codRestrict _ fun r ↦
    (by
      rw [valuationSubring_valuation_maximalPrime, ← coe_algebraMap_integerRing]
      exact (algebraMap 𝒪[K] 𝒪[L] r).2 :
        algebraMap K L r ∈ ((maximalPrime L).valuation L).valuationSubring)).toAlgebra

/-- The map from `𝒪[K]` to the valuation ring of the adic valuation of the maximal ideal of `𝒪[L]`
is the map `K → L` on elements. -/
@[simp]
theorem coe_algebraMap_valuationSubringMaximalPrime (r : 𝒪[K]) :
    ((algebraMap 𝒪[K] ((maximalPrime L).valuation L).valuationSubring r :
      ((maximalPrime L).valuation L).valuationSubring) : L) = algebraMap K L r :=
  (rfl)

instance isScalarTower_valuationSubringMaximalPrime :
    IsScalarTower 𝒪[K] ((maximalPrime L).valuation L).valuationSubring L :=
  .of_algebraMap_eq fun r ↦ (coe_algebraMap_valuationSubringMaximalPrime r).symm

/-- The map from `𝒪[K]` to the valuation ring of the adic valuation of the maximal ideal of `𝒪[L]`
is local. -/
instance isLocalHom_algebraMap_valuationSubringMaximalPrime :
    IsLocalHom (algebraMap 𝒪[K] ((maximalPrime L).valuation L).valuationSubring) :=
  ⟨fun r hr ↦ by
    by_contra hr'
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one] at hr'
    rw [(Valuation.valuationSubring.integers _).isUnit_iff_valuation_eq_one] at hr
    have h₁ : valuation L (algebraMap K L r) < 1 :=
      (Valuation.HasExtension.val_map_lt_one_iff (vR := valuation K) (vA := valuation L) _).mpr hr'
    exact ((isEquiv_valuation_maximalPrime L).lt_one_iff_lt_one.mpr h₁).ne hr⟩

/-- An integer nonzero in the residue field of `K` is a unit of `𝒪[L]`, so it lies outside the
maximal ideal of `𝒪[L]` (`TauCeti.valuation_natCast_eq_one_of_residueField_natCast_ne_zero`, read
in `𝒪[L]`). -/
theorem natCast_notMem_maximalPrime {n : ℕ} (hn : (n : 𝓀[K]) ≠ 0) :
    (n : (valuation L).valuationSubring) ∉ (maximalPrime L).asIdeal := fun h ↦
  ((Valuation.mem_maximalIdeal_iff (v := valuation L)).mp h).ne
    (by simpa using valuation_natCast_eq_one_of_residueField_natCast_ne_zero (L := L) hn)

end TauCeti

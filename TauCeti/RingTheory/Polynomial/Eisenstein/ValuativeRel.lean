/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.RingTheory.Valuation.Integral
import TauCeti.RingTheory.IntegralClosure.IsIntegral.Basic
import TauCeti.RingTheory.Polynomial.Eisenstein.Basic
import TauCeti.RingTheory.Polynomial.Eisenstein.LocalRing
import TauCeti.RingTheory.Polynomial.Eisenstein.Minpoly
import TauCeti.RingTheory.Valuation.ValuativeRel.Extension

/-!
# Roots of Eisenstein polynomials over valued fields

Let `K` be a valued field (`ValuativeRel K`) with valuation ring `𝒪ᵥ[K]` and maximal ideal
`𝓂ᵥ[K]`, and let `φ ∈ 𝒪ᵥ[K][X]` be an Eisenstein polynomial at `𝓂ᵥ[K]`. This file records the
general algebraic and valuation-theoretic properties of a root `α` of `φ` in a `K`-algebra `L`,
without any topology, completeness, or local-field hypotheses.

## Main results

* `Polynomial.IsEisensteinAt.ne_zero_of_isRoot`: any root `α : L` of `φ` in a nontrivial
  `K`-algebra is nonzero.
* `Polynomial.IsEisensteinAt.isIntegral_of_isRoot`: any root `α : L` of `φ` in a `K`-algebra is
  integral over `K`.
* `Polynomial.IsEisensteinAt.map_eq_C_leadingCoeff_mul_minpoly`: over `K`, `φ` mapped to `K[X]`
  equals `C (φ.leadingCoeff : K) * minpoly K α` for any root `α` in a domain `K`-algebra `L`.
* `Polynomial.IsEisensteinAt.mem_integer_of_isRoot`: in a `ValuativeExtension K L` of valued
  fields, any root `α : L` of `φ` lies in `𝒪ᵥ[L]`.
-/

public section

open ValuativeRel IsLocalRing TauCeti

namespace Polynomial.IsEisensteinAt

local notation "𝒪ᵥ[" K "]" => Valuation.integer (valuation K)
local notation "𝓂ᵥ[" K "]" => IsLocalRing.maximalIdeal 𝒪ᵥ[K]

section FieldRoots

variable {K L : Type*} [Field K] [ValuativeRel K]

/-- Any root `α : L` of an Eisenstein polynomial `φ : 𝒪ᵥ[K][X]` in a nontrivial `K`-algebra is
nonzero. -/
theorem ne_zero_of_isRoot [Semiring L] [Nontrivial L] [Algebra K L]
    {φ : 𝒪ᵥ[K][X]} (hφ : φ.IsEisensteinAt 𝓂ᵥ[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪ᵥ[K] K))).IsRoot α) :
    α ≠ 0 :=
  hφ.ne_zero_of_isRoot_map ((algebraMap K L).injective.comp Subtype.val_injective) hroot

/-- Any root `α : L` of an Eisenstein polynomial `φ : 𝒪ᵥ[K][X]` in a `K`-algebra is integral over
`K`. -/
theorem isIntegral_of_isRoot [Ring L] [Algebra K L]
    {φ : 𝒪ᵥ[K][X]} (hφ : φ.IsEisensteinAt 𝓂ᵥ[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪ᵥ[K] K))).IsRoot α) :
    IsIntegral K α := by
  have hlc : IsUnit (φ.map (algebraMap 𝒪ᵥ[K] K)).leadingCoeff := by
    rw [leadingCoeff_map_of_injective Subtype.val_injective]
    exact hφ.isUnit_leadingCoeff.map (algebraMap 𝒪ᵥ[K] K)
  exact IsIntegral.of_isUnit_leadingCoeff hlc (by
    rw [aeval_def, eval₂_eq_eval_map, Polynomial.map_map]
    exact hroot.eq_zero)

/-- Over `K`, an Eisenstein polynomial `φ : 𝒪ᵥ[K][X]` equals `C (φ.leadingCoeff : K) * minpoly K α`
for any root `α` in a domain `K`-algebra `L`. -/
theorem map_eq_C_leadingCoeff_mul_minpoly [CommRing L] [IsDomain L] [Algebra K L]
    {φ : 𝒪ᵥ[K][X]} (hφ : φ.IsEisensteinAt 𝓂ᵥ[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪ᵥ[K] K))).IsRoot α) :
    φ.map (algebraMap 𝒪ᵥ[K] K) = C (φ.leadingCoeff : K) * minpoly K α := by
  rw [← IsScalarTower.algebraMap_eq 𝒪ᵥ[K] K L] at hroot
  have hInt : IsIntegral 𝒪ᵥ[K] α :=
    hφ.isIntegral (by rw [aeval_def, eval₂_eq_eval_map]; exact hroot.eq_zero)
  have hscale := congrArg (Polynomial.map (algebraMap 𝒪ᵥ[K] K))
    (hφ.eq_C_leadingCoeff_mul_minpoly hφ.isUnit_leadingCoeff hroot)
  rw [Polynomial.map_mul, Polynomial.map_C,
    ← minpoly.isIntegrallyClosed_eq_field_fractions' K hInt,
    Algebra.algebraMap_ofSubsemiring_apply] at hscale
  exact hscale

end FieldRoots

section ValuativeExtensionRoots

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

/-- Any root `α : L` of an Eisenstein polynomial `φ : 𝒪ᵥ[K][X]` lies in `𝒪ᵥ[L]`. -/
theorem mem_integer_of_isRoot {φ : 𝒪ᵥ[K][X]} (hφ : φ.IsEisensteinAt 𝓂ᵥ[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪ᵥ[K] K))).IsRoot α) :
    α ∈ 𝒪ᵥ[L] :=
  mem_integer_of_isUnit_leadingCoeff_of_isRoot hφ.isUnit_leadingCoeff hroot

end ValuativeExtensionRoots

end Polynomial.IsEisensteinAt

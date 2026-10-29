/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.RamificationIndex
public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified

import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic
import TauCeti.NumberTheory.LocalField.IntegerRing.Basic

/-!
# Comparing tame ramification for local fields and discrete valuation rings

For an extension `L/K` of nonarchimedean local fields with compatible valuations, tameness
with respect to the discrete valuation ring `𝒪[K]` agrees with valuation-theoretic tameness.
The integral closure of `𝒪[K]` in `L` is the local ring `𝒪[L]`, and the residue fields are
finite, so the residue separability condition in the DVR definition is automatic.

The comparison uses `TauCeti.integerRingEquivIntegralClosure` and
`TauCeti.ramificationIndex_eq_ramificationIdx` to identify the rings and their ramification
indices. It permits results about either notion of tame ramification to be applied to the other.

## References

* [Stacks Project, Definition 15.113.7](https://stacks.math.columbia.edu/tag/09E9).
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter I, §4.
-/

public section

open ValuativeRel IsLocalRing

namespace TauCeti

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- For compatible extensions of nonarchimedean local fields, tameness with respect to the
valuation ring is equivalent to valuation-theoretic tameness. No separability hypothesis on
`L/K` is needed: the residue extension is separable because both residue fields are finite. -/
theorem isTamelyRamifiedWRT_iff_isTamelyRamified :
    Algebra.IsTamelyRamifiedWRT 𝒪[K] L ↔ IsTamelyRamified K L := by
  have := finite_of_valuativeExtension K L
  let e := integerRingEquivIntegralClosure K L
  let B := integralClosure 𝒪[K] L
  have : IsLocalRing B := e.isLocalRing
  have : IsDiscreteValuationRing B :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have : Finite (ResidueField B) :=
    Finite.of_equiv 𝓀[L] (ResidueField.mapEquiv e.toRingEquiv).toEquiv
  have : (maximalIdeal B).LiesOver 𝓂[K] :=
    ⟨(IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under 𝒪[K] (maximalIdeal B))).symm⟩
  have hidx : (maximalIdeal B).ramificationIdx 𝒪[K] = ramificationIndex K L := by
    rw [ramificationIndex_eq_ramificationIdx,
      ← Ideal.ramificationIdx'_eq_ramificationIdx 𝓂[K] (maximalIdeal B)
        (IsDiscreteValuationRing.not_a_field 𝒪[K]),
      ← Ideal.ramificationIdx'_eq_ramificationIdx 𝓂[K] 𝓂[L]
        (IsDiscreteValuationRing.not_a_field 𝒪[K])]
    have hcomap : (maximalIdeal B).comap e = 𝓂[L] :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.comap_isMaximal_of_surjective e e.surjective)
    simpa only [hcomap] using
      (𝓂[K].ramificationIdx'_comap_eq e (maximalIdeal B)).symm
  have htame : IsTamelyRamified K L ↔
      IsUnit ((maximalIdeal B).ramificationIdx 𝒪[K] : 𝓀[K]) := by
    rw [hidx, isTamelyRamified_iff_natCast_ne_zero, isUnit_iff_ne_zero]
  rw [Algebra.isTamelyRamifiedWRT_def]
  constructor
  · intro h
    exact htame.mpr (h (maximalIdeal B)).2
  · intro h P _ _
    have hP : P = maximalIdeal B := IsLocalRing.eq_maximalIdeal inferInstance
    subst P
    -- The DVR predicate uses literal quotients rather than the `ResidueField` wrapper.
    -- Supply their field structures and finiteness explicitly for the separability instance.
    let := Ideal.Quotient.field 𝓂[K]
    let := Ideal.Quotient.field (maximalIdeal B)
    have : Finite (B ⧸ maximalIdeal B) := inferInstanceAs (Finite (ResidueField B))
    have : Module.Finite (𝒪[K] ⧸ 𝓂[K]) (B ⧸ maximalIdeal B) := .of_finite
    have : Algebra.IsAlgebraic (𝒪[K] ⧸ 𝓂[K]) (B ⧸ maximalIdeal B) := .of_finite _ _
    have : Finite (𝒪[K] ⧸ 𝓂[K]) := inferInstanceAs (Finite 𝓀[K])
    exact ⟨Algebra.IsAlgebraic.isSeparable_of_perfectField, htame.mp h⟩

end TauCeti

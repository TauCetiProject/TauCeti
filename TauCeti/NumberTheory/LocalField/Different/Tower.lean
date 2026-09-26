/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Different.Basic
public import TauCeti.RingTheory.DedekindDomain.Different.Tower
import TauCeti.RingTheory.Valuation.ValuativeRel.Extension

/-!
# Different exponents in towers of local fields

For a finite separable tower `M/L/K`, the different exponent of `M/K` is the
sum of the different exponent of `M/L` and the different exponent of `L/K`
multiplied by the ramification index of `M/L`. This is the local form of
transitivity of different ideals. The formula computes the exponent of a
composite extension from its exponents over an intermediate local field.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §4.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing IsDedekindDomain

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti

variable (K L M : Type*)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension K L] [ValuativeExtension L M]
  [Algebra.IsSeparable K M]

/-- In a tower of finite separable extensions of nonarchimedean local fields,
`d(M/K) = d(M/L) + e(M/L) d(L/K)`. -/
theorem differentExponent_tower :
    letI : ValuativeExtension K M := ValuativeExtension.trans K L M
    differentExponent K M = differentExponent L M +
      ramificationIndex L M * differentExponent K L := by
  let _ : ValuativeExtension K M := ValuativeExtension.trans K L M
  let _ : IsScalarTower 𝒪[K] 𝒪[L] 𝒪[M] :=
    IsScalarTower.of_algebraMap_eq fun x ↦ Subtype.ext (by
      simp only [coe_algebraMap_integerRing]
      exact (IsScalarTower.algebraMap_apply K L M (x : K)))
  let _ : Module.Finite 𝒪[K] 𝒪[L] := integerRingModuleFinite K L
  let _ : Module.Finite 𝒪[L] 𝒪[M] := integerRingModuleFinite L M
  let _ : Algebra.IsSeparable K L :=
    Algebra.isSeparable_tower_bot_of_isSeparable K L M
  let _ : Algebra.IsSeparable L M :=
    Algebra.isSeparable_tower_top_of_isSeparable K L M
  let _ : Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing 𝒪[M]) :=
    isSeparable_fractionRing_integerRing K M
  let _ : (IsDiscreteValuationRing.maximalIdeal 𝒪[M]).asIdeal.LiesOver
      (IsDiscreteValuationRing.maximalIdeal 𝒪[L]).asIdeal := by
    -- These DVR ideals are definitionally the local-ring maximal ideals, for which
    -- the `LiesOver` instance is available.
    change (𝓂[M]).LiesOver 𝓂[L]
    infer_instance
  rw [differentExponent_def, differentExponent_def, differentExponent_def,
    ramificationIndex_eq_ramificationIdx]
  exact multiplicity_differentIdeal_tower 𝒪[K]
    (IsDiscreteValuationRing.maximalIdeal 𝒪[L])
    (IsDiscreteValuationRing.maximalIdeal 𝒪[M])

end TauCeti

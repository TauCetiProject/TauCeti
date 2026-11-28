/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.FieldTheory.Separable
public import TauCeti.RingTheory.Valuation.LocalizationAtCenter
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic
import TauCeti.RingTheory.Localization.AsSubring

/-!
# Localizations of integral closures of Dedekind domains are valuation rings

The localization of a Dedekind domain at a prime is a local Dedekind domain, hence a principal
ideal domain and so a valuation ring, as Mathlib's instances record. This passes to the integral
closure `B` of a Dedekind domain `R` in a separable algebraic extension `L` of its fraction field
`K`, which need not be finite and whose integral closure need not be Noetherian, for instance the
ring of all algebraic integers in an algebraic closure of `ℚ`: every localization of `B` at a
prime is a valuation ring (`IsIntegralClosure.preValuationRing_atPrime`), that is, `B` is a
Prüfer domain.

The proof is the directed union over finite subextensions. An element `x ∈ L` lies in the finite
separable extension `F = K(x)`, whose integral closure `C` of `R` is a Dedekind domain mapping to
`B`. The localization of `C` at the prime `P ∩ C` is a valuation ring of `F`, so `x` or `x⁻¹` is a
fraction `a / s` with `a, s ∈ C` and `s ∉ P`; read in `L`, this places `x` or `x⁻¹` in `B_P`.

With `TauCeti/RingTheory/Valuation/LocalizationAtCenter.lean` this says that the valuation
subrings of `L` containing `B` correspond to the primes of `B`, compatibly with Galois actions,
decomposition and inertia groups, and Frobenius elements.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_asIdeal`: at a nonzero prime, the
  localization as a valuation subring is Mathlib's
  `IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime`.
* `IsIntegralClosure.preValuationRing_atPrime`: the localizations at primes of the integral
  closure of a Dedekind domain in a separable algebraic extension of its fraction field are
  valuation rings.

## References

* [N. Bourbaki, *Commutative Algebra*], Chapter VII, §2, and Chapter VI, §8, no. 5 for integral
  closures in algebraic extensions and their localizations.
* [The Stacks Project](https://stacks.math.columbia.edu/tag/0307), Tag 0307, integral closure and
  localization.
-/

public section

open scoped nonZeroDivisors

/-- At a nonzero prime `v` of a Dedekind domain `C` with fraction field `L`, the localization at
`v.asIdeal` realized inside `L` is Mathlib's `HeightOneSpectrum.valuationSubringAtPrime`. So the
`Ideal.valuationSubringAtPrime` and `ValuationSubring.IsCenteredAt` API applies to it. -/
theorem IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_asIdeal {C L : Type*}
    [CommRing C] [IsDedekindDomain C] [Field L] [Algebra C L] [IsFractionRing C L]
    (v : HeightOneSpectrum C) :
    v.asIdeal.valuationSubringAtPrime L =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L v := by
  ext x
  rw [Ideal.mem_valuationSubringAtPrime_iff,
    IsDedekindDomain.HeightOneSpectrum.mem_valuationSubringAtPrime_iff]
  simp only [Ideal.mem_primeCompl_iff]

namespace IsIntegralClosure

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (L : Type*) [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
  [Algebra.IsSeparable K L] {B : Type*} [CommRing B] [Algebra R B] [Algebra B L]
  [IsScalarTower R B L] [IsIntegralClosure B R L]

include R K L in
/-- **The integral closure of a Dedekind domain in a separable algebraic extension is a Prüfer
domain**: if `R` is a Dedekind domain with fraction field `K` and `B` is the integral closure of
`R` in a separable algebraic, possibly infinite, extension `L` of `K`, then the localization of
`B` at every prime is a valuation ring. -/
theorem preValuationRing_atPrime (P : Ideal B) [P.IsPrime] :
    PreValuationRing (Localization.AtPrime P) := by
  have : Algebra.IsAlgebraic R L :=
    (IsFractionRing.comap_isAlgebraic_iff (K := K)).mpr inferInstance
  have : IsDomain B := (algebraMap_injective B R L).isDomain _
  have : IsFractionRing B L := isFractionRing_of_algebraic R B fun r hr ↦
    IsFractionRing.to_map_eq_zero_iff.mp
      ((map_eq_zero (algebraMap K L)).mp ((IsScalarTower.algebraMap_apply R K L r).symm.trans hr))
  rw [P.preValuationRing_atPrime_iff L]
  intro x
  -- `x` lies in the finite separable subextension `F = K(x)`
  let F := IntermediateField.adjoin K {x}
  have : FiniteDimensional K F :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsSeparable.isIntegral K x)
  have : Algebra.IsSeparable K F := Algebra.isSeparable_tower_bot_of_isSeparable K F L
  -- the integral closure `C` of `R` in `F` is a Dedekind domain, with a map `φ : C → B`
  let C := integralClosure R F
  have : IsDedekindDomain C := integralClosure.isDedekindDomain R K F
  have : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension R K F C
  let φ : C →ₐ[R] B := (IsIntegralClosure.equiv R (integralClosure R L) L B).toAlgHom.comp
    (F.val.restrictScalars R).mapIntegralClosure
  have hφ (c : C) : algebraMap B L (φ c) = ((c : F) : L) := by
    simp only [φ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, IsIntegralClosure.algebraMap_equiv]
    exact AlgHom.coe_mapIntegralClosure (F.val.restrictScalars R) c
  let P' := P.comap φ
  -- a fraction of `C` with denominator outside `P ∩ C` is a fraction of `B` outside `P`
  have htrans (y : F) (hy : y ∈ Localization.subalgebra.ofField F P'.primeCompl
      (P'.primeCompl_le_nonZeroDivisors_of_isFractionRing F)) :
      (y : L) ∈ Localization.subalgebra.ofField L P.primeCompl
        (P.primeCompl_le_nonZeroDivisors_of_isFractionRing L) := by
    obtain ⟨a, s, hs, rfl⟩ := (Localization.subalgebra.mem_ofField_iff _ _).mp hy
    refine (Localization.subalgebra.mem_ofField_iff _ _).mpr ⟨φ a, φ s,
      Ideal.mem_primeCompl_iff.mpr (Ideal.mem_comap.not.mp (Ideal.mem_primeCompl_iff.mp hs)), ?_⟩
    rw [hφ, hφ, IntermediateField.coe_mul, IntermediateField.coe_inv, Subalgebra.algebraMap_apply,
      Subalgebra.algebraMap_apply]
  exact ((P'.preValuationRing_atPrime_iff F).mp inferInstance
    ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩).imp (htrans _) (htrans _)

end IsIntegralClosure

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.RamificationIndex
public import TauCeti.NumberTheory.LocalField.Unramified
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeExtension

/-!
# The local ramification index of a completion is the global one

Let `R ⊆ B` be Dedekind domains with fraction fields `K ⊆ L`, and let `w` be a height-one prime
of `B` lying over the height-one prime `v` of `R`, both with finite residue fields. The
completions `K_v` and `L_w` are nonarchimedean local fields, and the canonical continuous map
`K_v → L_w` makes `L_w` a valuative extension of `K_v` in the `AdicCompletionExtension` scope.
This file proves that the ramification index of that extension of local fields is the
ramification index of `w` over `R`:

`IsDedekindDomain.HeightOneSpectrum.ramificationIndex_adicCompletion v w` identifies
`TauCeti.ramificationIndex K_v L_w` with `w.asIdeal.ramificationIdx R`.

So the local invariant, defined through the normalized valuations of `K_v` and `L_w` alone, is the
global one, defined as a length of a localization of `B`. In particular a place unramified over
the base completes to an unramified extension of local fields.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.normalizedValuationWithZero_adicCompletion`: the
  zero-preserving normalized valuation of `K_v` is the inverse of its adic valuation `Valued.v`.
* `IsDedekindDomain.HeightOneSpectrum.ramificationIndex_adicCompletion`: the ramification index
  of `L_w / K_v` is `w.asIdeal.ramificationIdx R`.
* `IsDedekindDomain.HeightOneSpectrum.isUnramified_adicCompletion_of_isUnramifiedAt`:
  unramifiedness of `w` over `R` gives unramifiedness of `L_w / K_v`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §8.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped AdicCompletionExtension

namespace IsDedekindDomain.HeightOneSpectrum

section Completion

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)]

/-- The zero-preserving normalized valuation of the completion `K_v` is the inverse of its adic
valuation `Valued.v`. -/
@[simp]
theorem normalizedValuationWithZero_adicCompletion (x : v.adicCompletion K) :
    TauCeti.normalizedValuationWithZero (v.adicCompletion K) x = (Valued.v x)⁻¹ :=
  Valuation.normalizedValuationWithZero_eq_inv_of_surjective _
    (v.valuedAdicCompletion_surjective K) x

end Completion

section Extension

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]
  [Finite (R ⧸ v.asIdeal)] [Finite (B ⧸ w.asIdeal)]

private theorem normalizedValuationWithZero_adicCompletion_algebraMap
    (x : v.adicCompletion K) :
    TauCeti.normalizedValuationWithZero (w.adicCompletion L)
        (algebraMap (v.adicCompletion K) (w.adicCompletion L) x) =
      TauCeti.normalizedValuationWithZero (v.adicCompletion K) x ^
        v.asIdeal.ramificationIdx' w.asIdeal := by
  rw [normalizedValuationWithZero_adicCompletion,
    normalizedValuationWithZero_adicCompletion, algebraMap_adicCompletionExtensionAlgebra,
    valued_adicCompletionExtension, inv_pow]

/-- **The local ramification index is the global one.** For `w` a height-one prime of `B` over the
height-one prime `v` of `R`, with finite residue fields, the ramification index of the extension
of local fields `L_w / K_v`, for the canonical algebra structure of `adicCompletionExtension`, is
the ramification index of `w` over `R`. -/
@[simp]
theorem ramificationIndex_adicCompletion :
    TauCeti.ramificationIndex (v.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.ramificationIdx R := by
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
  refine TauCeti.ramificationIndex_eq_iff.2 fun x ↦ WithZero.coe_injective ?_
  simpa only [WithZero.coe_pow, ← TauCeti.normalizedValuationWithZero_coe,
    Units.coe_map, MonoidHom.coe_coe] using
      normalizedValuationWithZero_adicCompletion_algebraMap v w (x : v.adicCompletion K)

/-- **An unramified place gives an unramified completed extension.** If `w` is unramified over
`R`, the extension of local fields `L_w / K_v` is unramified. -/
theorem isUnramified_adicCompletion_of_isUnramifiedAt [Algebra.EssFiniteType R B]
    [Algebra.IsUnramifiedAt R w.asIdeal] :
    TauCeti.IsUnramified (v.adicCompletion K) (w.adicCompletion L) := by
  rw [TauCeti.isUnramified_iff_ramificationIndex_eq_one, ramificationIndex_adicCompletion v w,
    Ideal.ramificationIdx_eq_one w.asIdeal R]

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.isUnramified_adicCompletion_of_isUnramifiedAt

end Extension

end IsDedekindDomain.HeightOneSpectrum

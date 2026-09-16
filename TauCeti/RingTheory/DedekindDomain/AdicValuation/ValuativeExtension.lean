/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# The completion of an extension of Dedekind domains is a valuative extension

Let `R ⊆ B` be Dedekind domains with fraction fields `K ⊆ L`, and let `w` be a height-one prime
of `B` lying over the height-one prime `v` of `R`. The completions `K_v` and `L_w` carry the
valuative relations induced by their adic valuations, and the canonical continuous extension
`adicCompletionExtension : K_v →+* L_w` of `K → L` makes `L_w` a `K_v`-algebra in the
`AdicCompletionExtension` scope.

This file proves that this canonical map reflects and preserves the valuative relations, so
that `L_w` is a `ValuativeExtension` of `K_v`. Local statements about valuative extensions can
then be applied to the completion of a global extension through this canonical structure, rather
than through an arbitrary compatible algebra or valuative relation.

The proof rests on `valued_adicCompletionExtension`: along the extension the valuation of `L_w`
is the valuation of `K_v` raised to the ramification index, which is nonzero, and raising to a
nonzero power is strictly monotone in `ℤᵐ⁰`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionExtension_vle_iff_vle`: the canonical map
  `K_v → L_w` preserves and reflects the valuative relations.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionExtensionValuativeExtension`: the resulting
  `ValuativeExtension K_v L_w` instance, in the `AdicCompletionExtension` scope.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §4 and §6.
-/

public section
noncomputable section

open ValuativeRel
open scoped AdicCompletionExtension WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

variable (K L) in
/-- The canonical map `K_v → L_w` preserves and reflects the valuative relations induced by the
adic valuations. -/
theorem adicCompletionExtension_vle_iff_vle (a b : v.adicCompletion K) :
    adicCompletionExtension K L v w a ≤ᵥ adicCompletionExtension K L v w b ↔ a ≤ᵥ b := by
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  rw [Valuation.vle_iff_le (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰),
    Valuation.vle_iff_le (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰),
    valued_adicCompletionExtension, valued_adicCompletionExtension]
  exact pow_le_pow_iff_left₀ zero_le zero_le
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot)

/-- The completion `L_w` of `L` above `v` is a valuative extension of `K_v`, for the canonical
algebra structure given by `adicCompletionExtension`. -/
theorem adicCompletionExtensionValuativeExtension :
    ValuativeExtension (v.adicCompletion K) (w.adicCompletion L) where
  vle_iff_vle a b := by
    rw [algebraMap_adicCompletionExtensionAlgebra]
    exact adicCompletionExtension_vle_iff_vle K L v w a b

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.adicCompletionExtensionValuativeExtension

end IsDedekindDomain.HeightOneSpectrum

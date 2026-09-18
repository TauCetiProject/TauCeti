/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.FiniteExtension
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.IntegersExtension
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeExtension

/-!
# The completed integer ring of an extension is an integral closure

Let `R ⊆ B` be Dedekind domains with fraction fields `K ⊆ L`, and let `w` be a height-one prime
of `B` lying over the height-one prime `v` of `R`. Suppose that the residue field `R ⧸ v` is
finite, so that `K_v` is a nonarchimedean local field, and that `L_w` is finite-dimensional over
`K_v` for the canonical algebra structure of the `AdicCompletionExtension` scope. Both hold for
every finite place of an extension of number fields.

This file proves that the completed integer ring `𝒪_w` is the integral closure of `𝒪_v` in `L_w`,
and that, when `L_w / K_v` is separable, `𝒪_w` is a finite `𝒪_v`-module. The valuation of `L_w` is
the unique extension of that of `K_v`, so an element of `L_w` is integral over `𝒪_v` exactly when
its valuation is at most `1` (`TauCeti.isIntegral_iff_valuation_le_one`). Together with the
algebra structure, scalar tower and torsion-freeness of `IntegersExtension.lean`, these are the
hypotheses under which Mathlib's theory of the different ideal and of `conductor_mul_differentIdeal`
applies to the local extension `𝒪_w / 𝒪_v`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers_isIntegralClosure`: `𝒪_w` is the
  integral closure of `𝒪_v` in `L_w`, a scoped instance.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers_moduleFinite`: `𝒪_w` is a finite
  `𝒪_v`-module when `L_w / K_v` is separable, a scoped instance.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §4 and §6.
-/

public section
noncomputable section

open IsDedekindDomain
open scoped AdicCompletionExtension

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]
  [Finite (R ⧸ v.asIdeal)] [FiniteDimensional (v.adicCompletion K) (w.adicCompletion L)]

variable (K L)

/-- The completed integer ring `𝒪_w` is the integral closure of `𝒪_v` in `L_w`. -/
theorem adicCompletionIntegers_isIntegralClosure :
    IsIntegralClosure (w.adicCompletionIntegers L) (v.adicCompletionIntegers K)
      (w.adicCompletion L) where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := by
    rw [TauCeti.isIntegral_iff_valuation_le_one (integers_adicCompletionIntegers v) x,
      ← Valuation.mem_integer_iff, integer_eq_adicCompletionIntegers,
      ValuationSubring.mem_toSubring]
    exact ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.2⟩

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers_isIntegralClosure

/-- The completed integer ring `𝒪_w` is a finite `𝒪_v`-module when `L_w / K_v` is separable. -/
theorem adicCompletionIntegers_moduleFinite
    [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] :
    Module.Finite (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  IsIntegralClosure.finite (v.adicCompletionIntegers K) (v.adicCompletion K) (w.adicCompletion L)
    (w.adicCompletionIntegers L)

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers_moduleFinite

end IsDedekindDomain.HeightOneSpectrum

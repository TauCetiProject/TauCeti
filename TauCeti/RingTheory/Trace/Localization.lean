/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.NormTrace
public import TauCeti.RingTheory.Localization.FiniteFree

/-!
# Vanishing of algebra traces and localization

For a finite free algebra, the trace vanishes exactly when it vanishes after localization at
non-zero-divisors of the base. Consequently, a finite free extension of domains with separable
fraction fields has nonzero trace. Neither domain needs to be integrally closed.

Nonzero trace is an input to injectivity of the differential trace pairing for finite maps of
smooth curves. The localization step uses the native finite-free total-fraction-ring criterion.

## Main results

* `Algebra.trace_eq_zero_iff_of_isLocalization`: trace vanishing can be tested after localization.
* `Algebra.trace_ne_zero_of_isSeparable_fractionRing`: separable fraction fields give nonzero trace.
-/

public section

namespace Algebra

open scoped nonZeroDivisors

/-- The trace of a finite free algebra vanishes if and only if it vanishes after localization
at a submonoid of non-zero-divisors of the base. -/
theorem trace_eq_zero_iff_of_isLocalization (R S Rₘ Sₘ : Type*) [CommRing R] [CommRing S]
    [CommRing Rₘ] [CommRing Sₘ] [Algebra R S] [Module.Free R S] [Module.Finite R S]
    [Algebra R Rₘ] [Algebra S Sₘ] [Algebra Rₘ Sₘ] [Algebra R Sₘ]
    [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
    (M : Submonoid R) [IsLocalization M Rₘ]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ] (hM : M ≤ R⁰) :
    trace Rₘ Sₘ = 0 ↔ trace R S = 0 := by
  constructor
  · intro h
    ext b
    apply IsLocalization.injective Rₘ hM
    rw [← trace_localization R (Rₘ := Rₘ) (Sₘ := Sₘ) M b]
    simp only [h, LinearMap.zero_apply, map_zero]
  · intro h
    apply ((Module.Free.chooseBasis R S).localizationLocalization Rₘ M Sₘ).ext
    intro i
    simp only [Module.Basis.localizationLocalization_apply, LinearMap.zero_apply,
      trace_localization R (Rₘ := Rₘ) (Sₘ := Sₘ) M, h, map_zero]

/-- A finite free extension of domains with separable fraction fields has nonzero trace.
No normality assumption is needed. -/
theorem trace_ne_zero_of_isSeparable_fractionRing (R S K L : Type*)
    [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
    [Field K] [Field L] [Algebra R K] [Algebra S L] [IsFractionRing R K] [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]
    [Algebra.IsSeparable K L] : trace R S ≠ 0 := by
  have := (IsFractionRing.isLocalization_algebraMapSubmonoid_iff R L).mpr
    (inferInstance : IsFractionRing S L)
  have := Module.Finite.of_isLocalization R S (Rₚ := K) (Sₚ := L) (nonZeroDivisors R)
  exact fun h ↦ trace_ne_zero K L
    ((trace_eq_zero_iff_of_isLocalization R S K L (nonZeroDivisors R) le_rfl).mpr h)

end Algebra

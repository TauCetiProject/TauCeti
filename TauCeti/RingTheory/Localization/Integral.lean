/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Integral

/-!
# Integral closures of localizations

If `Rₘ` is a localization of `R` at a submonoid `M`, and `S`, `Sₘ` are integral closures of `R`,
`Rₘ` in the same field `L`, then `Sₘ` is the localization of `S` at the image of `M`.

Mathlib's `IsLocalization.integralClosure` states this for the literal subalgebra
`integralClosure R L`; the version here applies to arbitrary types satisfying
`IsIntegralClosure`.

## Main results

* `TauCeti.isLocalization_algebraMapSubmonoid_of_isIntegralClosure`: an integral closure of a
  localization is the corresponding localization of an integral closure.
-/

public section

namespace TauCeti

universe uR uRm uS uSm uL

variable {R : Type uR} {Rₘ : Type uRm} {S : Type uS} {Sₘ : Type uSm} {L : Type uL}
variable [CommRing R] [CommRing Rₘ] [CommRing S] [CommRing Sₘ] [Field L]
variable {M : Submonoid R}
variable [Algebra R Rₘ] [Algebra R S] [Algebra R Sₘ] [Algebra R L]
variable [Algebra Rₘ Sₘ] [Algebra Rₘ L] [Algebra S Sₘ] [Algebra S L] [Algebra Sₘ L]
variable [IsScalarTower R Rₘ Sₘ] [IsScalarTower R Rₘ L] [IsScalarTower R S Sₘ]
variable [IsScalarTower R S L] [IsScalarTower S Sₘ L]
variable [IsIntegralClosure S R L] [IsIntegralClosure Sₘ Rₘ L]
variable [IsLocalization M Rₘ]

include Rₘ L M in
/-- If `Rₘ` is a localization of `R`, then an integral closure of `Rₘ` in a field `L`
is the corresponding localization of an integral closure of `R` in `L`.

Unlike `IsLocalization.integralClosure`, this applies when the original integral closure is an
arbitrary type satisfying `IsIntegralClosure`, rather than the literal `integralClosure R L`. -/
theorem isLocalization_algebraMapSubmonoid_of_isIntegralClosure :
    IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ := by
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨_, m, hm, rfl⟩
    rw [← IsScalarTower.algebraMap_apply R S Sₘ,
      IsScalarTower.algebraMap_apply R Rₘ Sₘ]
    exact (IsLocalization.map_units Rₘ ⟨m, hm⟩).map (algebraMap Rₘ Sₘ)
  · intro y
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (R := R) (Rₘ := Rₘ) M (algebraMap Sₘ L y)
        ((IsIntegralClosure.isIntegral_iff (A := Sₘ) (R := Rₘ)).mpr ⟨y, rfl⟩)
    obtain ⟨s, hs⟩ := (IsIntegralClosure.isIntegral_iff (A := S) (R := R)).mp hm
    refine ⟨⟨s, algebraMap R S m, m, m.2, rfl⟩, ?_⟩
    apply IsIntegralClosure.algebraMap_injective Sₘ Rₘ L
    rw [map_mul, ← IsScalarTower.algebraMap_apply S Sₘ L,
      ← IsScalarTower.algebraMap_apply S Sₘ L,
      ← IsScalarTower.algebraMap_apply R S L, hs,
      Submonoid.smul_def, Algebra.smul_def, mul_comm]
  · intro x y hxy
    refine ⟨1, ?_⟩
    simp only [Submonoid.coe_one, one_mul]
    apply IsIntegralClosure.algebraMap_injective S R L
    have h := congrArg (algebraMap Sₘ L) hxy
    simpa only [IsScalarTower.algebraMap_apply S Sₘ L] using h

end TauCeti

end

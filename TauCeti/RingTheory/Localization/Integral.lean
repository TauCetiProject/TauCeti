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
`Rₘ` in the same commutative ring `L`, then `Sₘ` is the localization of `S` at the image of `M`.

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
variable [CommRing R] [CommRing Rₘ] [CommSemiring S] [CommSemiring Sₘ] [CommRing L]
variable {M : Submonoid R}
variable [Algebra R Rₘ] [Algebra R S] [Algebra R L]
variable [Algebra Rₘ L] [Algebra S Sₘ] [Algebra S L] [Algebra Sₘ L]
variable [IsScalarTower R Rₘ L] [IsScalarTower R S L] [IsScalarTower S Sₘ L]
variable [IsIntegralClosure S R L] [IsIntegralClosure Sₘ Rₘ L]
variable [IsLocalization M Rₘ]

include Rₘ L M in
/-- If `Rₘ` is a localization of `R`, then an integral closure of `Rₘ` in a commutative ring `L`
is the corresponding localization of an integral closure of `R` in `L`.
The maps `R → Rₘ → L`, `R → S → L`, and `S → Sₘ → L` must agree with the direct maps
to `L`.

Unlike `IsLocalization.integralClosure`, this applies when the original integral closure is an
arbitrary type satisfying `IsIntegralClosure`, rather than the literal `integralClosure R L`. -/
theorem isLocalization_algebraMapSubmonoid_of_isIntegralClosure :
    IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ := by
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨_, m, hm, rfl⟩
    -- The inverse in `Rₘ` maps to an integral element of `L`, hence lifts to `Sₘ`.
    obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp (IsLocalization.map_units Rₘ ⟨m, hm⟩)
    obtain ⟨s, hs⟩ := (IsIntegralClosure.isIntegral_iff (A := Sₘ) (R := Rₘ)).mp
      (isIntegral_algebraMap (A := L) (x := z))
    apply isUnit_iff_exists_inv.mpr
    refine ⟨s, IsIntegralClosure.algebraMap_injective Sₘ Rₘ L ?_⟩
    simpa only [map_mul, map_one, ← IsScalarTower.algebraMap_apply S Sₘ L,
      ← IsScalarTower.algebraMap_apply R S L, ← IsScalarTower.algebraMap_apply R Rₘ L, hs]
      using congrArg (algebraMap Rₘ L) hz
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

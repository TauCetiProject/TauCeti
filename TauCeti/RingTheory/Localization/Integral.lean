/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Integral

import Mathlib.RingTheory.Localization.Finiteness

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
* `TauCeti.finite_integralClosure_of_isLocalization`: finiteness of the integral closure passes
  to localizations.
* `TauCeti.finite_integralClosure_of_span_eq_top`: conversely, finiteness of the integral closure
  is local on `Spec R`: it holds as soon as it holds for the localizations `R_{f_i}` at elements
  `f_i` generating the unit ideal.
-/

public section

namespace TauCeti

universe uR uRm uS uSm uL

section IsIntegralClosure

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

end IsIntegralClosure

section IntegralClosureLocalization

variable {R : Type*} [CommRing R] (S L : Type*) [CommRing S] [Algebra R S] [CommRing L]
  [Algebra R L] [Algebra S L] [IsScalarTower R S L]

variable (R) in
/-- The integral closure of `S` in `L` as an algebra over the integral closure of `R` in `L`,
through the inclusion: an element of `L` integral over `R` is integral over `S`. -/
private abbrev integralClosureAlgebra : Algebra (integralClosure R L) (integralClosure S L) :=
  RingHom.toAlgebra
    { toFun x := ⟨x, x.2.tower_top⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }

/-- If `S` is a localization of `R` at `M`, then the integral closure of `S` in `L` is the
localization at `M` of the integral closure of `R` in `L`, as an algebra over it through the
inclusion. -/
private theorem isLocalization_integralClosure (M : Submonoid R) [IsLocalization M S] :
    letI := integralClosureAlgebra R S L
    IsScalarTower R (integralClosure R L) (integralClosure S L) ∧
      IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R L) M)
        (integralClosure S L) := by
  let := integralClosureAlgebra R S L
  have : IsScalarTower (integralClosure R L) (integralClosure S L) L :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R (integralClosure R L) (integralClosure S L) :=
    .of_algebraMap_eq fun _ ↦ Subtype.ext <| by simp [RingHom.algebraMap_toAlgebra]
  exact ⟨this, isLocalization_algebraMapSubmonoid_of_isIntegralClosure (M := M) (Rₘ := S)
    (L := L) (S := integralClosure R L) (Sₘ := integralClosure S L)⟩

end IntegralClosureLocalization

/-- If `S` is a localization of `R` at a submonoid `M` and the integral closure of `R` in an
`S`-algebra `L` is a finite `R`-module, then the integral closure of `S` in `L` is a finite
`S`-module: it is the localization at `M` of the integral closure of `R`. -/
theorem finite_integralClosure_of_isLocalization {R : Type*} [CommRing R] (M : Submonoid R)
    (S L : Type*) [CommRing S] [Algebra R S] [IsLocalization M S] [CommRing L] [Algebra R L]
    [Algebra S L] [IsScalarTower R S L] [Module.Finite R (integralClosure R L)] :
    Module.Finite S (integralClosure S L) := by
  let := integralClosureAlgebra R S L
  obtain ⟨_, _⟩ := isLocalization_integralClosure S L M
  exact .of_isLocalization R (integralClosure R L) M

/-- **Finiteness of the integral closure is local on `Spec R`.** Let `t` be a set of elements
generating the unit ideal of `R`, and for each `f ∈ t` let `R_f` be a localization of `R` away
from `f` with an `R`-compatible algebra structure on `L`. If the integral closure of each `R_f`
in `L` is a finite `R_f`-module, then the integral closure of `R` in `L` is a finite `R`-module.
This is the converse of `finite_integralClosure_of_isLocalization`. -/
theorem finite_integralClosure_of_span_eq_top {R : Type*} [CommRing R] (L : Type*) [CommRing L]
    [Algebra R L] {t : Set R} (ht : Ideal.span t = ⊤) {Rₚ : t → Type*}
    [∀ f, CommRing (Rₚ f)] [∀ f, Algebra R (Rₚ f)] [∀ f, IsLocalization.Away f.1 (Rₚ f)]
    [∀ f, Algebra (Rₚ f) L] [∀ f, IsScalarTower R (Rₚ f) L]
    (H : ∀ f, Module.Finite (Rₚ f) (integralClosure (Rₚ f) L)) :
    Module.Finite R (integralClosure R L) := by
  -- The integral closure of `R_f` in `L` is the localization of that of `R` away from `f`.
  let (f : t) := integralClosureAlgebra R (Rₚ f) L
  have (f : t) := (isLocalization_integralClosure (Rₚ f) L (.powers f.1)).1
  have (f : t) := (isLocalization_integralClosure (Rₚ f) L (.powers f.1)).2
  exact Module.Finite.of_localizationSpan' t ht
    (fun f ↦ (IsScalarTower.toAlgHom R _ (integralClosure (Rₚ f) L)).toLinearMap) H

end TauCeti

end

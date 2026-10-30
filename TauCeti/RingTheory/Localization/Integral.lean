/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
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
* `TauCeti.integralClosureMapAlgebra`: the integral closure of `Rf` in `Sf` as an algebra over the
  integral closure of `R` in `S`, with its scalar-tower lemmas
  `isScalarTower_integralClosureMapAlgebra_left` and
  `isScalarTower_integralClosureMapAlgebra_right`; this is the structure Mathlib's
  `IsLocalization.integralClosure` asks its caller to supply.
* `TauCeti.IsLocalization.isIntegrallyClosedIn`: if `R` is integrally closed in `S`, then `M⁻¹R` is
  integrally closed in `M⁻¹S`. Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0),
  `lean/Pcf/Stacks/Common/EtaleNormal.lean`, where it is
  `Pcf.Stacks.isIntegrallyClosedIn_of_isLocalization`.
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

/-- The integral closure of `Rf` in `Sf` as an algebra over the integral closure of `R` in `S`,
where `Rf` and `Sf` are `R`- and `S`-algebras with `Rf → Sf` compatible: an element of `S` integral
over `R` maps to an element of `Sf` integral over `Rf`. -/
abbrev integralClosureMapAlgebra (R S Rf Sf : Type*) [CommRing R] [CommRing S]
    [CommRing Rf] [CommRing Sf] [Algebra R S] [Algebra R Rf] [Algebra S Sf] [Algebra Rf Sf]
    [Algebra R Sf] [IsScalarTower R S Sf] [IsScalarTower R Rf Sf] :
    Algebra (integralClosure R S) (integralClosure Rf Sf) :=
  RingHom.toAlgebra
    { toFun y := ⟨algebraMap S Sf y, (y.2.map (IsScalarTower.toAlgHom R S Sf)).tower_top⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' _ _ := Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' _ _ := Subtype.ext (map_add _ _ _) }

/-- The map `integralClosure R S → integralClosure Rf Sf` of `integralClosureMapAlgebra` is
compatible with the inclusion into `Sf`. -/
theorem isScalarTower_integralClosureMapAlgebra_right (R S Rf Sf : Type*) [CommRing R]
    [CommRing S] [CommRing Rf] [CommRing Sf] [Algebra R S] [Algebra R Rf] [Algebra S Sf]
    [Algebra Rf Sf] [Algebra R Sf] [IsScalarTower R S Sf] [IsScalarTower R Rf Sf] :
    letI := integralClosureMapAlgebra R S Rf Sf
    IsScalarTower (integralClosure R S) (integralClosure Rf Sf) Sf :=
  letI := integralClosureMapAlgebra R S Rf Sf
  .of_algebraMap_eq fun _ ↦ rfl

/-- The map `integralClosure R S → integralClosure Rf Sf` of `integralClosureMapAlgebra` is
compatible with the structure maps from `R`. -/
theorem isScalarTower_integralClosureMapAlgebra_left (R S Rf Sf : Type*) [CommRing R]
    [CommRing S] [CommRing Rf] [CommRing Sf] [Algebra R S] [Algebra R Rf] [Algebra S Sf]
    [Algebra Rf Sf] [Algebra R Sf] [IsScalarTower R S Sf] [IsScalarTower R Rf Sf] :
    letI := integralClosureMapAlgebra R S Rf Sf
    IsScalarTower R (integralClosure R S) (integralClosure Rf Sf) :=
  letI := integralClosureMapAlgebra R S Rf Sf
  .of_algebraMap_eq fun _ ↦ Subtype.ext <| by
    simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply]

/-- The structure map of `integralClosureMapAlgebra` is `algebraMap S Sf` on underlying
elements. -/
@[simp]
theorem coe_algebraMap_integralClosureMapAlgebra (R S Rf Sf : Type*) [CommRing R] [CommRing S]
    [CommRing Rf] [CommRing Sf] [Algebra R S] [Algebra R Rf] [Algebra S Sf] [Algebra Rf Sf]
    [Algebra R Sf] [IsScalarTower R S Sf] [IsScalarTower R Rf Sf] (y : integralClosure R S) :
    letI := integralClosureMapAlgebra R S Rf Sf
    ((algebraMap (integralClosure R S) (integralClosure Rf Sf) y : integralClosure Rf Sf) : Sf) =
      algebraMap S Sf y := rfl

/-- If `S` is a localization of `R` at `M`, then the integral closure of `S` in `L` is the
localization at `M` of the integral closure of `R` in `L`, as an algebra over it through the
inclusion. -/
private theorem isLocalization_integralClosure (M : Submonoid R) [IsLocalization M S] :
    letI := integralClosureMapAlgebra R L S L
    IsScalarTower R (integralClosure R L) (integralClosure S L) ∧
      IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R L) M)
        (integralClosure S L) := by
  let := integralClosureMapAlgebra R L S L
  have := isScalarTower_integralClosureMapAlgebra_right R L S L
  exact ⟨isScalarTower_integralClosureMapAlgebra_left R L S L,
    isLocalization_algebraMapSubmonoid_of_isIntegralClosure (M := M) (Rₘ := S) (L := L)
      (S := integralClosure R L) (Sₘ := integralClosure S L)⟩

end IntegralClosureLocalization

/-- If `S` is a localization of `R` at a submonoid `M` and the integral closure of `R` in an
`S`-algebra `L` is a finite `R`-module, then the integral closure of `S` in `L` is a finite
`S`-module: it is the localization at `M` of the integral closure of `R`. -/
theorem finite_integralClosure_of_isLocalization {R : Type*} [CommRing R] (M : Submonoid R)
    (S L : Type*) [CommRing S] [Algebra R S] [IsLocalization M S] [CommRing L] [Algebra R L]
    [Algebra S L] [IsScalarTower R S L] [Module.Finite R (integralClosure R L)] :
    Module.Finite S (integralClosure S L) := by
  let := integralClosureMapAlgebra R L S L
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
  let (f : t) := integralClosureMapAlgebra R L (Rₚ f) L
  have (f : t) := (isLocalization_integralClosure (Rₚ f) L (.powers f.1)).1
  have (f : t) := (isLocalization_integralClosure (Rₚ f) L (.powers f.1)).2
  exact Module.Finite.of_localizationSpan' t ht
    (fun f ↦ (IsScalarTower.toAlgHom R _ (integralClosure (Rₚ f) L)).toLinearMap) H

section IsIntegrallyClosedIn

variable {R S Rf Sf : Type*} [CommRing R] [CommRing S] [CommRing Rf] [CommRing Sf]
  [Algebra R S] [Algebra R Rf] [Algebra S Sf] [Algebra Rf Sf] [Algebra R Sf]
  [IsScalarTower R S Sf] [IsScalarTower R Rf Sf]

/-- Being integrally closed in an algebra is preserved by localizing both rings at the same
submonoid of the base: if `R` is integrally closed in `S`, then `M⁻¹R` is integrally closed in
`M⁻¹S`. It is not an instance: the submonoid `M` does not appear in the conclusion, so it
cannot be found by typeclass search. -/
theorem IsLocalization.isIntegrallyClosedIn (M : Submonoid R) [IsLocalization M Rf]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sf] [IsIntegrallyClosedIn R S] :
    IsIntegrallyClosedIn Rf Sf := by
  rw [isIntegrallyClosedIn_iff]
  refine ⟨?_, fun {x} hx ↦ ?_⟩
  · -- `Algebra.algebraMapSubmonoid S M` is defined as `M.map (algebraMap R S)`, the form that
    -- `IsLocalization.algebraMap_eq_map_map_submonoid` expects.
    have : IsLocalization (M.map (algebraMap R S)) Sf :=
      ‹IsLocalization (Algebra.algebraMapSubmonoid S M) Sf›
    rw [IsLocalization.algebraMap_eq_map_map_submonoid M S Rf Sf]
    exact IsLocalization.map_injective_of_injective (M := M) (g := algebraMap R S) Rf Sf
      (isIntegrallyClosedIn_iff.mp ‹IsIntegrallyClosedIn R S›).1
  · -- Use that `integralClosure Rf Sf` is the localization of `integralClosure R S` at `M`.
    let := integralClosureMapAlgebra R S Rf Sf
    have := isScalarTower_integralClosureMapAlgebra_right R S Rf Sf
    have := isScalarTower_integralClosureMapAlgebra_left R S Rf Sf
    have hloc := IsLocalization.integralClosure (R := R) (S := S) (Rf := Rf) (Sf := Sf) M
    obtain ⟨⟨⟨y, hy⟩, _, m, hm, rfl⟩, e⟩ := IsLocalization.surj
      (Algebra.algebraMapSubmonoid (integralClosure R S) M) (⟨x, hx⟩ : integralClosure Rf Sf)
    obtain ⟨r, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hy
    refine ⟨IsLocalization.mk' Rf r ⟨m, hm⟩, ?_⟩
    have e' := congrArg Subtype.val e
    have hu : IsUnit (algebraMap R Sf m) := by
      rw [IsScalarTower.algebraMap_apply R S Sf]
      exact IsLocalization.map_units Sf
        (⟨algebraMap R S m, Algebra.mem_algebraMapSubmonoid_of_mem (⟨m, hm⟩ : M)⟩ :
          Algebra.algebraMapSubmonoid S M)
    refine (hu.mul_left_inj).mp ?_
    have h1 := congrArg (algebraMap Rf Sf) (IsLocalization.mk'_spec Rf r (⟨m, hm⟩ : M))
    -- `e'`: `x * algebraMap R Sf m = algebraMap R Sf r`
    simp only [coe_algebraMap_integralClosureMapAlgebra, map_mul, ← IsScalarTower.algebraMap_apply]
      at h1 e'
    rw [h1]
    exact e'.symm

end IsIntegrallyClosedIn

end TauCeti

end

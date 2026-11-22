/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Defs
public import TauCeti.GroupTheory.MonoidLocalization.Basic
import Mathlib.Algebra.Algebra.Tower

/-!
# Basic facts about localizations of commutative semirings

For a localization `S` of a commutative semiring `R` at a submonoid `M`, a ring homomorphism
`g : R →+* P` that maps `M` into the units of `P` extends to `IsLocalization.lift hg : S →+* P`.
Complementing Mathlib's `IsLocalization.lift_injective_iff` and `IsLocalization.eq_of_eq`, this file
records that `IsLocalization.lift hg` is injective whenever `g` is injective
(`IsLocalization.lift_injective_of_injective`). Likewise, an injective ring homomorphism of
commutative rings that carries `M` into a submonoid of non-zero-divisors induces an injective map
of localizations (`IsLocalization.map_injective_of_injective_of_le_nonZeroDivisors`), with no
domain hypothesis; for instance, one carrying non-zero-divisors to non-zero-divisors induces an
injective map of total rings of fractions.

It also records that a localization of a commutative semiring in which sums vanish only when
every summand does inherits this property (`IsLocalization.subsingleton_addUnits`), and that a
submonoid along which a semiring without zero divisors localizes to a nontrivial semiring consists
of non-zero-divisors (`TauCeti.IsLocalization.le_nonZeroDivisors_of_nontrivial`).

Finally, if a localization `Rₘ` of `C` acts by monoid actions on `S` and on `E`, `S` acts on `E`,
and `C` acts on `S` and `E` so that `C, Rₘ, S`, `C, Rₘ, E` and `C, S, E` are scalar towers, then
`IsScalarTower Rₘ S E` (`IsLocalization.isScalarTower_of_isScalarTower`, the case of
`Submonoid.LocalizationMap.isScalarTower` for localizations of commutative semirings).
-/

public section

namespace IsLocalization

/-- A localization of a commutative semiring in which sums vanish only when every summand does
has the same property. -/
theorem subsingleton_addUnits {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*)
    [CommSemiring S] [Algebra R S] [IsLocalization M S] [Subsingleton (AddUnits R)] :
    Subsingleton (AddUnits S) :=
  Subsingleton.addUnits_of_isAddUnit fun a ha ↦ by
    obtain ⟨b, h⟩ := ha.exists_neg
    obtain ⟨⟨r, s⟩, rfl⟩ := mk'_surjective M a
    obtain ⟨⟨u, v⟩, rfl⟩ := mk'_surjective M b
    rw [← mk'_add, mk'_eq_zero_iff] at h
    obtain ⟨m, hm⟩ := h
    rw [mul_add, add_eq_zero] at hm
    exact (mk'_eq_zero_iff (S := S) r s).mpr
      ⟨m * v, by simpa [mul_assoc, mul_comm (v : R)] using hm.1⟩

section Lift

variable {R : Type*} [CommSemiring R] {M : Submonoid R} {S : Type*} [CommSemiring S]
  [Algebra R S] [IsLocalization M S] {P : Type*} [CommSemiring P] {g : R →+* P}

/-- If an injective ring homomorphism `g : R →+* P` sends every element of `M` to a unit, then its
lift `S →+* P` out of a localization `S` of `R` at `M` is injective. -/
theorem lift_injective_of_injective (hg : ∀ y : M, IsUnit (g y)) (hinj : Function.Injective g) :
    Function.Injective (lift (M := M) (S := S) hg) :=
  (lift_injective_iff hg).mpr fun _ _ ↦
    ⟨eq_of_eq (S := S) hg, fun h ↦ congrArg (algebraMap R S) (hinj h)⟩

end Lift

open scoped nonZeroDivisors

/-- Let `f : R →+* S` be injective, carrying a submonoid `M` into a submonoid `T` of
non-zero-divisors of `S`. Then the induced map from the localization of `R` at `M` to that of `S`
at `T` is injective. Unlike `IsLocalization.map_injective_of_injective'`, `S` need not be a domain;
the main case is the induced map of total quotient rings, `M = R⁰` and `T = S⁰`. -/
theorem map_injective_of_injective_of_le_nonZeroDivisors {R S : Type*} [CommRing R] [CommRing S]
    {M : Submonoid R} {T : Submonoid S} (Rₘ Sₘ : Type*) [CommRing Rₘ] [CommRing Sₘ]
    [Algebra R Rₘ] [Algebra S Sₘ] [IsLocalization M Rₘ] [IsLocalization T Sₘ] {f : R →+* S}
    (hf : Function.Injective f) (hMT : M ≤ T.comap f) (hT : T ≤ S⁰) :
    Function.Injective (map Sₘ f hMT : Rₘ →+* Sₘ) :=
  injective_of_map_algebraMap_zero (M := M) Rₘ _ fun x hx ↦ by
    rw [map_eq, to_map_eq_zero_iff Sₘ hT, _root_.map_eq_zero_iff f hf] at hx
    rw [hx, map_zero]

/-- **Scalar towers through a localization.** Let `Rₘ` be a localization of `C` at `M` that acts
on `S` and on `E` by monoid actions, and let `S` act on `E`. If `C` also acts on `S` and `E` so
that `C, Rₘ, S`, `C, Rₘ, E` and `C, S, E` are scalar towers, then `IsScalarTower Rₘ S E`. This is
the case of `Submonoid.LocalizationMap.isScalarTower` for `IsLocalization.toLocalizationMap`. -/
theorem isScalarTower_of_isScalarTower {C : Type*} [CommSemiring C] (M : Submonoid C)
    (Rₘ S E : Type*) [CommSemiring Rₘ] [Algebra C Rₘ] [IsLocalization M Rₘ]
    [SMul C S] [MulAction Rₘ S] [IsScalarTower C Rₘ S]
    [SMul C E] [MulAction Rₘ E] [IsScalarTower C Rₘ E]
    [SMul S E] [IsScalarTower C S E] :
    IsScalarTower Rₘ S E :=
  (toLocalizationMap M Rₘ).isScalarTower fun c s e ↦ by
    rw [toLocalizationMap_apply, IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul,
      smul_assoc]

end IsLocalization

namespace TauCeti.IsLocalization

/-- A submonoid of a commutative semiring without zero divisors along which the semiring localizes
to a nontrivial semiring consists of non-zero-divisors. -/
theorem le_nonZeroDivisors_of_nontrivial {R : Type*} [CommSemiring R] [NoZeroDivisors R]
    (M : Submonoid R) (S : Type*) [CommSemiring S] [Nontrivial S] [Algebra R S]
    [IsLocalization M S] : M ≤ nonZeroDivisors R :=
  le_nonZeroDivisors_of_noZeroDivisors fun h ↦
    not_subsingleton S (_root_.IsLocalization.subsingleton h)

end TauCeti.IsLocalization

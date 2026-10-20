/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Localization.Module

/-!
# Detecting injectivity at associated primes

An `R`-linear map between arbitrary modules over a Noetherian commutative ring is injective
if its localization is injective at every associated prime of its domain.

## References

* Stacks Project, Lemma 15.24.12 (Tag 0AV7).
-/

public section

namespace LinearMap

variable {R M N : Type*} [CommRing R] [IsNoetherianRing R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- A linear map is injective if, at every prime, its localization is injective or the prime
is not associated to its domain. Neither module needs to be finitely generated. -/
@[stacks 0AV7]
theorem injective_of_forall_localization (map : M →ₗ[R] N)
    (local_injective : ∀ (prime : Ideal R) [prime.IsPrime],
      Function.Injective (LocalizedModule.map prime.primeCompl map) ∨
      prime ∉ associatedPrimes R M) :
    Function.Injective map := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  rw [← LinearMap.ker_eq_bot]
  by_contra kernel_ne_bot
  have : Nontrivial (LinearMap.ker map) := Submodule.nontrivial_iff_ne_bot.mpr kernel_ne_bot
  obtain ⟨prime, associated⟩ := associatedPrimes.nonempty R (LinearMap.ker map)
  have : prime.IsPrime := associated.isPrime
  have associated_domain := associated.map_of_injective
    (LinearMap.ker map).subtype (Submodule.injective_subtype _)
  have injective := (local_injective prime).resolve_right (not_not.mpr associated_domain)
  obtain ⟨_, element, annihilator⟩ := isAssociatedPrime_iff.mp associated
  have element_zero : map element.val = 0 := LinearMap.mem_ker.mp element.property
  have localized_zero : LocalizedModule.mkLinearMap prime.primeCompl M element.val = 0 := by
    apply injective
    simp only [LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk, element_zero,
      LocalizedModule.zero_mk, map_zero]
  obtain ⟨denominator, annihilates⟩ :=
    (IsLocalizedModule.eq_zero_iff prime.primeCompl
      (LocalizedModule.mkLinearMap prime.primeCompl M)).mp localized_zero
  apply denominator.property
  apply annihilator.ge
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
  apply Subtype.ext
  simpa only [Submodule.coe_smul, Submodule.coe_zero, Submonoid.smul_def] using annihilates

end LinearMap

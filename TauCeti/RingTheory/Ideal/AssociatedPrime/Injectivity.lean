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

section IsLocalizedModule

variable {R M N : Type*} [CommSemiring R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [AddCommMonoid N] [Module R N]

/-- A linear map is injective if, at every associated prime of its domain, a compatible map
from a localization of the domain is injective. Neither module needs to be finitely generated,
and the target of the compatible map need not itself be a localization. The base may be a
commutative semiring when the source module has an additive group. -/
theorem injective_of_isLocalized_associatedPrimes
    (map : M →ₗ[R] N)
    (Mₚ : associatedPrimes R M → Type*)
    [∀ prime, AddCommMonoid (Mₚ prime)]
    [∀ prime, Module R (Mₚ prime)]
    (f : ∀ prime, M →ₗ[R] Mₚ prime)
    [∀ prime, IsLocalizedModule prime.1.primeCompl (f prime)]
    (Nₚ : associatedPrimes R M → Type*)
    [∀ prime, AddCommMonoid (Nₚ prime)]
    [∀ prime, Module R (Nₚ prime)]
    (g : ∀ prime, N →ₗ[R] Nₚ prime)
    (F : ∀ prime, Mₚ prime →ₗ[R] Nₚ prime)
    (commutes : ∀ prime, F prime ∘ₗ f prime = g prime ∘ₗ map)
    (local_injective : ∀ prime, Function.Injective (F prime)) :
    Function.Injective map := by
  refine (injective_iff_map_eq_zero map).mpr fun element element_zero ↦ ?_
  by_contra element_ne_zero
  obtain ⟨associated_prime, annihilator_le⟩ :
      ∃ associated_prime : associatedPrimes R M,
        (⊥ : Submodule R M).colon {element} ≤ associated_prime.1 := by
    obtain ⟨prime, associated, annihilator_le⟩ :=
      exists_le_isAssociatedPrime_of_isNoetherianRing R element element_ne_zero
    exact ⟨⟨prime, associated⟩, annihilator_le⟩
  have injective := local_injective associated_prime
  have localized_zero : f associated_prime element = 0 := by
    apply injective
    have mapped_zero : F associated_prime (f associated_prime element) = 0 := by
      calc
        F associated_prime (f associated_prime element) =
            g associated_prime (map element) :=
          LinearMap.congr_fun (commutes associated_prime) element
        _ = 0 := by rw [element_zero, map_zero]
    simpa only [map_zero] using mapped_zero
  obtain ⟨denominator, annihilates⟩ :=
    (IsLocalizedModule.eq_zero_iff associated_prime.1.primeCompl (f associated_prime)).mp
      localized_zero
  apply denominator.property
  apply annihilator_le
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
  have denominator_annihilates : (denominator : R) • element = 0 := by
    simpa only [Submonoid.smul_def] using annihilates
  exact denominator_annihilates

end IsLocalizedModule

section LocalizedModule

variable {R M N : Type*} [CommSemiring R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [AddCommMonoid N] [Module R N]

/-- A linear map from an additive group over a commutative semiring is injective if its
localization is injective at every associated prime of its domain. -/
theorem injective_of_forall_localization_of_addCommGroup (map : M →ₗ[R] N)
    (local_injective : ∀ (prime : Ideal R) [prime.IsPrime],
      Function.Injective (LocalizedModule.map prime.primeCompl map) ∨
      prime ∉ associatedPrimes R M) :
    Function.Injective map := by
  exact injective_of_isLocalized_associatedPrimes
    map
    (fun prime ↦ LocalizedModule prime.1.primeCompl M)
    (fun prime ↦ LocalizedModule.mkLinearMap prime.1.primeCompl M)
    (fun prime ↦ LocalizedModule prime.1.primeCompl N)
    (fun prime ↦ LocalizedModule.mkLinearMap prime.1.primeCompl N)
    (fun prime ↦ LocalizedModule.map prime.1.primeCompl map)
    (fun prime ↦ by ext; simp)
    (fun prime ↦ (local_injective prime.1).resolve_right (not_not.mpr prime.property))

end LocalizedModule

section LocalizedModule

variable {R M N : Type*} [CommRing R] [IsNoetherianRing R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- A linear map is injective if its localization is injective at every associated prime
of its domain. This is Stacks 0AV7 for the canonical localization modules. -/
@[stacks 0AV7]
theorem injective_of_forall_localization (map : M →ₗ[R] N)
    (local_injective : ∀ (prime : Ideal R) [prime.IsPrime],
      Function.Injective (LocalizedModule.map prime.primeCompl map) ∨
      prime ∉ associatedPrimes R M) :
    Function.Injective map := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  exact injective_of_forall_localization_of_addCommGroup map local_injective

end LocalizedModule

end LinearMap

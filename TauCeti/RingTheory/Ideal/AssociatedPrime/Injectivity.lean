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
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A linear map is injective if, at every associated prime of its domain, a compatible map
from a localization of the domain is injective. Neither module needs to be finitely generated,
and the target of the compatible map need not itself be a localization. The base may be a
commutative semiring when the original modules have additive groups. -/
theorem injective_of_forall_isLocalizedModule
    (map : M →ₗ[R] N)
    (Mₚ : ∀ (prime : Ideal R) [prime.IsPrime], Type*)
    [∀ (prime : Ideal R) [prime.IsPrime], AddCommMonoid (Mₚ prime)]
    [∀ (prime : Ideal R) [prime.IsPrime], Module R (Mₚ prime)]
    (f : ∀ (prime : Ideal R) [prime.IsPrime], M →ₗ[R] Mₚ prime)
    [∀ (prime : Ideal R) [prime.IsPrime], IsLocalizedModule prime.primeCompl (f prime)]
    (Nₚ : ∀ (prime : Ideal R) [prime.IsPrime], Type*)
    [∀ (prime : Ideal R) [prime.IsPrime], AddCommMonoid (Nₚ prime)]
    [∀ (prime : Ideal R) [prime.IsPrime], Module R (Nₚ prime)]
    (g : ∀ (prime : Ideal R) [prime.IsPrime], N →ₗ[R] Nₚ prime)
    (F : ∀ (prime : Ideal R) [prime.IsPrime], Mₚ prime →ₗ[R] Nₚ prime)
    (commutes : ∀ (prime : Ideal R) [prime.IsPrime], F prime ∘ₗ f prime = g prime ∘ₗ map)
    (local_injective : ∀ (prime : Ideal R) [prime.IsPrime],
      prime ∈ associatedPrimes R M → Function.Injective (F prime)) :
    Function.Injective map := by
  have kernel_bot : LinearMap.ker map = ⊥ := by
    by_contra kernel_ne_bot
    have : Nontrivial (LinearMap.ker map) := Submodule.nontrivial_iff_ne_bot.mpr kernel_ne_bot
    obtain ⟨prime, associated⟩ := associatedPrimes.nonempty R (LinearMap.ker map)
    have : prime.IsPrime := associated.isPrime
    have associated_domain := associated.map_of_injective
      (LinearMap.ker map).subtype (Submodule.injective_subtype _)
    have injective := local_injective prime associated_domain
    obtain ⟨_, element, annihilator⟩ := isAssociatedPrime_iff.mp associated
    have element_zero : map element.val = 0 := LinearMap.mem_ker.mp element.property
    have localized_zero : f prime element.val = 0 := by
      apply injective
      have mapped_zero : F prime (f prime element.val) = 0 := by
        calc
          F prime (f prime element.val) = g prime (map element.val) :=
            LinearMap.congr_fun (commutes prime) element.val
          _ = 0 := by rw [element_zero, map_zero]
      simpa only [map_zero] using mapped_zero
    obtain ⟨denominator, annihilates⟩ :=
      (IsLocalizedModule.eq_zero_iff prime.primeCompl (f prime)).mp localized_zero
    apply denominator.property
    apply annihilator.ge
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    apply Subtype.ext
    simpa only [Submodule.coe_smul, Submodule.coe_zero, Submonoid.smul_def] using annihilates
  have zero_kernel := LinearMap.ker_eq_bot'.mp kernel_bot
  intro first second equal
  apply sub_eq_zero.mp
  apply zero_kernel
  rw [map_sub, equal, sub_self]

end IsLocalizedModule

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
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  exact injective_of_forall_isLocalizedModule
    map
    (fun prime _ ↦ LocalizedModule prime.primeCompl M)
    (fun prime _ ↦ LocalizedModule.mkLinearMap prime.primeCompl M)
    (fun prime _ ↦ LocalizedModule prime.primeCompl N)
    (fun prime _ ↦ LocalizedModule.mkLinearMap prime.primeCompl N)
    (fun prime _ ↦ LocalizedModule.map prime.primeCompl map)
    (fun prime _ ↦ by ext; simp)
    (fun prime _ associated =>
      (local_injective prime).resolve_right (not_not.mpr associated))

end LocalizedModule

end LinearMap

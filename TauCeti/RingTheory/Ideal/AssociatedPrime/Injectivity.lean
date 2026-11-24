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

section AddCommGroup

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
    [∀ prime, IsLocalizedModule prime.val.primeCompl (f prime)]
    (Nₚ : associatedPrimes R M → Type*)
    [∀ prime, AddCommMonoid (Nₚ prime)]
    [∀ prime, Module R (Nₚ prime)]
    (g : ∀ prime, N →ₗ[R] Nₚ prime)
    (F : ∀ prime, Mₚ prime →ₗ[R] Nₚ prime)
    (commutes : ∀ prime, F prime ∘ₗ f prime = g prime ∘ₗ map)
    (local_injective : ∀ prime, Function.Injective (F prime)) :
    Function.Injective map := by
  refine (injective_iff_map_eq_zero map).mpr fun x map_eq_zero ↦ by_contra fun x_ne_zero ↦ ?_
  -- The annihilator of the nonzero element `x` lies in some associated prime.
  obtain ⟨prime, colon_le⟩ :
      ∃ prime : associatedPrimes R M, (⊥ : Submodule R M).colon {x} ≤ prime.val :=
    let ⟨p, associated, colon_le⟩ :=
      exists_le_isAssociatedPrime_of_isNoetherianRing R x x_ne_zero
    ⟨⟨p, associated⟩, colon_le⟩
  -- By the commuting square and injectivity of `F prime`, `x` vanishes in `Mₚ prime` ...
  have localized_zero : f prime x = 0 := local_injective prime <| by
    simpa [map_eq_zero] using LinearMap.congr_fun (commutes prime) x
  -- ... so some `s ∉ prime` annihilates `x`, contradicting `ann x ≤ prime`.
  obtain ⟨s, smul_eq_zero⟩ :=
    (IsLocalizedModule.eq_zero_iff prime.val.primeCompl (f prime)).mp localized_zero
  rw [Submonoid.smul_def] at smul_eq_zero
  exact s.property <| colon_le <|
    Submodule.mem_colon_singleton.mpr <| (Submodule.mem_bot R).mpr smul_eq_zero

/-- A linear map from an additive group over a commutative semiring is injective if its
localization is injective at every associated prime of its domain. -/
theorem injective_of_forall_localization_of_addCommGroup (map : M →ₗ[R] N)
    (local_injective : ∀ (prime : Ideal R) [prime.IsPrime],
      Function.Injective (LocalizedModule.map prime.primeCompl map) ∨
      prime ∉ associatedPrimes R M) :
    Function.Injective map :=
  injective_of_isLocalized_associatedPrimes map
    _ (fun prime ↦ LocalizedModule.mkLinearMap prime.val.primeCompl M)
    _ (fun prime ↦ LocalizedModule.mkLinearMap prime.val.primeCompl N)
    (fun prime ↦ LocalizedModule.map prime.val.primeCompl map) (fun prime ↦ by ext; simp)
    (fun prime ↦ (local_injective prime.val).resolve_right (not_not.mpr prime.property))

end AddCommGroup

section CommRing

variable {R M N : Type*} [CommRing R] [IsNoetherianRing R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- A linear map is injective if its localization is injective at every associated prime
of its domain. This is Stacks 0AV7 for the canonical localization modules. -/
@[stacks 0AV7]
theorem injective_of_forall_localization (map : M →ₗ[R] N)
    (local_injective : ∀ (prime : Ideal R) [prime.IsPrime],
      Function.Injective (LocalizedModule.map prime.primeCompl map) ∨
      prime ∉ associatedPrimes R M) :
    Function.Injective map :=
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  injective_of_forall_localization_of_addCommGroup map local_injective

end CommRing

end LinearMap

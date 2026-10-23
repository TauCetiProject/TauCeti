/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Depth.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Depth zero and associated primes

Over a Noetherian local ring, a module has depth zero exactly when the maximal ideal is
associated to it. After localization at a prime, depth zero is equivalent to that prime
being associated to the original module. These equivalences allow arbitrary modules.

They supply the depth-zero interface needed for Stacks, Lemma 15.24.13 (0AV8).
-/

public section

universe u v

/-- For an additive-group module over a Noetherian local ring, depth is zero exactly when the
maximal ideal is associated to the module. The depth term lifts the module to the ring universe. -/
@[simp 900]
theorem IsLocalRing.depth_eq_zero_iff_mem_associatedPrimes_of_addCommGroup
    (R : Type u) (M : Type v) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] :
    IsLocalRing.depth (ModuleCat.of R (ULift.{u} M)) = 0 ↔
      IsLocalRing.maximalIdeal R ∈ associatedPrimes R M := by
  rw [IsLocalRing.depth_eq_moduleCat_depth, ModuleCat.depth_eq_zero_iff_nontrivial_linearMap]
  -- `depth` represents the residue module by `Shrink` to control its universe.
  change Nontrivial (Shrink.{max u v} (R ⧸ IsLocalRing.maximalIdeal R) →ₗ[R]
    ULift.{u} M) ↔ _
  rw [(LinearEquiv.congrLeft (ULift.{u} M) R
    (Shrink.linearEquiv.{max u v} R (R ⧸ IsLocalRing.maximalIdeal R))).nontrivial_congr]
  rw [(LinearEquiv.congrRight (ULift.moduleEquiv : ULift.{u} M ≃ₗ[R] M)).nontrivial_congr]
  rw [AssociatedPrimes.mem_iff]
  rw [isAssociatedPrime_iff_exists_injective_linearMap]
  let : IsSimpleModule R (R ⧸ IsLocalRing.maximalIdeal R) :=
    isSimpleModule_iff_isCoatom.mpr
      (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal R))
  constructor
  · intro nontrivial_maps
    let := nontrivial_maps
    obtain ⟨map, nonzero⟩ := exists_ne (0 : R ⧸ IsLocalRing.maximalIdeal R →ₗ[R] M)
    exact ⟨inferInstance, map, LinearMap.injective_of_ne_zero nonzero⟩
  · rintro ⟨_, map, injective⟩
    exact ⟨⟨map, 0, fun equal ↦ by
      have zero_one : (0 : R ⧸ IsLocalRing.maximalIdeal R) = 1 :=
        injective (by simp [equal])
      exact zero_ne_one zero_one⟩⟩

/-- An arbitrary module over a Noetherian local ring has depth zero exactly when the
maximal ideal is an associated prime. The additive group is induced by the ring action. -/
@[simp]
theorem IsLocalRing.depth_eq_zero_iff_mem_associatedPrimes
    (R : Type u) (M : Type v) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommMonoid M] [Module R M] :
    letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
    IsLocalRing.depth (ModuleCat.of R (ULift.{u} M)) = 0 ↔
      IsLocalRing.maximalIdeal R ∈ associatedPrimes R M :=
  letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  IsLocalRing.depth_eq_zero_iff_mem_associatedPrimes_of_addCommGroup R M

open Module.associatedPrimes in
/-- For an additive-group module over a Noetherian ring, its localization at a prime `p` has depth
zero over `R_p` exactly when `p` is associated to the original module. -/
@[simp 1100]
theorem IsLocalRing.depth_localizedModule_eq_zero_iff_mem_associatedPrimes_of_addCommGroup
    (R : Type u) (M : Type v) [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] (prime : Ideal R) [prime.IsPrime] :
    IsLocalRing.depth
      (ModuleCat.of (Localization.AtPrime prime) (LocalizedModule prime.primeCompl M)) = 0 ↔
        prime ∈ associatedPrimes R M := by
  rw [← IsLocalRing.depth_eq_of_linearEquiv
    (ULift.moduleEquiv : ULift.{u} (LocalizedModule prime.primeCompl M) ≃ₗ[
      Localization.AtPrime prime] LocalizedModule prime.primeCompl M)]
  rw [IsLocalRing.depth_eq_zero_iff_mem_associatedPrimes_of_addCommGroup]
  rw [← preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
    prime.primeCompl (Localization.AtPrime prime) (LocalizedModule.mkLinearMap prime.primeCompl M)]
  rw [Set.mem_preimage, ← Ideal.under_def]
  rw [IsLocalization.AtPrime.under_maximalIdeal _ prime]

open Module.associatedPrimes in
/-- The depth of an arbitrary module localized at a prime is zero exactly when that prime
is associated to the original module. Depth is taken over the localized ring. -/
@[simp 1100]
theorem IsLocalRing.depth_localizedModule_eq_zero_iff_mem_associatedPrimes
    (R : Type u) (M : Type v) [CommRing R] [IsNoetherianRing R]
    [AddCommMonoid M] [Module R M] (prime : Ideal R) [prime.IsPrime] :
    letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
    IsLocalRing.depth
      (ModuleCat.of (Localization.AtPrime prime) (LocalizedModule prime.primeCompl M)) = 0 ↔
        prime ∈ associatedPrimes R M :=
  letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  IsLocalRing.depth_localizedModule_eq_zero_iff_mem_associatedPrimes_of_addCommGroup R M prime

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Depth.AssociatedPrime
public import TauCeti.RingTheory.Depth.Basic
public import TauCeti.RingTheory.Ideal.AssociatedPrime.Injectivity
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
# Bijectivity from local depth conditions

A linear map is bijective if, at every prime, either its localization is bijective, or the
localized source has depth at least two and the prime is not associated to the target.
This criterion applies to arbitrary source and target modules over a Noetherian ring.

## References

* Stacks Project, Lemma 15.24.12 (Tag 0AV7), for the injectivity criterion.
* Stacks Project, Lemma 15.24.13 (Tag 0AV8).
-/

public section

universe u v w

namespace LinearMap

private theorem injective_of_depth_alternative
    {R : Type u} {M : Type v} {N : Type w} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (map : M →ₗ[R] N)
    (hypothesis : ∀ (prime : Ideal R) [prime.IsPrime],
      Function.Bijective (LocalizedModule.map prime.primeCompl map) ∨
        2 ≤ IsLocalRing.depth
          (ModuleCat.of (Localization.AtPrime prime) (LocalizedModule prime.primeCompl M)) ∧
          prime ∉ associatedPrimes R N) :
    Function.Injective map := by
  apply LinearMap.injective_of_forall_localization map
  intro prime prime_isPrime
  rcases hypothesis prime with bijective | ⟨depth_bound, _⟩
  · exact Or.inl bijective.1
  · right
    intro associated
    have depth_zero :=
      (IsLocalRing.depth_localizedModule_eq_zero_iff_mem_associatedPrimes_of_addCommGroup
        R M prime).mpr associated
    simp [depth_zero] at depth_bound

/-- A linear map between arbitrary additive-group modules over a Noetherian ring is
bijective if, at each prime, its localization is bijective or the source has depth at least two
and the prime is not associated to the target. The additive-group structures are arbitrary;
`LinearMap.bijective_of_depth` is the version for the canonical group structure.

Divergence from Stacks: no finite-source hypothesis is needed here. -/
@[stacks 0AV8 "The finite-source hypothesis is omitted."]
theorem bijective_of_depth_of_addCommGroup
    {R : Type u} {M : Type v} {N : Type w} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (map : M →ₗ[R] N)
    (hypothesis : ∀ (prime : Ideal R) [prime.IsPrime],
      Function.Bijective (LocalizedModule.map prime.primeCompl map) ∨
        2 ≤ IsLocalRing.depth
          (ModuleCat.of (Localization.AtPrime prime) (LocalizedModule prime.primeCompl M)) ∧
          prime ∉ associatedPrimes R N) :
    Function.Bijective map := by
  classical
  -- The depth alternative excludes associated primes of the source, so 0AV7 gives injectivity.
  have injective := injective_of_depth_alternative map hypothesis
  refine ⟨injective, ?_⟩
  -- A nonzero cokernel has an associated prime; localizing there gives depth zero.
  by_contra not_surjective
  have range_ne_top : map.range ≠ ⊤ := by
    intro range_top
    exact not_surjective (LinearMap.range_eq_top.mp range_top)
  let : Nontrivial (N ⧸ map.range) := Submodule.Quotient.nontrivial_iff.mpr range_ne_top
  obtain ⟨prime, associated⟩ := associatedPrimes.nonempty R (N ⧸ map.range)
  let : prime.IsPrime := associated.1
  have depth_zero :=
    (IsLocalRing.depth_localizedModule_eq_zero_iff_mem_associatedPrimes_of_addCommGroup
      R (N ⧸ map.range) prime).mpr associated
  let localizedMap := LocalizedModule.map prime.primeCompl map
  let localizedQuotient := LocalizedModule.map prime.primeCompl map.range.mkQ
  have exactness : Function.Exact localizedMap localizedQuotient :=
    LocalizedModule.map_exact prime.primeCompl map map.range.mkQ map.exact_map_mkQ_range
  have quotient_surjective : Function.Surjective localizedQuotient :=
    LocalizedModule.map_surjective prime.primeCompl map.range.mkQ map.range.mkQ_surjective
  -- At this prime, either localized bijectivity kills the cokernel or the depth
  -- inequality for the localized short exact sequence contradicts its depth zero.
  rcases hypothesis prime with bijective | ⟨depth_bound, not_associated⟩
  · let : Subsingleton (LocalizedModule prime.primeCompl (N ⧸ map.range)) :=
      (LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker
        prime.primeCompl map).mp bijective.2
    rw [IsLocalRing.depth_eq_top_of_subsingleton] at depth_zero
    exact ENat.top_ne_zero depth_zero
  · have target_depth_ne_zero : IsLocalRing.depth
        (ModuleCat.of (Localization.AtPrime prime) (LocalizedModule prime.primeCompl N)) ≠ 0 :=
      fun equality ↦ not_associated
        ((IsLocalRing.depth_localizedModule_eq_zero_iff_mem_associatedPrimes_of_addCommGroup
          R N prime).mp equality)
    have inequality := IsLocalRing.depth_min_snd_fst_sub_one_le_trd_of_exact
      localizedMap localizedQuotient exactness
      (LocalizedModule.map_injective prime.primeCompl map injective) quotient_surjective
    have target_one : 1 ≤ IsLocalRing.depth
        (ModuleCat.of (Localization.AtPrime prime) (LocalizedModule prime.primeCompl N)) :=
      Order.one_le_iff_ne_zero.mpr target_depth_ne_zero
    -- `2 - 1 = 1` in `ℕ∞`: write `2 = 1 + 1` and cancel the finite summand.
    have two_sub_one : (2 : ℕ∞) - 1 = 1 := by
      rw [← one_add_one_eq_two]
      exact (ENat.addLECancellable_of_ne_top ENat.one_ne_top).add_tsub_cancel_right
    have source_one : 1 ≤ IsLocalRing.depth
        (ModuleCat.of (Localization.AtPrime prime) (LocalizedModule prime.primeCompl M)) - 1 :=
      two_sub_one ▸ tsub_le_tsub_right depth_bound 1
    have contradiction := le_trans (le_inf target_one source_one) inequality
    simp [depth_zero] at contradiction

/-- A linear map between arbitrary modules over a Noetherian ring is
bijective if, at each prime, its localization is bijective or the source has depth at least two
and the prime is not associated to the target. The depth hypothesis uses the canonical additive
group structure induced by the ring action; see `LinearMap.bijective_of_depth_of_addCommGroup`
for arbitrary additive-group structures.

Divergence from Stacks: no finite-source hypothesis is needed here. -/
@[stacks 0AV8 "The finite-source hypothesis is omitted."]
theorem bijective_of_depth
    {R : Type u} {M : Type v} {N : Type w} [CommRing R] [IsNoetherianRing R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (map : M →ₗ[R] N)
    (hypothesis :
      letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
      ∀ (prime : Ideal R) [prime.IsPrime],
      Function.Bijective (LocalizedModule.map prime.primeCompl map) ∨
        2 ≤ IsLocalRing.depth
          (ModuleCat.of (Localization.AtPrime prime) (LocalizedModule prime.primeCompl M)) ∧
          prime ∉ associatedPrimes R N) :
    Function.Bijective map :=
  letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  bijective_of_depth_of_addCommGroup map hypothesis

end LinearMap

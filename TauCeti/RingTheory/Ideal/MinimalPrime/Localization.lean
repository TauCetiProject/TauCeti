/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Minimal primes and localization

This file collects facts about the localization of a commutative ring or semiring and its minimal
primes:

* If the localization `A_m` is a domain, as it is when `A_m` is a regular local ring, then the
  kernel of `A → A_m` is a prime contained in every prime `q ≤ m`, so it is the only minimal prime
  of `A` contained in `m`. Consequently every prime `q ≤ m` contains every minimal prime `P ≤ m`:
  the primes below `m` all lie on the single irreducible component `V(P)` of `Spec A` through `m`.
  This is what makes the height of `m` a lower bound for the dimension of that component.
* If `m` is minimal over a radical ideal `I`, then `I` generates the maximal ideal of `A_m`. For a
  principal ideal `I = (f)` with `A ⧸ (f)` reduced, this says that `f` generates the maximal ideal
  of the localization at every prime minimal over `f`. For `I = ⊥` in a reduced ring, the maximal
  ideal of `A_P` is zero at every minimal prime `P`, so `P.ResidueField` is itself a localization
  of `A` at `P`.
* Every prime ideal `q` contains a minimal prime `p` disjoint from any submonoid `M` of
  non-zero-divisors, so `p` extends to a prime of `M⁻¹ A` contracting back to `p`.

## Main results

* `TauCeti.le_of_mem_minimalPrimes_of_isDomain_localization`: if `A_m` is a domain, a minimal
  prime `P ≤ m` lies below every prime `q ≤ m`.
* `TauCeti.exists_minimalPrime_le_and_map_isPrime`: every prime `q` contains a minimal prime `p`
  disjoint from a submonoid `M` of non-zero-divisors, extending to a prime of `M⁻¹ A` that
  contracts back to `p`.
* `TauCeti.isCoprime_of_mem_minimalPrimes_of_isDomain_localization`: distinct minimal primes
  are coprime when all maximal localizations are domains.
* `IsLocalization.AtPrime.map_eq_maximalIdeal_of_mem_minimalPrimes`: if `m` is minimal over a
  radical ideal `I`, then `I` generates the maximal ideal of `A_m`.
* `TauCeti.isLocalization_atPrime_residueField_of_mem_minimalPrimes`: at a minimal prime `P` of a
  reduced ring `B`, `P.ResidueField` is a localization of `B` at `P`.
* `IsLocalization.comap_mem_minimalPrimes_of_krullDimLE_zero`: in a localization at
  non-zero-divisors of Krull dimension zero, such as an Artinian total ring of fractions, every
  prime contracts to a minimal prime.
-/

public section

namespace TauCeti

/-- If a localization `S` of `A` at a prime `m` is a domain, then a minimal prime `P ≤ m` of `A`
lies below every prime `q ≤ m`. -/
theorem le_of_mem_minimalPrimes_of_isDomain_localization {A : Type*} [CommSemiring A]
    {m P q : Ideal A} [m.IsPrime] [q.IsPrime] (S : Type*) [CommSemiring S] [Algebra A S]
    [IsLocalization.AtPrime S m] [IsDomain S]
    (hP : P ∈ minimalPrimes A) (hPm : P ≤ m) (hqm : q ≤ m) : P ≤ q := by
  -- The kernel of `A → S` lies below every prime contained in `m`.
  have hker {q' : Ideal A} [q'.IsPrime] (hq' : q' ≤ m) :
      RingHom.ker (algebraMap A S) ≤ q' := fun a ha ↦ by
    obtain ⟨⟨s, hs⟩, hsa⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl _ a).mp ha
    exact (‹q'.IsPrime›.mem_or_mem (hsa ▸ q'.zero_mem)).resolve_left fun h ↦ hs (hq' h)
  have := hP.1.1
  exact (hP.2 ⟨RingHom.ker_isPrime _, bot_le⟩ (hker hPm)).trans (hker hqm)

open scoped nonZeroDivisors in
/-- Every prime ideal `q` of `A` contains a minimal prime `p` that is disjoint from any submonoid
`M` of non-zero-divisors; hence `p` extends to a prime of `M⁻¹ A` contracting back to `p`. -/
theorem exists_minimalPrime_le_and_map_isPrime {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (M : Submonoid A) [IsLocalization M B] (hM : M ≤ A⁰) (q : Ideal A) [q.IsPrime] :
    ∃ p : Ideal A, p ∈ minimalPrimes A ∧ p ≤ q ∧ Disjoint (M : Set A) p ∧
      (p.map (algebraMap A B)).IsPrime ∧
      (p.map (algebraMap A B)).comap (algebraMap A B) = p := by
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ q)
  have hp_prime : p.IsPrime := hp.1.1
  have hdisj : Disjoint (M : Set A) p :=
    (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp).symm.mono_left hM
  exact ⟨p, hp, hpq, hdisj,
    IsLocalization.isPrime_of_isPrime_disjoint M B p hp_prime hdisj,
    IsLocalization.under_map_of_isPrime_disjoint M B hp_prime hdisj⟩

/-- Over a semiring whose localizations at maximal ideals are domains, distinct minimal primes are
coprime: a maximal ideal containing both would contain two minimal primes of a local domain. -/
theorem isCoprime_of_mem_minimalPrimes_of_isDomain_localization {A : Type*} [CommSemiring A]
    (h : ∀ (m : Ideal A) [m.IsMaximal], IsDomain (Localization.AtPrime m)) {P Q : Ideal A}
    (hP : P ∈ minimalPrimes A) (hQ : Q ∈ minimalPrimes A) (hPQ : P ≠ Q) : IsCoprime P Q := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  have := h m
  have := hP.1.1
  have := hQ.1.1
  exact hPQ (le_antisymm
    (le_of_mem_minimalPrimes_of_isDomain_localization (Localization.AtPrime m)
      hP (le_sup_left.trans hle) (le_sup_right.trans hle))
    (le_of_mem_minimalPrimes_of_isDomain_localization (Localization.AtPrime m)
      hQ (le_sup_right.trans hle) (le_sup_left.trans hle)))

end TauCeti

namespace IsLocalization.AtPrime

/-- If a prime `q` is minimal over a radical ideal `I`, then `I` generates the maximal ideal of
the localization of `R` at `q`. -/
theorem map_eq_maximalIdeal_of_mem_minimalPrimes {R : Type*} [CommSemiring R] {I q : Ideal R}
    [q.IsPrime] (A : Type*) [CommSemiring A] [Algebra R A] [IsLocalization.AtPrime A q]
    [IsLocalRing A] (hI : I.IsRadical) (hIq : q ∈ I.minimalPrimes) :
    I.map (algebraMap R A) = IsLocalRing.maximalIdeal A := by
  rw [← map_eq_maximalIdeal q A, ← radical_map_of_mem_minimalPrimes (A := A) q I hIq,
    ← IsLocalization.map_radical q.primeCompl A, hI.radical]

end IsLocalization.AtPrime

namespace TauCeti

/-- At a minimal prime `P` of a reduced ring `B`, the residue field `P.ResidueField` is a
localization of `B` at `P`. -/
theorem isLocalization_atPrime_residueField_of_mem_minimalPrimes {B : Type*} [CommRing B]
    [IsReduced B] {P : Ideal B} (hP : P ∈ minimalPrimes B) :
    letI := hP.1.1
    IsLocalization.AtPrime P.ResidueField P := by
  have : P.IsPrime := hP.1.1
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime P) = ⊥ := by
    have h := IsLocalization.AtPrime.map_eq_maximalIdeal_of_mem_minimalPrimes
      (Localization.AtPrime P) (Ideal.isRadical_bot (R := B)) hP
    rwa [Ideal.map_bot, eq_comm] at h
  have hbij : Function.Bijective
      (IsScalarTower.toAlgHom B (Localization.AtPrime P) P.ResidueField) := by
    rw [IsScalarTower.coe_toAlgHom', IsLocalRing.ResidueField.algebraMap_eq]
    exact ⟨(RingHom.injective_iff_ker_eq_bot _).mpr (IsLocalRing.ker_residue.trans hmax),
      IsLocalRing.residue_surjective⟩
  exact IsLocalization.isLocalization_of_algEquiv P.primeCompl (AlgEquiv.ofBijective _ hbij)

/-- For a minimal prime `P` of a reduced `R`-algebra `B` and a submonoid `M ≤ P.primeCompl`,
`P.ResidueField` is a localization of `B` at `P` and of `S = M⁻¹ B` at the image of `P.primeCompl`,
compatibly with the `R → B → S` scalar tower. -/
theorem with_residueField_isLocalization_of_mem_minimalPrimes {R B S : Type*} [CommRing R]
    [CommRing B] [Algebra R B] [IsReduced B] {P : Ideal B} [P.IsPrime]
    (hP : P ∈ minimalPrimes B) (M : Submonoid B) (hM : M ≤ P.primeCompl)
    [CommRing S] [Algebra R S] [Algebra B S] [IsScalarTower R B S] [IsLocalization M S]
    {C : Prop}
    (h : [IsLocalization.AtPrime P.ResidueField P] → [Algebra S P.ResidueField] →
      [IsScalarTower B S P.ResidueField] → [IsScalarTower R S P.ResidueField] →
      [IsLocalization (P.primeCompl.map (algebraMap B S)) P.ResidueField] → C) : C := by
  have : IsLocalization.AtPrime P.ResidueField P :=
    isLocalization_atPrime_residueField_of_mem_minimalPrimes hP
  let : Algebra S P.ResidueField :=
    IsLocalization.localizationAlgebraOfSubmonoidLe S P.ResidueField M P.primeCompl hM
  have : IsScalarTower B S P.ResidueField :=
    IsLocalization.localization_isScalarTower_of_submonoid_le S P.ResidueField M P.primeCompl hM
  have : IsScalarTower R S P.ResidueField := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply R B P.ResidueField,
      IsScalarTower.algebraMap_apply B S P.ResidueField,
      ← IsScalarTower.algebraMap_apply R B S]
  have : IsLocalization (P.primeCompl.map (algebraMap B S)) P.ResidueField :=
    IsLocalization.isLocalization_of_submonoid_le S P.ResidueField M P.primeCompl hM
  exact h

end TauCeti

namespace IsLocalization

/-- In a localization at non-zero-divisors of Krull dimension zero, such as an Artinian total ring
of fractions, every prime contracts to a minimal prime of the original ring. -/
theorem comap_mem_minimalPrimes_of_krullDimLE_zero {R : Type*} [CommRing R] {M : Submonoid R}
    (hM : M ≤ nonZeroDivisors R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S]
    [Ring.KrullDimLE 0 S] (p : Ideal S) [p.IsPrime] :
    p.comap (algebraMap R S) ∈ minimalPrimes R := by
  have h := minimalPrimes_comap M S (⊥ : Ideal S)
  rw [Ideal.comap_bot_of_injective _ (IsLocalization.injective S hM)] at h
  exact (h ▸ ⟨p, Ideal.mem_minimalPrimes_of_krullDimLE_zero p, rfl⟩ :
    p.comap (algebraMap R S) ∈ (⊥ : Ideal R).minimalPrimes)

end IsLocalization

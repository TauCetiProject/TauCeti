/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Support

public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Localization.AtPrime.Basic

import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.Tactic.ENatToNat
import TauCeti.RingTheory.Length
import TauCeti.RingTheory.Localization.Annihilator

/-!
# Primes of small height in the support of a torsion module

A finitely generated torsion module `M` over a noetherian ring `A` vanishes at every minimal prime
of `A`, so every prime of height at most one in its support is minimal over the annihilator of
`M`. Hence there are only finitely many such primes
(`Module.IsTorsion.finite_setOf_mem_support_height_le_one`). Over a noetherian normal domain these
are the height-one primes at which the characteristic divisor of `M` is supported, and the
finiteness is what makes prime avoidance available for them
(`Module.IsTorsion.exists_mem_forall_notMem_of_forall_not_le`).

The localization of `M` at a prime of height at most one is a finitely generated module over a
noetherian local ring of dimension at most one, killed by a non-zero-divisor, so it has finite
length (`Module.IsTorsion.isFiniteLength_localizedModule`). These local lengths are the
multiplicities of the characteristic divisor.
-/

public section

namespace Module.IsTorsion

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- A torsion module vanishes at every minimal prime of the ring: elements of a minimal prime are
zero divisors. -/
theorem notMem_support_of_mem_minimalPrimes (hM : Module.IsTorsion A M) {𝔭 : PrimeSpectrum A}
    (h𝔭 : 𝔭.asIdeal ∈ minimalPrimes A) : 𝔭 ∉ Module.support A M := by
  refine Module.notMem_support_iff'.mpr fun m ↦ ?_
  obtain ⟨⟨s, hs⟩, hsm⟩ := @hM m
  exact ⟨s, fun h ↦ notMem_nonZeroDivisors_of_mem_mem_minimalPrimes h h𝔭 hs, hsm⟩

/-- A finitely generated torsion module over a noetherian ring has only finitely many primes of
height at most one in its support. -/
theorem finite_setOf_mem_support_height_le_one [IsNoetherianRing A] [Module.Finite A M]
    (hM : Module.IsTorsion A M) :
    {𝔭 ∈ Module.support A M | 𝔭.asIdeal.height ≤ 1}.Finite := by
  -- Every such prime is minimal over the annihilator of `M`: a prime strictly below it has
  -- height zero, so it is a minimal prime of `A`, where `M` vanishes.
  have hinj : Function.Injective (PrimeSpectrum.asIdeal (R := A)) := fun _ _ h ↦ PrimeSpectrum.ext h
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing A (Module.annihilator A M)).preimage
    hinj.injOn).subset ?_
  rintro 𝔭 ⟨hmem, hht⟩
  refine ⟨⟨𝔭.isPrime, Module.mem_support_iff_of_finite.mp hmem⟩, fun 𝔮 ⟨h𝔮, hann⟩ hle ↦ ?_⟩
  by_contra hne
  have hlt : 𝔮 < 𝔭.asIdeal := lt_of_le_of_ne hle fun h ↦ hne (h ▸ le_rfl)
  have h0 : 𝔮.height = 0 := by
    have := (Ideal.height_add_one_le_of_lt_of_isPrime hlt).trans hht
    generalize 𝔮.height = n at this ⊢
    enat_to_nat
    omega
  exact hM.notMem_support_of_mem_minimalPrimes (𝔭 := ⟨𝔮, h𝔮⟩) (Ideal.height_eq_zero_iff.mp h0)
    (Module.mem_support_iff_of_finite.mpr hann)

/-- Prime avoidance for the primes of height at most one in the support of a finitely generated
torsion module over a noetherian ring: an ideal contained in none of them has an element lying in
none of them. -/
theorem exists_mem_forall_notMem_of_forall_not_le [IsNoetherianRing A] [Module.Finite A M]
    (hM : Module.IsTorsion A M) {I : Ideal A}
    (hI : ∀ 𝔭 ∈ Module.support A M, 𝔭.asIdeal.height ≤ 1 → ¬ I ≤ 𝔭.asIdeal) :
    ∃ a ∈ I, ∀ 𝔭 ∈ Module.support A M, 𝔭.asIdeal.height ≤ 1 → a ∉ 𝔭.asIdeal := by
  by_contra! h
  obtain ⟨_, ⟨𝔭, ⟨hmem, hht⟩, rfl⟩, hle⟩ :=
    (Ideal.subset_union_prime_finite (f := id)
      (hM.finite_setOf_mem_support_height_le_one.image PrimeSpectrum.asIdeal) ⊥ ⊥
      fun _ ⟨𝔭, _, h⟩ _ _ ↦ h ▸ 𝔭.isPrime).mp fun x hx ↦ by
        obtain ⟨𝔭, hmem, hht, hx𝔭⟩ := h x hx
        exact Set.mem_biUnion (Set.mem_image_of_mem _ ⟨hmem, hht⟩) hx𝔭
  exact hI 𝔭 hmem hht hle

/-- The localization of a finitely generated torsion module over a noetherian ring at a prime of
height at most one has finite length. -/
theorem isFiniteLength_localizedModule [IsNoetherianRing A] [Module.Finite A M]
    (hM : Module.IsTorsion A M) {𝔭 : PrimeSpectrum A} (h𝔭 : 𝔭.asIdeal.height ≤ 1) :
    IsFiniteLength (Localization.AtPrime 𝔭.asIdeal) (LocalizedModule 𝔭.asIdeal.primeCompl M) := by
  have : Ring.KrullDimLE 1 (Localization.AtPrime 𝔭.asIdeal) := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭.asIdeal]
    exact_mod_cast h𝔭
  -- A non-zero-divisor `s` kills `M`, and its image kills the localization.
  obtain ⟨s, hsM, hs⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hM
  rw [SetLike.mem_coe, Submodule.annihilator_top] at hsM
  refine TauCeti.isFiniteLength_of_nonZeroDivisor_mem_annihilator
    (IsLocalizedModule.map_annihilator_le 𝔭.asIdeal.primeCompl _
      (LocalizedModule.mkLinearMap 𝔭.asIdeal.primeCompl M) (Ideal.mem_map_of_mem _ hsM)) ?_
  exact IsLocalization.map_nonZeroDivisors_le 𝔭.asIdeal.primeCompl _
    (Submonoid.mem_map_of_mem _ hs)

end Module.IsTorsion

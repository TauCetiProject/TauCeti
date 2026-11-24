/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Nagata's openness criterion

A generalization-stable subset of a Noetherian prime spectrum is open if every point in the
subset has a principal neighbourhood within its closure contained in the subset.

## References

* Matsumura, *Commutative Ring Theory*, Theorem 24.2.
-/

public section

namespace Ideal

variable {S : Type*} [CommSemiring S]

/-- Nagata's openness criterion: a generalization-stable predicate with principal
neighbourhoods in each prime's closure holds on a principal neighbourhood of every good prime.
See Matsumura, *Commutative Ring Theory*, Theorem 24.2. -/
theorem exists_notMem_forall_of_noetherian [IsNoetherianRing S] (P : Ideal S → Prop)
    (hgen : ∀ q q' : Ideal S, q.IsPrime → q'.IsPrime → q' ≤ q → P q → P q')
    (hrel : ∀ q : Ideal S, q.IsPrime → P q → ∃ a ∉ q,
      ∀ q' : Ideal S, q'.IsPrime → q ≤ q' → a ∉ q' → P q')
    (q : Ideal S) [q.IsPrime] (hq : P q) :
    ∃ a ∉ q, ∀ q' : Ideal S, q'.IsPrime → a ∉ q' → P q' := by
  classical
  let I : Ideal S := sInf {q : Ideal S | q.IsPrime ∧ ¬ P q}
  have hI (q' : Ideal S) (hq' : q'.IsPrime) (hP : ¬ P q') : I ≤ q' := sInf_le ⟨hq', hP⟩
  have hmin : ∀ q₀ ∈ I.minimalPrimes, ¬ P q₀ := by
    intro q₀ hq₀ hP
    have hq₀p : q₀.IsPrime := hq₀.1.1
    obtain ⟨a, ha, hPa⟩ := hrel q₀ hq₀p hP
    have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing S I
    let others := hfin.toFinset.erase q₀
    have hnot : ¬ others.inf id ≤ q₀ := by
      intro hle
      obtain ⟨q₁, hq₁, hq₁le⟩ :=
        (Ideal.IsPrime.inf_le' (s := others) (f := id) hq₀p).mp hle
      obtain ⟨hne, hq₁m⟩ := Finset.mem_erase.mp hq₁
      rw [Set.Finite.mem_toFinset] at hq₁m
      exact hne (le_antisymm hq₁le (hq₀.2 hq₁m.1 hq₁le))
    obtain ⟨b, hb, hbq₀⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
    have hab : a * b ∉ I := fun h ↦
      (hq₀p.mul_mem_iff_mem_or_mem.mp (hq₀.1.2 h)).elim ha hbq₀
    have hbad : ¬ ∀ q' ∈ {q' : Ideal S | q'.IsPrime ∧ ¬ P q'}, a * b ∈ q' :=
      fun h ↦ hab (Submodule.mem_sInf.mpr h)
    push Not at hbad
    obtain ⟨q', ⟨hq'p, hq'P⟩, hq'⟩ := hbad
    obtain ⟨q₁, hq₁, hq₁le⟩ := Ideal.exists_minimalPrimes_le (hI q' hq'p hq'P)
    have hbq' : b ∉ q' := fun h ↦ hq' (q'.mul_mem_left _ h)
    have hq₁eq : q₁ = q₀ := by
      by_contra hne
      have hq₁o : q₁ ∈ others :=
        Finset.mem_erase.mpr ⟨hne, (Set.Finite.mem_toFinset _).mpr hq₁⟩
      exact hbq' (hq₁le (Finset.inf_le (f := id) hq₁o hb))
    subst hq₁eq
    exact hq'P (hPa q' hq'p hq₁le fun h ↦ hq' (q'.mul_mem_right _ h))
  have hbad (q' : Ideal S) (hq' : q'.IsPrime) (hIq' : I ≤ q') : ¬ P q' := by
    intro hP
    obtain ⟨q₀, hq₀, hq₀le⟩ := Ideal.exists_minimalPrimes_le hIq'
    exact hmin q₀ hq₀ (hgen q' q₀ hq' hq₀.1.1 hq₀le hP)
  obtain ⟨a, haI, haq⟩ := IsConcreteLE.not_le_iff_exists.mp fun hle ↦ hbad q inferInstance hle hq
  refine ⟨a, haq, fun q' hq' haq' ↦ ?_⟩
  by_contra hP
  exact haq' (hI q' hq' hP haI)

end Ideal

namespace PrimeSpectrum

variable {S : Type*} [CommSemiring S] [IsNoetherianRing S]

/-- Nagata's openness criterion for subsets of a Noetherian prime spectrum. -/
theorem isOpen_of_stableUnderGeneralization_of_exists_notMem
    {s : Set (PrimeSpectrum S)} (hgen : StableUnderGeneralization s)
    (hrel : ∀ q ∈ s, ∃ a ∉ q.asIdeal,
      ∀ q' : PrimeSpectrum S, q.asIdeal ≤ q'.asIdeal → a ∉ q'.asIdeal → q' ∈ s) :
    IsOpen s := by
  rw [isOpen_iff_forall_mem_open]
  intro q hq
  obtain ⟨a, ha, hsub⟩ := Ideal.exists_notMem_forall_of_noetherian
    (fun I ↦ ∀ hI : I.IsPrime, (⟨I, hI⟩ : PrimeSpectrum S) ∈ s)
    (fun I J hI hJ hle hmem _ ↦ hgen ((le_iff_specializes ⟨J, hJ⟩ ⟨I, hI⟩).mp hle) (hmem hI))
    (fun I hI hmem ↦ by
      obtain ⟨a, ha, h⟩ := hrel ⟨I, hI⟩ (hmem hI)
      exact ⟨a, ha, fun J hJ hle haJ _ ↦ h ⟨J, hJ⟩ hle haJ⟩) q.asIdeal (fun _ ↦ hq)
  exact ⟨basicOpen a, fun q' hq' ↦ hsub q'.asIdeal q'.isPrime hq' q'.isPrime, isOpen_basicOpen, ha⟩

end PrimeSpectrum

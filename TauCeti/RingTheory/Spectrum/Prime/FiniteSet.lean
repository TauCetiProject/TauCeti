/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Basic open neighborhoods of finite sets

Prime avoidance puts a finite subset of an open in a single basic open contained in it.
-/

public section

namespace PrimeSpectrum

/-- A finite set in an open subset of an affine spectrum lies in a single basic open
contained in that open subset. -/
theorem exists_basicOpen_le_of_finite {R : Type*} [CommRing R]
    {O : Set (PrimeSpectrum R)} (hO : IsOpen O) {t : Set (PrimeSpectrum R)} (ht : t.Finite)
    (htO : t ⊆ O) :
    ∃ r : R, t ⊆ basicOpen r ∧ (basicOpen r : Set _) ⊆ O := by
  obtain ⟨J, hJ⟩ := (isClosed_iff_zeroLocus_ideal Oᶜ).mp hO.isClosed_compl
  have hJt : ¬ (J : Set R) ⊆ ⋃ I ∈ asIdeal '' t, ((id I : Ideal R) : Set R) := by
    rw [Ideal.subset_union_prime_finite (ht.image _) (f := id) ⊥ ⊥
      (by grind [PrimeSpectrum.isPrime])]
    rintro ⟨_, ⟨p, hp, rfl⟩, hle⟩
    have : p ∈ Oᶜ := hJ ▸ (mem_zeroLocus _ _).mpr hle
    exact this (htO hp)
  obtain ⟨r, hrJ, hr⟩ := Set.not_subset.mp hJt
  refine ⟨r, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · simp only [Set.mem_iUnion, Set.mem_image, id] at hr
    exact (mem_basicOpen _ _).mpr fun h ↦ hr ⟨_, ⟨p, hp, rfl⟩, h⟩
  · by_contra h
    have : p ∈ zeroLocus (J : Set R) := hJ ▸ h
    exact (mem_basicOpen _ _).mp hp (this hrJ)

end PrimeSpectrum

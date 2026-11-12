/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Minimal primes and disjoint basic opens

A generic point of a spectrum corresponds to a minimal prime. Such a point has a basic
open neighbourhood disjoint from any given quasi-compact open that avoids it.

## References

* The Stacks Project, Tags 00ES and 00EV.
-/

public noncomputable section

namespace PrimeSpectrum

variable {R : Type*} [CommSemiring R]

/-- A point of `Spec R` is the generic point of an irreducible component if and only if the
corresponding
prime ideal is a minimal prime of `R`. -/
@[stacks 00ES]
theorem mem_genericPoints_iff {p : PrimeSpectrum R} :
    p ∈ genericPoints (PrimeSpectrum R) ↔ p.asIdeal ∈ minimalPrimes R := by
  change closure ({p} : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R) ↔ _
  rw [closure_singleton, zeroLocus_ideal_mem_irreducibleComponents, p.2.radical]

end PrimeSpectrum

variable {R : Type*} [CommRing R]

/-- If `p` is a minimal prime of `R` and `x ∈ p`, there are `y ∉ p` and `n` with `y * x ^ n = 0`:
the
localization `R_p` is zero-dimensional and local, so the image of `x` in `R_p` is nilpotent. -/
theorem Ideal.exists_notMem_mul_pow_eq_zero_of_mem_minimalPrimes {p : Ideal R}
    (hp : p ∈ minimalPrimes R) {x : R} (hx : x ∈ p) : ∃ y ∉ p, ∃ n : ℕ, y * x ^ n = 0 := by
  have : p.IsPrime := hp.1.1
  have : Ring.KrullDimLE 0 (Localization.AtPrime p) := Ring.KrullDimLE.of_isLocalization p hp _
  obtain ⟨n, hn⟩ : IsNilpotent (algebraMap R (Localization.AtPrime p) x) :=
    Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff _ p x).mpr hx)
  rw [← map_pow] at hn
  obtain ⟨y, hy⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl _ _).mp hn
  exact ⟨y, y.2, n, hy⟩

namespace PrimeSpectrum

/-- A minimal prime `p` of `R` is separated from any quasi-compact open `W` of `Spec R` not
containing
it by a basic open: there is `f ∉ p` with `D(f) ∩ W = ∅`. -/
@[stacks 00EV]
theorem exists_notMem_and_disjoint_basicOpen_of_mem_minimalPrimes {p : PrimeSpectrum R}
    (hp : p.asIdeal ∈ minimalPrimes R) {W : Set (PrimeSpectrum R)} (hW : IsOpen W)
    (hW' : IsCompact W) (hpW : p ∉ W) :
    ∃ f : R, f ∉ p.asIdeal ∧ Disjoint (basicOpen f : Set (PrimeSpectrum R)) W := by
  classical
  obtain ⟨t, rfl⟩ := isCompact_isOpen_iff.mp ⟨hW', hW⟩
  rw [Set.notMem_compl_iff, mem_zeroLocus] at hpW
  choose points hs n hn using fun g : {x // x ∈ t} =>
    Ideal.exists_notMem_mul_pow_eq_zero_of_mem_minimalPrimes hp (hpW g.2)
  refine ⟨∏ g ∈ t.attach, points g, Submonoid.prod_mem p.asIdeal.primeCompl fun g _ ↦ hs g, ?_⟩
  rw [Set.disjoint_compl_right_iff_subset]
  intro otherPrime hq
  rw [mem_zeroLocus]
  intro g hg
  have hsg : points ⟨g, hg⟩ ∉ otherPrime.asIdeal := fun h ↦
    hq (otherPrime.asIdeal.mem_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_attach _ ⟨g, hg⟩)) h)
  exact otherPrime.2.mem_of_pow_mem (n ⟨g, hg⟩)
    ((otherPrime.2.mem_or_mem (hn ⟨g, hg⟩ ▸ otherPrime.asIdeal.zero_mem)).resolve_left hsg)

end PrimeSpectrum

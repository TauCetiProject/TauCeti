/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.LocallyConstant.Basic

import TauCeti.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Discrete logarithms of roots of unity on a prime spectrum

Let `R` be a commutative ring in which `n : ℕ` is a unit, and let `ζ ∈ R` be a root of the `n`-th
cyclotomic polynomial `Polynomial.cyclotomic n R`. If `y ∈ R` satisfies `y ^ n = 1`, then at every
prime `p ∈ PrimeSpectrum R` the residue class of `y` in the domain `R ⧸ p.asIdeal` is a unique
power of `ζ` with exponent `< n`, and this exponent defines a locally constant function
`e : LocallyConstant (PrimeSpectrum R) ℕ` satisfying `e p < n` and `y - ζ ^ e p ∈ p.asIdeal` for
every prime `p` (`PrimeSpectrum.exists_locallyConstant_sub_pow_mem_of_pow_eq_one`).

## Main results

* `PrimeSpectrum.exists_locallyConstant_sub_pow_mem_of_pow_eq_one`: an `n`-th root of unity `y` in
  `R` agrees modulo every prime `p` with `ζ ^ e p` for a locally constant exponent `e` with
  `e p < n`.

## Provenance

Generalized from `grh-lean` (https://github.com/lsernau/grh-lean at commit
72fead102f663d5c7a407964a13dc0cf9d977207, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Cohomology/ProperBaseChange/LineCharts.lean`
(`exists_locallyConstant_sub_pow_mem_of_pow_eq_one`).
-/

public section

universe u

/-- Let `n` be a unit in a commutative ring `R` and `ζ ∈ R` a root of the `n`-th cyclotomic
polynomial. For every `y ∈ R` with `y ^ n = 1`, there is a locally constant function
`e : LocallyConstant (PrimeSpectrum R) ℕ` such that `e p < n` and `y - ζ ^ e p ∈ p.asIdeal` for
every prime `p`. -/
theorem PrimeSpectrum.exists_locallyConstant_sub_pow_mem_of_pow_eq_one {R : Type u} [CommRing R]
    {n : ℕ} (hn : IsUnit (n : R)) {ζ : R} (hζ : (Polynomial.cyclotomic n R).IsRoot ζ)
    {y : R} (hy : y ^ n = 1) :
    ∃ e : LocallyConstant (PrimeSpectrum R) ℕ,
      ∀ p : PrimeSpectrum R, e p < n ∧ y - ζ ^ e p ∈ p.asIdeal := by
  have h_prim (p : PrimeSpectrum R) : IsPrimitiveRoot (Ideal.Quotient.mk p.asIdeal ζ) n := by
    have : NeZero (n : R ⧸ p.asIdeal) :=
      ⟨by simpa using (hn.map (Ideal.Quotient.mk p.asIdeal)).ne_zero⟩
    exact Polynomial.isPrimitiveRoot_map_of_isRoot_cyclotomic hζ (Ideal.Quotient.mk p.asIdeal)
  have h_exists (p : PrimeSpectrum R) :
      ∃ i < n, Ideal.Quotient.mk p.asIdeal ζ ^ i = Ideal.Quotient.mk p.asIdeal y := by
    have : NeZero n := ⟨fun h0 ↦ by
      have hne : (n : R ⧸ p.asIdeal) ≠ 0 := by
        simpa using (hn.map (Ideal.Quotient.mk p.asIdeal)).ne_zero
      exact hne (by simp [h0])⟩
    exact (h_prim p).eq_pow_of_pow_eq_one (by rw [← map_pow, hy, map_one])
  choose e h_lt he using h_exists
  refine ⟨⟨e, fun s ↦ ?_⟩, fun p ↦ ⟨h_lt p, Ideal.Quotient.eq.mp (he p).symm⟩⟩
  have h_eq : e ⁻¹' s = ⋂ i ∈ sᶜ ∩ Set.Iio n, (basicOpen (y - ζ ^ i)).carrier := by
    ext p
    simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_Iio,
      TopologicalSpace.Opens.carrier_eq_coe, SetLike.mem_coe, mem_basicOpen,
      ← Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← he, map_pow]
    exact ⟨fun hp i hi h_pow ↦ hi.1 (by rwa [← (h_prim p).pow_inj (h_lt p) hi.2 h_pow]),
      fun h ↦ by_contra fun hp ↦ h (e p) ⟨hp, h_lt p⟩ rfl⟩
  rw [h_eq]
  exact ((Set.finite_Iio n).inter_of_right _).isOpen_biInter fun i _ ↦ isOpen_basicOpen

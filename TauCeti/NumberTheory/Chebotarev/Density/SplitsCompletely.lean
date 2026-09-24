/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.Contraction
public import TauCeti.NumberTheory.Chebotarev.SplitsCompletely

/-!
# The completely split primes have density `1 / [L : K]`

Let `L / K` be a finite Galois extension of number fields. The primes of `𝓞 K` that split
completely in `L` — the identity fibre `frobeniusPrimeSet K L 1` of the Artin class — have
Dirichlet density `1 / [L : K]`.

## Main results

* `NumberField.Chebotarev.hasDirichletDensity_frobeniusPrimeSet_one`: the completely split primes
  have Dirichlet density `1 / [L : K]`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
-/

public section

open IsDedekindDomain (HeightOneSpectrum)

open NumberField

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

private theorem under_mem_frobeniusPrimeSet_one_of_inertiaDeg_eq_one {𝔓 : HeightOneSpectrum (𝓞 L)}
    (hdeg : 𝔓.asIdeal.inertiaDeg (𝓞 K) = 1) (hram : 𝔓.under (𝓞 K) ∉ ramifiedPrimes K L) :
    𝔓.under (𝓞 K) ∈ frobeniusPrimeSet K L 1 := by
  have : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 K)).asIdeal := ⟨HeightOneSpectrum.under_asIdeal _ 𝔓⟩
  rw [mem_ramifiedPrimes_iff, not_not] at hram
  exact (mem_frobeniusPrimeSet_one_iff_inertiaDeg_eq_one hram 𝔓.asIdeal).mpr hdeg

private theorem card_inertiaDeg_eq_one_fiber_of_mem_frobeniusPrimeSet_one
    {𝔭 : HeightOneSpectrum (𝓞 K)} (h𝔭 : 𝔭 ∈ frobeniusPrimeSet K L 1) :
    Nat.card {𝔓 : HeightOneSpectrum (𝓞 L) // 𝔓.under (𝓞 K) = 𝔭 ∧ 𝔓.asIdeal.inertiaDeg (𝓞 K) = 1} =
      Module.finrank K L := by
  -- Over a completely split prime every prime above has residue degree one, and there are
  -- `[L : K]` of them.
  have hdiv (𝔓 : HeightOneSpectrum (𝓞 L)) :
      (𝔓.under (𝓞 K) = 𝔭 ∧ 𝔓.asIdeal.inertiaDeg (𝓞 K) = 1) ↔
        𝔓.asIdeal ∣ Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔭.asIdeal := by
    rw [← Ideal.liesOver_iff_dvd_map 𝔓.isPrime.ne_top]
    refine ⟨fun h ↦ ⟨(congrArg HeightOneSpectrum.asIdeal h.1).symm⟩, fun h ↦ ?_⟩
    obtain rfl : 𝔓.under (𝓞 K) = 𝔭 := HeightOneSpectrum.ext h.over.symm
    exact ⟨rfl, inertiaDeg_eq_one_of_mem_frobeniusPrimeSet_one h𝔭 𝔓.asIdeal⟩
  rw [Nat.card_congr ((Equiv.subtypeEquivRight hdiv).trans
    (HeightOneSpectrum.equivPrimesOver (𝓞 L) 𝔭.ne_bot)), Nat.card_coe_set_eq]
  exact mem_frobeniusPrimeSet_one_iff_ncard_primesOver_eq_finrank.mp h𝔭

variable (K L) in
/-- **The completely split primes have density `1 / [L : K]`.** The primes of `𝓞 K` that split
completely in the finite Galois extension `L` have Dirichlet density `1 / [L : K]`. The
Chebotarev density theorem gives the same density as `1 / #Gal(L/K)`
(`hasDirichletDensity_splitCompletely`). -/
theorem hasDirichletDensity_frobeniusPrimeSet_one :
    (frobeniusPrimeSet K L 1).HasDirichletDensity (1 / Module.finrank K L) :=
  -- Contract all the primes of `𝓞 L`, which have density one: away from the ramified primes, a
  -- prime of residue degree one over `K` lies over a completely split prime, and each completely
  -- split prime has `[L : K]` primes above it.
  (Set.hasDirichletDensity_contraction (T := Set.univ)
    (Set.hasDirichletDensity_of_finite (K := K) (ramifiedPrimes K L).finite_toSet)
    (fun _ _ ↦ under_mem_frobeniusPrimeSet_one_of_inertiaDeg_eq_one) Module.finrank_pos.ne'
    fun _ h𝔭 ↦ by simpa using card_inertiaDeg_eq_one_fiber_of_mem_frobeniusPrimeSet_one h𝔭.1).mp
      Set.hasDirichletDensity_univ

end NumberField.Chebotarev

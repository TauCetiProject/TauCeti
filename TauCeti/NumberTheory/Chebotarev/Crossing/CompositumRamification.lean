/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.RamifiedPrimes
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification

/-!
# The ramified primes of a cyclotomic compositum

Let `K ⊆ L ⊆ M` be a tower of number fields. A prime of `K` ramifying in `L` ramifies in `M`: an
unramified prime of `𝓞 M` lies over an unramified prime of `𝓞 L`. When `M = L(μ_m)` is an `m`-th
cyclotomic extension of `L`, a partial converse holds: every prime of `K` that ramifies in `M` but
not in `L` divides `m`. Away from `m` the two ramified sets therefore agree.

This is the ramification half of the compositum step in the cyclotomic crossing for the
Chebotarev density theorem. The Frobenius compatibility of the compositum,
`NumberField.Chebotarev.mem_frobeniusPrimeSet_galEquivProd_symm_iff`, is stated for primes
unramified in `M` and prime to `m`; `notMem_ramifiedPrimes_iff_of_natCast_notMem` turns the first
hypothesis into unramifiedness in `L`, so the primes discarded on passing from `L` to `M` all lie
above `m` and form a finite set.

## Main results

* `NumberField.Chebotarev.mem_ramifiedPrimes_of_mem_ramifiedPrimes_of_natCast_notMem`: for
  `M = L(μ_m)`, a prime of `K` ramifying in `M` and not dividing `m` ramifies in `L`.
* `NumberField.Chebotarev.ramifiedPrimes_subset_ramifiedPrimes_union_natCast_mem`: the same
  statement as an inclusion of sets,
  `ramifiedPrimes K M ⊆ ramifiedPrimes K L ∪ {𝔭 | (m : 𝓞 K) ∈ 𝔭}`.
* `NumberField.Chebotarev.mem_ramifiedPrimes_iff_of_natCast_notMem` and
  `NumberField.Chebotarev.notMem_ramifiedPrimes_iff_of_natCast_notMem`: away from `m`, ramifying in
  `M` and ramifying in `L` are equivalent.

## References

* R. Sharifi, *Algebraic Number Theory*, the proof of Theorem 7.2.2, where the auxiliary
  cyclotomic compositum adds ramification only above the auxiliary prime.
-/

public section

open scoped NumberField

open IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

variable (m : ℕ) [IsCyclotomicExtension {m} L M]

/-- **A cyclotomic compositum ramifies newly only above the level.** Let `M = L(μ_m)` for a tower
`K ⊆ L ⊆ M` of number fields. A prime `𝔭` of `K` that ramifies in `M` and does not divide `m`
already ramifies in `L`. -/
theorem mem_ramifiedPrimes_of_mem_ramifiedPrimes_of_natCast_notMem {𝔭 : HeightOneSpectrum (𝓞 K)}
    (h𝔭 : 𝔭 ∈ ramifiedPrimes K M) (hm : (m : 𝓞 K) ∉ 𝔭.asIdeal) : 𝔭 ∈ ramifiedPrimes K L := by
  rw [mem_ramifiedPrimes_iff] at h𝔭 ⊢
  simp only [not_forall] at h𝔭 ⊢
  obtain ⟨Q, _, _, hQ⟩ := h𝔭
  -- `Q` is ramified over `𝓞 K`, so it divides one of the two factors of the tower different.
  have hdvd : Q ∣ differentIdeal (𝓞 K) (𝓞 M) := dvd_differentIdeal_iff.mpr hQ
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal (𝓞 K) (𝓞 L) (𝓞 M)] at hdvd
  have hQprime : Prime Q :=
    Ideal.prime_of_isPrime (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q) ‹_›
  rcases hQprime.dvd_or_dvd hdvd with hML | hLK
  · -- The factor `𝔡(M/L)` contains `m`, which would put `m` in `𝔭`.
    refine absurd ?_ hm
    have hmQ : (m : 𝓞 M) ∈ Q :=
      Ideal.le_of_dvd hML (IsCyclotomicExtension.natCast_mem_differentIdeal L M m)
    rw [Ideal.LiesOver.over (P := Q) (p := 𝔭.asIdeal), Ideal.mem_comap]
    simpa using hmQ
  · -- The prime of `𝓞 L` below `Q` divides `𝔡(L/K)`, so it is ramified over `𝓞 K`.
    set P : Ideal (𝓞 L) := Q.under (𝓞 L)
    have : P.LiesOver 𝔭.asIdeal := Ideal.LiesOver.tower_bot Q P 𝔭.asIdeal
    have hP : P ∣ differentIdeal (𝓞 K) (𝓞 L) := by
      rw [Ideal.dvd_iff_le] at hLK ⊢
      exact Ideal.map_le_iff_le_comap.mp hLK
    exact ⟨P, inferInstance, this, dvd_differentIdeal_iff.mp hP⟩

/-- **The ramified primes of a cyclotomic compositum.** For `M = L(μ_m)` over a tower
`K ⊆ L ⊆ M` of number fields, a prime of `K` ramifying in `M` ramifies in `L` or divides `m`. -/
theorem ramifiedPrimes_subset_ramifiedPrimes_union_natCast_mem :
    (ramifiedPrimes K M : Set (HeightOneSpectrum (𝓞 K))) ⊆
      ramifiedPrimes K L ∪ {𝔭 | (m : 𝓞 K) ∈ 𝔭.asIdeal} := by
  intro 𝔭 h𝔭
  by_cases hm : (m : 𝓞 K) ∈ 𝔭.asIdeal
  · exact Or.inr hm
  · exact Or.inl (mem_ramifiedPrimes_of_mem_ramifiedPrimes_of_natCast_notMem m h𝔭 hm)

/-- **Away from the level, a cyclotomic compositum ramifies exactly where its base does.** For
`M = L(μ_m)` over a tower `K ⊆ L ⊆ M` of number fields and a prime `𝔭` of `K` not dividing `m`,
`𝔭` ramifies in `M` if and only if it ramifies in `L`. -/
-- This is not a simp lemma: `mem_ramifiedPrimes_iff` already normalizes its left-hand side, and
-- neither the intermediate field `L` nor the level `m` can be inferred from that side alone.
theorem mem_ramifiedPrimes_iff_of_natCast_notMem {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hm : (m : 𝓞 K) ∉ 𝔭.asIdeal) : 𝔭 ∈ ramifiedPrimes K M ↔ 𝔭 ∈ ramifiedPrimes K L :=
  ⟨fun h ↦ mem_ramifiedPrimes_of_mem_ramifiedPrimes_of_natCast_notMem m h hm,
    fun h ↦ ramifiedPrimes_subset_ramifiedPrimes h⟩

/-- The negated form of `mem_ramifiedPrimes_iff_of_natCast_notMem`: away from `m`, a prime of `K`
is unramified in `M = L(μ_m)` if and only if it is unramified in `L`. This is the form in which
the unramifiedness hypothesis of the compositum's Frobenius compatibility is discharged. -/
theorem notMem_ramifiedPrimes_iff_of_natCast_notMem {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hm : (m : 𝓞 K) ∉ 𝔭.asIdeal) : 𝔭 ∉ ramifiedPrimes K M ↔ 𝔭 ∉ ramifiedPrimes K L :=
  (mem_ramifiedPrimes_iff_of_natCast_notMem m hm).not

end NumberField.Chebotarev

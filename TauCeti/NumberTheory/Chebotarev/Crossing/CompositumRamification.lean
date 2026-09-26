/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.RamifiedPrimes
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

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

* `NumberField.Chebotarev.mem_ramifiedPrimes_of_natCast_mem`: over `ℚ`, a prime dividing the
  level ramifies, provided that a prime of norm two divides the level to at least the second power.

## References

* L. Washington, *Introduction to Cyclotomic Fields*, Chapter 2.
* `IsCyclotomicExtension.Rat.ramificationIdx_eq` in
  `Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal` supplies the ramification-index formula
  used by `mem_ramifiedPrimes_of_natCast_mem`.
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

/-- Every prime dividing a cyclotomic level ramifies, provided the level is divisible by four
when the prime has norm two. -/
theorem mem_ramifiedPrimes_of_natCast_mem (F : Type*) [Field F] [NumberField F]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F] {𝔭 : HeightOneSpectrum (𝓞 ℚ)}
    (hn : Ideal.absNorm 𝔭.asIdeal = 2 → 4 ∣ n) (hm : (n : 𝓞 ℚ) ∈ 𝔭.asIdeal) :
    𝔭 ∈ ramifiedPrimes ℚ F := by
  let p := Ideal.absNorm 𝔭.asIdeal
  have hp : p.Prime := by
    simpa [p, Rat.HeightOneSpectrum.absNorm_asIdeal] using
      Rat.HeightOneSpectrum.prime_natGenerator 𝔭
  have : Fact p.Prime := ⟨hp⟩
  have hpn : p ∣ n := (Rat.HeightOneSpectrum.absNorm_asIdeal_dvd_iff_natCast_mem 𝔭).mpr hm
  obtain ⟨e, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne n) p hp.ne_one
  cases e with
  | zero => simp_all
  | succ e =>
    rw [mem_ramifiedPrimes_iff]
    intro hur
    let Q : 𝔭.asIdeal.primesOver (𝓞 F) := Classical.choice inferInstance
    have : Q.1.IsPrime := Q.2.1
    have : Q.1.LiesOver 𝔭.asIdeal := Q.2.2
    have hpQ : (p : 𝓞 F) ∈ Q.1 := by
      have hp𝔭 : (p : 𝓞 ℚ) ∈ 𝔭.asIdeal :=
        (Rat.HeightOneSpectrum.absNorm_asIdeal_dvd_iff_natCast_mem 𝔭).mp dvd_rfl
      simpa using (Ideal.mem_of_liesOver Q.1 𝔭.asIdeal (p : 𝓞 ℚ)).mp hp𝔭
    have : Q.1.LiesOver (Ideal.span {(p : ℤ)}) := by
      rw [Ideal.liesOver_iff]
      refine Ideal.IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime p)
        Ideal.IsPrime.ne_top' ?_
      simpa [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap] using hpQ
    have := hur Q.1
    have he := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 ℚ) (p := Q.1)
    rw [Ideal.ramificationIdx_ringOfIntegers_rat_eq_int Q.1
      (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q.1),
      IsCyclotomicExtension.Rat.ramificationIdx_eq n F Q.1 hnm hpm] at he
    have hp2 : p = 2 := by
      have := Nat.eq_one_of_mul_eq_one_left he
      have := hp.two_le
      omega
    have hfour := hn hp2
    rw [hp2] at he hnm hpm
    have he0 : e = 0 := by
      have := Nat.eq_one_of_mul_eq_one_right he
      simpa using this
    subst e
    simp only [zero_add, pow_one] at hnm
    omega

end NumberField.Chebotarev

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.RamificationInertia.Inertia
import TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds
import TauCeti.NumberTheory.NumberField.PrimeIdeal

/-!
# The number of ideals of a given norm

In a number field `K` of degree `d = [K : ℚ]`, the number `dedekindZetaCoeff K n` of integral
ideals of `𝓞 K` of absolute norm `n` is at most `d ^ Ω n`, where `Ω n` counts the prime factors of
`n` with multiplicity; for `n ≠ 0` this is at most `n ^ log₂ d`. The same bound holds for the
finset `normFiber K n` of nonzero ideals of norm `n`, which for `n ≠ 0` has
`dedekindZetaCoeff K n` members (`TauCeti.card_normFiber_eq_dedekindZetaCoeff`).

The proof is an induction on `n`. For `n ≥ 2` let `p` be a prime factor of `n`. An ideal of norm
`n` has a prime factor `P` above `p` (Mathlib's `Ideal.exists_isMaximal_dvd_of_dvd_absNorm'`), so
it is `P * J` with `absNorm P * absNorm J = n`. There are at most `d` primes above `p`
(`TauCeti.NumberField.card_primesOverFinset_le_finrank`), and `absNorm P` is a power `p ^ f` with
`f ≥ 1`, so `Ω (absNorm J) ≤ Ω n - 1`; hence the count is at most `d · d ^ (Ω n - 1)`. The power
form follows from `ArithmeticFunction.pow_cardFactors_le_rpow_logb`, that is, from
`2 ^ Ω n ≤ n`.

## Main results

* `TauCeti.dedekindZetaCoeff_le_finrank_pow_cardFactors`: `dedekindZetaCoeff K n ≤ d ^ Ω n`
  for every `n : ℕ`.
* `TauCeti.card_normFiber_le_finrank_pow_cardFactors`: `(normFiber K n).card ≤ d ^ Ω n` for every
  `n : ℕ`.
* `TauCeti.dedekindZetaCoeff_le_rpow_logb_finrank`: for `n ≠ 0`,
  `dedekindZetaCoeff K n ≤ n ^ log₂ d`, with the real exponent `Real.logb 2 d`.

These bounds on a single norm fibre complement `NumberField.card_ideal_absNorm_le` (in
`TauCeti/NumberTheory/EffectiveBounds/IdealCount/Basic.lean`), which bounds the number of ideals
of norm at most `X`, and `TauCeti.card_normFiber_isBigO`, the non-explicit linear bound on a fibre.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, Proposition 8.2: the fundamental identity
  `∑ eᵢ fᵢ = d`, which bounds the number of primes above a rational prime by `d`.
-/

public section

open Module Ideal ArithmeticFunction
open scoped NumberField ArithmeticFunction.Omega

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- At most one ideal has absolute norm `0` (namely `⊥`), and at most one has norm `1` (`⊤`). -/
private theorem ncard_setOf_absNorm_eq_le_one {n : ℕ} (hn : n ≤ 1) :
    {I : Ideal (𝓞 K) | absNorm I = n}.ncard ≤ 1 := by
  refine (Set.ncard_le_one (Ring.HasFiniteQuotients.finite_absNorm_eq n)).mpr fun I hI J hJ ↦ ?_
  interval_cases n <;> simp_all [absNorm_eq_zero_iff, absNorm_eq_one_iff]

/-- Every ideal of norm `n` is `P * J` for a prime `P` above a prime `p ∣ n`, so the ideals of norm
`n` number at most the sum over such `P` of the number of `J` with `absNorm P * absNorm J = n`. -/
private theorem ncard_setOf_absNorm_eq_le_sum {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    {I : Ideal (𝓞 K) | absNorm I = n}.ncard ≤
      ∑ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K),
        {J : Ideal (𝓞 K) | absNorm P * absNorm J = n}.ncard := by
  have hp0 : span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  have : Fact p.Prime := ⟨hp⟩
  have hsub : {I : Ideal (𝓞 K) | absNorm I = n} ⊆
      ⋃ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K),
        (P * ·) '' {J : Ideal (𝓞 K) | absNorm P * absNorm J = n} := by
    intro I hI
    simp only [Set.mem_ofPred_eq] at hI
    obtain ⟨P, hPmax, hPp, J, rfl⟩ := exists_isMaximal_dvd_of_dvd_absNorm' hp I (by rwa [hI])
    have hP : P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K) :=
      (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mpr ⟨hPmax.isPrime, ⟨hPp.symm⟩⟩
    exact Set.mem_biUnion hP ⟨J, by simpa [map_mul] using hI, rfl⟩
  have hfin : (⋃ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K),
      (P * ·) '' {J : Ideal (𝓞 K) | absNorm P * absNorm J = n}).Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_eq n).subset <| by
      simp only [Set.iUnion_subset_iff, Set.image_subset_iff]
      exact fun P _ J hJ ↦ by simpa [map_mul] using hJ
  refine (Set.ncard_le_ncard hsub hfin).trans ((Finset.set_ncard_biUnion_le _ _).trans ?_)
  refine Finset.sum_le_sum fun P hP ↦ (Set.ncard_image_of_injective _ ?_).le
  obtain ⟨_, _⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hP
  exact mul_right_injective₀ (ne_bot_of_liesOver_of_ne_bot hp0 P)

/-- The ideals of `𝓞 K` of absolute norm `n` number at most `[K : ℚ] ^ Ω n`. -/
private theorem ncard_setOf_absNorm_eq_le (n : ℕ) :
    {I : Ideal (𝓞 K) | absNorm I = n}.ncard ≤ finrank ℚ K ^ Ω n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases le_or_gt n 1 with hn | hn
  · rw [cardFactors_eq_zero_iff_eq_zero_or_one.mpr (by omega), pow_zero]
    exact ncard_setOf_absNorm_eq_le_one hn
  -- For `1 < a`, the ideals `J` with `a * absNorm J = n` number at most `[K : ℚ] ^ (Ω n - 1)`.
  have hstep (a : ℕ) (ha : 1 < a) :
      {J : Ideal (𝓞 K) | a * absNorm J = n}.ncard ≤ finrank ℚ K ^ (Ω n - 1) := by
    by_cases hdvd : a ∣ n
    · obtain ⟨k, hk⟩ := hdvd
      have hk0 : k ≠ 0 := by rintro rfl; omega
      have hset : {J : Ideal (𝓞 K) | a * absNorm J = n} = {J | absNorm J = k} := by
        simp [hk, mul_right_inj' (by omega : a ≠ 0)]
      rw [hset]
      refine (ih k (hk ▸ lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hk0) ha)).trans
        (pow_le_pow_right₀ Module.finrank_pos ?_)
      have := cardFactors_pos_iff_one_lt.mpr ha
      rw [hk, cardFactors_mul (by omega) hk0]
      omega
    · have hempty : {J : Ideal (𝓞 K) | a * absNorm J = n} = ∅ :=
        Set.eq_empty_of_forall_notMem fun J hJ ↦ hdvd (Dvd.intro _ hJ)
      simp [hempty]
  have hp := Nat.minFac_prime hn.ne'
  have : Fact n.minFac.Prime := ⟨hp⟩
  have hp0 : span {(n.minFac : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  refine (ncard_setOf_absNorm_eq_le_sum hp (Nat.minFac_dvd n)).trans ?_
  calc _ ≤ ∑ _P ∈ IsDedekindDomain.primesOverFinset (span {(n.minFac : ℤ)}) (𝓞 K),
        finrank ℚ K ^ (Ω n - 1) := by
        refine Finset.sum_le_sum fun P hP ↦ hstep _ ?_
        obtain ⟨_, _⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hP
        rw [← pow_inertiaDeg n.minFac P]
        exact Nat.one_lt_pow (inertiaDeg_pos P ℤ).ne' hp.one_lt
    _ ≤ finrank ℚ K * finrank ℚ K ^ (Ω n - 1) := by
        rw [Finset.sum_const, smul_eq_mul]
        gcongr
        exact NumberField.card_primesOverFinset_le_finrank
    _ = finrank ℚ K ^ Ω n := by
        rw [← pow_succ', Nat.sub_add_cancel (cardFactors_pos_iff_one_lt.mpr hn)]

/-- **The number of ideals of a given norm.** In a number field `K` of degree `d = [K : ℚ]`, the
number `dedekindZetaCoeff K n` of integral ideals of `𝓞 K` of absolute norm `n` is at most
`d ^ Ω n`, where `Ω n` is the number of prime factors of `n` counted with multiplicity. At `n = 0`
both sides are `1`. For `n ≠ 0` the count is `(normFiber K n).card`
(`card_normFiber_eq_dedekindZetaCoeff`); that form is `card_normFiber_le_finrank_pow_cardFactors`.
-/
theorem dedekindZetaCoeff_le_finrank_pow_cardFactors (n : ℕ) :
    dedekindZetaCoeff K n ≤ finrank ℚ K ^ Ω n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [← card_normFiber_eq_dedekindZetaCoeff K hn, ← Set.ncard_coe_finset]
  refine (Set.ncard_le_ncard_of_injOn Subtype.val (fun I hI ↦ ?_) Subtype.val_injective.injOn
    (Ring.HasFiniteQuotients.finite_absNorm_eq n)).trans (ncard_setOf_absNorm_eq_le n)
  simpa using hI

/-- **The number of nonzero ideals of a given norm.** In a number field `K` of degree
`d = [K : ℚ]`, the norm fibre `normFiber K n` of nonzero integral ideals of absolute norm `n` has
at most `d ^ Ω n` members. For `n ≠ 0` this is `dedekindZetaCoeff_le_finrank_pow_cardFactors`
through `card_normFiber_eq_dedekindZetaCoeff`; the fibre at `0` is empty. -/
theorem card_normFiber_le_finrank_pow_cardFactors (n : ℕ) :
    (normFiber K n).card ≤ finrank ℚ K ^ Ω n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [normFiber_zero]
  rw [card_normFiber_eq_dedekindZetaCoeff K hn]
  exact dedekindZetaCoeff_le_finrank_pow_cardFactors n

/-- **The number of ideals of a given norm, power form.** In a number field `K` of degree
`d = [K : ℚ]`, for `n ≠ 0` the number `dedekindZetaCoeff K n` of integral ideals of `𝓞 K` of
absolute norm `n` is at most `n ^ log₂ d`, a real power with exponent `Real.logb 2 d`. -/
theorem dedekindZetaCoeff_le_rpow_logb_finrank {n : ℕ} (hn : n ≠ 0) :
    (dedekindZetaCoeff K n : ℝ) ≤ (n : ℝ) ^ Real.logb 2 (finrank ℚ K) :=
  calc (dedekindZetaCoeff K n : ℝ) ≤ (finrank ℚ K : ℝ) ^ Ω n := by
        exact_mod_cast dedekindZetaCoeff_le_finrank_pow_cardFactors n
    _ ≤ (n : ℝ) ^ Real.logb 2 (finrank ℚ K) :=
        pow_cardFactors_le_rpow_logb (by exact_mod_cast Module.finrank_pos) hn

end TauCeti

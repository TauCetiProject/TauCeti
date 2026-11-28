/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import TauCeti.NumberTheory.ComplexMultiplication.PartnerExponents
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import TauCeti.NumberTheory.LegendreSymbol.NegOne
import TauCeti.NumberTheory.SumPrimePow

/-!
# Local contributions to quadratic prime sums

The von Mangoldt weight with the factor `1 - (n / d)` separates into local sums at the primes.
The local sum at `p` runs over the exponents `I_p`
(`ComplexMultiplication.positivePartnerExponents`) with weight `v(π_p)`
(`ComplexMultiplication.piPrimeValuation`): at `p = d` every positive exponent contributes with
weight `1/2`; at a prime with Legendre symbol `-1` only the odd exponents contribute, with weight
`1`; at a prime with symbol `1` there is no contribution. Multiplication by `2 log p` recovers the
contribution to the original sum. The kernel can depend on the entire prime power, as in a smoothed
prime sum whose cutoff varies with the residue class of that power.

The local normalization and the decomposition are those of `New.Data.localPrimeSum` and
`New.Data.primeSum_eq_sum_localPrimeSum` in lsernau/grh-lean (`72fead1`).
-/

public section

open ArithmeticFunction Finset
open TauCeti.ComplexMultiplication

namespace TauCeti.OneSidedBound

/-- The local sum for the Legendre symbol modulo `d` at a prime `p`, with kernel `f` on prime
powers: `v(π_p) · ∑_{e ∈ I_p} f(p ^ e)`. The prime `d` carries weight `1/2`, and the primes of
symbol `-1` carry weight `1` on odd exponents only. For a kernel supported below a cutoff this is a
finite sum, see `localPrimeSum_eq_sum_Icc_log`; otherwise it uses the usual `tsum` convention at
divergence. -/
noncomputable def localPrimeSum (d : ℕ) [Fact d.Prime] (p : ℕ) (f : ℕ → ℝ) : ℝ :=
  piPrimeValuation d p * ∑' e : positivePartnerExponents d p, f (p ^ (e : ℕ))

/-- The local sum is `v(π_p) · ∑_{e ∈ I_p} f(p ^ e)`. -/
theorem localPrimeSum_def (d : ℕ) [Fact d.Prime] (p : ℕ) (f : ℕ → ℝ) :
    localPrimeSum d p f =
      piPrimeValuation d p * ∑' e : positivePartnerExponents d p, f (p ^ (e : ℕ)) := (rfl)

/-- The local sum as a series over all exponents, cut off by the indicator of `I_p`. -/
theorem localPrimeSum_eq_mul_tsum_indicator (d : ℕ) [Fact d.Prime] (p : ℕ) (f : ℕ → ℝ) :
    localPrimeSum d p f = piPrimeValuation d p *
      ∑' e : ℕ, (positivePartnerExponents d p).indicator (fun e ↦ f (p ^ e)) e := by
  rw [localPrimeSum_def, _root_.tsum_subtype (positivePartnerExponents d p) fun e ↦ f (p ^ e)]

variable {d : ℕ} [Fact d.Prime]

/-- At the ramified prime, every positive exponent contributes with weight `1/2`. -/
@[simp] theorem localPrimeSum_self (f : ℕ → ℝ) :
    localPrimeSum d d f = (1 / 2) * ∑' e : ℕ, if 0 < e then f (d ^ e) else 0 := by
  classical
  simp [localPrimeSum_eq_mul_tsum_indicator, Set.indicator_apply]

/-- At a prime of Legendre symbol `-1`, precisely the odd exponents contribute. -/
@[simp] theorem localPrimeSum_eq_tsum_of_legendreSym_eq_neg_one {p : ℕ}
    (hp : legendreSym d p = -1) (f : ℕ → ℝ) :
    localPrimeSum d p f = ∑' e : ℕ, if Odd e then f (p ^ e) else 0 := by
  have hpd : p ≠ d := ne_of_legendreSym_eq_neg_one hp
  classical
  simp only [localPrimeSum_eq_mul_tsum_indicator, Set.indicator_apply,
    mem_positivePartnerExponents_iff, mem_partnerExponents_iff, piPrimeValuation_of_ne hpd, hpd,
    hp, true_and, false_or, one_mul]
  refine tsum_congr fun e ↦ ?_
  by_cases he : Odd e
  · simp [he, he.pos]
  · simp [he]

/-- The local sum written with the same Legendre weight at each prime power. -/
theorem localPrimeSum_eq_tsum {p : ℕ} (hp : p.Prime) (f : ℕ → ℝ) :
    localPrimeSum d p f = ∑' e : ℕ,
      if 0 < e then ((1 - (legendreSym d (p ^ e : ℕ) : ℝ)) / 2) * f (p ^ e) else 0 := by
  classical
  rw [localPrimeSum_eq_mul_tsum_indicator, ← tsum_mul_left]
  refine tsum_congr fun e ↦ ?_
  simp only [Set.indicator_apply, mem_positivePartnerExponents_iff, mem_partnerExponents_iff,
    piPrimeValuation_def]
  by_cases he : 0 < e
  · have hpow : legendreSym d (p ^ e : ℕ) = legendreSym d p ^ e := by
      simpa only [Nat.cast_pow, legendreSym.hom_apply] using map_pow (legendreSym.hom d) (p : ℤ) e
    rw [ite_eq_left he, hpow]
    by_cases hpd : p = d
    · subst p
      have hz : legendreSym d (d : ℕ) = 0 := by simp [legendreSym]
      simp [he, hz, he.ne']
    have hpz : (p : ZMod d) ≠ 0 := fun h ↦ hpd
      ((Nat.prime_dvd_prime_iff_eq Fact.out hp).mp ((ZMod.natCast_eq_zero_iff p d).mp h)).symm
    have hpz' : ((p : ℤ) : ZMod d) ≠ 0 := by exact_mod_cast hpz
    rcases legendreSym.eq_one_or_neg_one d hpz' with h | h
    · simp [he, hpd, h]
    · rcases Nat.even_or_odd e with hpar | hpar
      · simp [he, hpd, h, hpar.neg_one_pow, Nat.not_odd_iff_even.mpr hpar]
      · simp [he, hpd, h, hpar.neg_one_pow, hpar]
  · simp [he]

/-- The local sum vanishes at a prime of Legendre symbol `1`, regardless of the kernel. -/
@[simp] theorem localPrimeSum_eq_zero_of_legendreSym_eq_one {p : ℕ}
    (hp : legendreSym d p = 1) (f : ℕ → ℝ) : localPrimeSum d p f = 0 := by
  have hpd : p ≠ d := by
    intro h
    subst p
    simp [legendreSym] at hp
  rw [localPrimeSum_def,
    positivePartnerExponents_of_ne_of_legendreSym_ne_neg_one hpd (by rw [hp]; decide), tsum_empty,
    mul_zero]

/-- A nonnegative kernel on the positive powers of `p` gives a nonnegative local sum. -/
theorem localPrimeSum_nonneg {p : ℕ} {f : ℕ → ℝ} (hf : ∀ e : ℕ, 0 < e → 0 ≤ f (p ^ e)) :
    0 ≤ localPrimeSum d p f := by
  rw [localPrimeSum_def]
  exact mul_nonneg piPrimeValuation_pos.le
    (tsum_nonneg fun e ↦ hf e (mem_positivePartnerExponents_iff.mp e.property).2)

/-- A cutoff on the kernel gives an explicit finite range of exponents for the local sum. -/
theorem localPrimeSum_eq_sum_Icc_log {p N : ℕ} (hp : p.Prime) {f : ℕ → ℝ}
    (hf : ∀ e : ℕ, 0 < e → N < p ^ e → f (p ^ e) = 0) :
    localPrimeSum d p f = ∑ e ∈ Icc 1 (Nat.log p N),
      ((1 - (legendreSym d (p ^ e : ℕ) : ℝ)) / 2) * f (p ^ e) := by
  rw [localPrimeSum_eq_tsum hp]
  refine (tsum_eq_sum (s := Icc 1 (Nat.log p N)) fun e he ↦ ?_).trans
    (sum_congr rfl fun e he ↦ ite_eq_left (mem_Icc.mp he).1)
  by_cases he₀ : 0 < e
  · have hN : N < p ^ e := lt_of_not_ge fun h ↦ he
      (mem_Icc.mpr ⟨he₀, Nat.le_log_of_pow_le hp.one_lt h⟩)
    simp [hf e he₀ hN]
  · simp [he₀]

/-- No prime greater than the cutoff contributes. -/
theorem localPrimeSum_eq_zero_of_lt_prime {p N : ℕ} (hNp : N < p)
    {f : ℕ → ℝ} (hf : ∀ e : ℕ, 0 < e → N < p ^ e → f (p ^ e) = 0) :
    localPrimeSum d p f = 0 := by
  have hzero (e : positivePartnerExponents d p) : f (p ^ (e : ℕ)) = 0 := by
    have he := (mem_positivePartnerExponents_iff.mp e.property).2
    exact hf e he (hNp.trans_le (le_self_pow₀ (by omega) he.ne'))
  rw [localPrimeSum_def, tsum_congr hzero, tsum_zero, mul_zero]

/-- The weighted von Mangoldt sum is the sum of `2 log p` times the local contributions.
If the kernel vanishes at prime powers beyond `N`, the original cutoff `A` can be larger
than `N`, and the local sums require no separate truncation. -/
theorem sum_vonMangoldt_mul_one_sub_legendreSym_eq_sum_localPrimeSum (d : ℕ) [Fact d.Prime]
    {N A : ℕ} (hNA : N ≤ A) {f : ℕ → ℝ} (hf : ∀ n > N, IsPrimePow n → f n = 0) :
    ∑ n ∈ Icc 1 A, vonMangoldt n * (1 - (legendreSym d n : ℝ)) * f n =
      ∑ p ∈ Nat.primesLE N, (2 * Real.log p) * localPrimeSum d p f := by
  have hcut : (∑ n ∈ Icc 1 N, vonMangoldt n * (1 - (legendreSym d n : ℝ)) * f n) =
      ∑ n ∈ Icc 1 A, vonMangoldt n * (1 - (legendreSym d n : ℝ)) * f n := by
    refine sum_subset (Icc_subset_Icc le_rfl hNA) fun n hn hnN ↦ ?_
    by_cases hpow : IsPrimePow n
    · have hN : N < n := lt_of_not_ge fun h ↦ hnN (mem_Icc.mpr ⟨(mem_Icc.mp hn).1, h⟩)
      simp [hf n hN hpow]
    · simp [vonMangoldt_eq_zero_iff.mpr hpow]
  rw [← hcut, Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log (fun n hn ↦
    by simp [vonMangoldt_eq_zero_iff.mpr hn])]
  refine sum_congr rfl fun p hp ↦ ?_
  have hp' := Nat.prime_of_mem_primesLE hp
  have hfp (e : ℕ) (he : 0 < e) (hn : N < p ^ e) : f (p ^ e) = 0 :=
    hf _ hn ((isPrimePow_pow_iff he.ne').mpr hp'.isPrimePow)
  rw [localPrimeSum_eq_sum_Icc_log hp' hfp, mul_sum]
  refine sum_congr rfl fun e he ↦ ?_
  have he₀ : e ≠ 0 := Nat.ne_of_gt (mem_Icc.mp he).1
  rw [vonMangoldt_apply_pow he₀, vonMangoldt_apply_prime hp']
  ring

end TauCeti.OneSidedBound

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.PrimeCounting
public import TauCeti.NumberTheory.FrobeniusRiesz.PrimeSide
import TauCeti.NumberTheory.SumPrimePow

/-!
# Frobenius Riesz sums with split ramification

For a quadratic kernel, the unramified inert primes contribute exactly their odd powers.
At a prime with two inertia elements, one in the kernel and one outside it, each Frobenius
coset has one contributing element. The inertia mean halves the weight of this contribution.
Thus, when all other ramified primes split in the quadratic subfield, a sum off the kernel
can be compared prime by prime with local divisibility gains.

The normalization at the exceptional ramified prime is that of L. Alpöge's
`Formalism.LFunctionChainParameters.characterSumData.ASK` in
`Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean`
(<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open ArithmeticFunction Finset
open scoped BigOperators

namespace MonoidHom

variable {N : ℕ} [NeZero N] {G K : Type*} [Group G] [CommRing K] [IsDomain K]

open scoped Classical in
/-- The prime-by-prime form of the split-ramification identity. Twice the `Λ`-weighted means off
the quadratic kernel over the Frobenius cosets at `p ^ k`, for `1 ≤ k ≤ L`, are the odd-power
contribution of an unramified inert prime plus, at the exceptional prime `d`, the contribution of
the unique element outside the kernel in each coset. Here `g` represents the first Frobenius
coset at `p`, and `W k` is the weight at `p ^ k`. -/
theorem two_mul_sum_vonMangoldt_mul_expect_of_split_ramification
    (f : (ZMod N)ˣ →* G) (q : G →* Kˣ) (hq : q * q = 1) {p d : ℕ} (hp : p.Prime)
    {g : G} (hg : g ∈ f.frobeniusCoset hp 1)
    {σ : G} (hI : (f.cyclotomicInertia d : Set G) = {1, σ}) (hσ : q σ ≠ 1)
    (hsplit : p ≠ d → f.cyclotomicInertia p ≠ ⊥ → f.cyclotomicInertia p ≤ q.ker ∧ q g = 1)
    (L : ℕ) (W : ℕ → G → ℝ) :
    2 * (∑ k ∈ Icc 1 L, Λ (p ^ k) * 𝔼 t ∈ f.primePowerFrobeniusCoset (p ^ k),
        if q t ≠ 1 then W k t else 0) =
      (if f.cyclotomicInertia p = ⊥ ∧ q g ≠ 1 then
        (2 * Real.log p) * ∑ k ∈ Icc 1 L with Odd k, W k (g ^ k) else 0) +
      (if p = d then
        Real.log p * ∑ k ∈ Icc 1 L, W k (if q (g ^ k) = 1 then g ^ k * σ else g ^ k) else 0) := by
  classical
  have hterm (k : ℕ) (hk : k ∈ Icc 1 L) :
      2 * (Λ (p ^ k) * 𝔼 t ∈ f.primePowerFrobeniusCoset (p ^ k),
        if q t ≠ 1 then W k t else 0) =
      Real.log p * (2 * 𝔼 t ∈ f.frobeniusCoset hp k, if q t ≠ 1 then W k t else 0) := by
    have hk' : k ≠ 0 := Nat.ne_of_gt (mem_Icc.mp hk).1
    rw [f.primePowerFrobeniusCoset_pow hp hk', vonMangoldt_apply_pow hk',
      vonMangoldt_apply_prime hp, mul_left_comm]
  rw [mul_sum, sum_congr rfl hterm, ← mul_sum]
  by_cases he : p = d
  · subst d
    have hId := f.cyclotomicInertia_ne_bot_of_coe_eq_pair hI fun h ↦ hσ (h ▸ map_one q)
    simp only [hId, false_and, ite_false, ite_true, zero_add]
    refine congrArg (Real.log p * ·) (sum_congr rfl fun k _ ↦ ?_)
    simpa only [two_nsmul, two_mul] using
      f.two_nsmul_expect_frobeniusCoset_of_coe_cyclotomicInertia_eq_pair q hq hp hg hI hσ k (W k)
  · simp only [he, ite_false, add_zero]
    by_cases hIp : f.cyclotomicInertia p = ⊥
    · simp only [hIp, true_and,
        f.expect_frobeniusCoset_apply_ne_one_of_cyclotomicInertia_eq_bot q hq hp hg hIp, ← mul_sum]
      by_cases hqg : q g = 1
      · simp [hqg]
      · simp [hqg, ← sum_filter, ← mul_assoc, mul_comm (Real.log p) 2]
    · obtain ⟨hker, hqg⟩ := hsplit he hIp
      simp only [hIp, false_and, ite_false]
      refine mul_eq_zero_of_right _ (sum_eq_zero fun k _ ↦
        mul_eq_zero_of_right _ (expect_eq_zero fun t ht ↦ ?_))
      exact ite_eq_right (not_not_intro (q.mem_ker.mp <|
        f.coe_frobeniusCoset_subset_ker q hp hg hker hqg k (Finset.mem_coe.mpr ht)))

open scoped Classical in
/-- The doubled Frobenius Riesz sum off a quadratic kernel splits into the odd powers of
unramified inert primes and the positive powers of the exceptional prime `d`. The caps `w`
are read on the contributing Frobenius elements, so they can include a partner translation.
At `d` the coefficient is `log d`, not `2 log d`. Here `g p` is a representative of the first
Frobenius coset at each prime up to the common cutoff `M`; every other ramified prime has its
inertia and Frobenius in the kernel. -/
theorem two_mul_frobeniusRieszSum_eq_sum_of_split_ramification [Fintype G]
    (f : (ZMod N)ˣ →* G) (q : G →* Kˣ) (hq : q * q = 1) {M d : ℕ} (hd : d.Prime)
    (g : ℕ → G) (hg : ∀ {p} (hp : p.Prime), p ≤ M → g p ∈ f.frobeniusCoset hp 1)
    {σ : G} (hI : (f.cyclotomicInertia d : Set G) = {1, σ}) (hσ : q σ ≠ 1)
    (hsplit : ∀ p ∈ Nat.primesLE M, p ≠ d → f.cyclotomicInertia p ≠ ⊥ →
      f.cyclotomicInertia p ≤ q.ker ∧ q (g p) = 1)
    (w : G → ℝ) (a : ℝ) (hw : ∀ t, q t ≠ 1 → 0 < w t)
    (hM : ∀ t, q t ≠ 1 → ⌊a / w t⌋₊ ≤ M) :
    2 * f.frobeniusRieszSum (univ.filter fun t ↦ q t ≠ 1) w a =
      (∑ p ∈ Nat.primesLE M with f.cyclotomicInertia p = ⊥ ∧ q (g p) ≠ 1,
        (2 * Real.log p) * ∑ k ∈ Icc 1 (p.log M) with Odd k,
          max (a / ((p ^ k : ℕ) : ℝ) - w (g p ^ k)) 0) +
      Real.log d * ∑ k ∈ Icc 1 (d.log M),
        max (a / ((d ^ k : ℕ) : ℝ) - w (if q (g d ^ k) = 1 then g d ^ k * σ else g d ^ k)) 0 := by
  classical
  rw [f.frobeniusRieszSum_eq_sum _ w a M (by simpa using hw) (by simpa using hM)]
  simp only [mem_filter, mem_univ, true_and]
  rw [Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log (fun _ hn ↦ by
    simp [vonMangoldt_eq_zero_iff.mpr hn]), mul_sum]
  refine (sum_congr rfl fun p hp ↦ f.two_mul_sum_vonMangoldt_mul_expect_of_split_ramification q hq
    (Nat.mem_primesLE.mp hp).2 (hg (Nat.mem_primesLE.mp hp).2 (Nat.mem_primesLE.mp hp).1) hI hσ
    (hsplit p hp) (p.log M) fun k t ↦ max (a / ((p ^ k : ℕ) : ℝ) - w t) 0).trans ?_
  rw [sum_add_distrib, ← sum_filter, sum_ite_eq']
  by_cases hdM : d ≤ M
  · simp [Nat.mem_primesLE, hd, hdM]
  · simp [Nat.mem_primesLE, hdM, Nat.log_of_lt (lt_of_not_ge hdM)]

end MonoidHom

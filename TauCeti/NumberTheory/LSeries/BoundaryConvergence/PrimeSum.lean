/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.BoundaryConvergence.HigherPrimePowers
public import TauCeti.NumberTheory.LSeries.BoundaryConvergence.OrderedEulerProduct

/-!
# Ordered prime sums at the boundary

Let `c : ℕ → ℂ` satisfy `‖c p‖ ≤ 1` at every prime `p`, and let `a : ℕ → ℂ` be the coefficients
of the formal logarithm of the Euler product `∏ p, (1 - c p * p ^ (-s))⁻¹`: `a` vanishes off the
prime powers and `a (p ^ k) = c p ^ k / k` for `k ≥ 1`. At `s = 1` the partial sum
`∑ n ∈ Icc 1 N, a n / n` splits into the first powers `∑ p ≤ N, c p / p` and the higher prime
powers. The higher powers form an absolutely summable family, with sum
`T = ∑' (p, k), c p ^ (k + 2) / ((k + 2) * p ^ (k + 2))`
(`TauCeti.LSeries.summable_norm_higher_prime_powers`). Removing them shows that the ordered
partial sums of `∑ a n / n` converge to `L` exactly when the ordered prime sums
`∑ p ≤ N, c p / p` converge to `L - T`.

The comparison is made through the local logarithms: `log (1 - c p / p)⁻¹ - c p / p` is the sum
over `k ≥ 2` of the Taylor terms of the local factor
(`TauCeti.LSeries.hasSum_neg_log_one_sub_sub_div`), so its ordered sums over the primes tend to
`T`, while `TauCeti.LSeries.tendsto_sum_log_one_sub_inv_sub_sum_div` compares the sums of local
logarithms with the partial sums of `∑ a n / n`.

Only the higher-power tail is summed unconditionally: the prime sums are limits of ordered
cutoffs, and no unconditional `HasSum` over the primes is asserted. The specialization to a
nontrivial Dirichlet character is `DirichletCharacter.exists_tendsto_sum_primesLE_div`.

## Main result

* `TauCeti.LSeries.tendsto_sum_Icc_div_iff_tendsto_sum_primesLE_div`: the ordered partial sums of
  `∑ a n / n` converge to `L` if and only if the ordered prime sums `∑ p ≤ N, c p / p` converge
  to `L - T`.
-/

public section

open Filter Finset
open scoped Topology

namespace TauCeti.LSeries

variable {a c : ℕ → ℂ} (hc : ∀ p, p.Prime → ‖c p‖ ≤ 1) (ha : ∀ n, ¬IsPrimePow n → a n = 0)
  (ha_pow : ∀ p k : ℕ, p.Prime → k ≠ 0 → a (p ^ k) = c p ^ k / k)
include hc ha ha_pow

/-- **Removing the higher prime powers from an ordered Euler logarithm.** Let `a` be the
coefficients of the logarithm of the Euler product with local coefficients `c` of modulus at most
one. Then the ordered partial sums `∑ n ∈ Icc 1 N, a n / n` converge to `L` if and only if the
ordered prime sums `∑ p ≤ N, c p / p` converge to `L - T`, where `T` is the absolutely convergent
sum of the higher-prime-power terms `c p ^ (k + 2) / ((k + 2) * p ^ (k + 2))`. -/
theorem tendsto_sum_Icc_div_iff_tendsto_sum_primesLE_div {L : ℂ} :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, a n / n) atTop (𝓝 L) ↔
      Tendsto (fun N : ℕ ↦ ∑ p ∈ Nat.primesLE N, c p / p) atTop
        (𝓝 (L - ∑' q : Nat.Primes × ℕ,
          c q.1 ^ (q.2 + 2) / (((q.2 + 2 : ℕ) : ℂ) * (q.1 : ℂ) ^ (q.2 + 2)))) := by
  set T := ∑' q : Nat.Primes × ℕ,
    c q.1 ^ (q.2 + 2) / (((q.2 + 2 : ℕ) : ℂ) * (q.1 : ℂ) ^ (q.2 + 2))
  -- The difference of the two ordered sums is the difference of two comparisons with the sums
  -- of local logarithms, which tend to `T` and to `0`.
  have hdiff : Tendsto (fun N : ℕ ↦
      ∑ n ∈ Icc 1 N, a n / n - ∑ p ∈ Nat.primesLE N, c p / p) atTop (𝓝 T) := by
    have h := (tendsto_sum_primesLE_log_one_sub_inv_sub_div hc).sub
      (tendsto_sum_log_one_sub_inv_sub_sum_div hc ha ha_pow)
    rw [sub_zero] at h
    refine h.congr fun N ↦ ?_
    rw [sum_sub_distrib]
    ring
  refine ⟨fun h ↦ (h.sub hdiff).congr fun N ↦ by ring, fun h ↦ ?_⟩
  simpa using (h.add hdiff).congr fun N ↦ by ring

end TauCeti.LSeries

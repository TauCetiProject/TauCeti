/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.BoundaryConvergence.DirichletEulerProduct
public import TauCeti.NumberTheory.LSeries.BoundaryConvergence.HigherPrimePowers

/-!
# Removing higher prime powers from ordered boundary sums

Suppose `a` is supported on prime powers and `a (p ^ k) = c p ^ k / k`, with `‖c p‖ ≤ 1`.
The difference between the ordered sum `∑ n ≤ N, a n / n` and its prime part
`∑ p ≤ N, c p / p` converges to the absolutely convergent higher-prime-power tail
`∑' (p, k), c p ^ (k + 2) / ((k + 2) * p ^ (k + 2))`.
Consequently either ordered sum converges if and only if the other does, with this explicit
correction to the limit.

For a nontrivial Dirichlet character `χ` of positive level, this gives convergence of
`∑ p ≤ N, χ p / p` to a number `L` whose sum with the higher-power tail exponentiates to
`LFunction χ 1`. This specifies the branch through the ordered logarithmic sums; it does not
identify `L` with a principal logarithm. Only the higher-power tail is summed unconditionally.

The comparison uses the absolutely convergent local logarithmic remainders from
`hasSum_neg_log_one_sub_sub_div` and the vanishing truncation error from
`tendsto_sum_log_one_sub_inv_sub_sum_div`.

## References

* D. J. Newman, *Simple analytic proof of the prime number theorem*, Amer. Math. Monthly 87
  (1980), 693–696.
* D. Zagier, *Newman's short proof of the prime number theorem*, Amer. Math. Monthly 104
  (1997), 705–708.
-/

public section

open Filter Finset Complex
open scoped Topology

namespace TauCeti.LSeries

variable {a c : ℕ → ℂ}

/-- Removing the first powers from ordered prime-power logarithmic sums leaves a limit equal
to the absolutely convergent higher-prime-power tail. No convergence of either full ordered
sum is assumed. -/
theorem tendsto_sum_div_sub_sum_primesLE_div
    (hc : ∀ p, p.Prime → ‖c p‖ ≤ 1) (ha : ∀ n, ¬IsPrimePow n → a n = 0)
    (ha_pow : ∀ p k : ℕ, p.Prime → k ≠ 0 → a (p ^ k) = c p ^ k / k) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, a n / n - ∑ p ∈ Nat.primesLE N, c p / p)
      atTop (𝓝 (∑' q : Nat.Primes × ℕ, c q.1 ^ (q.2 + 2) /
        (((q.2 + 2 : ℕ) : ℂ) * (q.1 : ℂ) ^ (q.2 + 2)))) := by
  have hrem := ((hasSum_subtype_iff_indicator
    (s := {p : ℕ | p.Prime})
    (f := fun p ↦ -log (1 - c p / (p : ℂ)) - c p / (p : ℂ))).mp
      (hasSum_neg_log_one_sub_sub_div (fun p ↦ hc p p.prop))).tendsto_sum_nat
  have hlocal : Tendsto (fun N : ℕ ↦ ∑ p ∈ Nat.primesLE N,
      (log (1 - c p / p)⁻¹ - c p / p)) atTop
      (𝓝 (∑' q : Nat.Primes × ℕ, c q.1 ^ (q.2 + 2) /
        (((q.2 + 2 : ℕ) : ℂ) * (q.1 : ℂ) ^ (q.2 + 2)))) := by
    refine (hrem.comp (tendsto_add_atTop_nat 1)).congr fun N ↦ ?_
    simp only [Function.comp_apply, Nat.primesLE_eq_filter_range, sum_filter,
      Set.indicator_apply, Set.mem_ofPred_eq]
    refine sum_congr rfl fun p _ ↦ ?_
    split_ifs with hp
    · have hz : ‖c p / (p : ℂ)‖ < 1 := by
        rw [norm_div, Complex.norm_natCast, div_lt_one (by exact_mod_cast hp.pos)]
        exact (hc p hp).trans_lt (by exact_mod_cast hp.one_lt)
      have hslit : 1 - c p / (p : ℂ) ∈ slitPlane := by
        simpa only [sub_eq_add_neg] using
          mem_slitPlane_of_norm_lt_one ((norm_neg _).trans_lt hz)
      rw [log_inv _ (slitPlane_arg_ne_pi hslit)]
    · rfl
  simpa [sum_sub_distrib] using
    hlocal.sub (tendsto_sum_log_one_sub_inv_sub_sum_div hc ha ha_pow)

/-- An ordered prime-power logarithmic sum converges to `L` exactly when its prime part
converges to `L` minus the absolutely convergent higher-power tail. -/
theorem tendsto_sum_primesLE_div_iff
    (hc : ∀ p, p.Prime → ‖c p‖ ≤ 1) (ha : ∀ n, ¬IsPrimePow n → a n = 0)
    (ha_pow : ∀ p k : ℕ, p.Prime → k ≠ 0 → a (p ^ k) = c p ^ k / k) {L : ℂ} :
    Tendsto (fun N : ℕ ↦ ∑ p ∈ Nat.primesLE N, c p / p) atTop
        (𝓝 (L - ∑' q : Nat.Primes × ℕ, c q.1 ^ (q.2 + 2) /
          (((q.2 + 2 : ℕ) : ℂ) * (q.1 : ℂ) ^ (q.2 + 2)))) ↔
      Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, a n / n) atTop (𝓝 L) := by
  have hdiff := tendsto_sum_div_sub_sum_primesLE_div hc ha ha_pow
  constructor
  · intro h
    simpa using hdiff.add h
  · intro h
    simpa using h.sub hdiff

end TauCeti.LSeries

namespace DirichletCharacter

/-- For a nontrivial character of positive level, the ordered prime sum `∑ p ≤ N, χ p / p`
converges. Adding the absolutely convergent higher-power tail to its limit gives a logarithm
of `LFunction χ 1`, normalized by continuation from the half-plane of absolute convergence. -/
theorem exists_tendsto_sum_primesLE_div {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ L : ℂ, Tendsto (fun B : ℕ ↦ ∑ p ∈ Nat.primesLE B, χ p / (p : ℂ)) atTop (𝓝 L) ∧
      exp (L + ∑' q : Nat.Primes × ℕ, χ q.1 ^ (q.2 + 2) /
        (((q.2 + 2 : ℕ) : ℂ) * (q.1 : ℂ) ^ (q.2 + 2))) = LFunction χ 1 := by
  obtain ⟨L, hL, hexp⟩ := χ.exists_tendsto_sum_Icc_eulerLogCoeff_div hχ
  refine ⟨L - ∑' q : Nat.Primes × ℕ, χ q.1 ^ (q.2 + 2) /
    (((q.2 + 2 : ℕ) : ℂ) * (q.1 : ℂ) ^ (q.2 + 2)), ?_, by simpa using hexp⟩
  exact (TauCeti.LSeries.tendsto_sum_primesLE_div_iff (fun p _ ↦ χ.norm_le_one p)
    (fun _ hn ↦ χ.eulerLogCoeff_eq_zero_of_not_isPrimePow hn)
    (fun _ _ hp hk ↦ χ.eulerLogCoeff_prime_pow hp hk)).mpr hL

end DirichletCharacter

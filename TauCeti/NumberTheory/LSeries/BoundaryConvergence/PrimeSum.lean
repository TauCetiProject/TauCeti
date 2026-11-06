/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.BoundaryConvergence.DirichletEulerProduct
public import TauCeti.NumberTheory.LSeries.BoundaryConvergence.HigherPrimePowers

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

For a nontrivial Dirichlet character `χ` of positive level the coefficients are
`DirichletCharacter.eulerLogCoeff χ`, whose ordered sums converge to a logarithm of `L(χ, 1)`
(`DirichletCharacter.exists_tendsto_sum_Icc_eulerLogCoeff_div`). Hence the ordered sums
`∑ p ≤ B, χ p / p` converge, to a limit `ℓ` with `exp (ℓ + T) = L(χ, 1)`. Only the higher-power
tail is summed unconditionally: `∑ χ p / p` itself is a limit of ordered cutoffs, and no
unconditional `HasSum` over the primes is asserted. Limits along real cutoffs `⌊x⌋₊` follow from
`TauCeti.tendsto_comp_natFloor_iff`.

## Main results

* `TauCeti.LSeries.tendsto_sum_primesLE_log_one_sub_inv_sub_div`: the ordered sums of the local
  remainders `log (1 - c p / p)⁻¹ - c p / p` tend to the higher-power tail `T`.
* `TauCeti.LSeries.tendsto_sum_Icc_div_iff_tendsto_sum_primesLE_div`: the ordered partial sums of
  `∑ a n / n` converge to `L` if and only if the ordered prime sums `∑ p ≤ N, c p / p` converge
  to `L - T`.
* `DirichletCharacter.exists_tendsto_sum_primesLE_div`: for a nontrivial character `χ` of
  positive level, the ordered prime sums `∑ p ≤ B, χ p / p` converge to a limit `ℓ` with
  `exp (ℓ + T) = L(χ, 1)`.
-/

public section

open Filter Finset Complex
open scoped Topology

namespace TauCeti.LSeries

variable {a c : ℕ → ℂ}

/-- **The local remainders of an Euler logarithm.** If `‖c p‖ ≤ 1` at every prime `p`, the ordered
sums over the primes `p ≤ N` of `log (1 - c p / p)⁻¹ - c p / p` converge to the sum of the
higher-prime-power terms `c p ^ (k + 2) / ((k + 2) * p ^ (k + 2))`. -/
theorem tendsto_sum_primesLE_log_one_sub_inv_sub_div (hc : ∀ p, p.Prime → ‖c p‖ ≤ 1) :
    Tendsto (fun N : ℕ ↦ ∑ p ∈ Nat.primesLE N, (log (1 - c p / p)⁻¹ - c p / p)) atTop
      (𝓝 (∑' q : Nat.Primes × ℕ,
        c q.1 ^ (q.2 + 2) / (((q.2 + 2 : ℕ) : ℂ) * (q.1 : ℂ) ^ (q.2 + 2)))) := by
  set r : ℕ → ℂ := fun n ↦ log (1 - c n / n)⁻¹ - c n / n
  -- Extend the remainders by zero off the primes, so that the absolutely convergent sum over
  -- `Nat.Primes` becomes a sum over `ℕ` whose partial sums are the ordered prime sums.
  have hr : HasSum (fun n ↦ if n.Prime then r n else 0) (∑' q : Nat.Primes × ℕ,
      c q.1 ^ (q.2 + 2) / (((q.2 + 2 : ℕ) : ℂ) * (q.1 : ℂ) ^ (q.2 + 2))) := by
    refine (Function.Injective.hasSum_iff (g := fun p : Nat.Primes ↦ (p : ℕ))
      Nat.Primes.coe_nat_injective fun n hn ↦ ?_).mp ?_
    · simp only [ite_eq_right_iff]
      exact fun hp ↦ (hn ⟨⟨n, hp⟩, rfl⟩).elim
    · refine (hasSum_neg_log_one_sub_sub_div fun p ↦ hc p p.prop).congr_fun fun p ↦ ?_
      have hz : ‖-(c p / p)‖ < 1 := by
        have hp : (1 : ℝ) < (p : ℕ) := mod_cast p.prop.one_lt
        rw [norm_neg, norm_div, Complex.norm_natCast, div_lt_one (by linarith)]
        exact (hc p p.prop).trans_lt hp
      have hslit : 1 - c p / p ∈ slitPlane := by
        simpa [sub_eq_add_neg] using mem_slitPlane_of_norm_lt_one hz
      simp only [Function.comp_apply, p.prop, ↓reduceIte, r]
      exact congrArg (· - _) (log_inv _ (slitPlane_arg_ne_pi hslit))
  refine (hr.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr fun N ↦ ?_
  rw [Function.comp_apply, Nat.primesLE_eq_filter_range, sum_filter]

variable (hc : ∀ p, p.Prime → ‖c p‖ ≤ 1) (ha : ∀ n, ¬IsPrimePow n → a n = 0)
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

namespace DirichletCharacter

variable {N : ℕ} (χ : DirichletCharacter ℂ N)

/-- **The ordered prime sums of a Dirichlet character at `s = 1`.** For a nontrivial Dirichlet
character `χ` of positive level, the ordered sums `∑ p ≤ B, χ p / p` over the primes up to `B`
converge. Their limit `ℓ` satisfies `exp (ℓ + T) = L(χ, 1)`, where `T` is the absolutely
convergent sum of the higher-prime-power terms `χ p ^ (k + 2) / ((k + 2) * p ^ (k + 2))`.

This is a limit of ordered cutoffs; no unconditional sum of `χ p / p` over the primes is
asserted. -/
theorem exists_tendsto_sum_primesLE_div [NeZero N] (hχ : χ ≠ 1) :
    ∃ ℓ : ℂ, Tendsto (fun B : ℕ ↦ ∑ p ∈ Nat.primesLE B, χ p / (p : ℂ)) atTop (𝓝 ℓ) ∧
      exp (ℓ + ∑' q : Nat.Primes × ℕ,
        χ q.1 ^ (q.2 + 2) / (((q.2 + 2 : ℕ) : ℂ) * (q.1 : ℂ) ^ (q.2 + 2))) = LFunction χ 1 := by
  obtain ⟨L, hL, hexp⟩ := χ.exists_tendsto_sum_Icc_eulerLogCoeff_div hχ
  refine ⟨_, (TauCeti.LSeries.tendsto_sum_Icc_div_iff_tendsto_sum_primesLE_div
    (c := fun n ↦ χ n) (fun p _ ↦ χ.norm_le_one p)
    (fun _ hn ↦ χ.eulerLogCoeff_eq_zero_of_not_isPrimePow hn)
    (fun _ _ hp hk ↦ χ.eulerLogCoeff_prime_pow hp hk)).mp hL, ?_⟩
  rwa [sub_add_cancel]

end DirichletCharacter

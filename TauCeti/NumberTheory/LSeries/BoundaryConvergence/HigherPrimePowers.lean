/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.NumberTheory.PrimeCounting
import TauCeti.Analysis.SpecificLimits.ReciprocalSeries

/-!
# Absolute control of the higher prime powers at the boundary

For coefficients `c p` of modulus at most one, the terms
`c p ^ k / (k * p ^ k)` with `p` prime and `k ≥ 2` form an absolutely summable
family, with sum of norms at most one. Thus the higher powers in an Euler logarithm
can be removed without changing the ordering of its conditionally convergent
first-power terms. The exponent is indexed as `k + 2` throughout.

The majorant sums the geometric series at each integer `m ≥ 2` to
`1 / (m * (m - 1))`; summing over all such integers telescopes to one.
Only the higher-power tail is summed unconditionally here, not the boundary
Dirichlet series or the full Euler logarithm. The identification with the local
logarithmic remainders uses Mathlib's `Complex.hasSum_taylorSeries_neg_log'`. Extending these
remainders by zero off the primes, their ordered sums over the primes `p ≤ N` tend to the same
tail (`TauCeti.LSeries.tendsto_sum_primesLE_log_one_sub_inv_sub_div`).
-/

public section

open Filter Finset
open scoped Topology

namespace TauCeti.LSeries

variable {c : ℕ → ℂ}

/-- Every finite collection of higher-prime-power logarithmic terms has total norm
at most one. The collection need not be rectangular or ordered. -/
theorem sum_norm_higher_prime_powers_le_one
    (hc : ∀ p : Nat.Primes, ‖c p‖ ≤ 1) (s : Finset (Nat.Primes × ℕ)) :
    ∑ q ∈ s, ‖c q.1 ^ (q.2 + 2) /
      (((q.2 + 2 : ℕ) : ℂ) * (q.1 : ℂ) ^ (q.2 + 2))‖ ≤ 1 := by
  -- Sum a geometric majorant over all integers at least two, not just primes.
  let g : ℕ × ℕ → ℝ := fun q ↦ ((q.1 : ℝ) + 2)⁻¹ ^ (q.2 + 2)
  have hfiber (n : ℕ) : HasSum (fun k : ℕ ↦ g (n, k))
      (((n : ℝ) + 1)⁻¹ - ((n : ℝ) + 2)⁻¹) := hasSum_inv_add_two_pow_add_two n
  have htelescope := hasSum_inv_add_one_sub_inv_add_two
  have hg : Summable g :=
    (summable_prod_of_nonneg (fun q ↦ by dsimp [g]; positivity)).mpr
      ⟨fun n ↦ (hfiber n).summable, by
        simpa only [(hfiber _).tsum_eq] using htelescope.summable⟩
  have htotal : ∑' q, g q = 1 := by
    rw [hg.tsum_prod]
    simpa only [(hfiber _).tsum_eq] using htelescope.tsum_eq
  -- Embed the prime-indexed finite collection into the summable majorant.
  let j : Nat.Primes × ℕ → ℕ × ℕ := fun q ↦ (q.1.val - 2, q.2)
  have hj : Function.Injective j := by
    rintro ⟨p, k⟩ ⟨p', k'⟩ h
    have hp := p.prop.two_le
    have hp' := p'.prop.two_le
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    dsimp [j] at h₁ h₂
    have : p = p' := Subtype.ext (by omega)
    simp_all
  calc
    _ ≤ ∑ q ∈ s, g (j q) := by
      refine sum_le_sum fun q _ ↦ ?_
      have hp : (2 : ℝ) ≤ q.1.val := by exact_mod_cast q.1.prop.two_le
      have hc' : ‖c q.1‖ ^ (q.2 + 2) ≤ 1 := pow_le_one₀ (norm_nonneg _) (hc _)
      have hk : (1 : ℝ) ≤ (q.2 + 2 : ℕ) := by exact_mod_cast (by omega : 1 ≤ q.2 + 2)
      have hp' : ((q.1.val - 2 : ℕ) : ℝ) + 2 = q.1.val := by
        rw [Nat.cast_sub q.1.prop.two_le]
        norm_num
      simp only [g, j, hp', norm_div, norm_mul, norm_pow, Complex.norm_natCast,
        inv_pow]
      calc
        _ ≤ 1 / (q.1.val : ℝ) ^ (q.2 + 2) := by
          apply div_le_div₀ (by positivity) hc' (by positivity)
          exact le_mul_of_one_le_left (by positivity) hk
        _ = _ := one_div _
    _ = ∑ q ∈ s.image j, g q := (sum_image (fun _ _ _ _ h ↦ hj h)).symm
    _ ≤ ∑' q, g q := hg.sum_le_tsum _ (fun q _ ↦ by dsimp [g]; positivity)
    _ = 1 := htotal

/-- The higher-prime-power terms in a boundary Euler logarithm are absolutely
summable, even though its first-power terms need not be. -/
theorem summable_norm_higher_prime_powers (hc : ∀ p : Nat.Primes, ‖c p‖ ≤ 1) :
    Summable (fun q : Nat.Primes × ℕ ↦ ‖c q.1 ^ (q.2 + 2) /
      (((q.2 + 2 : ℕ) : ℂ) * (q.1 : ℂ) ^ (q.2 + 2))‖) :=
  summable_of_sum_le (fun _ ↦ norm_nonneg _) (sum_norm_higher_prime_powers_le_one hc)

/-- The sum of the norms of all higher-prime-power logarithmic terms is at most
one, uniformly in the coefficients of modulus at most one. -/
theorem tsum_norm_higher_prime_powers_le_one (hc : ∀ p : Nat.Primes, ‖c p‖ ≤ 1) :
    (∑' q : Nat.Primes × ℕ, ‖c q.1 ^ (q.2 + 2) /
      (((q.2 + 2 : ℕ) : ℂ) * (q.1 : ℂ) ^ (q.2 + 2))‖) ≤ 1 :=
  (summable_norm_higher_prime_powers hc).tsum_le_of_sum_le
    (sum_norm_higher_prime_powers_le_one hc)

/-- The local logarithmic remainders form an absolutely convergent prime sum.
Its sum is precisely the unconditionally summable higher-prime-power tail.
The logarithm here is local to each Euler factor; no logarithm of an infinite
product or unconditional first-power sum is asserted. -/
theorem hasSum_neg_log_one_sub_sub_div (hc : ∀ p : Nat.Primes, ‖c p‖ ≤ 1) :
    HasSum (fun p : Nat.Primes ↦ -Complex.log (1 - c p / (p : ℂ)) - c p / (p : ℂ))
      (∑' q : Nat.Primes × ℕ, c q.1 ^ (q.2 + 2) /
        (((q.2 + 2 : ℕ) : ℂ) * (q.1 : ℂ) ^ (q.2 + 2))) := by
  have hfiber (p : Nat.Primes) :
      HasSum (fun k : ℕ ↦ c p ^ (k + 2) /
        (((k + 2 : ℕ) : ℂ) * (p : ℂ) ^ (k + 2)))
        (-Complex.log (1 - c p / (p : ℂ)) - c p / (p : ℂ)) := by
    have hp : (1 : ℝ) < p.val := by exact_mod_cast p.prop.one_lt
    have hz : ‖c p / (p : ℂ)‖ < 1 := by
      rw [norm_div, Complex.norm_natCast, div_lt_one (by positivity)]
      exact (hc p).trans_lt hp
    have h := (hasSum_nat_add_iff' 1).mpr (Complex.hasSum_taylorSeries_neg_log' hz)
    simpa only [sum_range_one, Nat.cast_zero, zero_add, pow_one, div_one,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, one_add_one_eq_two,
      div_pow, div_div, mul_one, mul_comm] using h
  exact (summable_norm_higher_prime_powers hc).of_norm.hasSum.prod_fiberwise hfiber

/-- **The local remainders of an Euler logarithm.** If `‖c p‖ ≤ 1` at every prime `p`, the ordered
sums over the primes `p ≤ N` of `log (1 - c p / p)⁻¹ - c p / p` converge to the sum of the
higher-prime-power terms `c p ^ (k + 2) / ((k + 2) * p ^ (k + 2))`. -/
theorem tendsto_sum_primesLE_log_one_sub_inv_sub_div (hc : ∀ p, p.Prime → ‖c p‖ ≤ 1) :
    Tendsto (fun N : ℕ ↦ ∑ p ∈ Nat.primesLE N, (Complex.log (1 - c p / p)⁻¹ - c p / p)) atTop
      (𝓝 (∑' q : Nat.Primes × ℕ,
        c q.1 ^ (q.2 + 2) / (((q.2 + 2 : ℕ) : ℂ) * (q.1 : ℂ) ^ (q.2 + 2)))) := by
  set r : ℕ → ℂ := fun n ↦ Complex.log (1 - c n / n)⁻¹ - c n / n
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
      have hslit : 1 - c p / p ∈ Complex.slitPlane := by
        simpa [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hz
      simp only [Function.comp_apply, p.prop, ↓reduceIte, r]
      exact congrArg (· - _) (Complex.log_inv _ (Complex.slitPlane_arg_ne_pi hslit))
  refine (hr.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr fun N ↦ ?_
  rw [Function.comp_apply, Nat.primesLE_eq_filter_range, sum_filter]

end TauCeti.LSeries

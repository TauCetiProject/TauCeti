/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Data.Nat.Prime.Defs

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
logarithmic remainders uses Mathlib's `Complex.hasSum_taylorSeries_neg_log'`.
-/

public section

open Filter Finset
open scoped Topology

namespace TauCeti.LSeries

variable {c : ℕ → ℂ}

/-- The geometric series with ratio `(n + 2)⁻¹` starting at the exponent two sums to the
difference of consecutive reciprocals `(n + 1)⁻¹ - (n + 2)⁻¹`. -/
theorem hasSum_inv_add_two_pow_add_two (n : ℕ) :
    HasSum (fun k : ℕ ↦ (((n : ℝ) + 2)⁻¹) ^ (k + 2))
      (((n : ℝ) + 1)⁻¹ - ((n : ℝ) + 2)⁻¹) := by
  have h := (hasSum_geometric_of_lt_one
    (by positivity : 0 ≤ ((n : ℝ) + 2)⁻¹) (by
      rw [inv_lt_one₀ (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)).mul_right (((n : ℝ) + 2)⁻¹ ^ 2)
  simp only [pow_add] at ⊢
  convert h using 1
  field_simp
  ring_nf
  field_simp
  ring

/-- The reciprocal differences `(n + 1)⁻¹ - (n + 2)⁻¹` telescope to a series with sum one. -/
theorem hasSum_inv_add_one_sub_inv_add_two :
    HasSum (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ - ((n : ℝ) + 2)⁻¹) 1 := by
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ by
    apply sub_nonneg.mpr
    gcongr
    norm_num) _).mpr ?_
  have hsum (N : ℕ) :
      (∑ n ∈ range N, (((n : ℝ) + 1)⁻¹ - ((n : ℝ) + 2)⁻¹)) =
        1 - ((N : ℝ) + 1)⁻¹ := by
    simpa [Nat.cast_add, add_assoc, one_add_one_eq_two] using
      (sum_range_sub' (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) N)
  simp_rw [hsum]
  simpa using tendsto_const_nhds.sub
    (tendsto_inv_atTop_zero.comp (tendsto_atTop_mono
      (fun n : ℕ ↦ le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1))
      tendsto_natCast_atTop_atTop))

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

end TauCeti.LSeries

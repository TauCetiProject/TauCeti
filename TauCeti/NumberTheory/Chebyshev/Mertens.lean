/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.SpecialFunctions.Log.Factorial
import TauCeti.NumberTheory.Chebyshev.LogFactorial
import TauCeti.NumberTheory.Chebyshev.PrimeTail
import TauCeti.NumberTheory.SumPrimePow

/-!
# Elementary Mertens's first theorem on prime and von Mangoldt cutoffs

For real `x ≥ 1`, Chebyshev's factorial identity
`log ⌊x⌋₊! = ∑_{1 ≤ n ≤ x} Λ(n) ⌊x / n⌋₊` together with the Stirling bounds on `log ⌊x⌋₊!` and
Chebyshev's linear bound `ψ(x) ≤ (log 4 + 4) x` yields an elementary two-sided estimate for the
logarithmically weighted von Mangoldt sum:
`log x - 3 / 2 ≤ ∑_{1 ≤ n ≤ x} Λ(n) / n ≤ log x + log 4 + 4`
(with the lower bound holding for all `x ≥ 0`).

Regrouping prime powers by their prime base separates `∑_{1 ≤ n ≤ x} Λ(n) / n` into the prime sum
`∑_{p ≤ x} log p / p` over `Nat.primesLE ⌊x⌋₊` and the higher prime-power remainder
`∑_{p ≤ x} ∑_{2 ≤ k ≤ log_p ⌊x⌋₊} log p / p ^ k`. Geometric summation bounds each inner fibre by
`log p / (p (p - 1)) ≤ 2 log p / p ^ 2`, and the reciprocal-square prime tail bound gives a
cutoff-independent bound `2 log 4` on both the finite higher-power remainder and the full non-prime
von Mangoldt series `∑' n, (if n.Prime then 0 else Λ n) / n`.

Combining the two steps gives Mertens's first theorem with explicit effective constants on
`Nat.primesLE ⌊x⌋₊`, on its strict counterpart `Nat.primesBelow ⌈x⌉₊`, at integer cutoffs, and on
half-open intervals `y < p ≤ x`.

## Main results

* `TauCeti.primesLE_filter_lt_eq_primesBelow_ceil`,
  `TauCeti.sum_primesLE_floor_eq_sum_primesBelow_ceil_add`,
  `TauCeti.sum_primesLE_filter_gt_eq_sub`: exact finset and sum adapters between inclusive real
  cutoffs `Nat.primesLE ⌊x⌋₊`, strict cutoffs `Nat.primesBelow ⌈x⌉₊`, and prime intervals
  `y < p ≤ x`.
* `TauCeti.sum_Ioc_vonMangoldt_div_eq_sum_primesLE_add`,
  `TauCeti.sum_Ioc_vonMangoldt_div_sub_sum_primesLE_le`,
  `TauCeti.tsum_vonMangoldt_nonprime_div_le`: prime-power decomposition of `∑ Λ(n) / n` and the
  explicit bound `2 log 4` on the higher prime powers.
* `TauCeti.le_sum_Ioc_vonMangoldt_div`, `TauCeti.sum_Ioc_vonMangoldt_div_le`,
  `TauCeti.abs_sum_Ioc_vonMangoldt_div_sub_log_le`: explicit Mertens bounds for `∑ Λ(n) / n`.
* `TauCeti.le_sum_primesLE_floor_log_div`, `TauCeti.sum_primesLE_floor_log_div_le`,
  `TauCeti.abs_sum_primesLE_floor_log_div_sub_log_le`,
  `TauCeti.abs_sum_primesBelow_ceil_log_div_sub_log_le`,
  `TauCeti.abs_sum_primesLE_filter_gt_log_div_sub_log_div_le`: explicit Mertens bounds on inclusive,
  strict, integer, and interval prime cutoffs, together with `=O[atTop]` corollaries.

## References

* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Graduate Studies in Mathematics 203,
  American Mathematical Society, 2019, Theorem 3.4(a) and its proof, p. 40.
* A. Kontorovich et al., *PrimeNumberTheoremAnd* (`PrimeNumberTheoremAnd/IEANTN/Mertens.lean`),
  for a related formalization of elementary Mertens estimates (no code copied).
-/

public section

open ArithmeticFunction Asymptotics Filter Finset
open scoped Chebyshev Nat Topology

namespace TauCeti

/-! ### Prime-cutoff finset and sum adapters -/

section PrimeCutoffs

/-- Filtering the primes `p ≤ ⌊x⌋₊` by `(p : ℝ) < x` gives `Nat.primesBelow ⌈x⌉₊` for every real
`x`. -/
@[simp]
theorem primesLE_filter_lt_eq_primesBelow_ceil (x : ℝ) :
    (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ (p : ℝ) < x) = Nat.primesBelow ⌈x⌉₊ := by
  ext p
  simp only [mem_filter, Nat.mem_primesLE, Nat.mem_primesBelow, Nat.lt_ceil]
  refine ⟨fun ⟨⟨_, hp⟩, hpx⟩ ↦ ⟨hpx, hp⟩, fun ⟨hpx, hp⟩ ↦ ⟨⟨?_, hp⟩, hpx⟩⟩
  exact (Nat.le_floor_iff (le_trans (Nat.cast_nonneg p) hpx.le)).mpr hpx.le

/-- Every prime strictly below a real cutoff `x` lies in `Nat.primesLE ⌊x⌋₊`. -/
theorem primesBelow_ceil_subset_primesLE_floor (x : ℝ) :
    Nat.primesBelow ⌈x⌉₊ ⊆ Nat.primesLE ⌊x⌋₊ :=
  primesLE_filter_lt_eq_primesBelow_ceil x ▸ filter_subset _ _

/-- A sum over `Nat.primesLE ⌊x⌋₊` differs from the sum over `Nat.primesBelow ⌈x⌉₊` only when `x`
is itself a prime integer, in which case the difference is the single term at `⌊x⌋₊`. -/
theorem sum_primesLE_floor_eq_sum_primesBelow_ceil_add {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (x : ℝ) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, f p =
      (∑ p ∈ Nat.primesBelow ⌈x⌉₊, f p) +
        if (⌊x⌋₊ : ℝ) = x ∧ ⌊x⌋₊.Prime then f ⌊x⌋₊ else 0 := by
  rw [← sum_filter_add_sum_filter_not (Nat.primesLE ⌊x⌋₊) (fun p : ℕ ↦ (p : ℝ) < x),
    primesLE_filter_lt_eq_primesBelow_ceil]
  congr 1
  split_ifs with h
  · rcases h with ⟨hx, hprime⟩
    have hfilt : (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ ¬(p : ℝ) < x) = {⌊x⌋₊} := by
      ext p
      simp only [mem_filter, Nat.mem_primesLE, mem_singleton, not_lt]
      refine ⟨fun ⟨⟨hp_le, _⟩, hxp⟩ ↦ ?_, fun hp_eq ↦ ?_⟩
      · rw [← hx] at hxp
        exact le_antisymm hp_le (by exact_mod_cast hxp)
      · subst hp_eq
        exact ⟨⟨le_rfl, hprime⟩, hx.ge⟩
    rw [hfilt, sum_singleton]
  · refine sum_eq_zero fun p hp ↦ ?_
    exfalso
    simp only [mem_filter, Nat.mem_primesLE, not_lt] at hp
    obtain ⟨⟨hp_le, hp_prime⟩, hxp⟩ := hp
    have hx0 : 0 ≤ x := by
      by_contra hx0
      simp only [Nat.floor_of_nonpos (le_of_not_ge hx0), nonpos_iff_eq_zero] at hp_le
      exact hp_prime.ne_zero hp_le
    have hpx : (p : ℝ) = x := le_antisymm ((Nat.le_floor_iff hx0).mp hp_le) hxp
    have hfl : ⌊x⌋₊ = p := by rw [← hpx, Nat.floor_natCast]
    exact h ⟨by rw [hfl, hpx], hfl ▸ hp_prime⟩

/-- For `y ≤ x`, filtering `Nat.primesLE ⌊x⌋₊` by `(p : ℝ) ≤ y` recovers `Nat.primesLE ⌊y⌋₊`. -/
theorem primesLE_filter_le_eq_primesLE {x y : ℝ} (hyx : y ≤ x) :
    (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ (p : ℝ) ≤ y) = Nat.primesLE ⌊y⌋₊ := by
  ext p
  simp only [mem_filter, Nat.mem_primesLE]
  refine ⟨fun ⟨⟨_, hp⟩, hpy⟩ ↦ ⟨?_, hp⟩,
    fun ⟨hpy, hp⟩ ↦ ⟨⟨hpy.trans (Nat.floor_mono hyx), hp⟩, ?_⟩⟩
  · exact (Nat.le_floor_iff (le_trans (Nat.cast_nonneg p) hpy)).mpr hpy
  · have hy0 : 0 ≤ y := by
      by_contra hy0
      simp only [Nat.floor_of_nonpos (le_of_not_ge hy0), nonpos_iff_eq_zero] at hpy
      exact hp.ne_zero hpy
    exact (Nat.le_floor_iff hy0).mp hpy

/-- The primes `p ≤ y` and the primes `y < p ≤ x` are disjoint; an endpoint prime `p = y` belongs
only to the lower set. -/
theorem disjoint_primesLE_filter_gt (x y : ℝ) :
    Disjoint (Nat.primesLE ⌊y⌋₊) ((Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ y < (p : ℝ))) := by
  rw [disjoint_left]
  intro p hpy hpx
  obtain ⟨hpy_le, hp⟩ := Nat.mem_primesLE.mp hpy
  have hy0 : 0 ≤ y := by
    by_contra hy0
    simp only [Nat.floor_of_nonpos (le_of_not_ge hy0), nonpos_iff_eq_zero] at hpy_le
    exact hp.ne_zero hpy_le
  exact not_lt_of_ge ((Nat.le_floor_iff hy0).mp hpy_le) (mem_filter.mp hpx).2

/-- For `y ≤ x`, `Nat.primesLE ⌊x⌋₊` partitions into `Nat.primesLE ⌊y⌋₊` and the interval
`y < (p : ℝ) ≤ x`. -/
theorem primesLE_union_filter_gt_eq_primesLE {x y : ℝ} (hyx : y ≤ x) :
    Nat.primesLE ⌊y⌋₊ ∪ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ y < (p : ℝ)) =
      Nat.primesLE ⌊x⌋₊ := by
  rw [← primesLE_filter_le_eq_primesLE hyx]
  convert filter_union_filter_not_eq (p := fun p : ℕ ↦ (p : ℝ) ≤ y) (Nat.primesLE ⌊x⌋₊) using 2
  ext p
  simp

/-- Splitting a sum over `Nat.primesLE ⌊x⌋₊` at `y ≤ x` into `p ≤ y` and `y < p ≤ x`. -/
theorem sum_primesLE_add_sum_primesLE_filter_gt {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    {x y : ℝ} (hyx : y ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊y⌋₊, f p) +
        (∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ y < (p : ℝ)), f p) =
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, f p := by
  rw [← sum_union (disjoint_primesLE_filter_gt x y), primesLE_union_filter_gt_eq_primesLE hyx]

/-- A sum over the primes in `y < p ≤ x` equals the difference of the inclusive cutoff sums at `x`
and `y`. -/
theorem sum_primesLE_filter_gt_eq_sub {M : Type*} [AddCommGroup M] (f : ℕ → M)
    {x y : ℝ} (hyx : y ≤ x) :
    ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ y < (p : ℝ)), f p =
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, f p) - ∑ p ∈ Nat.primesLE ⌊y⌋₊, f p :=
  eq_sub_of_add_eq' (sum_primesLE_add_sum_primesLE_filter_gt f hyx)

end PrimeCutoffs

/-! ### Higher prime powers and the `log n / (n (n - 1))` majorant -/

section HigherPrimePowers

/-- For every natural number `n` and bound `K`, the geometric sum of `log n / n ^ k` over
`2 ≤ k ≤ K` is at most `log n / (n (n - 1))` (with both sides zero at `n = 0, 1`). -/
theorem sum_Icc_two_log_div_pow_le (n K : ℕ) :
    ∑ k ∈ Icc 2 K, Real.log n / (n : ℝ) ^ k ≤ Real.log n / ((n : ℝ) * (n - 1)) := by
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  have hn_cast : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := by linarith
  have hn1_pos : 0 < (n : ℝ) - 1 := by linarith
  have hr_nonneg : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hn_pos.le
  have hr_lt_one : (n : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hgeom : ∑ k ∈ Icc 2 K, ((n : ℝ) ^ k)⁻¹ ≤ ((n : ℝ) * (n - 1))⁻¹ := by
    rcases lt_or_ge K 2 with hK | hK
    · rw [Icc_eq_empty (by omega), sum_empty]
      positivity
    have himg : Icc 2 K = (range (K - 1)).image (· + 2) := by
      ext k
      simp only [mem_Icc, mem_image, mem_range]
      refine ⟨fun hk ↦ ⟨k - 2, by omega, by omega⟩, ?_⟩
      rintro ⟨j, hj, rfl⟩
      omega
    rw [himg, sum_image (fun _ _ _ _ h ↦ by omega)]
    calc ∑ j ∈ range (K - 1), ((n : ℝ) ^ (j + 2))⁻¹
        = ((n : ℝ)⁻¹ ^ 2) * ∑ j ∈ range (K - 1), ((n : ℝ)⁻¹) ^ j := by
          rw [mul_sum]
          refine sum_congr rfl fun j _ ↦ ?_
          rw [pow_add, mul_inv, inv_pow, inv_pow, mul_comm]
      _ ≤ ((n : ℝ)⁻¹ ^ 2) * ∑' j : ℕ, ((n : ℝ)⁻¹) ^ j :=
          mul_le_mul_of_nonneg_left
            ((summable_geometric_of_lt_one hr_nonneg hr_lt_one).sum_le_tsum _
              fun _ _ ↦ pow_nonneg hr_nonneg _)
            (by positivity)
      _ = ((n : ℝ)⁻¹ ^ 2) * (1 - (n : ℝ)⁻¹)⁻¹ := by
          rw [tsum_geometric_of_lt_one hr_nonneg hr_lt_one]
      _ = ((n : ℝ) * (n - 1))⁻¹ := by
          field_simp
  simp_rw [div_eq_mul_inv]
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left hgeom hlog

/-- For every natural number `n`, `log n / (n (n - 1)) ≤ 2 log n / n ^ 2`. -/
theorem log_div_mul_sub_one_le_two_mul_log_div_sq (n : ℕ) :
    Real.log n / ((n : ℝ) * (n - 1)) ≤ 2 * (Real.log n / (n : ℝ) ^ 2) := by
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  have hn_cast : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  rw [mul_div_assoc', div_le_div_iff₀ (by nlinarith) (by positivity)]
  have hsq : (n : ℝ) ^ 2 ≤ 2 * ((n : ℝ) * (n - 1)) := by nlinarith
  linarith [mul_le_mul_of_nonneg_left hsq hlog]

/-- The majorant series `∑ log n / (n (n - 1))` over all natural numbers is summable. -/
theorem summable_log_div_mul_sub_one :
    Summable (fun n : ℕ ↦ Real.log n / ((n : ℝ) * (n - 1))) := by
  refine Summable.of_nonneg_of_le (fun n ↦ ?_)
    (f := fun n : ℕ ↦ 4 * (n : ℝ) ^ (-3 / 2 : ℝ)) (fun n ↦ ?_)
    ((Real.summable_nat_rpow.mpr (by norm_num : (-3 / 2 : ℝ) < -1)).mul_left 4)
  · rcases lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp
    · have hn_cast : (2 : ℝ) ≤ n := by exact_mod_cast hn
      exact div_nonneg (Real.log_nonneg (by linarith)) (by nlinarith)
  · rcases lt_or_ge n 2 with hn | hn
    · interval_cases n <;> norm_num
    · have hn_cast : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hn_pos : (0 : ℝ) < n := by linarith
      have hlog : Real.log n ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
        have := Real.log_le_rpow_div hn_pos.le (by norm_num : (0 : ℝ) < 1 / 2)
        linarith
      calc Real.log n / ((n : ℝ) * (n - 1))
          ≤ 2 * (Real.log n / (n : ℝ) ^ 2) := log_div_mul_sub_one_le_two_mul_log_div_sq n
        _ ≤ 2 * (2 * (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2) := by gcongr
        _ = 4 * ((n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ (2 : ℝ)) := by
            rw [Real.rpow_two]
            ring
        _ = 4 * (n : ℝ) ^ (-3 / 2 : ℝ) := by
            rw [← Real.rpow_sub hn_pos]
            norm_num

/-- The prime-supported series `∑_p log p / (p (p - 1))` is summable. -/
theorem summable_prime_log_div_mul_sub_one :
    Summable (fun p : ℕ ↦ if p.Prime then Real.log p / ((p : ℝ) * (p - 1)) else 0) :=
  (summable_log_div_mul_sub_one.indicator {p : ℕ | p.Prime}).congr fun p ↦ by
    simp [Set.indicator_apply]

/-- Over `Nat.primesLE n`, the sum of `log p / (p (p - 1))` is at most `2 log 4`. -/
theorem sum_primesLE_log_div_mul_sub_one_le (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * (p - 1)) ≤ 2 * Real.log 4 := by
  calc ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * (p - 1))
      ≤ ∑ p ∈ Nat.primesLE n, 2 * (Real.log p / (p : ℝ) ^ 2) :=
        sum_le_sum fun p _ ↦ log_div_mul_sub_one_le_two_mul_log_div_sq p
    _ = 2 * ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ) ^ 2 := (mul_sum _ _ _).symm
    _ ≤ 2 * (2 * Real.log 4 / 2) :=
        mul_le_mul_of_nonneg_left
          (sum_log_div_sq_le_of_prime (by norm_num : (0 : ℝ) < 2)
            (fun _ hp ↦ Nat.prime_of_mem_primesLE hp)
            (fun _ hp ↦ by exact_mod_cast Nat.two_le_of_mem_primesLE hp))
          zero_le_two
    _ = 2 * Real.log 4 := by ring

/-- The infinite prime sum `∑'_p log p / (p (p - 1))` is at most `2 log 4`. -/
theorem tsum_prime_log_div_mul_sub_one_le :
    (∑' p : ℕ, if p.Prime then Real.log p / ((p : ℝ) * (p - 1)) else 0) ≤ 2 * Real.log 4 := by
  refine Real.tsum_le_of_sum_le (fun p ↦ ?_) fun s ↦ ?_
  · split_ifs with hp
    · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      exact div_nonneg (Real.log_nonneg (by linarith)) (by nlinarith)
    · exact le_rfl
  · rw [← sum_filter]
    refine (sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ ↦ ?_).trans
      (sum_primesLE_log_div_mul_sub_one_le (s.sup id))
    · intro p hp
      exact Nat.mem_primesLE.mpr ⟨le_sup (f := id) (mem_of_mem_filter p hp), (mem_filter.mp hp).2⟩
    · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
      exact div_nonneg (Real.log_nonneg (by linarith)) (by nlinarith)

/-- Regrouping `∑_{1 ≤ n ≤ N} Λ(n) / n` into the prime sum over `Nat.primesLE N` plus the higher
prime-power terms `2 ≤ k ≤ p.log N`. -/
theorem sum_Ioc_vonMangoldt_div_eq_sum_primesLE_add (N : ℕ) :
    ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ) =
      (∑ p ∈ Nat.primesLE N, Real.log p / p) +
        ∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 2 (p.log N), Real.log p / (p : ℝ) ^ k := by
  have hIoc : Ioc 0 N = Icc 1 N := rfl
  rw [hIoc, Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log
    (fun n hn ↦ by rw [vonMangoldt_eq_zero_iff.mpr hn, zero_div]), ← sum_add_distrib]
  refine sum_congr rfl fun p hp ↦ ?_
  have hp_prime := Nat.prime_of_mem_primesLE hp
  have hlog_pos : 1 ≤ p.log N := Nat.log_pos hp_prime.one_lt (Nat.le_of_mem_primesLE hp)
  have hIcc : Icc 1 (p.log N) = insert 1 (Icc 2 (p.log N)) := by
    ext k
    simp only [mem_Icc, mem_insert]
    omega
  rw [hIcc, sum_insert (by simp), pow_one, vonMangoldt_apply_prime hp_prime]
  congr 1
  refine sum_congr rfl fun k hk ↦ ?_
  rw [vonMangoldt_apply_pow (by grind), vonMangoldt_apply_prime hp_prime, Nat.cast_pow]

/-- The prime sum `∑_{p ≤ N} log p / p` is at most the von Mangoldt sum `∑_{1 ≤ n ≤ N} Λ(n) / n`. -/
theorem sum_primesLE_log_div_le_sum_Ioc_vonMangoldt_div (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ) := by
  rw [sum_Ioc_vonMangoldt_div_eq_sum_primesLE_add]
  refine le_add_of_nonneg_right (sum_nonneg fun p hp ↦ sum_nonneg fun k _ ↦ ?_)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le
  exact div_nonneg (Real.log_nonneg hp1) (by positivity)

/-- The higher prime-power difference `∑_{1 ≤ n ≤ N} Λ(n) / n - ∑_{p ≤ N} log p / p` is at most
`2 log 4` for every `N`. -/
theorem sum_Ioc_vonMangoldt_div_sub_sum_primesLE_le (N : ℕ) :
    (∑ n ∈ Ioc 0 N, Λ n / (n : ℝ)) - ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ 2 * Real.log 4 := by
  rw [sum_Ioc_vonMangoldt_div_eq_sum_primesLE_add, add_sub_cancel_left]
  exact (sum_le_sum fun p _ ↦ sum_Icc_two_log_div_pow_le p (p.log N)).trans
    (sum_primesLE_log_div_mul_sub_one_le N)

/-- The infinite sum of `Λ(n) / n` over all non-prime `n` is at most `2 log 4`. -/
theorem tsum_vonMangoldt_nonprime_div_le :
    (∑' n : ℕ, (if n.Prime then 0 else Λ n) / (n : ℝ)) ≤ 2 * Real.log 4 := by
  refine Real.tsum_le_of_sum_le (fun n ↦ ?_) fun s ↦ ?_
  · split_ifs <;> positivity
  · set N := s.sup id
    have hsub : ∑ n ∈ s, (if n.Prime then 0 else Λ n) / (n : ℝ) ≤
        ∑ n ∈ Icc 0 N, (if n.Prime then 0 else Λ n) / (n : ℝ) :=
      sum_le_sum_of_subset_of_nonneg
        (fun n hn ↦ mem_Icc.mpr ⟨Nat.zero_le n, le_sup (f := id) hn⟩)
        (fun _ _ _ ↦ by split_ifs <;> positivity)
    have hIcc : ∑ n ∈ Icc 0 N, (if n.Prime then 0 else Λ n) / (n : ℝ) =
        (∑ n ∈ Ioc 0 N, Λ n / (n : ℝ)) - ∑ p ∈ Nat.primesLE N, Real.log p / p := by
      rw [← add_sum_Ioc_eq_sum_Icc (Nat.zero_le N)]
      simp only [Nat.cast_zero, div_zero, zero_add]
      rw [Nat.primesLE_eq_filter_Ioc_zero, sum_filter, ← sum_sub_distrib]
      refine sum_congr rfl fun n _ ↦ ?_
      split_ifs with hn
      · simp [vonMangoldt_apply_prime hn]
      · simp
    exact hsub.trans (hIcc.le.trans (sum_Ioc_vonMangoldt_div_sub_sum_primesLE_le N))

end HigherPrimePowers

/-! ### Mertens's estimate for the von Mangoldt sum -/

section VonMangoldtMertens

/-- Floor replacement from below: for every real `x`, `log ⌊x⌋₊! ≤ x ∑_{1 ≤ n ≤ x} Λ(n) / n`. -/
theorem log_floor_factorial_le_mul_sum_Ioc_vonMangoldt_div (x : ℝ) :
    Real.log ⌊x⌋₊ ! ≤ x * ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n : ℝ) := by
  rcases lt_or_ge x 0 with hx | hx
  · simp [Nat.floor_of_nonpos hx.le]
  rw [Chebyshev.log_floor_factorial_eq_sum_vonMangoldt, mul_sum]
  refine sum_le_sum fun n _ ↦ ?_
  calc Λ n * (⌊x / n⌋₊ : ℝ) ≤ Λ n * (x / n) :=
        mul_le_mul_of_nonneg_left (Nat.floor_le (div_nonneg hx (Nat.cast_nonneg n)))
          vonMangoldt_nonneg
    _ = x * (Λ n / n) := by ring

/-- Floor replacement from above: for every real `x`,
`x (∑_{1 ≤ n ≤ x} Λ(n) / n) - log ⌊x⌋₊! ≤ ψ(x)`. -/
theorem mul_sum_Ioc_vonMangoldt_div_sub_log_floor_factorial_le_psi (x : ℝ) :
    x * (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n : ℝ)) - Real.log ⌊x⌋₊ ! ≤ ψ x := by
  rw [Chebyshev.log_floor_factorial_eq_sum_vonMangoldt, Chebyshev.psi, mul_sum, ← sum_sub_distrib]
  refine sum_le_sum fun n _ ↦ ?_
  have hlt : x / n - 1 < (⌊x / n⌋₊ : ℝ) := Nat.sub_one_lt_floor (x / n)
  calc x * (Λ n / n) - Λ n * (⌊x / n⌋₊ : ℝ)
      = Λ n * (x / n - (⌊x / n⌋₊ : ℝ)) := by ring
    _ ≤ Λ n * 1 := mul_le_mul_of_nonneg_left (by linarith) vonMangoldt_nonneg
    _ = Λ n := mul_one _

/-- **Lower von Mangoldt Mertens bound**: for `x ≥ 0`,
`log x - 3 / 2 ≤ ∑_{1 ≤ n ≤ x} Λ(n) / n`. -/
theorem le_sum_Ioc_vonMangoldt_div {x : ℝ} (hx : 0 ≤ x) :
    Real.log x - 3 / 2 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n : ℝ) := by
  rcases lt_or_ge x 1 with hx1 | hx1
  · have hsum : (0 : ℝ) ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n : ℝ) :=
      sum_nonneg fun _ _ ↦ div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
    linarith [Real.log_nonpos hx hx1.le]
  have hx0 : 0 < x := by linarith
  have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.two_le_pi])
  have hlog : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx0
  have hfac := (Real.le_log_floor_factorial hx1).trans
    (log_floor_factorial_le_mul_sum_Ioc_vonMangoldt_div x)
  rw [← mul_le_mul_iff_right₀ hx0]
  linarith

/-- **Upper von Mangoldt Mertens bound**: for `x ≥ 1`,
`∑_{1 ≤ n ≤ x} Λ(n) / n ≤ log x + log 4 + 4`. -/
theorem sum_Ioc_vonMangoldt_div_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n : ℝ) ≤ Real.log x + Real.log 4 + 4 := by
  have hx0 : 0 < x := by linarith
  have hlog : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx0
  have hpsi := (mul_sum_Ioc_vonMangoldt_div_sub_log_floor_factorial_le_psi x).trans
    (Chebyshev.psi_le_const_mul_self hx0.le)
  have hfac := Real.log_floor_factorial_le hx
  rw [← mul_le_mul_iff_right₀ hx0]
  nlinarith

/-- **Two-sided von Mangoldt Mertens bound**: for `x ≥ 1`,
`|∑_{1 ≤ n ≤ x} Λ(n) / n - log x| ≤ log 4 + 4`. -/
theorem abs_sum_Ioc_vonMangoldt_div_sub_log_le {x : ℝ} (hx : 1 ≤ x) :
    |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n : ℝ)) - Real.log x| ≤ Real.log 4 + 4 := by
  have hlo := le_sum_Ioc_vonMangoldt_div (by linarith : 0 ≤ x)
  have hhi := sum_Ioc_vonMangoldt_div_le hx
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]
  constructor <;> linarith

/-- Asymptotic form of the von Mangoldt Mertens estimate:
`∑_{1 ≤ n ≤ x} Λ(n) / n - log x = O(1)` as `x → ∞`. -/
theorem sum_Ioc_vonMangoldt_div_sub_log_isBigO :
    (fun x : ℝ ↦ (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n : ℝ)) - Real.log x) =O[atTop] (1 : ℝ → ℝ) := by
  refine IsBigO.of_bound (Real.log 4 + 4) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.norm_eq_abs, Pi.one_apply, norm_one, mul_one]
  exact abs_sum_Ioc_vonMangoldt_div_sub_log_le hx

end VonMangoldtMertens

/-! ### Mertens's first theorem on inclusive, strict, integer, and interval prime cutoffs -/

section PrimeMertens

/-- **Mertens's first theorem (inclusive lower bound)**: for real `x ≥ 0`,
`log x - (3 / 2 + 2 log 4) ≤ ∑_{p ≤ x} log p / p`. -/
theorem le_sum_primesLE_floor_log_div {x : ℝ} (hx : 0 ≤ x) :
    Real.log x - (3 / 2 + 2 * Real.log 4) ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p := by
  linarith [le_sum_Ioc_vonMangoldt_div hx, sum_Ioc_vonMangoldt_div_sub_sum_primesLE_le ⌊x⌋₊]

/-- **Mertens's first theorem (inclusive upper bound)**: for real `x ≥ 1`,
`∑_{p ≤ x} log p / p ≤ log x + log 4 + 4`. -/
theorem sum_primesLE_floor_log_div_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p ≤ Real.log x + Real.log 4 + 4 :=
  (sum_primesLE_log_div_le_sum_Ioc_vonMangoldt_div ⌊x⌋₊).trans (sum_Ioc_vonMangoldt_div_le hx)

/-- **Mertens's first theorem (inclusive two-sided bound)**: for real `x ≥ 1`,
`|∑_{p ≤ x} log p / p - log x| ≤ log 4 + 4`. -/
theorem abs_sum_primesLE_floor_log_div_sub_log_le {x : ℝ} (hx : 1 ≤ x) :
    |(∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p) - Real.log x| ≤ Real.log 4 + 4 := by
  have hlo := le_sum_primesLE_floor_log_div (by linarith : 0 ≤ x)
  have hhi := sum_primesLE_floor_log_div_le hx
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [h4, Real.log_pow]
    ring
  have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  rw [abs_le]
  constructor <;> linarith

/-- Asymptotic form of Mertens's first theorem with inclusive cutoff:
`∑_{p ≤ x} log p / p - log x = O(1)` as `x → ∞`. -/
theorem sum_primesLE_floor_log_div_sub_log_isBigO :
    (fun x : ℝ ↦ (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p) - Real.log x) =O[atTop] (1 : ℝ → ℝ) := by
  refine IsBigO.of_bound (Real.log 4 + 4) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.norm_eq_abs, Pi.one_apply, norm_one, mul_one]
  exact abs_sum_primesLE_floor_log_div_sub_log_le hx

/-- **Mertens's first theorem at integer cutoffs (lower bound)**: for every natural number `n`,
`log n - (3 / 2 + 2 log 4) ≤ ∑_{p ≤ n} log p / p`. -/
theorem le_sum_primesLE_log_div (n : ℕ) :
    Real.log n - (3 / 2 + 2 * Real.log 4) ≤ ∑ p ∈ Nat.primesLE n, Real.log p / p := by
  have h := le_sum_primesLE_floor_log_div (x := (n : ℝ)) (Nat.cast_nonneg n)
  rwa [Nat.floor_natCast] at h

/-- **Mertens's first theorem at integer cutoffs (upper bound)**: for every natural number `n`,
`∑_{p ≤ n} log p / p ≤ log n + log 4 + 4`. -/
theorem sum_primesLE_log_div_le (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 + 4 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Nat.primesLE_zero, sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  · have h := sum_primesLE_floor_log_div_le (x := (n : ℝ))
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
    rwa [Nat.floor_natCast] at h

/-- **Mertens's first theorem at integer cutoffs (two-sided bound)**: for every natural number `n`,
`|∑_{p ≤ n} log p / p - log n| ≤ log 4 + 4`. -/
theorem abs_sum_primesLE_log_div_sub_log_le (n : ℕ) :
    |(∑ p ∈ Nat.primesLE n, Real.log p / p) - Real.log n| ≤ Real.log 4 + 4 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Nat.primesLE_zero, sum_empty, Nat.cast_zero, Real.log_zero, sub_self, abs_zero]
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  · have h := abs_sum_primesLE_floor_log_div_sub_log_le (x := (n : ℝ))
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
    rwa [Nat.floor_natCast] at h

/-- Monotonicity between strict and inclusive Mertens sums:
`∑_{p < x} log p / p ≤ ∑_{p ≤ x} log p / p` for every real `x`. -/
theorem sum_primesBelow_ceil_log_div_le_sum_primesLE_floor (x : ℝ) :
    ∑ p ∈ Nat.primesBelow ⌈x⌉₊, Real.log p / p ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p := by
  refine sum_le_sum_of_subset_of_nonneg (primesBelow_ceil_subset_primesLE_floor x) fun p hp _ ↦ ?_
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le
  exact div_nonneg (Real.log_nonneg hp1) (by positivity)

/-- **Strict-versus-inclusive Mertens comparison**: for `x ≥ 1`, changing `p ≤ x` to `p < x` reduces
the Mertens sum by at most `log x / x` (and by `0` unless `x` is a prime integer). -/
theorem sum_primesLE_floor_log_div_sub_sum_primesBelow_ceil_le {x : ℝ} (hx : 1 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p) - ∑ p ∈ Nat.primesBelow ⌈x⌉₊, Real.log p / p ≤
      Real.log x / x := by
  rw [sum_primesLE_floor_eq_sum_primesBelow_ceil_add, add_sub_cancel_left]
  split_ifs with h
  · rw [h.1]
  · exact div_nonneg (Real.log_nonneg hx) (by positivity)

/-- **Mertens's first theorem (strict upper bound)**: for real `x ≥ 1`,
`∑_{p < x} log p / p ≤ log x + log 4 + 4`. -/
theorem sum_primesBelow_ceil_log_div_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ p ∈ Nat.primesBelow ⌈x⌉₊, Real.log p / p ≤ Real.log x + Real.log 4 + 4 :=
  (sum_primesBelow_ceil_log_div_le_sum_primesLE_floor x).trans (sum_primesLE_floor_log_div_le hx)

/-- **Mertens's first theorem (strict lower bound)**: for real `x ≥ 0`,
`log x - (5 / 2 + 2 log 4) ≤ ∑_{p < x} log p / p`. -/
theorem le_sum_primesBelow_ceil_log_div {x : ℝ} (hx : 0 ≤ x) :
    Real.log x - (5 / 2 + 2 * Real.log 4) ≤ ∑ p ∈ Nat.primesBelow ⌈x⌉₊, Real.log p / p := by
  rcases lt_or_ge x 1 with hx1 | hx1
  · have hsum : (0 : ℝ) ≤ ∑ p ∈ Nat.primesBelow ⌈x⌉₊, Real.log p / p := by
      refine sum_nonneg fun p hp ↦ ?_
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt.le
      exact div_nonneg (Real.log_nonneg hp1) (by positivity)
    linarith [Real.log_nonpos hx hx1.le, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  have hx0 : 0 < x := by linarith
  have hlogx : Real.log x / x ≤ 1 := by
    rw [div_le_one hx0]
    linarith [Real.log_le_sub_one_of_pos hx0]
  linarith [le_sum_primesLE_floor_log_div hx,
    sum_primesLE_floor_log_div_sub_sum_primesBelow_ceil_le hx1]

/-- **Mertens's first theorem (strict two-sided bound)**: for real `x ≥ 1`,
`|∑_{p < x} log p / p - log x| ≤ log 4 + 4`. -/
theorem abs_sum_primesBelow_ceil_log_div_sub_log_le {x : ℝ} (hx : 1 ≤ x) :
    |(∑ p ∈ Nat.primesBelow ⌈x⌉₊, Real.log p / p) - Real.log x| ≤ Real.log 4 + 4 := by
  have hlo := le_sum_primesBelow_ceil_log_div (by linarith : 0 ≤ x)
  have hhi := sum_primesBelow_ceil_log_div_le hx
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [h4, Real.log_pow]
    ring
  have hlog2 : Real.log 2 < 3 / 4 := by linarith [Real.log_two_lt_d9]
  rw [abs_le]
  constructor <;> linarith

/-- **Mertens's first theorem on `Nat.primesBelow n`**: for every natural number `n`,
`|∑_{p < n} log p / p - log n| ≤ log 4 + 4`. -/
theorem abs_sum_primesBelow_log_div_sub_log_le (n : ℕ) :
    |(∑ p ∈ Nat.primesBelow n, Real.log p / p) - Real.log n| ≤ Real.log 4 + 4 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Nat.primesBelow_zero, sum_empty, Nat.cast_zero, Real.log_zero, sub_self, abs_zero]
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  · have h := abs_sum_primesBelow_ceil_log_div_sub_log_le (x := (n : ℝ))
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
    rwa [Nat.ceil_natCast] at h

/-- Asymptotic form of Mertens's first theorem with strict cutoff:
`∑_{p < x} log p / p - log x = O(1)` as `x → ∞`. -/
theorem sum_primesBelow_ceil_log_div_sub_log_isBigO :
    (fun x : ℝ ↦ (∑ p ∈ Nat.primesBelow ⌈x⌉₊, Real.log p / p) - Real.log x) =O[atTop]
      (1 : ℝ → ℝ) := by
  refine IsBigO.of_bound (Real.log 4 + 4) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.norm_eq_abs, Pi.one_apply, norm_one, mul_one]
  exact abs_sum_primesBelow_ceil_log_div_sub_log_le hx

/-- **Mertens's interval estimate**: for `1 ≤ y ≤ x`,
`|∑_{y < p ≤ x} log p / p - log (x / y)| ≤ 2 (log 4 + 4)`. -/
theorem abs_sum_primesLE_filter_gt_log_div_sub_log_div_le {x y : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) :
    |(∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ y < (p : ℝ)), Real.log p / p) -
        Real.log (x / y)| ≤ 2 * (Real.log 4 + 4) := by
  have hx : 1 ≤ x := hy.trans hyx
  rw [sum_primesLE_filter_gt_eq_sub _ hyx, Real.log_div (by positivity) (by positivity)]
  have hx_bound := abs_sum_primesLE_floor_log_div_sub_log_le hx
  have hy_bound := abs_sum_primesLE_floor_log_div_sub_log_le hy
  rw [abs_le] at hx_bound hy_bound ⊢
  constructor <;> linarith

end PrimeMertens

end TauCeti

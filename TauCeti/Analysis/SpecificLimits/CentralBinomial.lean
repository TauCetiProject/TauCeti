/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.RingTheory.Binomial

/-!
# Central-binomial probabilities and series

The normalized central binomial coefficient has square at most `1 / (n + 1)`;
in particular it tends to zero. This estimate gives vanishing individual return
probabilities even when the return series diverges.

For real `q`, the series with terms `Nat.centralBinom n * q ^ n` is summable
exactly when `|q| < 1 / 4`. At the boundary, the elementary lower bound on central
binomial coefficients compares this series with the harmonic series; no asymptotic
formula is needed.

Inside the radius the sum is `1 / √(1 - 4q)`: the central binomial coefficients divided by
`4 ^ n` are the multiset coefficients of one half, so this is the binomial series of
`(1 - 4q) ^ (-1/2)`.

The extended nonnegative sum detects the same boundary without the convention that
an unsummable real series has sum zero. In particular, for a nearest-neighbor walk
with right-step probability `p`, the sum of the even-time return probabilities
`Nat.centralBinom n * (p * (1 - p)) ^ n` is infinite exactly at `p = 1 / 2`.
This is the numerical input to the Green-function recurrence criterion. For every
nonnegative `q` the extended sum equals `1 / √(1 - 4q)`, read as infinite from `q = 1 / 4` on;
at `q = p (1 - p)` this is `1 / |2p - 1|`, which gives the return probability of the walk.

The random-walk application follows J. R. Norris, *Markov Chains* (1997), §1.6.
The estimates used here are Mathlib's `Nat.centralBinom_le_four_pow` and
`Nat.four_pow_le_two_mul_self_mul_centralBinom`; the upper bound uses
`Nat.succ_mul_centralBinom_succ`.
-/

public section

open scoped NNReal ENNReal

namespace TauCeti

/-- An elementary squared upper bound for the normalized central binomial coefficient. -/
theorem centralBinom_div_four_pow_sq_le (n : ℕ) :
    ((n.centralBinom : ℝ) / 4 ^ n) ^ 2 ≤ 1 / (n + 1) := by
  have hb : ∀ n : ℕ, (n + 1 : ℝ) * ((n.centralBinom : ℝ) / 4 ^ n) ^ 2 ≤ 1 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      have hr : ((n + 1).centralBinom : ℝ) / 4 ^ (n + 1) =
          (2 * n + 1) / (2 * (n + 1)) * ((n.centralBinom : ℝ) / 4 ^ n) := by
        have h := congrArg (fun k : ℕ => (k : ℝ)) (Nat.succ_mul_centralBinom_succ n)
        push_cast at h
        rw [pow_succ]
        field_simp
        nlinarith
      rw [hr]
      push_cast
      have hn : (0 : ℝ) < n + 1 := by positivity
      have hfactor : (n + 2 : ℝ) * ((2 * n + 1) / (2 * (n + 1))) ^ 2 ≤ n + 1 := by
        field_simp
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      calc
        _ ≤ (n + 1) * ((n.centralBinom : ℝ) / 4 ^ n) ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_right hfactor
            (sq_nonneg ((n.centralBinom : ℝ) / 4 ^ n))]
        _ ≤ 1 := ih
  exact (le_div_iff₀ (by positivity)).2 (by nlinarith [hb n])

/-- Central binomial probabilities tend to zero, despite their divergent sum. -/
theorem tendsto_centralBinom_div_four_pow :
    Filter.Tendsto (fun n : ℕ => (n.centralBinom : ℝ) / 4 ^ n)
      Filter.atTop (nhds 0) := by
  have hsq : Filter.Tendsto (fun n : ℕ => ((n.centralBinom : ℝ) / 4 ^ n) ^ 2)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun _ => sq_nonneg _) centralBinom_div_four_pow_sq_le
      (by simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [Real.sqrt_sq_eq_abs, abs_div, Nat.abs_cast, abs_pow, show |(4 : ℝ)| = 4 by norm_num,
    Real.sqrt_zero] using hsq.sqrt

/-- The central-binomial series diverges at its radius of convergence. -/
theorem not_summable_centralBinom_div_four_pow :
    ¬ Summable (fun n : ℕ => (n.centralBinom : ℝ) / 4 ^ n) := by
  intro h
  apply Real.not_summable_natCast_inv
  refine (h.mul_left 2).of_nonneg_of_le (fun n => by positivity) fun n => ?_
  rcases n.eq_zero_or_pos with rfl | hn
  · norm_num
  have hbound : (4 : ℝ) ^ n ≤ 2 * n * (n.centralBinom : ℝ) := by
    exact_mod_cast Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← mul_div_assoc, le_div_iff₀ (by positivity : (0 : ℝ) < 4 ^ n),
    inv_mul_le_iff₀ hn']
  nlinarith

/-- A real central-binomial power series is summable exactly inside its
radius of convergence; both boundary points are excluded. -/
theorem summable_centralBinom_mul_pow_iff {q : ℝ} :
    Summable (fun n : ℕ => (n.centralBinom : ℝ) * q ^ n) ↔ |q| < 1 / 4 := by
  have key (q : ℝ) (hq : 0 ≤ q) :
      Summable (fun n : ℕ => (n.centralBinom : ℝ) * q ^ n) ↔ q < 1 / 4 := by
    constructor
    · intro h
      by_contra hlt
      have hq' : 1 / 4 ≤ q := le_of_not_gt hlt
      apply not_summable_centralBinom_div_four_pow
      refine h.of_nonneg_of_le (fun n => by positivity) fun n => ?_
      rw [div_eq_mul_inv, ← inv_pow]
      gcongr
      simpa using hq'
    · intro hq'
      have hgeo : Summable (fun n : ℕ => (4 * q) ^ n) :=
        summable_geometric_of_lt_one (by positivity) (by linarith)
      refine hgeo.of_nonneg_of_le (fun n => by positivity) fun n => ?_
      rw [mul_pow]
      gcongr
      exact_mod_cast Nat.centralBinom_le_four_pow n
  rw [← summable_abs_iff]
  simpa only [abs_mul, abs_pow, Nat.abs_cast] using key |q| (abs_nonneg q)

/-- **The central-binomial generating function.** Inside its radius of convergence,
`∑ n, (2n choose n) q ^ n = 1 / √(1 - 4q)`. -/
theorem hasSum_centralBinom_mul_pow {q : ℝ} (hq : |q| < 1 / 4) :
    HasSum (fun n : ℕ => (n.centralBinom : ℝ) * q ^ n) (√(1 - 4 * q))⁻¹ := by
  have h := hasSum_multichoose_mul_geometric_of_abs_lt_one (r := 2⁻¹) (x := 4 * q)
    (by rw [abs_mul, abs_of_pos four_pos]; linarith)
  convert h using 1
  · ext n
    rw [Ring.multichoose_inv_two, mul_pow]
    field_simp
  · norm_num [Real.sqrt_eq_rpow]

end TauCeti

namespace NNReal

/-- The extended central-binomial series is infinite exactly at and beyond the
radius of convergence. This statement also includes `q = 0`. -/
theorem tsum_centralBinom_mul_pow_eq_top_iff (q : ℝ≥0) :
    (∑' n : ℕ, (n.centralBinom : ℝ≥0∞) * (q : ℝ≥0∞) ^ n) = ∞ ↔ 1 / 4 ≤ q := by
  rw [← NNReal.coe_le_coe]
  simpa only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_natCast,
    NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast,
    TauCeti.summable_centralBinom_mul_pow_iff, abs_of_nonneg q.coe_nonneg, not_lt,
    NNReal.coe_le_coe, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
    (ENNReal.tsum_coe_eq_top_iff_not_summable_coe
      (f := fun n : ℕ => (n.centralBinom : ℝ≥0) * q ^ n))

/-- The even-time return series of a nearest-neighbor walk is infinite exactly
for the symmetric step law. Deterministic steps (`p = 0` or `p = 1`) are included. -/
theorem tsum_centralBinom_mul_mul_one_sub_pow_eq_top_iff (p : ℝ≥0) :
    (∑' n : ℕ, (n.centralBinom : ℝ≥0∞) * ((p * (1 - p) : ℝ≥0) : ℝ≥0∞) ^ n) = ∞ ↔
      p = 1 / 2 := by
  rw [tsum_centralBinom_mul_pow_eq_top_iff]
  constructor
  · intro h
    have hp : p ≤ 1 := by
      by_contra hp
      simp [tsub_eq_zero_of_le (not_le.1 hp).le] at h
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_sub hp] at h
    have h' : (1 : ℝ) / 4 ≤ (p : ℝ) * (1 - p) := by exact_mod_cast h
    have heq : (p : ℝ) = 1 / 2 := by nlinarith [sq_nonneg ((p : ℝ) - 1 / 2)]
    exact NNReal.coe_injective (by simpa using heq)
  · rintro rfl
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_sub (by norm_num)]
    norm_num

/-- The extended central-binomial generating function, for every nonnegative `q`:
`∑ n, (2n choose n) q ^ n = 1 / √(1 - 4q)`. At and beyond the radius of convergence both sides
are infinite, since the real square root of a nonpositive number is zero. -/
theorem tsum_centralBinom_mul_pow (q : ℝ≥0) :
    ∑' n : ℕ, (n.centralBinom : ℝ≥0∞) * (q : ℝ≥0∞) ^ n =
      (ENNReal.ofReal √(1 - 4 * (q : ℝ)))⁻¹ := by
  rcases lt_or_ge q (1 / 4) with hq | hq
  · have hq' : (q : ℝ) < 1 / 4 := by exact_mod_cast hq
    have hs := TauCeti.hasSum_centralBinom_mul_pow (q := q) (by rwa [abs_of_nonneg q.coe_nonneg])
    have hterm (n : ℕ) : (n.centralBinom : ℝ≥0∞) * (q : ℝ≥0∞) ^ n =
        ENNReal.ofReal ((n.centralBinom : ℝ) * (q : ℝ) ^ n) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_pow q.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs.summable, hs.tsum_eq,
      ENNReal.ofReal_inv_of_pos (Real.sqrt_pos.2 (by linarith))]
  · have hq' : (1 : ℝ) / 4 ≤ q := by exact_mod_cast hq
    rw [(tsum_centralBinom_mul_pow_eq_top_iff q).2 hq, Real.sqrt_eq_zero'.2 (by linarith),
      ENNReal.ofReal_zero, ENNReal.inv_zero]

end NNReal

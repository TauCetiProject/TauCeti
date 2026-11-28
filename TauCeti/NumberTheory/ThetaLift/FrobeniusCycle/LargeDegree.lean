/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ThetaLift.FrobeniusCycle.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Large degrees for Frobenius cycles

The degree in each letter must be large enough to control the proportion of monomials of
bounded defect, but small enough for polynomial interpolation over the residue field.
`FrobeniusCycle.IsLargeDegree` records these two bounds and the range of the parabolic
rank and tolerance. It supplies a strict interpolation bound for half of the cycle and
controls the loss from a prescribed defect threshold.

The size condition is that of `New.FrobeniusCycle.IsLargeDegree` in
`grh/src/New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) (`72fead1`).
-/

public section

open Real

namespace TauCeti.FrobeniusCycle

variable {W R : Type*} [CommRing W] [IsLocalRing W] [CommRing R] {N : ℕ}

/-- The large-degree condition for forms of degree `n` in each letter, with `k` variables per
letter, parabolic rank `r`, and relative error tolerance `θ`. -/
structure IsLargeDegree (T : FrobeniusCycle W R N) (k n r : ℕ) (θ : ℝ) : Prop where
  /-- The first parabolic block is nonempty. -/
  rank_pos : 0 < r
  /-- The first parabolic block is no larger than the second. -/
  two_mul_rank_le : 2 * r ≤ k
  /-- The tolerance is positive. -/
  tolerance_pos : 0 < θ
  /-- The tolerance is at most one. -/
  tolerance_le_one : θ ≤ 1
  /-- The fourth power of the degree does not exceed the residue field size. -/
  degree_pow_le : n ^ 4 ≤ T.q
  /-- The degree absorbs the logarithmic and Frobenius factors in the dimension bound. -/
  le_degree : ((N : ℝ) * k * log T.q / θ) ^ 5 * (T.P : ℝ) ^ (3 * r) ≤ n

/-- The large-degree condition is unchanged by mapping the target of the letter embeddings. -/
@[simp] theorem isLargeDegree_map_iff (T : FrobeniusCycle W R N) {S : Type*} [CommRing S]
    (f : R →+* S) {k n r : ℕ} {θ : ℝ} : (T.map f).IsLargeDegree k n r θ ↔
      T.IsLargeDegree k n r θ := by
  constructor <;> rintro ⟨hr, hk, hθ, hθ₁, hn, hlow⟩ <;>
    exact ⟨hr, hk, hθ, hθ₁, by simpa only [map_q] using hn,
      by simpa only [map_q, map_P] using hlow⟩

/-- The logarithm of the residue size is at least the number of letters. -/
theorem numLetters_le_log_q (T : FrobeniusCycle W R N) : (N : ℝ) ≤ log T.q := by
  rw [q_def, Nat.cast_pow, log_pow]
  have h := log_le_log (by norm_num : 0 < (5 : ℝ)) (Nat.cast_le.mpr T.five_le_P)
  have hP : 1 ≤ log (T.P : ℝ) := by linarith [log_five_gt_d9]
  exact le_mul_of_one_le_right (Nat.cast_nonneg _) hP

/-- The large-degree condition supplies the strict interpolation bound for a cycle with
`2 * ℓ` letters. In particular it pays for both the substitution degree and the auxiliary
polynomial degrees `n + k` within a half-cycle Frobenius power. -/
theorem IsLargeDegree.interpolation_bound {T : FrobeniusCycle W R N} {k n r : ℕ} {θ : ℝ}
    (h : T.IsLargeDegree k n r θ) : N * k * (N / 2 + 2) * n + n + k < T.P ^ (N / 2) := by
  obtain ⟨ℓ, hℓ⟩ := T.even
  have hN : N = 2 * (N / 2) := by omega
  have hN₀ : N ≠ 0 := T.neZero.ne
  have hN₂ : 2 ≤ N := by omega
  have hk₂ : 2 ≤ k := by have := h.rank_pos; have := h.two_mul_rank_le; omega
  have hNpow : 4 ≤ N ^ 2 := Nat.pow_le_pow_left hN₂ 2
  have hNk : 4 ≤ N ^ 2 * k := hNpow.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hS : (N : ℝ) ^ 2 * k ≤ (N : ℝ) * k * log T.q / θ := by
    calc
      _ = (N : ℝ) * k * N := by ring
      _ ≤ (N : ℝ) * k * log T.q := by gcongr; exact T.numLetters_le_log_q
      _ ≤ _ := (le_div_iff₀ h.tolerance_pos).mpr
        (mul_le_of_le_one_right (by positivity) h.tolerance_le_one)
  have hP : (1 : ℝ) ≤ T.P := by exact_mod_cast (by have := T.five_le_P; omega : 1 ≤ T.P)
  have hS₀ := (show 0 ≤ (N : ℝ) ^ 2 * k by positivity).trans hS
  have hn : 4 * N ^ 2 * k ≤ n := by
    have hA : 4 ≤ (N : ℝ) ^ 2 * k := by exact_mod_cast hNk
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    calc
      4 * (N : ℝ) ^ 2 * k ≤ ((N : ℝ) ^ 2 * k) ^ 2 := by nlinarith only [hA]
      _ ≤ ((N : ℝ) ^ 2 * k) ^ 5 := pow_le_pow_right₀ (by linarith) (by decide)
      _ ≤ ((N : ℝ) * k * log T.q / θ) ^ 5 := by gcongr
      _ ≤ _ := (le_mul_of_one_le_right (pow_nonneg hS₀ _) (one_le_pow₀ hP)).trans h.le_degree
  have hpow : n ^ 2 ≤ T.P ^ (N / 2) := by
    apply (pow_le_pow_iff_left₀ (n := 2) (Nat.zero_le _) (Nat.zero_le _) (by decide)).mp
    simpa only [← pow_mul, Nat.reduceMul, mul_comm (N / 2) 2, ← hN, ← T.q_def] using
      h.degree_pow_le
  have hfactor : N * k * (N / 2 + 2) + 1 + k < n := by
    have hhalf : N / 2 + 2 ≤ 2 * N := by omega
    have hmul := Nat.mul_le_mul_left (N * k) hhalf
    nlinarith only [hmul, hn, hNk, Nat.mul_le_mul_right k (show 1 ≤ N ^ 2 by omega)]
  have hn₀ : 0 < n := by nlinarith only [hn, hNk]
  calc
    _ ≤ (N * k * (N / 2 + 2) + 1 + k) * n := by
      nlinarith only [Nat.le_mul_of_pos_right k hn₀]
    _ < n ^ 2 := by simpa only [sq] using Nat.mul_lt_mul_of_pos_right hfactor hn₀
    _ ≤ _ := hpow

/-- The logarithm of the residue size is at least the step exponent. -/
theorem stepExponent_le_log_q (T : FrobeniusCycle W R N) : (T.e : ℝ) ≤ log T.q := by
  obtain ⟨ℓ, hℓ⟩ := T.even
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast (by have := T.neZero.ne; omega : 2 ≤ N)
  have hp := log_le_log (by norm_num : 0 < (2 : ℝ)) (Nat.cast_le.mpr T.prime.two_le)
  have hp' : (1 / 2 : ℝ) ≤ log (T.p : ℝ) := by linarith [log_two_gt_d9]
  rw [q_def, P_def, Nat.cast_pow, Nat.cast_pow, log_pow, log_pow]
  calc
    (T.e : ℝ) = 2 * T.e * (1 / 2) := by ring
    _ ≤ (N : ℝ) * T.e * log T.p := by gcongr
    _ = _ := mul_assoc _ _ _

/-- At the precision `c = 5 * N * (k² * e * N)`, the defect threshold `t = 3 * k * c`
fits the dimension-counting inequality `8 * N * k * t * P^(2r) ≤ θ * n`. -/
theorem IsLargeDegree.defect_count_bound {T : FrobeniusCycle W R N} {k n r : ℕ} {θ : ℝ}
    (h : T.IsLargeDegree k n r θ) :
    (8 : ℝ) * N * k * (3 * k * (5 * N * (k ^ 2 * (T.e : ℝ) * N))) *
      (T.P : ℝ) ^ (2 * r) ≤ θ * n := by
  obtain ⟨ℓ, hℓ⟩ := T.even
  have hN₂ : (2 : ℝ) ≤ N := by exact_mod_cast (by have := T.neZero.ne; omega : 2 ≤ N)
  have hk₂ : (2 : ℝ) ≤ k := by
    exact_mod_cast (by have := h.rank_pos; have := h.two_mul_rank_le; omega : 2 ≤ k)
  have hlog := T.numLetters_le_log_q
  have he := T.stepExponent_le_log_q
  have hL : 2 ≤ log T.q := hN₂.trans hlog
  let A : ℝ := N * k * log T.q
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hP : (1 : ℝ) ≤ T.P := by exact_mod_cast (by have := T.five_le_P; omega : 1 ≤ T.P)
  have hcoeff : 120 ≤ (N : ℝ) ^ 2 * k * 16 := by
    calc 120 ≤ (2 : ℝ) ^ 2 * 2 * 16 := by norm_num
         _ ≤ _ := by gcongr
  have hlogpow : 16 * (T.e : ℝ) ≤ log T.q ^ 5 := by
    calc
      _ ≤ 2 ^ 4 * log T.q := by gcongr; norm_num
      _ ≤ log T.q ^ 4 * log T.q := by gcongr
      _ = _ := by ring
  have hpoly : 120 * (N : ℝ) ^ 3 * k ^ 4 * T.e ≤ A ^ 5 := by
    calc
      _ ≤ ((N : ℝ) ^ 2 * k * 16) * ((N : ℝ) ^ 3 * k ^ 4 * T.e) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoeff
          (show 0 ≤ (N : ℝ) ^ 3 * k ^ 4 * T.e by positivity)
      _ = (N : ℝ) ^ 5 * k ^ 5 * (16 * T.e) := by ring
      _ ≤ (N : ℝ) ^ 5 * k ^ 5 * log T.q ^ 5 := by gcongr
      _ = _ := by dsimp only [A]; ring
  have hdiv : A ≤ A / θ := (le_div_iff₀ h.tolerance_pos).mpr
    (mul_le_of_le_one_right hA h.tolerance_le_one)
  have hscale : A ^ 5 ≤ θ * (A / θ) ^ 5 := by
    calc
      _ = A * A ^ 4 := by ring
      _ ≤ A * (A / θ) ^ 4 := by gcongr
      _ = _ := by field_simp
  calc
    _ = (120 * (N : ℝ) ^ 3 * k ^ 4 * T.e) * (T.P : ℝ) ^ (2 * r) := by ring
    _ ≤ A ^ 5 * (T.P : ℝ) ^ (3 * r) := by gcongr; omega
    _ ≤ θ * (((N : ℝ) * k * log T.q / θ) ^ 5 * (T.P : ℝ) ^ (3 * r)) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hscale (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left h.le_degree h.tolerance_pos.le

end TauCeti.FrobeniusCycle

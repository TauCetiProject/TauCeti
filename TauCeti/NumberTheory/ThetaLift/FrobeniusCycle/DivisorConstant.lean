/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ThetaLift.FrobeniusCycle.Basic

import Mathlib.Data.Nat.Log

/-!
# The divisor constant of a Frobenius cycle

The colength estimate for an edge Hecke operator has a contribution from deep monomials,
measured by the divisor constant. For the split at `r = ⌈log_p m⌉`, where `m` is the number of
lifts, the two terms after the prefactor `N a` are each at most `1 / (m p)` when `m > 1`
and `m r² ≤ k`. The rank bounds of the one-sided prime-sum construction ensure this
inequality. In a cycle with `2ℓ` letters the resulting colength contribution per coordinate
is at most `12 a ℓ / (m p)` at degree `a`.

The normalization and estimate follow `New.FrobeniusCycle.divisorConstant` and
`New.Data.three_mul_divisorConstant_le` in lsernau/grh-lean at
`72fead102f663d5c7a407964a13dc0cf9d977207`
(`grh/src/New/UpperBound/ElementaryDivisors/Depth.lean` and
`grh/src/New/UpperBound/Divisibility/MarkOperator.lean`).
-/

public section

namespace TauCeti.FrobeniusCycle

variable {W R : Type*} [CommRing W] [IsLocalRing W] [CommRing R] {N : ℕ}

/-- The divisor constant for `N` letters of degree `a` with `k` variables per letter, split
at `r`. Here `P` is the power of the cycle's Frobenius congruences. -/
noncomputable def divisorConstant (T : FrobeniusCycle W R N) (k a r : ℕ) : ℝ :=
  N * a * (1 / (T.P : ℝ) ^ (2 * r) + (r : ℝ) ^ 2 / (k * (T.P : ℝ)))

/-- The formula for the divisor constant in terms of the cycle power. -/
theorem divisorConstant_def (T : FrobeniusCycle W R N) (k a r : ℕ) :
    T.divisorConstant k a r =
      N * a * (1 / (T.P : ℝ) ^ (2 * r) + (r : ℝ) ^ 2 / (k * (T.P : ℝ))) := (rfl)

/-- The divisor constant vanishes in degree zero. -/
@[simp] theorem divisorConstant_degree_zero (T : FrobeniusCycle W R N) (k r : ℕ) :
    T.divisorConstant k 0 r = 0 := by simp [divisorConstant_def]

/-- The divisor constant is nonnegative, including in degree zero. -/
theorem divisorConstant_nonneg (T : FrobeniusCycle W R N) (k a r : ℕ) :
    0 ≤ T.divisorConstant k a r := by rw [divisorConstant_def]; positivity

/-- At the ceiling-log split, the divisor contribution is at most `6 N a / (m p)`. This
only needs `m r² ≤ k` for the rank, and puts no upper bound on the Frobenius exponent. -/
theorem three_mul_divisorConstant_le (T : FrobeniusCycle W R N) {k m : ℕ} (a : ℕ)
    (hm : 1 < m) (hk : m * (Nat.clog T.p m) ^ 2 ≤ k) :
    3 * T.divisorConstant k a (Nat.clog T.p m) ≤ 6 * N * a / (m * (T.p : ℝ)) := by
  let r := Nat.clog T.p m
  have hmpr : m ≤ T.p ^ r := Nat.le_pow_clog T.prime.one_lt m
  have hr : 0 < r := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h, pow_zero] at hmpr
    omega
  have he : T.e ≠ 0 := by
    intro he
    have h := T.five_le_pow
    simp [he] at h
  have hpP : T.p ≤ T.P := by rw [T.P_def]; exact Nat.le_self_pow he _
  have hmp : (m : ℝ) * T.p ≤ (T.P : ℝ) ^ (2 * r) := by
    exact_mod_cast calc
      m * T.p ≤ T.P ^ r * T.P ^ r :=
        Nat.mul_le_mul (hmpr.trans (Nat.pow_le_pow_left hpP _))
          (hpP.trans (Nat.le_self_pow hr.ne' _))
      _ = T.P ^ (2 * r) := by rw [two_mul, pow_add]
  have hp : (0 : ℝ) < T.p := by exact_mod_cast T.prime.pos
  have hpP' : (T.p : ℝ) ≤ T.P := by exact_mod_cast hpP
  have hP := hp.trans_le hpP'
  have hm₀ : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hk₀ : (0 : ℝ) < k := by
    exact_mod_cast (Nat.mul_pos (by omega) (pow_pos hr 2)).trans_le hk
  have hsmall : (r : ℝ) ^ 2 / (k * (T.P : ℝ)) ≤ 1 / (m * (T.p : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (mul_pos hm₀ hp)).2
    rw [one_mul, mul_left_comm, ← mul_assoc]
    have h₁ : (m : ℝ) * (r : ℝ) ^ 2 ≤ k := by exact_mod_cast hk
    exact (mul_le_mul_of_nonneg_right h₁ hp.le).trans
      (mul_le_mul_of_nonneg_left hpP' hk₀.le)
  have hlarge : 1 / (T.P : ℝ) ^ (2 * r) ≤ 1 / (m * (T.p : ℝ)) :=
    one_div_le_one_div_of_le (mul_pos hm₀ hp) hmp
  rw [divisorConstant_def]
  calc
    _ ≤ 3 * (N * a * (1 / (m * (T.p : ℝ)) + 1 / (m * (T.p : ℝ)))) := by
      gcongr
    _ = _ := by ring

/-- For ranks `m² ≤ 4x` and `x⁵ ≤ r₀`, with `x ≥ 2`, the source rank `r₀ + 1 - m`
pays for the ceiling-log split. Thus the divisor estimate applies at the ranks of the
one-sided prime-sum construction. -/
theorem three_mul_divisorConstant_le_of_rank_bounds (T : FrobeniusCycle W R N)
    {x m r₀ : ℕ} (a : ℕ) (hx : 2 ≤ x) (hm : 1 < m)
    (hmx : m ^ 2 ≤ 4 * x) (hrx : x ^ 5 ≤ r₀) :
    3 * T.divisorConstant (r₀ + 1 - m) a (Nat.clog T.p m) ≤ 6 * N * a / (m * (T.p : ℝ)) := by
  have hmx' : m ≤ x := by
    by_contra! h
    have hs : (x + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (by omega) _
    have hx' : (2 : ℝ) ≤ x := by exact_mod_cast hx
    have h₁ : ((x : ℝ) + 1) ^ 2 ≤ (m : ℝ) ^ 2 := by exact_mod_cast hs
    have h₂ : (m : ℝ) ^ 2 ≤ 4 * (x : ℝ) := by exact_mod_cast hmx
    nlinarith [mul_nonneg (sub_nonneg.mpr hx') (sub_nonneg.mpr hx')]
  have hlog : Nat.clog T.p m ≤ m := Nat.clog_le_of_le_pow
    (m.lt_two_pow_self.le.trans (Nat.pow_le_pow_left T.prime.two_le _))
  apply T.three_mul_divisorConstant_le a hm
  have hcost : m * Nat.clog T.p m ^ 2 + m ≤ r₀ := calc
    _ ≤ x * x ^ 2 + x := by gcongr; exact hlog.trans hmx'
    _ ≤ 2 * x ^ 3 := by
      rw [← pow_succ', two_mul]
      exact Nat.add_le_add_left (Nat.le_self_pow (by decide : 3 ≠ 0) x) _
    _ ≤ x ^ 4 := by rw [pow_succ' x 3]; gcongr
    _ ≤ x ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
    _ ≤ r₀ := hrx
  omega

end TauCeti.FrobeniusCycle

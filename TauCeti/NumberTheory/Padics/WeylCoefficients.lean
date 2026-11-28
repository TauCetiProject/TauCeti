/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Basic
import Mathlib.Analysis.Normed.Ring.Ultra
import TauCeti.NumberTheory.Padics.Factorial
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Norm bounds for Weyl normal-ordering coefficients

For the relation `∂x = x∂ + c` with central `c`, the normal ordering of `∂^m x^n`
has a term `x^(n - k) ∂^(m - k)` with coefficient `(m.choose k) (n.choose k) k! c^k`
for each `k ≤ min m n`. The binomial factors are integral, so growth is controlled by
the factorial and the scale `c`.

`TauCeti.norm_choose_mul_choose_mul_factorial_mul_pow_le` bounds these coefficients linearly in
`k` when `‖c‖^(p - 1) ≤ p`. It uses `TauCeti.div_sub_log_le_multiplicity_factorial` and
`Padic.norm_natCast_eq_zpow`. The linear bound lets exponential decay absorb the
normal-ordering coefficients in products of overconvergent series.
-/

public section

namespace TauCeti

/-- The Weyl normal-ordering coefficient `(m.choose k) (n.choose k) k! c^k` has norm at most
`p * (k + 1)` if `‖c‖^(p - 1) ≤ p`. In particular this scale condition holds for
`c = π⁻¹` in a normed extension of `ℚ_[p]` with `π^(p - 1) = -p`.
See Kedlaya, *Fourier transforms and p-adic 'Weil II'*, Proposition 4.1.3. -/
theorem norm_choose_mul_choose_mul_factorial_mul_pow_le {p : ℕ} [Fact p.Prime] {K : Type*}
    [SeminormedRing K] [NormOneClass K] [NormedAlgebra ℚ_[p] K]
    {c : K} (hc : ‖c‖ ^ (p - 1) ≤ (p : ℝ)) (m n k : ℕ) :
    ‖(m.choose k : K) * (n.choose k : K) * (k.factorial : K) * c ^ k‖ ≤
      (p : ℝ) * (k + 1) := by
  have hp : 1 < (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp' : 0 < (p : ℝ) - 1 := sub_pos.mpr hp
  have hscale : ‖c‖ ^ k ≤ (p : ℝ) ^ ((k : ℝ) / ((p : ℝ) - 1)) := by
    have h := Real.rpow_le_rpow (by positivity) hc (by positivity : 0 ≤ (k : ℝ) / (p - 1))
    rw [← Real.rpow_natCast_mul (norm_nonneg c),
      Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one, ← mul_div_assoc,
      mul_div_cancel_left₀ _ hp'.ne'] at h
    simpa only [Real.rpow_natCast] using h
  have hfactorial :
      ‖(k.factorial : K)‖ ≤
        (p : ℝ) ^ ((Nat.log p k + 1 : ℝ) - (k : ℝ) / ((p : ℝ) - 1)) := by
    rw [norm_natCast_eq_norm_padic (p := p),
      Padic.norm_natCast_eq_zpow (Nat.factorial_ne_zero k), ← Real.rpow_intCast]
    simp only [Int.cast_neg, Int.cast_natCast, Nat.padicValNat_def]
    apply Real.rpow_le_rpow_of_exponent_le hp.le
    linarith [div_sub_log_le_multiplicity_factorial p k]
  have hbinom : ‖(m.choose k : K) * (n.choose k : K)‖ ≤ 1 := by
    rw [← Nat.cast_mul, norm_natCast_eq_norm_padic (p := p)]
    exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] _
  calc
    _ ≤ ‖(k.factorial : K)‖ * ‖c‖ ^ k := by
      calc
        _ ≤ (‖(m.choose k : K) * (n.choose k : K)‖ * ‖(k.factorial : K)‖) * ‖c‖ ^ k :=
          (norm_mul_le _ _).trans (mul_le_mul (norm_mul_le _ _) (norm_pow_le _ _)
            (norm_nonneg _) (by positivity))
        _ ≤ _ := by
          gcongr
          exact mul_le_of_le_one_left (norm_nonneg _) hbinom
    _ ≤ (p : ℝ) ^ ((Nat.log p k + 1 : ℝ) - (k : ℝ) / ((p : ℝ) - 1)) *
        (p : ℝ) ^ ((k : ℝ) / ((p : ℝ) - 1)) := by gcongr
    _ = (p : ℝ) * (p : ℝ) ^ Nat.log p k := by
      rw [← Real.rpow_add (by positivity : 0 < (p : ℝ)), sub_add_cancel,
        Real.rpow_add_one (by positivity : (p : ℝ) ≠ 0), Real.rpow_natCast, mul_comm]
    _ ≤ _ := by
      gcongr
      exact_mod_cast Nat.pow_log_le_add_one p k

end TauCeti

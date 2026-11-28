/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.GainFactor
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.ShortForms

/-!
# Short forms after normalization by the rounded local gains

The uniform bound after projection has a positive contribution from the prime gains.
Use the rational factor whose valuations remove the actual rounded gains to cancel that
contribution. The rounding and divisibility losses are included in the final size bound.
A rational seminorm can measure size even after applying a complex field automorphism,
which need not preserve the complex norm but fixes the normalizing factor.

The normalization follows `New.Data.log_invGainFactor_le` and the size comparison in
`New.Data.span_short_integralRamified_eq_top` of `New/Reduction/ShortAndEnough.lean` in
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at `72fead1`.
-/

public section

open Real TauCeti.OneSidedBound

namespace Seminorm

/-- Normalize a projected lift by the rational product of reciprocal rounded net gains.
Small nonsplit primes lie in `S` and the level prime is `N`. The input seminorm may include
an observation of a conjugate of the lift. If the divisibility losses cost at most
`f * (x * b) * (log b) ^ 3` and rounding costs at most `b`, the size bound after rescaling
no longer contains the prime gains. -/
theorem sq_apply_inverseGainFactor_smul_le {V : Type*} [AddGroup V] [SMul ℚ V]
    (q : Seminorm ℚ V) (v : V) (S : Finset Nat.Primes) (N : Nat.Primes)
    (gain loss : Nat.Primes → ℝ) {H f x b X : ℝ}
    (hf : 1 ≤ f) (hx : 1 ≤ x) (hxb : x ^ 98 ≤ b) (hb : 5 ≤ log b)
    (hS : ∀ p ∈ S, (p.val : ℝ) ≤ X) (hN : 0 ≤ gain N)
    (hloss : ∑ p ∈ insert N S, loss p * log p.val ≤ f * (x * b) * log b ^ 3)
    (hround : Chebyshev.theta X + log N.val ≤ b)
    (hv : q v ^ 2 ≤ exp (H + 2 * (∑ p ∈ S, gain p * log p.val) +
      2 * (f * (x * b) * log b ^ 3) + x ^ 99)) :
    q ((insert N S).inverseGainFactor gain loss • v) ^ 2 ≤ exp (H + f * (x * b) * log b ^ 4) := by
  let c := (insert N S).inverseGainFactor gain loss
  have hc : log ‖c‖ ≤ -(∑ p ∈ S, gain p * log p.val) + f * (x * b) * log b ^ 3 + b := by
    rw [← Rat.norm_cast_real, Real.norm_of_nonneg (Rat.cast_nonneg.mpr
      ((insert N S).inverseGainFactor_pos gain loss).le)]
    have h := S.log_inverseGainFactor_insert_le N gain loss hS hN hloss
    linarith only [h, hround]
  have hq : ‖q v‖ = q v := Real.norm_of_nonneg (apply_nonneg q v)
  rw [map_smul_eq_mul]
  simpa only [norm_smul, hq] using
    norm_sq_smul_le_exp_of_prime_gain_bound c (q v) hf hx hxb hb hc (by simpa only [hq] using hv)

end Seminorm

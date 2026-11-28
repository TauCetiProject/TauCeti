/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Size of the logarithmic window for the level prime

A prime in a logarithmic window of width `W = x^(ε/6)` can be used as a level prime when
`W ≤ √(log b)`. To use a prime-window theorem uniform in powers of a fixed modulus, both
the lower endpoint of the window and the modulus `q₂(s)²` must be bounded by a fixed power
of `W`. We prove these estimates for the level window using the tower and cutoff bounds.

These are the level-prime window estimates in `New.Parameters.IsLargeScale.exists_isAdmissibleData`
in `grh/src/New/Reduction/Data/Existence.lean` of
[grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207).
-/

public section

namespace TauCeti.OneSidedBound.Parameters

open Filter Real

/-- Put `W = x^(ε/6)`. For sufficiently large integer `x`, a level-window start `U` between
`m L` and `24 m L` lies in `[W, W^(A+7)]`, and width `W` fits inside width `√L`. The required
modulus `q₂(s)²` is also at most `W^(A+7)`. Here `m` is the number of lifts and `L = log b`
is given through its cutoff bounds `W^6 ≤ L ≤ W^6 + 1`. -/
theorem eventually_level_prime_window_bounds (P : Parameters) {ε : ℝ} {A : ℕ}
    (hA : (66 : ℝ) * P.q₀ * P.d ≤ (ε / 6) * A) :
    ∀ᶠ x : ℕ in atTop,
      let W := (x : ℝ) ^ (ε / 6)
      ∀ (s m : ℕ) (L U : ℝ), P.q₂ s ≤ x ^ (33 * (P.q₀ * P.d)) →
        m ≠ 0 → (m : ℝ) ≤ 2 * √(x : ℝ) → W ^ 6 ≤ L → L ≤ W ^ 6 + 1 →
        (m : ℝ) * L ≤ U → U ≤ 24 * m * L →
        U ∈ Set.Icc W (W ^ (A + 7)) ∧ W ≤ √L ∧ (P.q₂ s : ℝ) ^ 2 ≤ W ^ (A + 7) := by
  have hqd : (1 : ℝ) ≤ (P.q₀ : ℝ) * P.d := by
    exact_mod_cast Nat.mul_pos P.q₀_pos P.prime_d.pos
  have hA₁ : 1 ≤ (ε / 6) * A := by nlinarith only [hA, hqd]
  have hε : 0 < ε / 6 := pos_of_mul_pos_left (zero_lt_one.trans_le hA₁) (Nat.cast_nonneg A)
  have hWlim := (tendsto_rpow_atTop hε).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hWlim.eventually_ge_atTop (96 : ℝ), eventually_ge_atTop (1 : ℕ)] with x hW hx
  dsimp only [Function.comp_apply] at hW
  intro W s m L U hq hm hm' hL hL' hU hU'
  have hW₁ : 1 ≤ W := by linarith
  have hW₆ : 1 ≤ W ^ 6 := one_le_pow₀ hW₁
  have hx₁ : 1 ≤ (x : ℝ) := by exact_mod_cast hx
  have hWA : W ^ A = (x : ℝ) ^ ((ε / 6) * A) :=
    (Real.rpow_mul_natCast (zero_le_one.trans hx₁) _ _).symm
  have hWx : (x : ℝ) ≤ W ^ A := by
    simpa only [hWA, Real.rpow_one] using rpow_le_rpow_of_exponent_le hx₁ hA₁
  have hm₁ : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hm
  have hL₁ : 0 ≤ L := by linarith
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · calc
      W ≤ W ^ 6 := by simpa using pow_le_pow_right₀ hW₁ (by decide : 1 ≤ 6)
      _ ≤ L := hL
      _ ≤ m * L := by simpa using mul_le_mul_of_nonneg_right hm₁ hL₁
      _ ≤ U := hU
  · have hsqrt := Real.sqrt_le_self_iff.2 (Or.inr hx₁)
    calc
      U ≤ 24 * m * L := hU'
      _ ≤ 24 * (2 * W ^ A) * (2 * W ^ 6) := by
        have hmW : (m : ℝ) ≤ 2 * W ^ A := hm'.trans (by gcongr; exact hsqrt.trans hWx)
        have hLL : L ≤ 2 * W ^ 6 := by linarith
        gcongr
      _ = 96 * W ^ (A + 6) := by rw [pow_add]; ring
      _ ≤ W ^ (A + 7) := by
        rw [pow_succ W (A + 6)]
        exact mul_le_mul_of_nonneg_right hW (by positivity) |>.trans_eq (mul_comm _ _)
  · rw [le_sqrt (zero_le_one.trans hW₁) hL₁]
    exact (pow_le_pow_right₀ hW₁ (by decide : 2 ≤ 6)).trans hL
  · have hq' : (P.q₂ s : ℝ) ≤ (x : ℝ) ^ (33 * (P.q₀ * P.d) : ℕ) := by exact_mod_cast hq
    calc
      (P.q₂ s : ℝ) ^ 2 ≤ ((x : ℝ) ^ (33 * (P.q₀ * P.d) : ℕ)) ^ 2 := by gcongr
      _ = (x : ℝ) ^ ((66 : ℝ) * P.q₀ * P.d) := by
        rw [← pow_mul, ← Real.rpow_natCast]
        push_cast
        ring_nf
      _ ≤ W ^ A := by
        rw [hWA]
        exact rpow_le_rpow_of_exponent_le hx₁ hA
      _ ≤ W ^ (A + 7) := pow_le_pow_right₀ hW₁ (Nat.le_add_right _ _)

end TauCeti.OneSidedBound.Parameters

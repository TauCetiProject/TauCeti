/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.Gronwall

/-!
# One step of the discrete Grönwall inequality in `gronwallBound` form

Mathlib's `gronwallBound δ K ε x` solves `G' = K G + ε`, `G 0 = δ`. This file shows that it also
dominates the explicit Euler steps of that equation: one step of size `h ≥ 0` from a value below
`gronwallBound δ K ε x` stays below `gronwallBound δ K ε (x + h)`, and an additive perturbation
`ρ ≥ 0` of the step is absorbed into the initial value `δ`.

By induction on `n`, a sequence with `u (n + 1) ≤ (1 + h n K) u n + h n ε + ρ n` and
`u 0, K, ε, h n, ρ n ≥ 0` is then bounded by
`gronwallBound (u 0 + ∑ k < n, ρ k) K ε (∑ k < n, h k)`.
Unlike Mathlib's exponential form `discrete_gronwall`, which gives
`(u 0 + ∑ k < n, (h k ε + ρ k)) exp (K ∑ k < n, h k)`, this bound has the exact continuous
Grönwall constant `(ε / K) (exp (K x) - 1)`. Such recursions are satisfied by the errors of
one-step methods for ordinary differential equations, and the discrete stability theorem
`TauCeti.norm_sub_le_gronwallBound_of_oneStep` carries out this induction.

## Main results

* `TauCeti.gronwallBound_add_δ`: `gronwallBound` is affine in `δ`, with slope `exp (K x)`.
* `TauCeti.gronwallBound_mono_δ`: `gronwallBound` is monotone in `δ`.
* `TauCeti.one_add_mul_mul_gronwallBound_add_le`: one explicit Euler step of `G' = K G + ε` stays
  below `gronwallBound`.
* `TauCeti.le_gronwallBound_add_of_le_one_add_mul_add`: one step of the discrete Grönwall
  inequality.
-/

public section

open Real

namespace TauCeti

/-- `gronwallBound` is affine in the initial value `δ`, with slope `exp (K x)`. -/
theorem gronwallBound_add_δ (δ ρ K ε x : ℝ) :
    gronwallBound (δ + ρ) K ε x = gronwallBound δ K ε x + ρ * exp (K * x) := by
  rcases eq_or_ne K 0 with rfl | hK
  · simp only [gronwallBound_K0, zero_mul, exp_zero, mul_one]
    ring
  · simp only [gronwallBound_of_K_ne_0 hK]
    ring

/-- `gronwallBound` is monotone in the initial value `δ`. -/
theorem gronwallBound_mono_δ (K ε x : ℝ) : Monotone fun δ ↦ gronwallBound δ K ε x := by
  intro δ δ' hδ
  dsimp only
  rw [← add_sub_cancel δ δ', gronwallBound_add_δ]
  exact le_add_of_nonneg_right <| mul_nonneg (sub_nonneg.2 hδ) (exp_pos _).le

/-- For `δ, K, ε ≥ 0`, one explicit Euler step of `G' = K G + ε` of any size `h` stays below the
solution `gronwallBound δ K ε`: `(1 + h K) G(x) + h ε ≤ G(x + h)`, with equality when `K = 0`. -/
theorem one_add_mul_mul_gronwallBound_add_le {δ K ε : ℝ} (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hε : 0 ≤ ε) (x h : ℝ) :
    (1 + h * K) * gronwallBound δ K ε x + h * ε ≤ gronwallBound δ K ε (x + h) := by
  rcases hK.eq_or_lt with rfl | hK
  · simp only [gronwallBound_K0, mul_zero, add_zero, one_mul]
    linarith
  · simp only [gronwallBound_of_K_ne_0 hK.ne']
    -- With `c = δ + ε / K ≥ 0`, the right side minus the left side is
    -- `c exp (K x) (exp (K h) - (1 + h K))`.
    have hc : 0 ≤ (δ + ε / K) * exp (K * x) := by positivity
    have hexp : 0 ≤ exp (K * h) - (1 + h * K) := by
      linarith [add_one_le_exp (K * h)]
    have key : δ * exp (K * (x + h)) + ε / K * (exp (K * (x + h)) - 1) -
        ((1 + h * K) * (δ * exp (K * x) + ε / K * (exp (K * x) - 1)) + h * ε) =
        (δ + ε / K) * exp (K * x) * (exp (K * h) - (1 + h * K)) := by
      rw [show K * (x + h) = K * x + K * h by ring, exp_add]
      field_simp
      ring
    nlinarith [mul_nonneg hc hexp]

/-- **One step of the discrete Grönwall inequality.** Let `δ, K, ε, x, h, ρ ≥ 0`. If
`u ≤ gronwallBound δ K ε x` and `v ≤ (1 + h K) u + h ε + ρ`, then
`v ≤ gronwallBound (δ + ρ) K ε (x + h)`. -/
theorem le_gronwallBound_add_of_le_one_add_mul_add {u v δ K ε h ρ x : ℝ} (hδ : 0 ≤ δ)
    (hK : 0 ≤ K) (hε : 0 ≤ ε) (hh : 0 ≤ h) (hρ : 0 ≤ ρ) (hx : 0 ≤ x)
    (hu : u ≤ gronwallBound δ K ε x) (hv : v ≤ (1 + h * K) * u + h * ε + ρ) :
    v ≤ gronwallBound (δ + ρ) K ε (x + h) := by
  have hstep := one_add_mul_mul_gronwallBound_add_le hδ hK hε x h
  have hρexp : ρ ≤ ρ * exp (K * (x + h)) :=
    le_mul_of_one_le_right hρ (one_le_exp (by positivity))
  have hmul : (1 + h * K) * u ≤ (1 + h * K) * gronwallBound δ K ε x :=
    mul_le_mul_of_nonneg_left hu (by positivity)
  rw [gronwallBound_add_δ]
  linarith

end TauCeti

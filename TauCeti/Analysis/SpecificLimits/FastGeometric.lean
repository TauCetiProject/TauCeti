/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Geometric bounds and convergence of superlinear recurrences

Let `Y : ℕ → ℝ` be a nonnegative sequence satisfying the superlinear recurrence

`Y (n + 1) ≤ C * b ^ n * Y n ^ (1 + α)`

with `b ≥ 0` and `α ≥ 0`. If `q ≥ 0`, `b * q ^ α ≤ 1`, and `C * Y 0 ^ α ≤ q`, then
`Y n ≤ q ^ n * Y 0`. When `q < 1`, this bound implies `Y n → 0`. In its classical form, for
`C > 0`, `b > 1`, `α > 0`,

`Y 0 ≤ C ^ (-α⁻¹) * b ^ (-(α ^ 2)⁻¹)` implies `Y n ≤ (b ^ (-α⁻¹)) ^ n * Y 0`, so `Y n → 0`.

This is the numerical lemma behind De Giorgi's method. In the proof of local boundedness of weak
subsolutions of a divergence-form elliptic equation, `Y n` is the `L²` mass of the truncation
`(u - kₙ)⁺` on a ball `B_{rₙ}`, along increasing levels `kₙ` and shrinking radii `rₙ`. The
Caccioppoli inequality for truncations, the Sobolev inequality and Chebyshev's inequality combine
into a recurrence of the above shape, with `b` accounting for the geometric shrinking of the
gaps `rₙ - rₙ₊₁` and `kₙ₊₁ - kₙ`. The vanishing of the limit then says that `u` is bounded
above on the limiting ball by the limiting level.

The general statement `TauCeti.le_geom_of_le_mul_pow_mul_rpow` only asks for a ratio `q` with
`b * q ^ α ≤ 1` and `C * Y 0 ^ α ≤ q`; the classical threshold is the choice `q = b ^ (-α⁻¹)`.

## Main declarations

* `TauCeti.le_geom_of_le_mul_pow_mul_rpow`: geometric bound `Y n ≤ q ^ n * Y 0` for a
  superlinear recurrence from a small start.
* `TauCeti.le_rpow_neg_inv_pow_mul_of_le_mul_pow_mul_rpow`: the same bound at the classical
  threshold `Y 0 ≤ C ^ (-α⁻¹) * b ^ (-(α ^ 2)⁻¹)`, with ratio `b ^ (-α⁻¹)`.
* `TauCeti.tendsto_atTop_zero_of_le_mul_pow_mul_rpow_of_ratio_lt_one`: for `q < 1`, the sequence
  tends to zero.
* `TauCeti.tendsto_atTop_zero_of_le_mul_pow_mul_rpow`: convergence at the classical threshold
  when `b > 1`.

## References

* E. DiBenedetto, *Degenerate Parabolic Equations*, Chapter I, Lemma 4.1 (fast geometric
  convergence).
* O. A. Ladyzhenskaya, N. N. Ural'tseva, *Linear and Quasilinear Elliptic Equations*,
  Chapter 2, Lemma 4.7.
* The same recurrence is closed out in Scott Armstrong and Julia Kempe's Apache-2.0
  `scottnarmstrong/DeGiorgi/DeGiorgi/DeGiorgiIteration/Recurrence.lean`, commit
  `4c1b3077d3782b24065184df4ba59501b2e56fc7` (`DeGiorgi.deGiorgi_recurrence_closeout`), by a
  rescaling argument; the proof here is the direct induction of DiBenedetto.
-/

public section

namespace TauCeti

open Filter Topology

/-- **Geometric bound.** Let `Y` be a nonnegative sequence with

`Y (n + 1) ≤ C * b ^ n * Y n ^ (1 + α)`

for some `b ≥ 0` and `α ≥ 0`. If `q ≥ 0` satisfies `b * q ^ α ≤ 1` and the starting value is
small in the sense that `C * Y 0 ^ α ≤ q`, then `Y n ≤ q ^ n * Y 0` for every `n`.

No sign condition on `C` is needed. -/
theorem le_geom_of_le_mul_pow_mul_rpow {Y : ℕ → ℝ} {C b q α : ℝ} (hY : ∀ n, 0 ≤ Y n)
    (hb : 0 ≤ b) (hq : 0 ≤ q) (hα : 0 ≤ α) (hbq : b * q ^ α ≤ 1) (h0 : C * Y 0 ^ α ≤ q)
    (hrec : ∀ n, Y (n + 1) ≤ C * b ^ n * Y n ^ (1 + α)) (n : ℕ) :
    Y n ≤ q ^ n * Y 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hgeom : 0 ≤ q ^ n * Y 0 := mul_nonneg (pow_nonneg hq n) (hY 0)
    refine (hrec n).trans ?_
    rcases lt_or_ge C 0 with hC | hC
    · -- A negative constant makes the right-hand side of the recurrence nonpositive.
      have : C * b ^ n * Y n ^ (1 + α) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg hC.le (pow_nonneg hb n))
          (Real.rpow_nonneg (hY n) _)
      exact this.trans (mul_nonneg (pow_nonneg hq _) (hY 0))
    · -- Insert the inductive bound and regroup the powers of `q`.
      have hsplit : (q ^ n * Y 0) ^ (1 + α) = (q ^ n * Y 0) * ((q ^ α) ^ n * Y 0 ^ α) := by
        rw [Real.rpow_one_add' hgeom (by positivity), Real.mul_rpow (pow_nonneg hq n) (hY 0),
          Real.rpow_pow_comm hq]
      calc C * b ^ n * Y n ^ (1 + α)
          ≤ C * b ^ n * (q ^ n * Y 0) ^ (1 + α) := by
            gcongr
            exact hY n
        _ = (C * Y 0 ^ α) * (b * q ^ α) ^ n * (q ^ n * Y 0) := by
            rw [hsplit, mul_pow]
            ring
        _ ≤ q * 1 * (q ^ n * Y 0) := by
            gcongr
            exact pow_le_one₀ (mul_nonneg hb (Real.rpow_nonneg hq _)) hbq
        _ = q ^ (n + 1) * Y 0 := by ring

private theorem rpow_neg_inv_pow_ratio_conditions {Y : ℕ → ℝ} {C b α : ℝ}
    (hY : ∀ n, 0 ≤ Y n) (hC : 0 < C) (hb : 0 < b) (hα : 0 < α)
    (h0 : Y 0 ≤ C ^ (-α⁻¹) * b ^ (-(α ^ 2)⁻¹)) :
    b * (b ^ (-α⁻¹)) ^ α ≤ 1 ∧ C * Y 0 ^ α ≤ b ^ (-α⁻¹) := by
  have e1 : -α⁻¹ * α = -1 := by field_simp
  have e2 : -(α ^ 2)⁻¹ * α = -α⁻¹ := by field_simp
  constructor
  · rw [← Real.rpow_mul hb.le, e1, Real.rpow_neg_one, mul_inv_cancel₀ hb.ne']
  · calc C * Y 0 ^ α ≤ C * (C ^ (-α⁻¹) * b ^ (-(α ^ 2)⁻¹)) ^ α := by
          gcongr
          exact hY 0
      _ = b ^ (-α⁻¹) := by
          rw [Real.mul_rpow (Real.rpow_nonneg hC.le _) (Real.rpow_nonneg hb.le _),
            ← Real.rpow_mul hC.le, ← Real.rpow_mul hb.le, e1, e2, Real.rpow_neg_one,
            mul_inv_cancel_left₀ hC.ne']

/-- **Geometric bound, classical threshold.** Let `Y` be a nonnegative sequence with

`Y (n + 1) ≤ C * b ^ n * Y n ^ (1 + α)`

for constants `C > 0`, `b > 0` and `α > 0`. If `Y 0 ≤ C ^ (-α⁻¹) * b ^ (-(α ^ 2)⁻¹)`, then
`Y n ≤ (b ^ (-α⁻¹)) ^ n * Y 0` for every `n`. -/
theorem le_rpow_neg_inv_pow_mul_of_le_mul_pow_mul_rpow {Y : ℕ → ℝ} {C b α : ℝ}
    (hY : ∀ n, 0 ≤ Y n) (hC : 0 < C) (hb : 0 < b) (hα : 0 < α)
    (h0 : Y 0 ≤ C ^ (-α⁻¹) * b ^ (-(α ^ 2)⁻¹))
    (hrec : ∀ n, Y (n + 1) ≤ C * b ^ n * Y n ^ (1 + α)) (n : ℕ) :
    Y n ≤ (b ^ (-α⁻¹)) ^ n * Y 0 := by
  obtain ⟨hbq, hq⟩ := rpow_neg_inv_pow_ratio_conditions hY hC hb hα h0
  exact le_geom_of_le_mul_pow_mul_rpow hY hb.le (Real.rpow_nonneg hb.le _) hα.le hbq hq hrec n

/-- **Convergence to zero from a geometric bound.** If the ratio `q` in
`le_geom_of_le_mul_pow_mul_rpow` is less than one, then `Y n → 0`. -/
theorem tendsto_atTop_zero_of_le_mul_pow_mul_rpow_of_ratio_lt_one {Y : ℕ → ℝ}
    {C b q α : ℝ} (hY : ∀ n, 0 ≤ Y n) (hb : 0 ≤ b) (hq : 0 ≤ q) (hq1 : q < 1)
    (hα : 0 ≤ α) (hbq : b * q ^ α ≤ 1) (h0 : C * Y 0 ^ α ≤ q)
    (hrec : ∀ n, Y (n + 1) ≤ C * b ^ n * Y n ^ (1 + α)) :
    Tendsto Y atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => q ^ n * Y 0) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const (Y 0)
  exact squeeze_zero hY (le_geom_of_le_mul_pow_mul_rpow hY hb hq hα hbq h0 hrec) hlim

/-- **Fast geometric convergence to zero, classical threshold.** Let `Y` be a nonnegative
sequence with

`Y (n + 1) ≤ C * b ^ n * Y n ^ (1 + α)`

for constants `C > 0`, `b > 1` and `α > 0`. If `Y 0 ≤ C ^ (-α⁻¹) * b ^ (-(α ^ 2)⁻¹)`, then
`Y n → 0`. This is the form in which De Giorgi's iteration concludes. -/
theorem tendsto_atTop_zero_of_le_mul_pow_mul_rpow {Y : ℕ → ℝ} {C b α : ℝ}
    (hY : ∀ n, 0 ≤ Y n) (hC : 0 < C) (hb : 1 < b) (hα : 0 < α)
    (h0 : Y 0 ≤ C ^ (-α⁻¹) * b ^ (-(α ^ 2)⁻¹))
    (hrec : ∀ n, Y (n + 1) ≤ C * b ^ n * Y n ^ (1 + α)) :
    Tendsto Y atTop (𝓝 0) := by
  have hq : b ^ (-α⁻¹) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hb (neg_lt_zero.mpr (inv_pos.mpr hα))
  obtain ⟨hbq, hq0⟩ :=
    rpow_neg_inv_pow_ratio_conditions hY hC (zero_lt_one.trans hb) hα h0
  exact tendsto_atTop_zero_of_le_mul_pow_mul_rpow_of_ratio_lt_one hY (zero_lt_one.trans hb).le
    (Real.rpow_nonneg (zero_lt_one.trans hb).le _) hq hα.le hbq hq0 hrec

end TauCeti

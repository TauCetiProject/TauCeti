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

with `α > 0`. If `b * q ^ α ≤ 1` and `C * Y 0 ^ α ≤ q`, then
`Y n ≤ q ^ n * Y 0`; this bound holds more generally for every `α > -1`. When `q < 1`, it implies
`Y n → 0`. In its classical form, for `b > 1`, `α > 0`,

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
* `TauCeti.strictAnti_of_eq_one_add_mul_sq_sub_one`: strict decrease for a quadratic recurrence
  starting above one with a sufficiently small coefficient.

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

for some `α > -1`. If `q` satisfies `b * q ^ α ≤ 1` and the starting value is small in the sense
that `C * Y 0 ^ α ≤ q`, then `Y n ≤ q ^ n * Y 0` for every `n`.

No sign condition on `C`, `b` or `q` is needed. The superlinear case `α > 0` is the one used by
De Giorgi's method. -/
theorem le_geom_of_le_mul_pow_mul_rpow {Y : ℕ → ℝ} {C b q α : ℝ} (hY : ∀ n, 0 ≤ Y n)
    (hα : -1 < α) (hbq : b * q ^ α ≤ 1) (h0 : C * Y 0 ^ α ≤ q)
    (hrec : ∀ n, Y (n + 1) ≤ C * b ^ n * Y n ^ (1 + α)) (n : ℕ) :
    Y n ≤ q ^ n * Y 0 := by
  have hα' : 0 < 1 + α := by linarith
  have hY0 := hY 0
  have hzero : ∀ n, Y n = 0 → Y (n + 1) = 0 := fun n h ↦
    le_antisymm (by simpa [h, Real.zero_rpow hα'.ne'] using hrec n) (hY _)
  rcases hY0.eq_or_lt with h | hY0pos
  · have : ∀ n, Y n = 0 := fun n ↦ by
      induction n with
      | zero => exact h.symm
      | succ n ih => exact hzero n ih
    simp [this]
  have hY0α : 0 < Y 0 ^ α := Real.rpow_pos_of_pos hY0pos α
  have hC : 0 ≤ C := by
    by_contra hC
    have : C * Y 0 ^ (1 + α) < 0 :=
      mul_neg_of_neg_of_pos (not_le.1 hC) (Real.rpow_pos_of_pos hY0pos _)
    linarith [hY 1, hrec 0, show C * b ^ 0 * Y 0 ^ (1 + α) = C * Y 0 ^ (1 + α) by simp]
  have hq : 0 ≤ q := by
    by_contra hq
    nlinarith [mul_nonneg hC hY0α.le]
  have hY1 : Y 1 ≤ q * Y 0 := by
    calc Y 1 ≤ C * b ^ 0 * Y 0 ^ (1 + α) := hrec 0
      _ = (C * Y 0 ^ α) * Y 0 := by
          rw [Real.rpow_one_add' hY0 hα'.ne']
          ring
      _ ≤ q * Y 0 := by gcongr
  rcases le_or_gt 0 b with hb | hb
  · induction n with
    | zero => simp
    | succ n ih =>
      refine (hrec n).trans ?_
      have hYn := hY n
      -- Insert the inductive bound and regroup the powers of `q`.
      calc C * b ^ n * Y n ^ (1 + α)
          ≤ C * b ^ n * (q ^ n * Y 0) ^ (1 + α) := by gcongr
        _ = (C * Y 0 ^ α) * (b * q ^ α) ^ n * (q ^ n * Y 0) := by
            rw [Real.rpow_one_add' (by positivity) hα'.ne', Real.mul_rpow (by positivity) hY0,
              ← Real.rpow_pow_comm hq, mul_pow]
            ring
        _ ≤ q * 1 * (q ^ n * Y 0) := by
            gcongr
            exact pow_le_one₀ (by positivity) hbq
        _ = q ^ (n + 1) * Y 0 := by ring
  · -- For negative `b`, the recurrence forces `Y n = 0` from the third term on.
    have hY2 : Y 2 = 0 := by
      refine le_antisymm ((hrec 1).trans ?_) (hY 2)
      have : 0 ≤ Y 1 ^ (1 + α) := Real.rpow_nonneg (hY 1) _
      nlinarith [mul_nonneg hC this, pow_one b]
    have hY' : ∀ k, Y (k + 2) = 0 := fun k ↦ by
      induction k with
      | zero => exact hY2
      | succ k ih => exact hzero _ ih
    match n with
    | 0 => simp
    | 1 => simpa using hY1
    | k + 2 => rw [hY']; positivity

private theorem rpow_neg_inv_pow_ratio_conditions {Y₀ C b α : ℝ}
    (hY₀ : 0 ≤ Y₀) (hb : 0 < b) (hα : 0 < α)
    (h0 : Y₀ ≤ C ^ (-α⁻¹) * b ^ (-(α ^ 2)⁻¹)) :
    b * (b ^ (-α⁻¹)) ^ α ≤ 1 ∧ C * Y₀ ^ α ≤ b ^ (-α⁻¹) := by
  have e1 : -α⁻¹ * α = -1 := by field_simp
  have e2 : -(α ^ 2)⁻¹ * α = -α⁻¹ := by field_simp
  constructor
  · rw [← Real.rpow_mul hb.le, e1, Real.rpow_neg_one, mul_inv_cancel₀ hb.ne']
  · rcases le_or_gt C 0 with hC | hC
    · exact (mul_nonpos_of_nonpos_of_nonneg hC (Real.rpow_nonneg hY₀ _)).trans
        (Real.rpow_nonneg hb.le _)
    calc C * Y₀ ^ α ≤ C * (C ^ (-α⁻¹) * b ^ (-(α ^ 2)⁻¹)) ^ α := by gcongr
      _ = b ^ (-α⁻¹) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hC.le,
            ← Real.rpow_mul hb.le, e1, e2, Real.rpow_neg_one, mul_inv_cancel_left₀ hC.ne']

/-- **Geometric bound, classical threshold.** Let `Y` be a nonnegative sequence with

`Y (n + 1) ≤ C * b ^ n * Y n ^ (1 + α)`

for constants `b > 0` and `α > 0`. If `Y 0 ≤ C ^ (-α⁻¹) * b ^ (-(α ^ 2)⁻¹)`, then
`Y n ≤ (b ^ (-α⁻¹)) ^ n * Y 0` for every `n`. -/
theorem le_rpow_neg_inv_pow_mul_of_le_mul_pow_mul_rpow {Y : ℕ → ℝ} {C b α : ℝ}
    (hY : ∀ n, 0 ≤ Y n) (hb : 0 < b) (hα : 0 < α)
    (h0 : Y 0 ≤ C ^ (-α⁻¹) * b ^ (-(α ^ 2)⁻¹))
    (hrec : ∀ n, Y (n + 1) ≤ C * b ^ n * Y n ^ (1 + α)) (n : ℕ) :
    Y n ≤ (b ^ (-α⁻¹)) ^ n * Y 0 := by
  obtain ⟨hbq, hq⟩ := rpow_neg_inv_pow_ratio_conditions (hY 0) hb hα h0
  exact le_geom_of_le_mul_pow_mul_rpow hY (by linarith) hbq hq hrec n

/-- **Convergence to zero from a geometric bound.** If the ratio `q` in
`le_geom_of_le_mul_pow_mul_rpow` is less than one, then `Y n → 0`. -/
theorem tendsto_atTop_zero_of_le_mul_pow_mul_rpow_of_ratio_lt_one {Y : ℕ → ℝ}
    {C b q α : ℝ} (hY : ∀ n, 0 ≤ Y n) (hq1 : q < 1)
    (hα : -1 < α) (hbq : b * q ^ α ≤ 1) (h0 : C * Y 0 ^ α ≤ q)
    (hrec : ∀ n, Y (n + 1) ≤ C * b ^ n * Y n ^ (1 + α)) :
    Tendsto Y atTop (𝓝 0) := by
  have hle := le_geom_of_le_mul_pow_mul_rpow hY hα hbq h0 hrec
  rcases (hY 0).eq_or_lt with h | hY0
  · exact squeeze_zero hY (fun n ↦ by simpa [← h] using hle n) tendsto_const_nhds
  have hq : 0 ≤ q := by
    have := (hY 1).trans (by simpa using hle 1)
    exact nonneg_of_mul_nonneg_left this hY0
  have hlim : Tendsto (fun n : ℕ => q ^ n * Y 0) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const (Y 0)
  exact squeeze_zero hY hle hlim

/-- **Fast geometric convergence to zero, classical threshold.** Let `Y` be a nonnegative
sequence with

`Y (n + 1) ≤ C * b ^ n * Y n ^ (1 + α)`

for constants `b > 1` and `α > 0`. If `Y 0 ≤ C ^ (-α⁻¹) * b ^ (-(α ^ 2)⁻¹)`, then
`Y n → 0`. This is the form in which De Giorgi's iteration concludes. -/
theorem tendsto_atTop_zero_of_le_mul_pow_mul_rpow {Y : ℕ → ℝ} {C b α : ℝ}
    (hY : ∀ n, 0 ≤ Y n) (hb : 1 < b) (hα : 0 < α)
    (h0 : Y 0 ≤ C ^ (-α⁻¹) * b ^ (-(α ^ 2)⁻¹))
    (hrec : ∀ n, Y (n + 1) ≤ C * b ^ n * Y n ^ (1 + α)) :
    Tendsto Y atTop (𝓝 0) := by
  have hb₀ : 0 < b := one_pos.trans hb
  have hq : b ^ (-α⁻¹) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hb (by simpa)
  obtain ⟨hbq, hq0⟩ := rpow_neg_inv_pow_ratio_conditions (hY 0) hb₀ hα h0
  exact tendsto_atTop_zero_of_le_mul_pow_mul_rpow_of_ratio_lt_one hY hq (by linarith) hbq hq0 hrec

/-- A real sequence with `cₙ₊₁ = 1 + κ (cₙ² - 1)`, where `κ > 0`, `c₀ > 1` and `κ (1 + c₀) < 1`,
decreases strictly: while `1 < cₙ ≤ c₀`, the step `cₙ₊₁ - 1 = κ (cₙ + 1) (cₙ - 1)` multiplies
`cₙ - 1 > 0` by `κ (cₙ + 1) < 1`. -/
theorem strictAnti_of_eq_one_add_mul_sq_sub_one {c : ℕ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hc₀ : 1 < c 0) (hlt : κ * (1 + c 0) < 1) (hrec : ∀ n, c (n + 1) = 1 + κ * (c n ^ 2 - 1)) :
    StrictAnti c := by
  have hstep (n : ℕ) (h₁ : 1 < c n) (h₀ : c n ≤ c 0) : 1 < c (n + 1) ∧ c (n + 1) < c n := by
    have hκc : κ * (c n + 1) < 1 := by nlinarith
    constructor <;> nlinarith [hrec n, mul_pos hκ (sub_pos.2 h₁)]
  have hdec (n : ℕ) : 1 < c n ∧ c n ≤ c 0 := by
    induction n with
    | zero => exact ⟨hc₀, le_rfl⟩
    | succ n ih => exact ⟨(hstep n ih.1 ih.2).1, (hstep n ih.1 ih.2).2.le.trans ih.2⟩
  exact strictAnti_nat_of_succ_lt fun n ↦ (hstep n (hdec n).1 (hdec n).2).2

end TauCeti

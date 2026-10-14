/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Average
public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p
import TauCeti.MeasureTheory.Integral.JohnNirenberg

/-!
# The borderline Sobolev embedding `W^{1,n} ⊆ BMO`

Let `u ∈ W^{1,p}(Ω)` on an open subset `Ω` of a real inner product space of dimension `n`, with an
additive Haar measure `μ`, and let `ω = μ(B(0, 1))`. On every ball `B = B(x, r) ⊆ Ω`, the mean
oscillation of `u` is controlled by the `Lᵖ` norm of its gradient on that ball:

`⨍_B |u - u_B| ≤ 2^(n + 1) r μ(B)^(-1/p) ‖∇u‖_{Lᵖ(B)}`.

Since `μ(B) = ω rⁿ`, the factor `r μ(B)^(-1/p)` is `ω^(-1/p) r^(1 - n/p)`. In the borderline case
`p = n` the power of `r` disappears and the bound is scale invariant,

`⨍_B |u - u_B| ≤ 2^(n + 1) ω^(-1/n) ‖∇u‖_{Lⁿ(B)}`,

so `u` has **bounded mean oscillation** on `Ω`, with BMO seminorm at most
`2^(n + 1) ω^(-1/n) ‖∇u‖_{Lⁿ(Ω)}`. This is the substitute for the embedding of `W^{1,n}` in `L^∞`,
which fails for `n ≥ 2`. Unlike Trudinger's inequality
(`TauCeti.W1p.setLIntegral_exp_abs_value_div_rpow_le`), it needs no boundary condition on `u`.

By the John–Nirenberg inequality, functions of bounded mean oscillation are exponentially
integrable. In `ℝⁿ = EuclideanSpace ℝ ι` this gives a local form of exponential integrability for
every `u ∈ W^{1,n}(Ω)`: there are constants `A > 0` and `C`, depending only on `n`, such that if
`B(x₀, R) ⊆ Ω` and `σ ω^(-1/n) ‖∇u‖_{Lⁿ(B(x₀, R))} ≤ A`, then on `B' = B(x₀, R / (3√n))`

`∫_{B'} exp (σ |u - u_{B'}|) ≤ C |B'|`.

The mean oscillation bound is the Poincaré–Wirtinger inequality in `L¹` on the ball
(`TauCeti.W1p.setIntegral_abs_value_sub_setAverage_le_of_ball_subset`), followed by Hölder's
inequality on the ball to pass from `‖∇u‖_{L¹(B)}` to `‖∇u‖_{Lᵖ(B)}`.

## Main declarations

* `TauCeti.W1p.setLAverage_enorm_value_sub_setAverage_ball_le_mul_measure_rpow`: the mean
  oscillation of `u ∈ W^{1,p}(Ω)` on a ball, for every exponent `p`.
* `TauCeti.W1p.setLAverage_enorm_value_sub_setAverage_ball_le`: the scale-invariant bound for
  `p = n`, which places `W^{1,n}(Ω)` in `BMO(Ω)`.
* `TauCeti.W1p.exists_setLIntegral_exp_mul_abs_value_sub_setAverage_ball_le`: local exponential
  integrability of `W^{1,n}` functions in `ℝⁿ`.

## References

* F. John and L. Nirenberg, *On functions of bounded mean oscillation*, Comm. Pure Appl. Math.
  **14** (1961), 415–426.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 7.8, Theorem 7.21 (exponential integrability of `W^{1,1}` functions whose gradient
  satisfies `∫_{B_r} |Du| ≤ K r^(n - 1)`, which `W^{1,n}` functions do by Hölder's inequality).
-/

public section

noncomputable section

open Metric Set MeasureTheory Module TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

section General

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The mean oscillation of a Sobolev function on a ball.** If `u ∈ W^{1,p}(Ω)` and
`B = B(x, r) ⊆ Ω`, then

`⨍_B |u - u_B| ≤ 2^(n + 1) r μ(B)^(-1/p) ‖∇u‖_{Lᵖ(B)}`,

where for `p = ∞` the factor `μ(B)^(-1/p)` is `1`. For `p = n` the right side does not depend
on `r`; see `TauCeti.W1p.setLAverage_enorm_value_sub_setAverage_ball_le`. -/
theorem W1p.setLAverage_enorm_value_sub_setAverage_ball_le_mul_measure_rpow {x : E} {r : ℝ}
    (hball : ball x r ⊆ (Omega : Set E)) (u : W1p mu Omega p) :
    ⨍⁻ y in ball x r, ‖W1p.value u y - ⨍ z in ball x r, W1p.value u z ∂mu‖ₑ ∂mu ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * r) * mu (ball x r) ^ (-p.toReal⁻¹) *
        eLpNorm (W1p.gradient u) p (mu.restrict (ball x r)) := by
  rcases le_or_gt r 0 with hr | hr
  · -- The ball is empty.
    simp [ball_eq_empty.2 hr]
  set B := ball x r
  set m := ⨍ z in B, W1p.value u z ∂mu
  have hB0 : mu B ≠ 0 := (measure_ball_pos mu x hr).ne'
  have hBtop : mu B ≠ ∞ := measure_ball_lt_top.ne
  have : IsFiniteMeasure (mu.restrict B) := isFiniteMeasure_restrict.2 hBtop
  have hle : mu.restrict B ≤ mu.restrict Omega := Measure.restrict_mono hball le_rfl
  have hint : IntegrableOn (fun y ↦ W1p.value u y - m) B mu :=
    (((Lp.memLp (W1p.value u)).mono_measure hle).integrable Fact.out).sub (integrable_const m)
  have hgint : IntegrableOn (W1p.gradient u) B mu :=
    ((Lp.memLp (W1p.gradient u)).mono_measure hle).integrable Fact.out
  -- Poincaré–Wirtinger in `L¹`, written in `ℝ≥0∞`.
  have hPW : ∫⁻ y in B, ‖W1p.value u y - m‖ₑ ∂mu ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * r) * eLpNorm (W1p.gradient u) 1 (mu.restrict B) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm hint,
      eLpNorm_one_eq_lintegral_enorm ((Lp.aestronglyMeasurable _).mono_measure hle),
      ← ofReal_integral_norm_eq_lintegral_enorm hgint, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    simpa only [Real.norm_eq_abs] using
      W1p.setIntegral_abs_value_sub_setAverage_le_of_ball_subset hr hball u
  -- Hölder's inequality on the ball.
  have hH : eLpNorm (W1p.gradient u) 1 (mu.restrict B) ≤
      eLpNorm (W1p.gradient u) p (mu.restrict B) * mu B ^ (1 - p.toReal⁻¹) := by
    simpa [Measure.restrict_apply_univ] using
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ (Fact.out : 1 ≤ p)
        ((Lp.aestronglyMeasurable (W1p.gradient u)).mono_measure hle)
  have hpow : mu B ^ (1 - p.toReal⁻¹) / mu B = mu B ^ (-p.toReal⁻¹) := by
    rw [div_eq_mul_inv, ← ENNReal.rpow_neg_one, ← ENNReal.rpow_add _ _ hB0 hBtop]
    ring_nf
  calc ⨍⁻ y in B, ‖W1p.value u y - m‖ₑ ∂mu
      = (∫⁻ y in B, ‖W1p.value u y - m‖ₑ ∂mu) / mu B := setLAverage_eq ..
    _ ≤ ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * r) *
          (eLpNorm (W1p.gradient u) p (mu.restrict B) * mu B ^ (1 - p.toReal⁻¹)) / mu B := by
        gcongr
        exact hPW.trans (by gcongr)
    _ = ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * r) * mu B ^ (-p.toReal⁻¹) *
          eLpNorm (W1p.gradient u) p (mu.restrict B) := by
        rw [mul_div_assoc, mul_div_assoc, hpow]
        ring

/-- **`W^{1,n}(Ω)` has bounded mean oscillation.** If `u ∈ W^{1,n}(Ω)`, where `n` is the
dimension, then on every ball `B ⊆ Ω`

`⨍_B |u - u_B| ≤ 2^(n + 1) ω^(-1/n) ‖∇u‖_{Lⁿ(B)}`, where `ω = μ(B(0, 1))`.

The bound does not depend on the radius of `B`. Since `‖∇u‖_{Lⁿ(B)} ≤ ‖∇u‖_{Lⁿ(Ω)}`, the mean
oscillation of `u` on balls in `Ω` is bounded uniformly: `u ∈ BMO(Ω)`, with BMO seminorm at most
`2^(n + 1) ω^(-1/n) ‖∇u‖_{Lⁿ(Ω)}`. -/
theorem W1p.setLAverage_enorm_value_sub_setAverage_ball_le (hp : p = finrank ℝ E) {x : E}
    {r : ℝ} (hball : ball x r ⊆ (Omega : Set E)) (u : W1p mu Omega p) :
    ⨍⁻ y in ball x r, ‖W1p.value u y - ⨍ z in ball x r, W1p.value u z ∂mu‖ₑ ∂mu ≤
      2 ^ (finrank ℝ E + 1) * mu (ball (0 : E) 1) ^ (-(finrank ℝ E : ℝ)⁻¹) *
        eLpNorm (W1p.gradient u) p (mu.restrict (ball x r)) := by
  rcases le_or_gt r 0 with hr | hr
  · -- The ball is empty.
    simp [ball_eq_empty.2 hr]
  set n := finrank ℝ E
  have hn : n ≠ 0 := by
    rintro h
    have h1 : (1 : ℝ≥0∞) ≤ p := Fact.out
    simp [hp, h] at h1
  have hpn : p.toReal = n := by rw [hp, ENNReal.toReal_natCast]
  have h0 : mu (ball (0 : E) 1) ≠ 0 := (measure_ball_pos mu 0 one_pos).ne'
  have htop : mu (ball (0 : E) 1) ≠ ∞ := measure_ball_lt_top.ne
  -- The radius cancels: `r (rⁿ)^(-1/n) = 1`.
  have hrad : ENNReal.ofReal r * ENNReal.ofReal (r ^ n) ^ (-(n : ℝ)⁻¹) = 1 := by
    rw [ENNReal.ofReal_rpow_of_pos (by positivity), ← ENNReal.ofReal_mul hr.le,
      Real.rpow_neg (by positivity), Real.pow_rpow_inv_natCast hr.le hn,
      mul_inv_cancel₀ hr.ne', ENNReal.ofReal_one]
  -- The measure of the ball scales out: `r μ(B(x, r))^(-1/n) = ω^(-1/n)`.
  have hscale : ENNReal.ofReal (2 ^ (n + 1) * r) * mu (ball x r) ^ (-p.toReal⁻¹) =
      2 ^ (n + 1) * mu (ball (0 : E) 1) ^ (-(n : ℝ)⁻¹) := by
    rw [Measure.addHaar_ball_of_pos mu x hr, hpn,
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top htop, ENNReal.ofReal_mul (by positivity)]
    calc _ = ENNReal.ofReal (2 ^ (n + 1)) *
          (ENNReal.ofReal r * ENNReal.ofReal (r ^ n) ^ (-(n : ℝ)⁻¹)) *
          mu (ball (0 : E) 1) ^ (-(n : ℝ)⁻¹) := by ring
      _ = 2 ^ (n + 1) * mu (ball (0 : E) 1) ^ (-(n : ℝ)⁻¹) := by
        rw [hrad, mul_one, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
  rw [← hscale]
  exact W1p.setLAverage_enorm_value_sub_setAverage_ball_le_mul_measure_rpow hball u

end General

section Euclidean

variable {ι : Type*} [Fintype ι]

/-- **Local exponential integrability of `W^{1,n}` functions.** There are constants `A > 0` and
`C`, depending only on the dimension `n`, such that the following holds for every additive Haar
measure `μ` on `ℝⁿ = EuclideanSpace ℝ ι`, with `ω = μ(B(0, 1))`. Let `u ∈ W^{1,n}(Ω)` and
`B(x₀, R) ⊆ Ω`. If `σ ω^(-1/n) ‖∇u‖_{Lⁿ(B(x₀, R))} ≤ A`, then on `B' = B(x₀, R / (3√n))`

`∫_{B'} exp (σ |u - u_{B'}|) ≤ C |B'|`.

No boundary condition is imposed on `u`. The hypothesis is invariant under rescaling `μ`. -/
theorem W1p.exists_setLIntegral_exp_mul_abs_value_sub_setAverage_ball_le :
    ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ≥0, ∀ {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {p : ℝ≥0∞} [Fact (1 ≤ p)], p = Fintype.card ι →
      ∀ (u : W1p mu Omega p) {x₀ : EuclideanSpace ℝ ι} {R σ : ℝ},
      ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      σ * (mu.real (ball 0 1) ^ (-(Fintype.card ι : ℝ)⁻¹) *
        (eLpNorm (W1p.gradient u) p (mu.restrict (ball x₀ R))).toReal) ≤ A →
      ∫⁻ x in ball x₀ (R / (3 * √(Fintype.card ι))),
          ENNReal.ofReal (Real.exp (σ * |W1p.value u x -
            ⨍ y in ball x₀ (R / (3 * √(Fintype.card ι))), W1p.value u y ∂mu|)) ∂mu ≤
        C * mu (ball x₀ (R / (3 * √(Fintype.card ι)))) := by
  obtain ⟨A, hA, C, hJN⟩ := exists_setLIntegral_exp_mul_norm_sub_setAverage_ball_le (ι := ι)
  set n := Fintype.card ι
  refine ⟨A / 2 ^ (n + 1), by positivity, C, fun {mu} _ Omega p _ hp u x₀ R σ hball hσ => ?_⟩
  have hpn : p = finrank ℝ (EuclideanSpace ℝ ι) := by rw [hp, finrank_euclideanSpace]
  -- The BMO constant of `u` on `B(x₀, R)`.
  set N := eLpNorm (W1p.gradient u) p (mu.restrict (ball x₀ R))
  set K : ℝ≥0∞ := 2 ^ (n + 1) * mu (ball (0 : EuclideanSpace ℝ ι) 1) ^ (-(n : ℝ)⁻¹) * N
  have hN : N ≠ ∞ := ((eLpNorm_mono_measure _ (Measure.restrict_mono hball le_rfl)).trans_lt
    (Lp.eLpNorm_lt_top (W1p.gradient u))).ne
  have hω0 : mu (ball (0 : EuclideanSpace ℝ ι) 1) ≠ 0 := (measure_ball_pos mu 0 one_pos).ne'
  have hK : K ≠ ∞ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) ?_) hN
    exact ENNReal.rpow_ne_top_of_ne_zero hω0 measure_ball_lt_top.ne
  have hint : IntegrableOn (W1p.value u) (ball x₀ R) mu := by
    have : IsFiniteMeasure (mu.restrict (ball x₀ R)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    exact ((Lp.memLp (W1p.value u)).mono_measure (Measure.restrict_mono hball le_rfl)).integrable
      Fact.out
  -- `u` has mean oscillation at most `K` on every ball inside `B(x₀, R)`.
  have hosc : ∀ y s, ball y s ⊆ ball x₀ R →
      ⨍⁻ x in ball y s, ‖W1p.value u x - ⨍ z in ball y s, W1p.value u z ∂mu‖ₑ ∂mu ≤
        K.toNNReal := by
    intro y s hys
    rw [ENNReal.coe_toNNReal hK]
    refine (W1p.setLAverage_enorm_value_sub_setAverage_ball_le hpn (hys.trans hball) u).trans ?_
    rw [finrank_euclideanSpace]
    simp only [K]
    gcongr
    exact eLpNorm_mono_measure _ (Measure.restrict_mono hys le_rfl)
  have hσK : σ * (K.toNNReal : ℝ) ≤ A := by
    have hKreal : (K.toNNReal : ℝ) = 2 ^ (n + 1) * (mu.real (ball 0 1) ^ (-(n : ℝ)⁻¹) *
        N.toReal) := by
      simp only [ENNReal.coe_toNNReal_eq_toReal, K, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofNat, ENNReal.toReal_rpow, measureReal_def, mul_assoc]
    rw [hKreal, mul_left_comm]
    calc 2 ^ (n + 1) * (σ * (mu.real (ball 0 1) ^ (-(n : ℝ)⁻¹) * N.toReal))
        ≤ 2 ^ (n + 1) * (A / 2 ^ (n + 1)) := by gcongr
      _ = A := mul_div_cancel₀ A (by positivity)
  simpa only [Real.norm_eq_abs] using hJN hint hosc hσK

end Euclidean

end TauCeti

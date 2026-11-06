/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.MaximalFunction
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# The Hardy–Littlewood–Sobolev inequality

Let `E` be a real normed space of finite dimension `n ≥ 1` with an additive Haar measure `μ`, let
`1 < p < q < ∞` and put `κ = 1/p - 1/q`. This file proves the **Hardy–Littlewood–Sobolev
inequality**: the Riesz potential of order `n κ`,

`I f (x) = ∫ ‖x - y‖ ^ (n (κ - 1)) f(y) dy`,

maps `Lᵖ(E)` to `L^q(E)`, `‖I f‖_q ≤ C ‖f‖_p`, with `C` depending only on `μ`, `p` and `q`
(`TauCeti.exists_eLpNorm_lintegral_enorm_sub_rpow_mul_le`). This is the critical case
`1/p - 1/q = κ` of the bound for Riesz potentials on sets of finite measure,
`TauCeti.eLpNorm_setLIntegral_enorm_sub_rpow_mul_le`, which needs `1/p - 1/q < κ` and a factor of
the measure of the set; on the whole space only the critical exponent is compatible with
dilations. On the real line it is the fractional integration inequality
`‖∫ |t - s| ^ (-γ) F(s) ds‖_{L^q} ≤ C ‖F‖_{Lᵖ}` for `1/p - 1/q = 1 - γ`, which converts decay
of the form `|t - s| ^ (-γ)` in time into `Lᵖ`-`L^q` bounds for time integrals, as in the `TT*`
proof of the non-endpoint Strichartz estimates.

## The argument

The proof is Hedberg's. Fix `x` and a radius `R > 0`, and split `E` into dyadic shells about
`x`: the shells `R / 2 ^ (k + 1) < ‖x - y‖ ≤ R / 2 ^ k` inside the ball of radius `R`, and the
shells `2 ^ k R ≤ ‖x - y‖ < 2 ^ (k + 1) R` outside it. On an inner shell the kernel is at most
`(R / 2 ^ (k + 1)) ^ (n (κ - 1))`, and the integral of `f` over the ball containing the shell is
bounded by the Hardy–Littlewood maximal function `M f (x)` times the measure of the ball. On an
outer shell Hölder's inequality bounds the integral of `f` by `‖f‖_p` times a power of the measure
of the ball. Summing the two geometric series gives

`I f (x) ≤ A R ^ (n κ) M f (x) + B R ^ (-n / q) ‖f‖_p`,

and choosing `R` to balance the two terms gives Hedberg's pointwise inequality
(`TauCeti.exists_lintegral_enorm_sub_rpow_mul_le`)

`I f (x) ≤ C M f (x) ^ (p / q) ‖f‖_p ^ (1 - p / q)`.

Raising it to the power `q` and integrating, the strong type `(p, p)` bound for the maximal
function (`TauCeti.lintegral_rpow_maximalFunction_le`) gives the inequality.

## Main declarations

* `TauCeti.exists_lintegral_enorm_sub_rpow_mul_le`: Hedberg's pointwise inequality.
* `TauCeti.exists_eLpNorm_lintegral_enorm_sub_rpow_mul_le`: the Hardy–Littlewood–Sobolev
  inequality.

## References

* L. I. Hedberg, *On certain convolution inequalities*, Proc. Amer. Math. Soc. 36 (1972),
  505–510.
* E. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V, §1.2.
* L. Grafakos, *Modern Fourier Analysis*, Theorem 1.2.3.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Metric Set Module
open scoped ENNReal NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
  [BorelSpace E] in
/-- Every point other than `x` lies in a dyadic shell about `x`: in
`ball x (4 ρₖ) \ closedBall x ρₖ` with `ρₖ = R / 2 ^ (k + 1)` when it is within `R` of `x`, and
in `ball x (2 σₖ) \ ball x σₖ` with `σₖ = 2 ^ k R` otherwise. -/
private theorem mem_iUnion_shell_or_mem_iUnion_shell {R : ℝ} (hR : 0 < R) (x : E) {y : E}
    (hy : y ≠ x) :
    y ∈ (⋃ k : ℕ, ball x (4 * (R / 2 ^ (k + 1))) \ closedBall x (R / 2 ^ (k + 1))) ∪
      ⋃ k : ℕ, ball x (2 * (2 ^ k * R)) \ ball x (2 ^ k * R) := by
  have hd : 0 < dist y x := dist_pos.2 hy
  rcases le_or_gt (dist y x) R with h | h
  · obtain ⟨k, hk₁, hk₂⟩ := exists_nat_pow_near ((one_le_div hd).2 h) one_lt_two
    rw [le_div_iff₀ hd] at hk₁
    rw [div_lt_iff₀ hd] at hk₂
    have h2 : (0 : ℝ) < 2 ^ k := by positivity
    refine Or.inl (mem_iUnion.2 ⟨k, ?_, ?_⟩)
    · have h4 : 4 * (R / 2 ^ (k + 1)) = 2 * R / 2 ^ k := by
        rw [pow_succ]
        field_simp
        norm_num
      rw [mem_ball, h4, lt_div_iff₀ h2]
      nlinarith
    · rw [mem_closedBall, not_le, div_lt_iff₀ (by positivity)]
      linarith
  · obtain ⟨k, hk₁, hk₂⟩ := exists_nat_pow_near ((one_le_div hR).2 h.le) one_lt_two
    rw [le_div_iff₀ hR] at hk₁
    rw [div_lt_iff₀ hR] at hk₂
    refine Or.inr (mem_iUnion.2 ⟨k, ?_, ?_⟩)
    · rw [pow_succ] at hk₂
      rw [mem_ball]
      linarith
    · rw [mem_ball, not_lt]
      exact hk₁

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E]
  [μ.IsAddHaarMeasure] in
/-- On a set where `ρ ≤ dist y x`, a kernel `‖x - y‖ ^ s` with `s ≤ 0` is at most `ρ ^ s`. -/
private theorem setLIntegral_enorm_sub_rpow_mul_le {S : Set E} (hS : MeasurableSet S) {ρ s : ℝ}
    (hρ : 0 < ρ) (hs : s ≤ 0) (x : E) (h : ∀ y ∈ S, ρ ≤ dist y x) (f : E → ℝ≥0∞) :
    ∫⁻ y in S, ‖x - y‖ₑ ^ s * f y ∂μ ≤ ENNReal.ofReal (ρ ^ s) * ∫⁻ y in S, f y ∂μ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hS fun y hy => ?_
  gcongr
  rw [← ofReal_norm, norm_sub_rev, ← dist_eq_norm,
    ENNReal.ofReal_rpow_of_pos (hρ.trans_le (h y hy))]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hρ (h y hy) hs)

/-- The integral of the kernel against `f` over the inner shell of index `k`, bounded by the
maximal function. -/
private theorem setLIntegral_inner_shell_le {κ : ℝ} (hκ1 : κ ≤ 1) {R : ℝ} (hR : 0 < R) (x : E)
    (f : E → ℝ≥0∞) (k : ℕ) :
    ∫⁻ y in ball x (4 * (R / 2 ^ (k + 1))) \ closedBall x (R / 2 ^ (k + 1)),
        ‖x - y‖ₑ ^ ((finrank ℝ E : ℝ) * (κ - 1)) * f y ∂μ ≤
      ENNReal.ofReal (4 ^ finrank ℝ E * R ^ ((finrank ℝ E : ℝ) * κ)) * μ (ball 0 1) *
        maximalFunction μ f x * ENNReal.ofReal (2 ^ (-((finrank ℝ E : ℝ) * κ))) ^ (k + 1) := by
  set n := finrank ℝ E
  have hn : (0 : ℝ) < n := by exact_mod_cast finrank_pos
  set ρ : ℝ := R / 2 ^ (k + 1)
  have hρ : 0 < ρ := by positivity
  have hpow : ρ ^ ((n : ℝ) * (κ - 1)) * (4 * ρ) ^ n =
      4 ^ n * R ^ ((n : ℝ) * κ) * (2 ^ (-((n : ℝ) * κ))) ^ (k + 1) := by
    rw [mul_pow, ← Real.rpow_natCast ρ, mul_left_comm, ← Real.rpow_add hρ,
      show (n : ℝ) * (κ - 1) + n = n * κ by ring, Real.div_rpow hR.le (by positivity),
      ← Real.rpow_natCast (2 : ℝ), ← Real.rpow_mul two_pos.le, mul_comm _ ((n : ℝ) * κ),
      Real.rpow_mul two_pos.le, Real.rpow_natCast, div_eq_mul_inv, ← inv_pow,
      ← Real.rpow_neg two_pos.le]
    ring
  calc
    _ ≤ ENNReal.ofReal (ρ ^ ((n : ℝ) * (κ - 1))) *
          ∫⁻ y in ball x (4 * ρ) \ closedBall x ρ, f y ∂μ :=
      setLIntegral_enorm_sub_rpow_mul_le (measurableSet_ball.diff measurableSet_closedBall) hρ
        (mul_nonpos_of_nonneg_of_nonpos hn.le (by linarith)) x
        (fun y hy => (not_le.1 hy.2).le) f
    _ ≤ ENNReal.ofReal (ρ ^ ((n : ℝ) * (κ - 1))) *
          (μ (ball x (4 * ρ)) * maximalFunction μ f x) := by
      gcongr
      refine (lintegral_mono_set sdiff_subset).trans ?_
      simpa only [enorm_eq_self] using setLIntegral_ball_le_measure_mul_maximalFunction μ f x
        (by positivity) measure_ball_lt_top.ne
    _ = _ := by
      rw [Measure.addHaar_ball μ x (by positivity), ← mul_assoc, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity), hpow,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
      ring

/-- The integral of the kernel against `f` over the outer shell of index `k`, bounded by `‖f‖_p`
through Hölder's inequality. -/
private theorem setLIntegral_outer_shell_le {p : ℝ≥0} (hp : 1 ≤ p) {κ : ℝ} (hκ1 : κ ≤ 1) {R : ℝ}
    (hR : 0 < R) (x : E) (f : E → ℝ≥0∞) (k : ℕ) :
    ∫⁻ y in ball x (2 * (2 ^ k * R)) \ ball x (2 ^ k * R),
        ‖x - y‖ₑ ^ ((finrank ℝ E : ℝ) * (κ - 1)) * f y ∂μ ≤
      ENNReal.ofReal (2 ^ ((finrank ℝ E : ℝ) * (1 - (p : ℝ)⁻¹)) *
          R ^ ((finrank ℝ E : ℝ) * (κ - (p : ℝ)⁻¹))) * μ (ball 0 1) ^ (1 - (p : ℝ)⁻¹) *
        eLpNorm f p μ * ENNReal.ofReal (2 ^ ((finrank ℝ E : ℝ) * (κ - (p : ℝ)⁻¹))) ^ k := by
  set n := finrank ℝ E
  have hn : (0 : ℝ) < n := by exact_mod_cast finrank_pos
  set c : ℝ := 1 - (p : ℝ)⁻¹
  have hc : 0 ≤ c := sub_nonneg.2 (inv_le_one_of_one_le₀ (by exact_mod_cast hp))
  set e : ℝ := (n : ℝ) * (κ - (p : ℝ)⁻¹)
  set σ : ℝ := 2 ^ k * R
  have hσ : 0 < σ := by positivity
  -- The powers of `σ = 2 ^ k R` combine into `R ^ e (2 ^ e) ^ k`.
  have hpow : σ ^ ((n : ℝ) * (κ - 1)) * ((2 * σ) ^ n) ^ c =
      2 ^ ((n : ℝ) * c) * R ^ e * (2 ^ e) ^ k := by
    have h₁ : ((2 * σ) ^ n) ^ c = 2 ^ ((n : ℝ) * c) * σ ^ ((n : ℝ) * c) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.mul_rpow two_pos.le hσ.le]
    have h₂ : σ ^ ((n : ℝ) * (κ - 1)) * σ ^ ((n : ℝ) * c) = σ ^ e := by
      rw [← Real.rpow_add hσ]
      congr 1
      simp only [c, e]
      ring
    have h₃ : σ ^ e = R ^ e * (2 ^ e) ^ k := by
      rw [Real.mul_rpow (by positivity) hR.le, ← Real.rpow_natCast (2 : ℝ) k,
        ← Real.rpow_mul two_pos.le, mul_comm (k : ℝ), Real.rpow_mul two_pos.le,
        Real.rpow_natCast, mul_comm]
    rw [h₁, mul_left_comm, h₂, h₃]
    ring
  calc
    _ ≤ ENNReal.ofReal (σ ^ ((n : ℝ) * (κ - 1))) * ∫⁻ y in ball x (2 * σ) \ ball x σ, f y ∂μ :=
      setLIntegral_enorm_sub_rpow_mul_le (measurableSet_ball.diff measurableSet_ball) hσ
        (mul_nonpos_of_nonneg_of_nonpos hn.le (by linarith)) x (fun y hy => not_lt.1 hy.2) f
    _ ≤ ENNReal.ofReal (σ ^ ((n : ℝ) * (κ - 1))) * (μ (ball x (2 * σ)) ^ c * eLpNorm f p μ) := by
      gcongr
      refine (lintegral_mono_set sdiff_subset).trans ?_
      simpa only [enorm_eq_self] using
        setLIntegral_enorm_le_measure_rpow_mul_eLpNorm (μ := μ) hp (ball x (2 * σ)) f
    _ = _ := by
      rw [Measure.addHaar_ball μ x (by positivity), ENNReal.mul_rpow_of_nonneg _ _ hc,
        ENNReal.ofReal_rpow_of_nonneg (by positivity) hc, ← mul_assoc, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity), hpow, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow (by positivity)]
      ring

/-- The two-scale bound behind Hedberg's inequality: for every radius `R > 0`, the potential at
`x` is at most `A R ^ (n κ) M f (x) + B R ^ (n (κ - 1/p)) ‖f‖_p`, with `A` and `B` independent of
`R`, `x` and `f`. -/
private theorem lintegral_enorm_sub_rpow_mul_le_add {p : ℝ≥0} (hp : 1 ≤ p) {κ : ℝ}
    (hκ1 : κ ≤ 1) {R : ℝ} (hR : 0 < R) (x : E) (f : E → ℝ≥0∞) :
    ∫⁻ y, ‖x - y‖ₑ ^ ((finrank ℝ E : ℝ) * (κ - 1)) * f y ∂μ ≤
      ENNReal.ofReal (4 ^ finrank ℝ E * R ^ ((finrank ℝ E : ℝ) * κ)) * μ (ball 0 1) *
          maximalFunction μ f x *
          (ENNReal.ofReal (2 ^ (-((finrank ℝ E : ℝ) * κ))) *
            (1 - ENNReal.ofReal (2 ^ (-((finrank ℝ E : ℝ) * κ))))⁻¹) +
        ENNReal.ofReal (2 ^ ((finrank ℝ E : ℝ) * (1 - (p : ℝ)⁻¹)) *
            R ^ ((finrank ℝ E : ℝ) * (κ - (p : ℝ)⁻¹))) * μ (ball 0 1) ^ (1 - (p : ℝ)⁻¹) *
          eLpNorm f p μ * (1 - ENNReal.ofReal (2 ^ ((finrank ℝ E : ℝ) * (κ - (p : ℝ)⁻¹))))⁻¹ := by
  set g := fun y => ‖x - y‖ₑ ^ ((finrank ℝ E : ℝ) * (κ - 1)) * f y
  set S₁ := ⋃ k : ℕ, ball x (4 * (R / 2 ^ (k + 1))) \ closedBall x (R / 2 ^ (k + 1))
  set S₂ := ⋃ k : ℕ, ball x (2 * (2 ^ k * R)) \ ball x (2 ^ k * R)
  have hcover : univ ⊆ {x} ∪ (S₁ ∪ S₂) := fun y _ => by
    rcases eq_or_ne y x with rfl | hy
    · exact Or.inl rfl
    · exact Or.inr (mem_iUnion_shell_or_mem_iUnion_shell hR x hy)
  calc
    ∫⁻ y, g y ∂μ ≤ ∫⁻ y in {x}, g y ∂μ + (∫⁻ y in S₁, g y ∂μ + ∫⁻ y in S₂, g y ∂μ) := by
      rw [← setLIntegral_univ]
      refine (lintegral_mono_set hcover).trans ((lintegral_union_le _ _ _).trans ?_)
      gcongr
      exact lintegral_union_le _ _ _
    _ ≤ ∑' k : ℕ, ∫⁻ y in ball x (4 * (R / 2 ^ (k + 1))) \ closedBall x (R / 2 ^ (k + 1)),
          g y ∂μ + ∑' k : ℕ, ∫⁻ y in ball x (2 * (2 ^ k * R)) \ ball x (2 ^ k * R), g y ∂μ := by
      rw [setLIntegral_measure_zero _ _ (measure_singleton x), zero_add]
      exact add_le_add (lintegral_iUnion_le _ _) (lintegral_iUnion_le _ _)
    _ ≤ _ := by
      gcongr
      · refine (tsum_le_tsum (setLIntegral_inner_shell_le hκ1 hR x f)).trans_eq ?_
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
      · refine (tsum_le_tsum (setLIntegral_outer_shell_le hp hκ1 hR x f)).trans_eq ?_
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- The two-scale bound with its constants collected: for `1 ≤ p` and `0 < κ < 1/p` there are
finite constants `A ≠ 0` and `B` with
`∫ ‖x - y‖ ^ (n (κ - 1)) f(y) dy ≤ A R ^ (n κ) M f (x) + B R ^ (n (κ - 1/p)) ‖f‖_p` for all `f`,
`x` and `R > 0`. -/
private theorem exists_lintegral_enorm_sub_rpow_mul_le_add {p : ℝ≥0} (hp : 1 ≤ p) {κ : ℝ}
    (hκ0 : 0 < κ) (hκp : κ < (p : ℝ)⁻¹) :
    ∃ A B : ℝ≥0∞, A ≠ 0 ∧ A + B ≠ ∞ ∧ ∀ (f : E → ℝ≥0∞) (x : E) (R : ℝ), 0 < R →
      ∫⁻ y, ‖x - y‖ₑ ^ ((finrank ℝ E : ℝ) * (κ - 1)) * f y ∂μ ≤
        A * ENNReal.ofReal (R ^ ((finrank ℝ E : ℝ) * κ)) * maximalFunction μ f x +
          B * ENNReal.ofReal (R ^ ((finrank ℝ E : ℝ) * (κ - (p : ℝ)⁻¹))) * eLpNorm f p μ := by
  set n := finrank ℝ E
  have hn : (0 : ℝ) < n := by exact_mod_cast finrank_pos
  have hκ1 : κ ≤ 1 := hκp.le.trans (inv_le_one_of_one_le₀ (by exact_mod_cast hp))
  have hc : 0 ≤ 1 - (p : ℝ)⁻¹ := sub_nonneg.2 (inv_le_one_of_one_le₀ (by exact_mod_cast hp))
  set r := ENNReal.ofReal (2 ^ (-((n : ℝ) * κ)))
  set r' := ENNReal.ofReal (2 ^ ((n : ℝ) * (κ - (p : ℝ)⁻¹)))
  have hr : r < 1 := ENNReal.ofReal_lt_one.2
    (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by nlinarith))
  have hr' : r' < 1 := ENNReal.ofReal_lt_one.2
    (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (mul_neg_of_pos_of_neg hn (by linarith)))
  set ω := μ (ball (0 : E) 1)
  have hω : ω ≠ ∞ := measure_ball_lt_top.ne
  refine ⟨ENNReal.ofReal (4 ^ n) * ω * (r * (1 - r)⁻¹),
    ENNReal.ofReal (2 ^ ((n : ℝ) * (1 - (p : ℝ)⁻¹))) * ω ^ (1 - (p : ℝ)⁻¹) * (1 - r')⁻¹,
    ?_, ?_, fun f x R hR => (lintegral_enorm_sub_rpow_mul_le_add hp hκ1 hR x f).trans_eq ?_⟩
  · have hr0 : r ≠ 0 := by simp only [r, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    have h4 : ENNReal.ofReal (4 ^ n) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    exact mul_ne_zero (mul_ne_zero h4 (measure_ball_pos μ 0 one_pos).ne')
      (mul_ne_zero hr0 (ENNReal.inv_ne_zero.2 (ENNReal.sub_ne_top ENNReal.one_ne_top)))
  · have h₁ : (1 - r)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr).ne'
    have h₂ : (1 - r')⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr').ne'
    have h₃ : ω ^ (1 - (p : ℝ)⁻¹) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hc hω
    simp only [ne_eq, ENNReal.add_eq_top, ENNReal.mul_eq_top, ENNReal.ofReal_ne_top, hω, h₁, h₂,
      h₃, r, false_and, and_false, or_false, not_false_eq_true]
  · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    ring

/-- If `I ≤ B R ^ e` for every `R > 0`, with `B` finite and `e < 0`, then `I = 0`. -/
private theorem eq_zero_of_forall_le_mul_ofReal_rpow {I B : ℝ≥0∞} {e : ℝ} (he : e < 0)
    (hB : B ≠ ∞) (h : ∀ R : ℝ, 0 < R → I ≤ B * ENNReal.ofReal (R ^ e)) : I = 0 := by
  have h₀ : Tendsto (fun R : ℝ => ENNReal.ofReal (R ^ e)) atTop (𝓝 0) := by
    simpa only [neg_neg, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (tendsto_rpow_neg_atTop (y := -e) (by linarith))
  have ht := ENNReal.Tendsto.const_mul h₀ (Or.inr hB)
  rw [mul_zero] at ht
  exact le_antisymm (ge_of_tendsto ht ((eventually_gt_atTop 0).mono h)) zero_le

/-- Balancing the two scales in real numbers: for `m, ν > 0`,
`(ν / m) ^ (1 - a) m = m ^ a ν ^ (1 - a) = (ν / m) ^ (-a) ν`. -/
private theorem rpow_div_rpow_one_sub_mul_eq {m ν a : ℝ} (hm : 0 < m) (hν : 0 < ν) :
    (ν / m) ^ (1 - a) * m = m ^ a * ν ^ (1 - a) ∧ (ν / m) ^ (-a) * ν = m ^ a * ν ^ (1 - a) := by
  have hma : m ^ a * m ^ (1 - a) = m := by rw [← Real.rpow_add hm]; simp
  have hνa : ν ^ a * ν ^ (1 - a) = ν := by rw [← Real.rpow_add hν]; simp
  refine ⟨?_, ?_⟩
  · rw [Real.div_rpow hν.le hm.le, div_mul_eq_mul_div, div_eq_iff (by positivity)]
    nth_rw 1 [← hma]
    ring
  · rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div,
      Real.div_rpow hm.le hν.le, div_mul_eq_mul_div, div_eq_iff (by positivity)]
    nth_rw 1 [← hνa]
    ring

/-- Balancing the two scales: if `0 < M < ∞` and `0 < N < ∞`, then at the radius
`R = (N / M) ^ (p / n)` both terms of the two-scale bound equal `M ^ (p / q) N ^ (1 - p / q)`. -/
private theorem exists_ofReal_rpow_mul_eq {n p q κ : ℝ} (hn : 0 < n) (hp : 0 < p) (hpq : p ≤ q)
    (hκ : p⁻¹ - q⁻¹ = κ) {M N : ℝ≥0∞} (hM : M ≠ 0) (hMt : M ≠ ∞) (hN : N ≠ 0) (hNt : N ≠ ∞) :
    ∃ R : ℝ, 0 < R ∧ ENNReal.ofReal (R ^ (n * κ)) * M = M ^ (p / q) * N ^ (1 - p / q) ∧
      ENNReal.ofReal (R ^ (n * (κ - p⁻¹))) * N = M ^ (p / q) * N ^ (1 - p / q) := by
  have hq : 0 < q := hp.trans_le hpq
  obtain ⟨m, hm, rfl⟩ : ∃ m, 0 < m ∧ M = ENNReal.ofReal m :=
    ⟨M.toReal, ENNReal.toReal_pos hM hMt, (ENNReal.ofReal_toReal hMt).symm⟩
  obtain ⟨ν, hν, rfl⟩ : ∃ ν, 0 < ν ∧ N = ENNReal.ofReal ν :=
    ⟨N.toReal, ENNReal.toReal_pos hN hNt, (ENNReal.ofReal_toReal hNt).symm⟩
  obtain ⟨h₁, h₂⟩ := rpow_div_rpow_one_sub_mul_eq (a := p / q) hm hν
  have hX : ENNReal.ofReal m ^ (p / q) * ENNReal.ofReal ν ^ (1 - p / q) =
      ENNReal.ofReal (m ^ (p / q) * ν ^ (1 - p / q)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hm.le (by positivity),
      ENNReal.ofReal_rpow_of_nonneg hν.le (sub_nonneg.2 ((div_le_one hq).2 hpq)),
      ← ENNReal.ofReal_mul (by positivity)]
  refine ⟨(ν / m) ^ (p / n), by positivity, ?_, ?_⟩
  · rw [hX, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_mul (by positivity),
      show p / n * (n * κ) = 1 - p / q by rw [← hκ]; field_simp, h₁]
  · rw [hX, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_mul (by positivity),
      show p / n * (n * (κ - p⁻¹)) = -(p / q) by rw [← hκ]; field_simp; ring, h₂]

/-- **Hedberg's inequality.** Let `1 ≤ p < q < ∞` and `κ = 1/p - 1/q`. There is a constant `C`,
depending only on `μ`, `p` and `q`, such that for every `f` with finite `Lᵖ` seminorm and every
point `x`, the Riesz potential of order `n κ` is bounded by the Hardy–Littlewood maximal function:

`∫ ‖x - y‖ ^ (n (κ - 1)) f(y) dy ≤ C M f (x) ^ (p / q) ‖f‖_p ^ (1 - p / q)`,

where `n` is the dimension of `E`. -/
theorem exists_lintegral_enorm_sub_rpow_mul_le {p q : ℝ≥0} (hp : 1 ≤ p) (hpq : p < q) {κ : ℝ}
    (hκ : (p : ℝ)⁻¹ - (q : ℝ)⁻¹ = κ) :
    ∃ C : ℝ≥0, ∀ f : E → ℝ≥0∞, eLpNorm f p μ ≠ ∞ → ∀ x,
      ∫⁻ y, ‖x - y‖ₑ ^ ((finrank ℝ E : ℝ) * (κ - 1)) * f y ∂μ ≤
        C * maximalFunction μ f x ^ ((p : ℝ) / q) * eLpNorm f p μ ^ (1 - (p : ℝ) / q) := by
  have hn : (0 : ℝ) < finrank ℝ E := by exact_mod_cast finrank_pos
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp)
  have hpq' : (p : ℝ) < q := by exact_mod_cast hpq
  have hq0 : (0 : ℝ) < q := hp0.trans hpq'
  have hκ0 : 0 < κ := by rw [← hκ]; exact sub_pos.2 (inv_strictAnti₀ hp0 hpq')
  have hκp : κ < (p : ℝ)⁻¹ := by rw [← hκ]; linarith [inv_pos.2 hq0]
  obtain ⟨A, B, hA0, hAB, key⟩ := exists_lintegral_enorm_sub_rpow_mul_le_add (μ := μ) hp hκ0 hκp
  refine ⟨(A + B).toNNReal, fun f hf x => ?_⟩
  rw [ENNReal.coe_toNNReal hAB]
  have hkey := fun R => key f x R
  set M := maximalFunction μ f x
  set N := eLpNorm f p μ
  -- If the maximal function vanishes at `x`, the outer term alone bounds the potential, and it
  -- tends to zero as `R → ∞`.
  rcases eq_or_ne M 0 with hM | hM
  · refine (eq_zero_of_forall_le_mul_ofReal_rpow (B := B * N)
      (mul_neg_of_pos_of_neg hn (sub_neg.2 hκp))
      (ENNReal.mul_ne_top (ENNReal.add_ne_top.1 hAB).2 hf) fun R hR => ?_).trans_le zero_le
    simpa only [hM, mul_zero, zero_add, mul_right_comm B] using hkey R hR
  -- Otherwise `f` is not almost everywhere zero, so `‖f‖_p ≠ 0`.
  have hN : N ≠ 0 := fun hN => hM (by
    have hf0 := (eLpNorm_eq_zero_iff (by positivity)).1 hN
    simp only [M]
    rw [maximalFunction_congr_ae (μ := μ) (x := x) (g := (0 : E → ℝ≥0∞))
      (hf0.mono fun y hy => by rw [hy]), maximalFunction_zero])
  rcases eq_or_ne M ∞ with hMt | hMt
  · rw [hMt, ENNReal.top_rpow_of_pos (by positivity), ENNReal.mul_top (by simp [hA0]),
      ENNReal.top_mul (by simp [hN, (div_le_one hq0).2 hpq'.le])]
    exact le_top
  -- In the remaining case `0 < M f (x) < ∞` and `0 < ‖f‖_p < ∞`, choose `R` to balance the two
  -- terms.
  obtain ⟨R, hR, h₁, h₂⟩ := exists_ofReal_rpow_mul_eq hn hp0 hpq'.le hκ hM hMt hN hf
  calc
    _ ≤ _ := hkey R hR
    _ = (A + B) * M ^ ((p : ℝ) / q) * N ^ (1 - (p : ℝ) / q) := by
      rw [mul_assoc A, h₁, mul_assoc B, h₂, ← add_mul, mul_assoc]

omit [Nontrivial E] in
/-- Integrating Hedberg's inequality: if `I x ≤ C M f (x) ^ (p / q) ‖f‖_p ^ (1 - p / q)` for every
`x`, then `∫ I ^ q ≤ C ^ q K ‖f‖_p ^ q`, where `K` is the constant of the maximal inequality. -/
private theorem lintegral_rpow_le_of_le_mul_maximalFunction_rpow {p q : ℝ≥0} (hp : 1 < p)
    (hpq : p < q) {f I : E → ℝ≥0∞} (hf : eLpNorm f p μ ≠ ∞) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h : ∀ x, I x ≤ C * maximalFunction μ f x ^ ((p : ℝ) / q) * eLpNorm f p μ ^ (1 - (p : ℝ) / q)) :
    ∫⁻ x, I x ^ (q : ℝ) ∂μ ≤ C ^ (q : ℝ) *
      (ENNReal.ofReal (2 * p * 2 ^ ((p : ℝ) - 1) / ((p : ℝ) - 1)) * 4 ^ finrank ℝ E) *
        eLpNorm f p μ ^ (q : ℝ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hpq' : (p : ℝ) < q := by exact_mod_cast hpq
  have hq0 : (0 : ℝ) < q := by linarith
  have hfm : AEMeasurable f μ := (aestronglyMeasurable_of_eLpNorm_ne_top hf).aemeasurable
  set N := eLpNorm f p μ
  have hN : N ^ ((q : ℝ) - p) * N ^ (p : ℝ) = N ^ (q : ℝ) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by positivity)]
    ring_nf
  calc
    _ ≤ ∫⁻ x, C ^ (q : ℝ) * N ^ ((q : ℝ) - p) * maximalFunction μ f x ^ (p : ℝ) ∂μ := by
      refine lintegral_mono fun x => (ENNReal.rpow_le_rpow (h x) hq0.le).trans_eq ?_
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, div_mul_cancel₀ _ hq0.ne',
        show (1 - (p : ℝ) / q) * q = q - p by field_simp]
      ring
    _ = C ^ (q : ℝ) * N ^ ((q : ℝ) - p) * ∫⁻ x, maximalFunction μ f x ^ (p : ℝ) ∂μ :=
      lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq0.le hC)
        (ENNReal.rpow_ne_top_of_nonneg (by linarith) hf))
    _ ≤ C ^ (q : ℝ) * N ^ ((q : ℝ) - p) *
          (ENNReal.ofReal (2 * p * 2 ^ ((p : ℝ) - 1) / ((p : ℝ) - 1)) * 4 ^ finrank ℝ E *
            ∫⁻ x, ‖f x‖ₑ ^ (p : ℝ) ∂μ) := by
      gcongr
      exact lintegral_rpow_maximalFunction_le μ (by simpa only [enorm_eq_self] using hfm) hp1
    _ = _ := by
      rw [← eLpNorm_nnreal_pow_eq_lintegral (by positivity) hfm.aestronglyMeasurable, ← hN]
      ring

/-- **The Hardy–Littlewood–Sobolev inequality.** Let `1 < p < q < ∞` and `κ = 1/p - 1/q`. The
Riesz potential of order `n κ` maps `Lᵖ(E)` to `L^q(E)`: there is a constant `C`, depending only
on `μ`, `p` and `q`, such that for every `f`

`‖∫ ‖· - y‖ ^ (n (κ - 1)) f(y) dy‖_q ≤ C ‖f‖_p`,

where `n` is the dimension of `E`. -/
theorem exists_eLpNorm_lintegral_enorm_sub_rpow_mul_le {p q : ℝ≥0} (hp : 1 < p) (hpq : p < q)
    {κ : ℝ} (hκ : (p : ℝ)⁻¹ - (q : ℝ)⁻¹ = κ) :
    ∃ C : ℝ≥0, ∀ f : E → ℝ≥0∞,
      eLpNorm (fun x => ∫⁻ y, ‖x - y‖ₑ ^ ((finrank ℝ E : ℝ) * (κ - 1)) * f y ∂μ) q μ ≤
        C * eLpNorm f p μ := by
  obtain ⟨C₀, hC₀⟩ := exists_lintegral_enorm_sub_rpow_mul_le (μ := μ) hp.le hpq hκ
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by linarith [(show (p : ℝ) < q by exact_mod_cast hpq)]
  -- The constant of the maximal inequality.
  set K := ENNReal.ofReal (2 * p * 2 ^ ((p : ℝ) - 1) / ((p : ℝ) - 1)) * 4 ^ finrank ℝ E
  have hK : K ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)
  have hK0 : K ≠ 0 := mul_ne_zero (by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have : (0 : ℝ) < p - 1 := by linarith
    positivity) (by simp)
  set D := ((C₀ : ℝ≥0∞) + 1) * K ^ (1 / (q : ℝ))
  have hD : D ≠ ∞ := ENNReal.mul_ne_top (by simp) (ENNReal.rpow_ne_top_of_nonneg (by positivity) hK)
  refine ⟨D.toNNReal, fun f => ?_⟩
  rw [ENNReal.coe_toNNReal hD]
  set N := eLpNorm f p μ
  rcases eq_or_ne N ∞ with hN | hN
  · rw [hN, ENNReal.mul_top (mul_ne_zero (by simp) (by simp [hK0]))]
    exact le_top
  have hfm : AEMeasurable f μ := (aestronglyMeasurable_of_eLpNorm_ne_top hN).aemeasurable
  have hk : Measurable (Function.uncurry fun x y : E =>
      ‖x - y‖ₑ ^ ((finrank ℝ E : ℝ) * (κ - 1))) := by
    fun_prop
  have hI : AEMeasurable
      (fun x => ∫⁻ y, ‖x - y‖ₑ ^ ((finrank ℝ E : ℝ) * (κ - 1)) * f y ∂μ) μ :=
    (hk.aemeasurable.mul hfm.comp_snd).lintegral_prod_right'
  rw [eLpNorm_nnreal_eq_lintegral (NNReal.coe_pos.1 hq0).ne' hI.aestronglyMeasurable]
  simp only [enorm_eq_self]
  calc
    _ ≤ ((C₀ : ℝ≥0∞) ^ (q : ℝ) * K * N ^ (q : ℝ)) ^ (1 / (q : ℝ)) :=
      ENNReal.rpow_le_rpow (lintegral_rpow_le_of_le_mul_maximalFunction_rpow hp hpq hN
        ENNReal.coe_ne_top (hC₀ f hN)) (by positivity)
    _ = (C₀ : ℝ≥0∞) * K ^ (1 / (q : ℝ)) * N := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        mul_one_div_cancel hq0.ne', ENNReal.rpow_one, ENNReal.rpow_one]
    _ ≤ D * N := by
      simp only [D]
      gcongr
      exact le_self_add

end TauCeti

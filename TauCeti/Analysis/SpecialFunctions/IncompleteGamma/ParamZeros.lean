/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Tricomi
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Gamma
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Real

/-!
# Real parameter zeros of Tricomi's incomplete Gamma function

This file classifies the real zeros of `a ↦ γ*(a, x)` for fixed real `x` (DLMF §8.13(iii)(a)–(c)),
where `γ* = Complex.tricomiIncompleteGamma`:

* **Zero argument (`x = 0`)**: `γ*(a, 0) = 1 / Γ(a + 1)` vanishes precisely at the negative
  integers `a = -n`, `n ≥ 1` (`Complex.tricomiIncompleteGamma_zero_right_eq_zero_iff`,
  `Complex.tricomiIncompleteGamma_ofReal_zero_right_eq_zero_iff`).
* **Negative argument (`x < 0`)**: in each open unit interval `(-(m + 1), -m)`, the function
  `a ↦ γ*(a, x)` has a unique real zero, which is simple
  (`Complex.existsUnique_tricomiIncompleteGamma_eq_zero_of_neg`,
  `Complex.deriv_tricomiIncompleteGamma_re_ne_zero_of_neg`). In particular, for `n ≥ 1`, there are
  exactly two simple zeros in `(-2n, 2 - 2n)`
  (`Complex.tricomiIncompleteGamma_param_zeros_of_neg`).
* **Positive argument (`x > 0`)**: for each `n ≥ 1`, there is a critical threshold `x*_n > 0` such
  that on `(-2n, 1 - 2n)`, `a ↦ γ*(a, x)` has two simple zeros for `0 < x < x*_n`, one double zero
  for `x = x*_n`, and no zeros for `x > x*_n` (`Complex.tricomiIncompleteGamma_param_zeros`).

## Implementation notes

For `x < 0`, the series `Γ(a) γ*(a, x) = ∑ (-x)^k / (k! (a + k))` is termwise strictly decreasing
with strictly negative derivative on each unit interval `(-(m + 1), -m)`, while the endpoint values
`γ*(-m, x) = x^m` alternate in sign.

For `x > 0`, on each positive-Gamma band `I_n = (-2n, 1 - 2n)` we rewrite
`Γ(a) (1 - x^a γ*(a, x)) = U(a, x) := ∫_x^∞ t^{a - 1} e^{-t} dt` and analyze the logarithmic ratio
`H_x(a) = log Γ(a) - log U(a, x)`. The trigamma shift recurrence yields `ψ'(a) ≥ 8` on `I_n`, while
a pointwise Chebyshev comparison after substituting `t = x e^s` bounds the logarithmic variance of
`U(·, x)` above by `2 / a^2 < 2`, giving `H_x''(a) > 6 > 0`. Combined with the endpoint blowups
`H_x(a) → +∞` as `a → -2n⁺` or `a → (1 - 2n)⁻`, the minimum value `m_n(x) = inf_{I_n} H_x` is
continuous and strictly increasing from negative to positive values on `(0, ∞)`, producing the
unique threshold `x*_n > 0` where `m_n(x*_n) = 0`.

## References

* *NIST Digital Library of Mathematical Functions*,
  [§8.13(iii)](https://dlmf.nist.gov/8.13#iii).
* F. G. Tricomi, *Sulla funzione gamma incompleta*, Ann. Mat. Pura Appl. (4) 31 (1950).
* K. S. Kölbig, *On the zeros of the incomplete gamma function*, Math. Comp. 26 (1972), 751–755.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Nat Topology Interval

namespace Complex

/-! ### Reality and differentiability in the real parameter -/

private theorem tricomiIncompleteGamma_ofReal_eq_zero_iff (a x : ℝ) :
    tricomiIncompleteGamma a x = 0 ↔ (tricomiIncompleteGamma a x).re = 0 := by
  simp [Complex.ext_iff]

private theorem differentiable_tricomiIncompleteGamma_re (x : ℝ) :
    Differentiable ℝ fun a : ℝ => (tricomiIncompleteGamma a x).re := fun a =>
  reCLM.differentiableAt.comp a
    ((differentiable_tricomiIncompleteGamma_left (x : ℂ) a).hasDerivAt.comp_ofReal).differentiableAt

private theorem ne_neg_natCast_of_mem_Ioo {m : ℕ} {a : ℝ}
    (ha : a ∈ Ioo (-((m : ℝ) + 1)) (-(m : ℝ))) (k : ℕ) : a ≠ -(k : ℝ) := by
  intro hk
  rcases le_or_gt k m with hle | hlt
  · have hle' : (k : ℝ) ≤ m := by exact_mod_cast hle
    linarith [ha.2]
  · have hge : (m : ℝ) + 1 ≤ k := by exact_mod_cast hlt
    linarith [ha.1]

private theorem ofReal_ne_neg_natCast {a : ℝ} (ha : ∀ k : ℕ, a ≠ -(k : ℝ)) (k : ℕ) :
    (a : ℂ) ≠ -(k : ℂ) := by
  intro h
  exact ha k (by exact_mod_cast h)

/-! ### Zeros at `x = 0` (DLMF §8.13(iii)(c)) -/

/-- For `z = 0`, Tricomi's function `γ*(a, 0) = 1 / Γ(a + 1)` vanishes precisely at the negative
integers `a = -n`, `n ≥ 1` (DLMF §8.13(iii)(c)). -/
theorem tricomiIncompleteGamma_zero_right_eq_zero_iff (a : ℂ) :
    tricomiIncompleteGamma a 0 = 0 ↔ ∃ n : ℕ, 1 ≤ n ∧ a = -(n : ℂ) := by
  rw [tricomiIncompleteGamma_zero_right, inv_eq_zero, Gamma_eq_zero_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m + 1, Nat.succ_le_succ (Nat.zero_le m), ?_⟩
    push_cast
    linear_combination hm
  · rintro ⟨n, hn, rfl⟩
    refine ⟨n - 1, ?_⟩
    have hn' : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by rw [Nat.cast_sub hn]; simp
    rw [hn']
    ring

/-- Real specialization of `tricomiIncompleteGamma_zero_right_eq_zero_iff`: for real `a`,
`γ*(a, 0) = 0` if and only if `a = -n` for some `n ≥ 1`. -/
theorem tricomiIncompleteGamma_ofReal_zero_right_eq_zero_iff (a : ℝ) :
    tricomiIncompleteGamma a 0 = 0 ↔ ∃ n : ℕ, 1 ≤ n ∧ a = -(n : ℝ) := by
  rw [tricomiIncompleteGamma_zero_right_eq_zero_iff]
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, by exact_mod_cast h⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, by push_cast; rfl⟩

/-! ### Zeros for `x < 0` (DLMF §8.13(iii)(a)) -/

private theorem hasSum_Gamma_mul_tricomi_re {a : ℝ} (ha : ∀ k : ℕ, a ≠ -(k : ℝ)) (x : ℝ) :
    HasSum (fun k : ℕ => (-x) ^ k / (k ! * (a + k)))
      (Real.Gamma a * (tricomiIncompleteGamma a x).re) := by
  have hC := (hasSum_tricomiIncompleteGamma_of_ne_neg_natCast (ofReal_ne_neg_natCast ha)
    (x : ℂ)).mul_left (Gamma (a : ℂ))
  have hΓ : Gamma (a : ℂ) ≠ 0 := Gamma_ne_zero (ofReal_ne_neg_natCast ha)
  have hC' : HasSum (fun k : ℕ => (-(x : ℂ)) ^ k / ((k ! : ℂ) * ((a : ℂ) + k)))
      (Gamma (a : ℂ) * tricomiIncompleteGamma a x) := by
    refine hC.congr_fun fun k => ?_
    rw [← mul_assoc, mul_inv_cancel₀ hΓ, one_mul]
  have hre := hasSum_re hC'
  have hval : (Gamma (a : ℂ) * tricomiIncompleteGamma a x).re =
      Real.Gamma a * (tricomiIncompleteGamma a x).re := by
    simp [Gamma_ofReal]
  rw [hval] at hre
  refine hre.congr_fun fun k => ?_
  have hcast : (-(x : ℂ)) ^ k / ((k ! : ℂ) * ((a : ℂ) + k)) =
      (((-x) ^ k / ((k ! : ℝ) * (a + k)) : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, ofReal_re]

private theorem strictAntiOn_tsum_of_neg {x : ℝ} (hx : x < 0) (m : ℕ) :
    StrictAntiOn (fun a : ℝ => ∑' k : ℕ, (-x) ^ k / (k ! * (a + k)))
      (Ioo (-((m : ℝ) + 1)) (-(m : ℝ))) := by
  intro a ha b hb hab
  have hsumA := (hasSum_Gamma_mul_tricomi_re (ne_neg_natCast_of_mem_Ioo ha) x).summable
  have hsumB := (hasSum_Gamma_mul_tricomi_re (ne_neg_natCast_of_mem_Ioo hb) x).summable
  have hpos : 0 < -x := by linarith
  have hinv_lt : ∀ k : ℕ, (b + k)⁻¹ < (a + k)⁻¹ := fun k => by
    rcases le_or_gt k m with hle | hlt
    · have hle' : (k : ℝ) ≤ m := by exact_mod_cast hle
      have hneg := inv_strictAnti₀ (by linarith [hb.2] : 0 < -(b + k))
        (by linarith : -(b + k) < -(a + k))
      simp only [inv_neg] at hneg
      linarith
    · have hge : (m : ℝ) + 1 ≤ k := by exact_mod_cast hlt
      exact inv_strictAnti₀ (by linarith [ha.1]) (by linarith)
  refine hsumB.tsum_lt_tsum (i := 0) (fun k => ?_) ?_ hsumA
  · have hfac : (0 : ℝ) ≤ (-x) ^ k / (k ! : ℝ) := by positivity
    rw [div_mul_eq_div_div, div_mul_eq_div_div, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (hinv_lt k).le hfac
  · simpa only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero, add_zero,
      one_div] using hinv_lt 0

private theorem neg_series_term_bound {x : ℝ} (hx : x < 0) {m : ℕ} {a : ℝ}
    (ha : a ∈ Ioo (-((m : ℝ) + 1)) (-(m : ℝ))) :
    let δ : ℝ := min (a - (-((m : ℝ) + 1))) (-(m : ℝ) - a) / 2
    0 < δ ∧ ∀ b ∈ Metric.ball a δ, ∀ k : ℕ,
      δ ≤ |b + k| ∧ (-x) ^ k / (k ! * (b + k) ^ 2) ≤ (-x) ^ k / (k ! : ℝ) * (δ ^ 2)⁻¹ := by
  set δ : ℝ := min (a - (-((m : ℝ) + 1))) (-(m : ℝ) - a) / 2
  have h1 : δ ≤ (a - (-((m : ℝ) + 1))) / 2 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have h2 : δ ≤ (-(m : ℝ) - a) / 2 :=
    div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hδ : 0 < δ := by
    have ha1 : 0 < a - (-((m : ℝ) + 1)) := by linarith [ha.1]
    have ha2 : 0 < -(m : ℝ) - a := by linarith [ha.2]
    positivity
  refine ⟨hδ, fun b hb k => ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hb
  have hgap : δ ≤ |b + k| := by
    rcases le_or_gt k m with hle | hlt
    · have hle' : (k : ℝ) ≤ m := by exact_mod_cast hle
      have hneg : b + k ≤ -δ := by linarith
      rw [abs_of_nonpos (by linarith [hneg])]
      linarith
    · have hge : (m : ℝ) + 1 ≤ k := by exact_mod_cast hlt
      have hpos : δ ≤ b + k := by linarith
      rw [abs_of_nonneg (by linarith [hpos])]
      exact hpos
  have hsq : δ ^ 2 ≤ (b + k) ^ 2 := by
    rw [← sq_abs (b + k)]
    exact pow_le_pow_left₀ hδ.le hgap 2
  have hxpos : 0 < -x := by linarith
  refine ⟨hgap, ?_⟩
  rw [div_mul_eq_div_div, div_eq_mul_inv]
  gcongr

private theorem hasDerivAt_tsum_of_neg {x : ℝ} (hx : x < 0) {m : ℕ} {a : ℝ}
    (ha : a ∈ Ioo (-((m : ℝ) + 1)) (-(m : ℝ))) :
    HasDerivAt (fun b : ℝ => ∑' k : ℕ, (-x) ^ k / (k ! * (b + k)))
      (∑' k : ℕ, -((-x) ^ k / (k ! * (a + k) ^ 2))) a := by
  set δ : ℝ := min (a - (-((m : ℝ) + 1))) (-(m : ℝ) - a) / 2
  obtain ⟨hδ, hbound⟩ := neg_series_term_bound hx ha
  have hu : Summable fun k : ℕ => (-x) ^ k / (k ! : ℝ) * (δ ^ 2)⁻¹ :=
    (Real.summable_pow_div_factorial (-x)).mul_right _
  have hxpos : 0 < -x := by linarith
  have hne := ne_neg_natCast_of_mem_Ioo ha
  refine hasDerivAt_tsum_of_isPreconnected (g := fun k b => (-x) ^ k / (k ! * (b + k)))
    (g' := fun k b => -((-x) ^ k / (k ! * (b + k) ^ 2))) hu Metric.isOpen_ball
    (convex_ball a δ).isPreconnected (fun k b hb => ?_) (fun k b hb => ?_)
    (Metric.mem_ball_self hδ) (hasSum_Gamma_mul_tricomi_re hne x).summable (Metric.mem_ball_self hδ)
  · have hbk : b + k ≠ 0 := fun h0 => by
      have := (hbound b hb k).1; rw [h0, abs_zero] at this; linarith
    have hd := (((hasDerivAt_id' b).add_const (k : ℝ)).inv hbk).const_mul ((-x) ^ k / (k ! : ℝ))
    convert hd using 1
    · ext y; rw [div_mul_eq_div_div, div_eq_mul_inv]; rfl
    · rw [div_mul_eq_div_div, div_eq_mul_inv]; ring
  · rw [Real.norm_eq_abs, abs_neg, abs_div, abs_of_nonneg (pow_nonneg hxpos.le k),
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))]
    exact (hbound b hb k).2

/-- For `x < 0` and every `m : ℕ`, Tricomi's function `a ↦ γ*(a, x)` has a unique real zero in the
open unit interval `(-(m + 1), -m)`. -/
theorem existsUnique_tricomiIncompleteGamma_eq_zero_of_neg {x : ℝ} (hx : x < 0) (m : ℕ) :
    ∃! a : ℝ, a ∈ Ioo (-((m : ℝ) + 1)) (-(m : ℝ)) ∧ tricomiIncompleteGamma a x = 0 := by
  set g : ℝ → ℝ := fun a => (tricomiIncompleteGamma a x).re
  set L : ℝ := -((m : ℝ) + 1)
  set R : ℝ := -(m : ℝ)
  have hLR : L ≤ R := by linarith
  have hcont : ContinuousOn g (Icc L R) :=
    (differentiable_tricomiIncompleteGamma_re x).continuous.continuousOn
  have hgR : g R = x ^ m := by
    have hRcast : (R : ℂ) = -(m : ℂ) := by simp [R]
    simp only [g, hRcast, tricomiIncompleteGamma_neg_natCast, ← ofReal_pow, ofReal_re]
  have hgL : g L = x ^ (m + 1) := by
    have hLcast : (L : ℂ) = -((m + 1 : ℕ) : ℂ) := by simp [L]
    simp only [g, hLcast, tricomiIncompleteGamma_neg_natCast, ← ofReal_pow, ofReal_re]
  have hprod : g L * g R < 0 := by
    rw [hgL, hgR, pow_succ]
    have hsq : 0 < (x ^ m) ^ 2 := sq_pos_of_ne_zero (pow_ne_zero m hx.ne)
    nlinarith
  have hex : ∃ a ∈ Ioo L R, g a = 0 := by
    have hLne : g L ≠ 0 := fun h => by rw [h, zero_mul] at hprod; linarith
    rcases lt_or_gt_of_ne hLne with hLneg | hLpos
    · exact intermediate_value_Ioo hLR hcont ⟨hLneg, by nlinarith⟩
    · exact intermediate_value_Ioo' hLR hcont ⟨by nlinarith, hLpos⟩
  obtain ⟨a₀, ha₀, hga₀⟩ := hex
  refine ⟨a₀, ⟨ha₀, (tricomiIncompleteGamma_ofReal_eq_zero_iff a₀ x).mpr hga₀⟩, ?_⟩
  rintro a ⟨ha, hza⟩
  have hga : g a = 0 := (tricomiIncompleteGamma_ofReal_eq_zero_iff a x).mp hza
  have hF : ∀ b ∈ Ioo L R, (∑' k : ℕ, (-x) ^ k / (k ! * (b + k))) = Real.Gamma b * g b :=
    fun b hb => (hasSum_Gamma_mul_tricomi_re (ne_neg_natCast_of_mem_Ioo hb) x).tsum_eq
  have heq : (∑' k : ℕ, (-x) ^ k / (k ! * (a + k))) =
      ∑' k : ℕ, (-x) ^ k / (k ! * (a₀ + k)) := by
    rw [hF a ha, hF a₀ ha₀, hga, hga₀, mul_zero, mul_zero]
  exact (strictAntiOn_tsum_of_neg hx m).injOn ha ha₀ heq

/-- For `x < 0`, every real zero of `a ↦ γ*(a, x)` in `(-(m + 1), -m)` is simple. -/
theorem deriv_tricomiIncompleteGamma_re_ne_zero_of_neg {x : ℝ} (hx : x < 0) {m : ℕ} {a : ℝ}
    (ha : a ∈ Ioo (-((m : ℝ) + 1)) (-(m : ℝ))) (hzero : tricomiIncompleteGamma a x = 0) :
    deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a ≠ 0 := by
  set F : ℝ → ℝ := fun b => ∑' k : ℕ, (-x) ^ k / (k ! * (b + k))
  set g : ℝ → ℝ := fun b => (tricomiIncompleteGamma b x).re
  have hga : g a = 0 := (tricomiIncompleteGamma_ofReal_eq_zero_iff a x).mp hzero
  have hF_eq : F =ᶠ[𝓝 a] fun b => Real.Gamma b * g b := by
    filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
    exact (hasSum_Gamma_mul_tricomi_re (ne_neg_natCast_of_mem_Ioo hb) x).tsum_eq
  have hprod_deriv : HasDerivAt (fun b => Real.Gamma b * g b) (Real.Gamma a * deriv g a) a := by
    have h : HasDerivAt (fun b => Real.Gamma b * g b)
        (deriv Real.Gamma a * g a + Real.Gamma a * deriv g a) a :=
      (Real.differentiableAt_Gamma (ne_neg_natCast_of_mem_Ioo ha)).hasDerivAt.mul
        (differentiable_tricomiIncompleteGamma_re x a).hasDerivAt
    rwa [hga, mul_zero, zero_add] at h
  have heq : Real.Gamma a * deriv g a = ∑' k : ℕ, -((-x) ^ k / (k ! * (a + k) ^ 2)) :=
    (hprod_deriv.congr_of_eventuallyEq hF_eq).unique (hasDerivAt_tsum_of_neg hx ha)
  have hxpos : 0 < -x := by linarith
  obtain ⟨hδ, hbound⟩ := neg_series_term_bound hx ha
  have hsum : Summable fun k : ℕ => (-x) ^ k / (k ! * (a + k) ^ 2) :=
    Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => (hbound a (Metric.mem_ball_self hδ) k).2)
      ((Real.summable_pow_div_factorial (-x)).mul_right _)
  have h0 : 0 < (-x) ^ 0 / ((0 : ℕ)! * (a + (0 : ℕ)) ^ 2) := by
    have ha0 : a ≠ 0 := by simpa using ne_neg_natCast_of_mem_Ioo ha 0
    simpa using inv_pos.mpr (sq_pos_of_ne_zero ha0)
  have hpos_sum : 0 < ∑' k : ℕ, (-x) ^ k / (k ! * (a + k) ^ 2) :=
    lt_of_lt_of_le h0 (hsum.le_tsum 0 fun k _ => by positivity)
  rw [tsum_neg] at heq
  intro hd0
  rw [hd0, mul_zero] at heq
  linarith

/-- **DLMF §8.13(iii)(a)**: for `x < 0` and `n ≥ 1`, `a ↦ γ*(a, x)` has exactly two zeros in
`-2n < a < 2 - 2n`, and both are simple. -/
theorem tricomiIncompleteGamma_param_zeros_of_neg {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x < 0) :
    ∃ a₁ a₂ : ℝ, a₁ < a₂ ∧
      Set.ofPred (fun a : ℝ => a ∈ Ioo (-2 * (n : ℝ)) (2 - 2 * (n : ℝ)) ∧
        tricomiIncompleteGamma a x = 0) = {a₁, a₂} ∧
      deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₁ ≠ 0 ∧
      deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₂ ≠ 0 := by
  obtain ⟨a₁, ⟨ha₁, hz₁⟩, huniq₁⟩ :=
    existsUnique_tricomiIncompleteGamma_eq_zero_of_neg hx (2 * n - 1)
  obtain ⟨a₂, ⟨ha₂, hz₂⟩, huniq₂⟩ :=
    existsUnique_tricomiIncompleteGamma_eq_zero_of_neg hx (2 * n - 2)
  have hcast1 : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hcast2 : ((2 * n - 2 : ℕ) : ℝ) = 2 * (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have ha₁' : a₁ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) := by
    rw [hcast1] at ha₁; exact ⟨by linarith [ha₁.1], by linarith [ha₁.2]⟩
  have ha₂' : a₂ ∈ Ioo (1 - 2 * (n : ℝ)) (2 - 2 * (n : ℝ)) := by
    rw [hcast2] at ha₂; exact ⟨by linarith [ha₂.1], by linarith [ha₂.2]⟩
  refine ⟨a₁, a₂, ha₁'.2.trans ha₂'.1, ?_,
    deriv_tricomiIncompleteGamma_re_ne_zero_of_neg hx ha₁ hz₁,
    deriv_tricomiIncompleteGamma_re_ne_zero_of_neg hx ha₂ hz₂⟩
  ext a
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hza⟩
    rcases lt_trichotomy a (1 - 2 * (n : ℝ)) with hlt | heq | hgt
    · exact Or.inl (huniq₁ a ⟨by rw [hcast1]; exact ⟨by linarith, by linarith⟩, hza⟩)
    · exfalso
      have hcast : (a : ℂ) = -((2 * n - 1 : ℕ) : ℂ) := by
        have : a = -((2 * n - 1 : ℕ) : ℝ) := by linarith
        rw [this]; push_cast; rfl
      rw [hcast, tricomiIncompleteGamma_neg_natCast] at hza
      exact pow_ne_zero _ (ofReal_ne_zero.mpr hx.ne) hza
    · exact Or.inr (huniq₂ a ⟨by rw [hcast2]; exact ⟨by linarith, by linarith⟩, hza⟩)
  · rintro (rfl | rfl)
    · exact ⟨⟨ha₁'.1, by linarith [ha₁'.2]⟩, hz₁⟩
    · exact ⟨⟨by linarith [ha₂'.1], ha₂'.2⟩, hz₂⟩

/-! ### The real upper incomplete Gamma tail integral and its logarithmic moments -/

/-- The `k`-th logarithmic moment of the real upper incomplete Gamma tail integral,
`U_k(a, x) = ∫ t in Ioi x, (log t)^k t^(a - 1) e^(-t)`. -/
private def upperGammaMoment (k : ℕ) (a x : ℝ) : ℝ :=
  ∫ t in Ioi x, (Real.log t) ^ k * t ^ (a - 1) * Real.exp (-t)

private theorem integrableOn_pow_mul_exp_neg_mul_Ioi (k : ℕ) {α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun s : ℝ => s ^ k * Real.exp (-α * s)) (Ioi (0 : ℝ)) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k : ℝ)) (b := α)
    (by linarith [Nat.cast_nonneg (α := ℝ) k]) one_pos hα
  refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp [Real.rpow_natCast, Real.rpow_one]

private theorem exists_upperGammaMoment_bound (k : ℕ) (A B : ℝ) {x : ℝ} (hx : 0 < x) :
    ∃ bound : ℝ → ℝ, IntegrableOn bound (Ioi x) ∧
      ∀ a ∈ Icc A B, ∀ t ∈ Ioi x,
        ‖(Real.log t) ^ k * t ^ (a - 1) * Real.exp (-t)‖ ≤ bound t := by
  set C : ℝ := |Real.log x| ^ k * max (x ^ (A - 1)) 1
  set M : ℝ := max (B - 1) 0 + (k : ℝ)
  have hM0 : 0 ≤ M := add_nonneg (le_max_right _ _) (Nat.cast_nonneg k)
  have hG : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ M) (Ioi x) := by
    simpa only [add_sub_cancel_right] using
      (Real.GammaIntegral_convergent (s := M + 1) (by linarith)).mono_set (Ioi_subset_Ioi hx.le)
  refine ⟨fun t => C * Real.exp (-t) + Real.exp (-t) * t ^ M,
    ((integrableOn_exp_neg_Ioi x).const_mul C).add hG, fun a ha t ht => ?_⟩
  have ht0 : 0 < t := hx.trans ht
  have hC0 : 0 ≤ C :=
    mul_nonneg (pow_nonneg (abs_nonneg _) _) (le_max_of_le_right zero_le_one)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
    abs_of_pos (Real.rpow_pos_of_pos ht0 _), abs_of_pos (Real.exp_pos _)]
  rcases le_total t 1 with h1 | h1
  · have hlog : |Real.log t| ≤ |Real.log x| := by
      have hlt : Real.log t ≤ 0 := Real.log_nonpos ht0.le h1
      have hlx : Real.log x ≤ Real.log t := Real.log_le_log hx ht.le
      rw [abs_of_nonpos hlt, abs_of_nonpos (hlx.trans hlt)]; linarith
    have hrpow : t ^ (a - 1) ≤ max (x ^ (A - 1)) 1 := by
      rcases le_total (a - 1) 0 with ha0 | ha0
      · exact ((Real.rpow_le_rpow_of_nonpos hx ht.le ha0).trans
          (Real.rpow_le_rpow_of_exponent_ge hx (ht.le.trans h1) (by linarith [ha.1]))).trans
          (le_max_left _ _)
      · exact (Real.rpow_le_one ht0.le h1 ha0).trans (le_max_right _ _)
    have hprod : |Real.log t| ^ k * t ^ (a - 1) ≤ C :=
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hlog k) hrpow
        (Real.rpow_pos_of_pos ht0 _).le (pow_nonneg (abs_nonneg _) _)
    linarith [mul_le_mul_of_nonneg_right hprod (Real.exp_pos (-t)).le,
      mul_nonneg (Real.exp_pos (-t)).le (Real.rpow_pos_of_pos ht0 M).le]
  · have hlog : |Real.log t| ^ k ≤ t ^ (k : ℝ) := by
      rw [Real.rpow_natCast, abs_of_nonneg (Real.log_nonneg h1)]
      exact pow_le_pow_left₀ (Real.log_nonneg h1) (by linarith [Real.log_le_sub_one_of_pos ht0]) k
    have hrpow : t ^ (a - 1) ≤ t ^ max (B - 1) 0 :=
      Real.rpow_le_rpow_of_exponent_le h1 (by linarith [ha.2, le_max_left (B - 1) 0])
    have hprod : |Real.log t| ^ k * t ^ (a - 1) ≤ t ^ M := by
      calc |Real.log t| ^ k * t ^ (a - 1)
          ≤ t ^ (k : ℝ) * t ^ max (B - 1) 0 :=
            mul_le_mul hlog hrpow (Real.rpow_pos_of_pos ht0 _).le (Real.rpow_pos_of_pos ht0 _).le
        _ = t ^ M := by rw [← Real.rpow_add ht0, add_comm]
    dsimp only
    rw [mul_comm (Real.exp (-t)) (t ^ M)]
    linarith [mul_le_mul_of_nonneg_right hprod (Real.exp_pos (-t)).le,
      mul_nonneg hC0 (Real.exp_pos (-t)).le]

private theorem continuousOn_upperGammaIntegrand (k : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    ContinuousOn (fun t : ℝ => (Real.log t) ^ k * t ^ (a - 1) * Real.exp (-t)) (Ioi x) := by
  intro t ht
  have ht0 : t ≠ 0 := (hx.trans ht).ne'
  refine ((((Real.continuousAt_log ht0).pow k).mul
    (Real.continuousAt_rpow_const t (a - 1) (Or.inl ht0))).mul
    (Real.continuous_exp.continuousAt.comp continuousAt_neg)).continuousWithinAt

private theorem integrableOn_upperGammaMoment (k : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => (Real.log t) ^ k * t ^ (a - 1) * Real.exp (-t)) (Ioi x) := by
  obtain ⟨bound, hbound_int, hbound⟩ := exists_upperGammaMoment_bound k a a hx
  refine hbound_int.mono'
    ((continuousOn_upperGammaIntegrand k a hx).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact hbound a ⟨le_rfl, le_rfl⟩ t ht

private theorem hasDerivAt_upperGammaMoment (k : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun b : ℝ => upperGammaMoment k b x) (upperGammaMoment (k + 1) a x) a := by
  obtain ⟨bound, hbound_int, hbound⟩ := exists_upperGammaMoment_bound (k + 1) (a - 1) (a + 1) hx
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun b t => (Real.log t) ^ k * t ^ (b - 1) * Real.exp (-t))
    (F' := fun b t => (Real.log t) ^ (k + 1) * t ^ (b - 1) * Real.exp (-t))
    (bound := bound)
    (Icc_mem_nhds (by linarith : a - 1 < a) (by linarith : a < a + 1))
    (Eventually.of_forall fun b =>
      (continuousOn_upperGammaIntegrand k b hx).aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_upperGammaMoment k a hx)
    ((continuousOn_upperGammaIntegrand (k + 1) a hx).aestronglyMeasurable measurableSet_Ioi)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht b hb
      exact hbound b hb t ht)
    hbound_int
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht b _
      have hr : HasDerivAt (fun c : ℝ => t ^ (c - 1)) (Real.log t * t ^ (b - 1)) b := by
        simpa only [mul_one] using ((hasDerivAt_id' b).sub_const 1).const_rpow (hx.trans ht)
      have hd := (hr.const_mul ((Real.log t) ^ k)).mul_const (Real.exp (-t))
      convert hd using 1
      rw [pow_succ]; ring)
  exact hmain.2

private theorem mul_le_integral_Ioc_upperGamma {a x₁ x₂ m : ℝ} (hx₁ : 0 < x₁) (h12 : x₁ ≤ x₂)
    (hm : ∀ t ∈ Ioc x₁ x₂, m ≤ t ^ (a - 1) * Real.exp (-t)) :
    (x₂ - x₁) * m ≤ ∫ t in Ioc x₁ x₂, t ^ (a - 1) * Real.exp (-t) := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-t)) (Ioc x₁ x₂) := by
    simpa only [pow_zero, one_mul] using
      (integrableOn_upperGammaMoment 0 a hx₁).mono_set Ioc_subset_Ioi_self
  have hle := setIntegral_mono_on (integrableOn_const (hs := measure_Ioc_lt_top.ne)) hint
    measurableSet_Ioc hm
  rw [setIntegral_const, Measure.real_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul] at hle
  exact hle

private theorem integral_Ioc_upperGamma_le_mul {a x₁ x₂ M : ℝ} (hx₁ : 0 < x₁) (h12 : x₁ ≤ x₂)
    (hM : ∀ t ∈ Ioc x₁ x₂, t ^ (a - 1) * Real.exp (-t) ≤ M) :
    ∫ t in Ioc x₁ x₂, t ^ (a - 1) * Real.exp (-t) ≤ (x₂ - x₁) * M := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-t)) (Ioc x₁ x₂) := by
    simpa only [pow_zero, one_mul] using
      (integrableOn_upperGammaMoment 0 a hx₁).mono_set Ioc_subset_Ioi_self
  have hle := setIntegral_mono_on hint (integrableOn_const (hs := measure_Ioc_lt_top.ne))
    measurableSet_Ioc hM
  rw [setIntegral_const, Measure.real_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul] at hle
  exact hle

private theorem integral_Ioc_le_upperGammaMoment_zero (a : ℝ) {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) :
    ∫ t in Ioc x₁ x₂, t ^ (a - 1) * Real.exp (-t) ≤ upperGammaMoment 0 a x₁ := by
  have h := setIntegral_mono_set (integrableOn_upperGammaMoment 0 a hx₁)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [pow_zero, one_mul]
      exact mul_nonneg (Real.rpow_pos_of_pos (hx₁.trans ht) _).le (Real.exp_pos _).le)
    (Eventually.of_forall (Ioc_subset_Ioi_self : Ioc x₁ x₂ ⊆ Ioi x₁))
  simpa only [pow_zero, one_mul, upperGammaMoment] using h

private theorem integral_Ioc_upperGamma_pos (a : ℝ) {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (h12 : x₁ < x₂) :
    0 < ∫ t in Ioc x₁ x₂, t ^ (a - 1) * Real.exp (-t) := by
  set m : ℝ := min (x₁ ^ (a - 1)) (x₂ ^ (a - 1)) * Real.exp (-x₂)
  have hm_pos : 0 < m :=
    mul_pos (lt_min (Real.rpow_pos_of_pos hx₁ _) (Real.rpow_pos_of_pos (hx₁.trans h12) _))
      (Real.exp_pos _)
  have hle : (x₂ - x₁) * m ≤ ∫ t in Ioc x₁ x₂, t ^ (a - 1) * Real.exp (-t) := by
    refine mul_le_integral_Ioc_upperGamma hx₁ h12.le fun t ht => ?_
    have hbase : min (x₁ ^ (a - 1)) (x₂ ^ (a - 1)) ≤ t ^ (a - 1) := by
      rcases le_total 0 (a - 1) with ha0 | ha0
      · exact (min_le_left _ _).trans (Real.rpow_le_rpow hx₁.le ht.1.le ha0)
      · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos (hx₁.trans ht.1) ht.2 ha0)
    exact mul_le_mul hbase (Real.exp_le_exp.mpr (by linarith [ht.2])) (Real.exp_pos _).le
      (Real.rpow_pos_of_pos (hx₁.trans ht.1) _).le
  exact lt_of_lt_of_le (mul_pos (by linarith) hm_pos) hle

private theorem upperGammaMoment_zero_pos (a : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < upperGammaMoment 0 a x :=
  (integral_Ioc_upperGamma_pos a hx (by linarith : x < x + 1)).trans_le
    (integral_Ioc_le_upperGammaMoment_zero a hx)

private theorem upperGammaMoment_zero_split (a : ℝ) {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (h12 : x₁ < x₂) :
    upperGammaMoment 0 a x₁ =
      (∫ t in Ioc x₁ x₂, t ^ (a - 1) * Real.exp (-t)) + upperGammaMoment 0 a x₂ := by
  have hint := integrableOn_upperGammaMoment 0 a hx₁
  have hunion : Ioc x₁ x₂ ∪ Ioi x₂ = Ioi x₁ := Ioc_union_Ioi_eq_Ioi h12.le
  rw [upperGammaMoment, ← hunion,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi h12.le))]
  simp only [pow_zero, one_mul, upperGammaMoment]

private theorem upperGammaMoment_zero_strictAntiOn (a : ℝ) :
    StrictAntiOn (fun x : ℝ => upperGammaMoment 0 a x) (Ioi 0) := fun _ hx₁ _ _ h12 => by
  dsimp only
  rw [upperGammaMoment_zero_split a hx₁ h12]
  linarith [integral_Ioc_upperGamma_pos a hx₁ h12]

private theorem upperGammaMoment_zero_add_one (a : ℝ) {x : ℝ} (hx : 0 < x) :
    upperGammaMoment 0 (a + 1) x = a * upperGammaMoment 0 a x + x ^ a * Real.exp (-x) := by
  have hu : ∀ t ∈ Ioi x, HasDerivAt (fun s : ℝ => s ^ a) (a * t ^ (a - 1)) t := fun t ht => by
    simpa only [one_mul] using (hasDerivAt_id' t).rpow_const (p := a) (Or.inl (hx.trans ht).ne')
  have hv : ∀ t ∈ Ioi x, HasDerivAt (fun s : ℝ => -Real.exp (-s)) (Real.exp (-t)) t := fun t _ => by
    convert ((hasDerivAt_neg t).exp).neg using 1
    ring
  have huv' : IntegrableOn ((fun s : ℝ => s ^ a) * fun s : ℝ => Real.exp (-s)) (Ioi x) := by
    simpa only [Pi.mul_def, pow_zero, one_mul, add_sub_cancel_right] using
      integrableOn_upperGammaMoment 0 (a + 1) hx
  have hu'v : IntegrableOn ((fun s : ℝ => a * s ^ (a - 1)) * fun s : ℝ => -Real.exp (-s))
      (Ioi x) := by
    have h := (integrableOn_upperGammaMoment 0 a hx).const_mul (-a)
    have hfun : (fun s : ℝ => -a * (Real.log s ^ 0 * s ^ (a - 1) * Real.exp (-s))) =
        (fun s : ℝ => a * s ^ (a - 1)) * fun s : ℝ => -Real.exp (-s) := by
      ext s; simp only [Pi.mul_apply, pow_zero, one_mul]; ring
    rwa [hfun] at h
  have hzero : Tendsto ((fun s : ℝ => s ^ a) * fun s : ℝ => -Real.exp (-s))
      (𝓝[>] x) (𝓝 (-(x ^ a * Real.exp (-x)))) := by
    have hcont : ContinuousAt (fun s : ℝ => s ^ a * -Real.exp (-s)) x :=
      (Real.continuousAt_rpow_const x a (Or.inl hx.ne')).mul
        (Real.continuous_exp.continuousAt.comp continuousAt_neg).neg
    simpa only [Pi.mul_def, mul_neg] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hinfty : Tendsto ((fun s : ℝ => s ^ a) * fun s : ℝ => -Real.exp (-s))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a 1 one_pos).neg
    simpa only [Pi.mul_def, neg_one_mul, neg_zero, mul_neg] using h
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v hzero hinfty
  have hL : ∫ t in Ioi x, t ^ a * Real.exp (-t) = upperGammaMoment 0 (a + 1) x := by
    simp only [upperGammaMoment, pow_zero, one_mul, add_sub_cancel_right]
  have hR : ∫ t in Ioi x, a * t ^ (a - 1) * -Real.exp (-t) = -(a * upperGammaMoment 0 a x) := by
    have : (fun t : ℝ => a * t ^ (a - 1) * -Real.exp (-t)) =
        fun t => (-a) * ((Real.log t) ^ 0 * t ^ (a - 1) * Real.exp (-t)) := by
      ext t; simp only [pow_zero, one_mul]; ring
    rw [this, integral_const_mul, upperGammaMoment]
    ring
  rw [hL, hR] at hibp
  linarith

private theorem integral_Ioc_rpow_mul_exp_eq (a : ℝ) {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioc 0 x, t ^ (a - 1) * Real.exp (-t) =
      x ^ a * ∫ s in (0 : ℝ)..1, s ^ (a - 1) * Real.exp (-(x * s)) := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  have himg : (fun s : ℝ => x * s) '' Ioc 0 1 = Ioc 0 x := by
    ext t
    simp only [mem_image, mem_Ioc]
    constructor
    · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩; exact ⟨mul_pos hx hs0, by nlinarith⟩
    · rintro ⟨ht0, htx⟩
      exact ⟨t / x, ⟨div_pos ht0 hx, (div_le_one hx).mpr htx⟩, mul_div_cancel₀ t hx.ne'⟩
  have hxa : x * x ^ (a - 1) = x ^ a := by
    have := Real.rpow_add hx 1 (a - 1)
    rw [Real.rpow_one, add_sub_cancel] at this
    exact this.symm
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
    (fun s _ => ((hasDerivAt_id' s).const_mul x).hasDerivWithinAt)
    (fun s₁ _ s₂ _ h => mul_left_cancel₀ hx.ne' h), ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  simp only [smul_eq_mul, mul_one, abs_of_pos hx]
  rw [Real.mul_rpow hx.le hs.1.le, ← mul_assoc, ← mul_assoc, hxa, mul_assoc]

private theorem Gamma_mul_one_sub_rpow_mul_tricomi_re_of_pos {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    Real.Gamma a * (1 - x ^ a * (tricomiIncompleteGamma a x).re) = upperGammaMoment 0 a x := by
  have hΓ_int : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (a - 1)) (Ioi (0 : ℝ)) :=
    Real.GammaIntegral_convergent ha
  have hunion : Ioc 0 x ∪ Ioi x = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi hx.le
  have hsplit : Real.Gamma a = (∫ t in Ioc 0 x, t ^ (a - 1) * Real.exp (-t)) +
      upperGammaMoment 0 a x := by
    rw [Real.Gamma_eq_integral ha, ← hunion,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hΓ_int.mono_set Ioc_subset_Ioi_self) (hΓ_int.mono_set (Ioi_subset_Ioi hx.le))]
    congr 1
    · refine setIntegral_congr_fun measurableSet_Ioc fun t _ => mul_comm _ _
    · simp only [upperGammaMoment, pow_zero, one_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => mul_comm _ _
  have hT := tricomiIncompleteGamma_eq_integral (a := (a : ℂ)) (by simpa using ha) (x : ℂ)
  have hΓne : Gamma (a : ℂ) ≠ 0 := by
    rw [Gamma_ofReal]; exact ofReal_ne_zero.mpr (Real.Gamma_pos_of_pos ha).ne'
  have hmul : Gamma (a : ℂ) * tricomiIncompleteGamma a x =
      ((∫ s in (0 : ℝ)..1, s ^ (a - 1) * Real.exp (-(x * s)) : ℝ) : ℂ) := by
    rw [hT, ← mul_assoc, mul_inv_cancel₀ hΓne, one_mul, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le zero_le_one] at hs
    rw [ofReal_mul, ofReal_cpow hs.1, ofReal_exp]
    push_cast; rfl
  have hre_int : Real.Gamma a * (tricomiIncompleteGamma a x).re =
      ∫ s in (0 : ℝ)..1, s ^ (a - 1) * Real.exp (-(x * s)) := by
    simpa [Gamma_ofReal] using congrArg Complex.re hmul
  have hlow : Real.Gamma a * (x ^ a * (tricomiIncompleteGamma a x).re) =
      ∫ t in Ioc 0 x, t ^ (a - 1) * Real.exp (-t) := by
    rw [integral_Ioc_rpow_mul_exp_eq a hx, ← hre_int]; ring
  linarith

private theorem Gamma_mul_one_sub_rpow_mul_tricomi_re {a : ℝ} (ha : ∀ m : ℕ, a ≠ -(m : ℝ))
    {x : ℝ} (hx : 0 < x) :
    Real.Gamma a * (1 - x ^ a * (tricomiIncompleteGamma a x).re) = upperGammaMoment 0 a x := by
  suffices h : ∀ N : ℕ, ∀ a : ℝ, (∀ m : ℕ, a ≠ -(m : ℝ)) → 0 < a + N →
      Real.Gamma a * (1 - x ^ a * (tricomiIncompleteGamma a x).re) = upperGammaMoment 0 a x by
    obtain ⟨N, hN⟩ := exists_nat_gt (-a)
    exact h N a ha (by linarith)
  intro N
  induction N with
  | zero =>
    intro a _ ha_pos
    exact Gamma_mul_one_sub_rpow_mul_tricomi_re_of_pos (by simpa using ha_pos) hx
  | succ N ih =>
    intro a ha ha_pos
    have ha0 : a ≠ 0 := by simpa using ha 0
    have ha1 : ∀ m : ℕ, a + 1 ≠ -(m : ℝ) := fun m hm => ha (m + 1) (by push_cast; linarith)
    have hstep := ih (a + 1) ha1 (by push_cast at ha_pos; linarith)
    have hrec_T := congrArg Complex.re
      (tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one (a : ℂ) (x : ℂ))
    have hcast1 : ((a : ℂ) + 1) = ((a + 1 : ℝ) : ℂ) := by push_cast; rfl
    have hT_re : (tricomiIncompleteGamma a x).re =
        x * (tricomiIncompleteGamma (a + 1 : ℝ) x).re + Real.exp (-x) / Real.Gamma (a + 1) := by
      have hcast2 : cexp (-(x : ℂ)) / Gamma ((a : ℂ) + 1) =
          ((Real.exp (-x) / Real.Gamma (a + 1) : ℝ) : ℂ) := by
        rw [hcast1, Gamma_ofReal, ← ofReal_neg, ← ofReal_exp, ← ofReal_div]
      rw [add_re, hcast2, ofReal_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
        hcast1] at hrec_T
      exact hrec_T
    have hΓ1 : Real.Gamma (a + 1) = a * Real.Gamma a := Real.Gamma_add_one ha0
    have hΓ1_ne : Real.Gamma (a + 1) ≠ 0 := Real.Gamma_ne_zero ha1
    have hmul : a * (Real.Gamma a * (1 - x ^ a * (tricomiIncompleteGamma a x).re)) =
        a * upperGammaMoment 0 a x := by
      have h1 : Real.Gamma (a + 1) *
          (1 - x ^ (a + 1) * (tricomiIncompleteGamma (a + 1 : ℝ) x).re) =
          a * upperGammaMoment 0 a x + x ^ a * Real.exp (-x) := by
        rw [hstep, upperGammaMoment_zero_add_one a hx]
      have hcancel : Real.Gamma (a + 1) * (Real.exp (-x) / Real.Gamma (a + 1)) = Real.exp (-x) :=
        mul_div_cancel₀ _ hΓ1_ne
      calc a * (Real.Gamma a * (1 - x ^ a * (tricomiIncompleteGamma a x).re))
          = Real.Gamma (a + 1) * (1 - x ^ a * (tricomiIncompleteGamma a x).re) := by
              rw [hΓ1]; ring
        _ = Real.Gamma (a + 1) * (1 - x ^ (a + 1) * (tricomiIncompleteGamma (a + 1 : ℝ) x).re) -
              x ^ a * (Real.Gamma (a + 1) * (Real.exp (-x) / Real.Gamma (a + 1))) := by
              rw [hT_re, Real.rpow_add_one hx.ne' a]; ring
        _ = a * upperGammaMoment 0 a x := by rw [h1, hcancel]; ring
    exact mul_left_cancel₀ ha0 hmul

private theorem upperGammaMoment_eq_expSubst (k : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    upperGammaMoment k a x =
      x ^ a * ∫ s in Ioi (0 : ℝ), (Real.log x + s) ^ k * Real.exp (a * s - x * Real.exp s) := by
  have himg : (fun s : ℝ => x * Real.exp s) '' Ioi (0 : ℝ) = Ioi x := by
    ext t
    simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨s, hs, rfl⟩
      have : 1 < Real.exp s := Real.one_lt_exp_iff.mpr hs
      nlinarith
    · intro ht
      refine ⟨Real.log (t / x), Real.log_pos ((one_lt_div hx).mpr ht), ?_⟩
      rw [Real.exp_log (div_pos (hx.trans ht) hx), mul_div_cancel₀ t hx.ne']
  have hxa : x * x ^ (a - 1) = x ^ a := by
    have := Real.rpow_add hx 1 (a - 1)
    rw [Real.rpow_one, add_sub_cancel] at this
    exact this.symm
  rw [upperGammaMoment, ← himg,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun s _ => ((Real.hasDerivAt_exp s).const_mul x).hasDerivWithinAt)
      (fun s₁ _ s₂ _ h => Real.exp_injective (mul_left_cancel₀ hx.ne' h)),
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only [smul_eq_mul, abs_of_pos (mul_pos hx (Real.exp_pos s))]
  rw [Real.log_mul hx.ne' (Real.exp_pos s).ne', Real.log_exp,
    Real.mul_rpow hx.le (Real.exp_pos s).le, ← Real.exp_mul]
  have hexp : Real.exp s * Real.exp (s * (a - 1)) * Real.exp (-(x * Real.exp s)) =
      Real.exp (a * s - x * Real.exp s) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc x * Real.exp s * ((Real.log x + s) ^ k * (x ^ (a - 1) * Real.exp (s * (a - 1))) *
        Real.exp (-(x * Real.exp s)))
      = (x * x ^ (a - 1)) * ((Real.log x + s) ^ k *
          (Real.exp s * Real.exp (s * (a - 1)) * Real.exp (-(x * Real.exp s)))) := by ring
    _ = x ^ a * ((Real.log x + s) ^ k * Real.exp (a * s - x * Real.exp s)) := by rw [hxa, hexp]

private theorem integrableOn_pow_mul_expSubst (k : ℕ) {α x : ℝ} (hα : 0 < α) (hx : 0 < x) :
    IntegrableOn (fun s : ℝ => s ^ k * Real.exp (-α * s - x * Real.exp s)) (Ioi (0 : ℝ)) := by
  refine (integrableOn_pow_mul_exp_neg_mul_Ioi k hα).mono'
    ((Continuous.continuousOn (by fun_prop)).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hs.out.le k),
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by nlinarith [Real.exp_pos s])) (pow_nonneg hs.out.le k)

private theorem expSubst_second_moment_ptwise {α x c s : ℝ} (hx : 0 < x) (hc : 0 < c)
    (hs : 0 < s) :
    (s ^ 2 - c) * Real.exp (-α * s - x * Real.exp s) ≤
      Real.exp (-x * Real.exp (Real.sqrt c)) * ((s ^ 2 - c) * Real.exp (-α * s)) := by
  set s₀ : ℝ := Real.sqrt c
  have hs₀_sq : s₀ ^ 2 = c := Real.sq_sqrt hc.le
  have hw_eq : Real.exp (-α * s - x * Real.exp s) =
      Real.exp (-α * s) * Real.exp (-x * Real.exp s) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hw_eq]
  have hsign : (s ^ 2 - c) * (Real.exp (-x * Real.exp s) - Real.exp (-x * Real.exp s₀)) ≤ 0 := by
    rcases le_total s s₀ with hle | hle
    · have h1 : s ^ 2 - c ≤ 0 := by rw [← hs₀_sq]; nlinarith [Real.sqrt_nonneg c]
      have hle_arg : -x * Real.exp s₀ ≤ -x * Real.exp s := by
        have := Real.exp_le_exp.mpr hle; nlinarith
      have h2 : 0 ≤ Real.exp (-x * Real.exp s) - Real.exp (-x * Real.exp s₀) :=
        sub_nonneg.mpr (Real.exp_le_exp.mpr hle_arg)
      exact mul_nonpos_of_nonpos_of_nonneg h1 h2
    · have h1 : 0 ≤ s ^ 2 - c := by rw [← hs₀_sq]; nlinarith [Real.sqrt_nonneg c]
      have hle_arg : -x * Real.exp s ≤ -x * Real.exp s₀ := by
        have := Real.exp_le_exp.mpr hle; nlinarith
      have h2 : Real.exp (-x * Real.exp s) - Real.exp (-x * Real.exp s₀) ≤ 0 :=
        sub_nonpos.mpr (Real.exp_le_exp.mpr hle_arg)
      exact mul_nonpos_of_nonneg_of_nonpos h1 h2
  have hmul := mul_nonpos_of_nonpos_of_nonneg hsign (Real.exp_pos (-α * s)).le
  linarith

private theorem expSubst_second_moment_le {α x : ℝ} (hα : 0 < α) (hx : 0 < x) :
    ∫ s in Ioi (0 : ℝ), s ^ 2 * Real.exp (-α * s - x * Real.exp s) ≤
      (2 / α ^ 2) * ∫ s in Ioi (0 : ℝ), Real.exp (-α * s - x * Real.exp s) := by
  set w : ℝ → ℝ := fun s => Real.exp (-α * s - x * Real.exp s)
  set c : ℝ := 2 / α ^ 2
  set s₀ : ℝ := Real.sqrt c
  have hc_pos : 0 < c := by positivity
  have hw0 : IntegrableOn w (Ioi (0 : ℝ)) := by
    simpa only [pow_zero, one_mul] using integrableOn_pow_mul_expSubst 0 hα hx
  have hw2 : IntegrableOn (fun s : ℝ => s ^ 2 * w s) (Ioi (0 : ℝ)) :=
    integrableOn_pow_mul_expSubst 2 hα hx
  have hR0_int : IntegrableOn (fun s : ℝ => Real.exp (-α * s)) (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hR2_int : IntegrableOn (fun s : ℝ => s ^ 2 * Real.exp (-α * s)) (Ioi (0 : ℝ)) :=
    integrableOn_pow_mul_exp_neg_mul_Ioi 2 hα
  have hL_eq : (fun s : ℝ => (s ^ 2 - c) * w s) = fun s => s ^ 2 * w s - c * w s := by
    ext s; ring
  have hR_eq : (fun s : ℝ => (s ^ 2 - c) * Real.exp (-α * s)) =
      fun s => s ^ 2 * Real.exp (-α * s) - c * Real.exp (-α * s) := by
    ext s; ring
  have hL_int : IntegrableOn (fun s : ℝ => (s ^ 2 - c) * w s) (Ioi (0 : ℝ)) := by
    rw [hL_eq]; exact hw2.sub (hw0.const_mul c)
  have hR_int : IntegrableOn
      (fun s : ℝ => Real.exp (-x * Real.exp s₀) * ((s ^ 2 - c) * Real.exp (-α * s)))
      (Ioi (0 : ℝ)) := by
    have hsub : IntegrableOn (fun s : ℝ => (s ^ 2 - c) * Real.exp (-α * s)) (Ioi (0 : ℝ)) := by
      rw [hR_eq]; exact hR2_int.sub (hR0_int.const_mul c)
    exact hsub.const_mul _
  have hint_le := setIntegral_mono_on hL_int hR_int measurableSet_Ioi
    fun s hs => expSubst_second_moment_ptwise hx hc_pos hs
  have hR2_val : ∫ s in Ioi (0 : ℝ), s ^ 2 * Real.exp (-α * s) = 2 / α ^ 3 := by
    have h := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 2) (b := α)
      one_pos (by norm_num) hα
    simp only [Real.rpow_two, Real.rpow_one, div_one, mul_one] at h
    have hG3 : Real.Gamma (2 + 1 : ℝ) = 2 := by
      simpa using Real.Gamma_nat_eq_factorial 2
    have h3 : -(2 + 1 : ℝ) = -((3 : ℕ) : ℝ) := by norm_num
    rw [hG3, h3, Real.rpow_neg hα.le, Real.rpow_natCast] at h
    rw [h]; ring
  have hR0_val : ∫ s in Ioi (0 : ℝ), Real.exp (-α * s) = 1 / α := by
    simpa [one_div] using integral_exp_mul_Ioi (a := -α) (by linarith) 0
  have hR_zero : ∫ s in Ioi (0 : ℝ),
      Real.exp (-x * Real.exp s₀) * ((s ^ 2 - c) * Real.exp (-α * s)) = 0 := by
    rw [integral_const_mul, hR_eq, integral_sub hR2_int (hR0_int.const_mul c),
      integral_const_mul, hR2_val, hR0_val]
    simp only [c]; field_simp; ring
  have hL_val : ∫ s in Ioi (0 : ℝ), (s ^ 2 - c) * w s =
      (∫ s in Ioi (0 : ℝ), s ^ 2 * w s) - c * ∫ s in Ioi (0 : ℝ), w s := by
    rw [hL_eq, integral_sub hw2 (hw0.const_mul c), integral_const_mul]
  linarith

private theorem upperGammaMoment_variance_le {a x : ℝ} (ha : a < 0) (hx : 0 < x) :
    (upperGammaMoment 2 a x * upperGammaMoment 0 a x - (upperGammaMoment 1 a x) ^ 2) /
      (upperGammaMoment 0 a x) ^ 2 ≤ 2 / a ^ 2 := by
  set α : ℝ := -a
  have hα : 0 < α := by linarith
  set w : ℝ → ℝ := fun s => Real.exp (a * s - x * Real.exp s)
  set M₀ : ℝ := ∫ s in Ioi (0 : ℝ), w s
  set M₁ : ℝ := ∫ s in Ioi (0 : ℝ), s * w s
  set M₂ : ℝ := ∫ s in Ioi (0 : ℝ), s ^ 2 * w s
  have hw_eq : ∀ s : ℝ, Real.exp (-α * s - x * Real.exp s) = w s := fun s => by
    simp only [α, w, neg_neg]
  have hw_int (k : ℕ) : IntegrableOn (fun s : ℝ => s ^ k * w s) (Ioi (0 : ℝ)) := by
    simpa only [hw_eq] using integrableOn_pow_mul_expSubst k hα hx
  have hw0 : IntegrableOn w (Ioi (0 : ℝ)) := by simpa only [pow_zero, one_mul] using hw_int 0
  have hw1 : IntegrableOn (fun s : ℝ => s * w s) (Ioi (0 : ℝ)) := by
    simpa only [pow_one] using hw_int 1
  have hU0 : upperGammaMoment 0 a x = x ^ a * M₀ := by
    rw [upperGammaMoment_eq_expSubst 0 a hx]; simp only [pow_zero, one_mul]; rfl
  have hU1 : upperGammaMoment 1 a x = x ^ a * (Real.log x * M₀ + M₁) := by
    have hfun : (fun s : ℝ => (Real.log x + s) ^ 1 * w s) =
        fun s => Real.log x * w s + s * w s := by ext s; ring
    rw [upperGammaMoment_eq_expSubst 1 a hx, hfun, integral_add (hw0.const_mul _) hw1,
      integral_const_mul]
  have hU2 : upperGammaMoment 2 a x =
      x ^ a * ((Real.log x) ^ 2 * M₀ + 2 * Real.log x * M₁ + M₂) := by
    have hfun : (fun s : ℝ => (Real.log x + s) ^ 2 * w s) =
        fun s => ((Real.log x) ^ 2 * w s + 2 * Real.log x * (s * w s)) + s ^ 2 * w s := by
      ext s; ring
    have h01 : IntegrableOn (fun s : ℝ => (Real.log x) ^ 2 * w s + 2 * Real.log x * (s * w s))
        (Ioi (0 : ℝ)) := (hw0.const_mul _).add (hw1.const_mul _)
    rw [upperGammaMoment_eq_expSubst 2 a hx, hfun, integral_add h01 (hw_int 2),
      integral_add (hw0.const_mul _) (hw1.const_mul _), integral_const_mul, integral_const_mul]
  have hM0_pos : 0 < M₀ := by
    have hU0_pos := upperGammaMoment_zero_pos a hx
    rw [hU0] at hU0_pos
    exact pos_of_mul_pos_right hU0_pos (Real.rpow_pos_of_pos hx a).le
  have hvar_eq : (upperGammaMoment 2 a x * upperGammaMoment 0 a x - (upperGammaMoment 1 a x) ^ 2) /
      (upperGammaMoment 0 a x) ^ 2 = (M₂ * M₀ - M₁ ^ 2) / M₀ ^ 2 := by
    rw [hU0, hU1, hU2]
    have hxa : x ^ a ≠ 0 := (Real.rpow_pos_of_pos hx a).ne'
    have hM0_ne : M₀ ≠ 0 := hM0_pos.ne'
    field_simp; ring
  have hM2_le : M₂ ≤ (2 / a ^ 2) * M₀ := by
    have h := expSubst_second_moment_le hα hx
    simp_rw [hw_eq] at h
    simpa only [α, neg_sq] using h
  rw [hvar_eq, div_le_iff₀ (sq_pos_of_pos hM0_pos)]
  nlinarith [sq_nonneg M₁]

/-! ### The logarithmic barrier function on `(-2n, 1 - 2n)` -/

/-- The logarithmic barrier `H_x(a) = log Γ(a) - log U(a, x)` on the positive-Gamma bands
`(-2n, 1 - 2n)`, whose zeros match those of `a ↦ γ*(a, x)`. -/
private def paramBarrier (x a : ℝ) : ℝ :=
  Real.log (Real.Gamma a) - Real.log (upperGammaMoment 0 a x)

private theorem mem_evenBand_ne_neg_natCast {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) (k : ℕ) : a ≠ -(k : ℝ) := by
  have hcast : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  exact ne_neg_natCast_of_mem_Ioo (m := 2 * n - 1)
    ⟨by rw [hcast]; linarith [ha.1], by rw [hcast]; linarith [ha.2]⟩ k

private theorem Gamma_pos_of_mem_evenBand {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) : 0 < Real.Gamma a := by
  have hcast : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h := Real.neg_one_pow_mul_Gamma_pos (m := 2 * n - 1) (x := a)
    (by rw [hcast]; linarith [ha.1]) (by rw [hcast]; linarith [ha.2])
  have heven : Even ((2 * n - 1) + 1) := by
    rw [Nat.sub_add_cancel (by omega)]; exact ⟨n, by ring⟩
  simpa only [heven.neg_one_pow, one_mul] using h

private theorem hasDerivAt_paramBarrier {n : ℕ} (hn : 1 ≤ n) {x a : ℝ} (hx : 0 < x)
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) :
    HasDerivAt (paramBarrier x)
      (Real.digamma a - upperGammaMoment 1 a x / upperGammaMoment 0 a x) a := by
  have hΓ := Real.hasDerivAt_log_Gamma (mem_evenBand_ne_neg_natCast hn ha)
  have hU := (hasDerivAt_upperGammaMoment 0 a hx).log (upperGammaMoment_zero_pos a hx).ne'
  exact hΓ.sub hU

private theorem hasDerivAt_deriv_paramBarrier {n : ℕ} (hn : 1 ≤ n) {x a : ℝ} (hx : 0 < x)
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) :
    HasDerivAt (deriv (paramBarrier x))
      (deriv Real.digamma a -
        (upperGammaMoment 2 a x * upperGammaMoment 0 a x - (upperGammaMoment 1 a x) ^ 2) /
          (upperGammaMoment 0 a x) ^ 2) a := by
  have heq : deriv (paramBarrier x) =ᶠ[𝓝 a]
      fun b => Real.digamma b - upperGammaMoment 1 b x / upperGammaMoment 0 b x := by
    filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
    exact (hasDerivAt_paramBarrier hn hx hb).deriv
  have hψ := (Real.differentiableAt_digamma (mem_evenBand_ne_neg_natCast hn ha)).hasDerivAt
  have hdiv := (hasDerivAt_upperGammaMoment 1 a hx).div (hasDerivAt_upperGammaMoment 0 a hx)
    (upperGammaMoment_zero_pos a hx).ne'
  have hsub := hψ.sub hdiv
  have hval : (upperGammaMoment 2 a x * upperGammaMoment 0 a x -
        upperGammaMoment 1 a x * upperGammaMoment 1 a x) / (upperGammaMoment 0 a x) ^ 2 =
      (upperGammaMoment 2 a x * upperGammaMoment 0 a x - (upperGammaMoment 1 a x) ^ 2) /
        (upperGammaMoment 0 a x) ^ 2 := by ring
  rw [hval] at hsub
  exact hsub.congr_of_eventuallyEq heq

private theorem deriv_digamma_ge_eight_of_mem_evenBand {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) : 8 ≤ deriv Real.digamma a := by
  have hrec := Real.deriv_digamma_apply_add_nat (mem_evenBand_ne_neg_natCast hn ha) (2 * n + 1)
  have hpos : 0 < a + ((2 * n + 1 : ℕ) : ℝ) := by push_cast; linarith [ha.1]
  have hnonneg : 0 ≤ deriv Real.digamma (a + ((2 * n + 1 : ℕ) : ℝ)) :=
    Real.deriv_digamma_nonneg hpos
  have hpair : ({2 * n - 1, 2 * n} : Finset ℕ) ⊆ Finset.range (2 * n + 1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rw [Finset.mem_range]; omega
  have hsum_ge : ((a + ((2 * n - 1 : ℕ) : ℝ)) ^ 2)⁻¹ + ((a + ((2 * n : ℕ) : ℝ)) ^ 2)⁻¹ ≤
      ∑ k ∈ Finset.range (2 * n + 1), ((a + (k : ℝ)) ^ 2)⁻¹ := by
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k : ℕ => ((a + (k : ℝ)) ^ 2)⁻¹)
      hpair (fun k _ _ => inv_nonneg.mpr (sq_nonneg _))
    rwa [Finset.sum_pair (by omega : 2 * n - 1 ≠ 2 * n)] at hsub
  set u : ℝ := a + 2 * (n : ℝ)
  have hu0 : 0 < u := by simp only [u]; linarith [ha.1]
  have hu1 : u < 1 := by simp only [u]; linarith [ha.2]
  have h1 : a + ((2 * n - 1 : ℕ) : ℝ) = u - 1 := by
    rw [Nat.cast_sub (by omega)]; simp only [u]; push_cast; ring
  have h2 : a + ((2 * n : ℕ) : ℝ) = u := by simp only [u]; push_cast; ring
  have height : 8 ≤ ((u - 1) ^ 2)⁻¹ + (u ^ 2)⁻¹ := by
    have hu_sq : 0 < u ^ 2 := sq_pos_of_pos hu0
    have hu1_sq : 0 < (u - 1) ^ 2 := sq_pos_of_ne_zero (by linarith)
    have hadd : ((u - 1) ^ 2)⁻¹ + (u ^ 2)⁻¹ = (u ^ 2 + (u - 1) ^ 2) / ((u - 1) ^ 2 * u ^ 2) := by
      rw [← one_div, ← one_div, div_add_div 1 1 hu1_sq.ne' hu_sq.ne', one_mul, mul_one]
    rw [hadd, le_div_iff₀ (mul_pos hu1_sq hu_sq), ← sub_nonneg]
    calc 0 ≤ (2 * u - 1) ^ 2 * (1 + 2 * (u * (1 - u))) :=
          mul_nonneg (sq_nonneg _) (by nlinarith)
      _ = u ^ 2 + (u - 1) ^ 2 - 8 * ((u - 1) ^ 2 * u ^ 2) := by ring
  rw [h1, h2] at hsum_ge
  linarith

private theorem deriv_deriv_paramBarrier_gt_six {n : ℕ} (hn : 1 ≤ n) {x a : ℝ} (hx : 0 < x)
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) :
    6 < deriv (deriv (paramBarrier x)) a := by
  rw [(hasDerivAt_deriv_paramBarrier hn hx ha).deriv]
  have hψ := deriv_digamma_ge_eight_of_mem_evenBand hn ha
  have ha_lt : a < -1 := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [ha.2]
  have hvar := upperGammaMoment_variance_le (by linarith) hx
  have ha_sq : 1 < a ^ 2 := by nlinarith
  have h2 : 2 / a ^ 2 < 2 := by rw [div_lt_iff₀ (by positivity)]; linarith
  linarith

private theorem tendsto_paramBarrier_endpoint {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x)
    {L : ℝ} (hGL : Real.Gamma L = 0) :
    Tendsto (paramBarrier x) (𝓝[Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))] L) atTop := by
  have hinv_tendsto : Tendsto (fun a : ℝ => (Real.Gamma a)⁻¹)
      (𝓝[Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))] L) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Tendsto (fun a : ℝ => (Real.Gamma a)⁻¹) (𝓝 L) (𝓝 ((Real.Gamma L)⁻¹)) :=
        (Real.continuous_inv_Gamma.continuousAt (x := L)).tendsto
      rw [hGL, inv_zero] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with a ha
      exact inv_pos.mpr (Gamma_pos_of_mem_evenBand hn ha)
  have hΓ_top : Tendsto Real.Gamma (𝓝[Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))] L) atTop := by
    simpa only [Function.comp_def, inv_inv] using tendsto_inv_nhdsGT_zero.comp hinv_tendsto
  have hlogΓ := Real.tendsto_log_atTop.comp hΓ_top
  have hlogU : Tendsto (fun a : ℝ => -Real.log (upperGammaMoment 0 a x))
      (𝓝[Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))] L) (𝓝 (-Real.log (upperGammaMoment 0 L x))) :=
    ((hasDerivAt_upperGammaMoment 0 L hx).continuousAt.log
      (upperGammaMoment_zero_pos L hx).ne').neg.tendsto.mono_left nhdsWithin_le_nhds
  convert hlogΓ.atTop_add hlogU using 1
  ext a
  simp only [paramBarrier, sub_eq_add_neg, Function.comp_apply]

private theorem tendsto_paramBarrier_left {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    Tendsto (paramBarrier x) (𝓝[>] (-2 * (n : ℝ))) atTop := by
  have hG : Real.Gamma (-2 * (n : ℝ)) = 0 := by
    have : -2 * (n : ℝ) = -((2 * n : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.Gamma_neg_nat_eq_zero]
  rw [← nhdsWithin_Ioo_eq_nhdsGT (by linarith : -2 * (n : ℝ) < 1 - 2 * (n : ℝ))]
  exact tendsto_paramBarrier_endpoint hn hx hG

private theorem tendsto_paramBarrier_right {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    Tendsto (paramBarrier x) (𝓝[<] (1 - 2 * (n : ℝ))) atTop := by
  have hG : Real.Gamma (1 - 2 * (n : ℝ)) = 0 := by
    have : 1 - 2 * (n : ℝ) = -((2 * n - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this, Real.Gamma_neg_nat_eq_zero]
  rw [← nhdsWithin_Ioo_eq_nhdsLT (by linarith : -2 * (n : ℝ) < 1 - 2 * (n : ℝ))]
  exact tendsto_paramBarrier_endpoint hn hx hG

private theorem exists_compact_sublevel_paramBarrier {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x)
    (M : ℝ) :
    ∃ c d : ℝ, -2 * (n : ℝ) < c ∧ c < d ∧ d < 1 - 2 * (n : ℝ) ∧
      ∀ a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)), paramBarrier x a ≤ M → a ∈ Icc c d := by
  have hL := (tendsto_paramBarrier_left hn hx).eventually (eventually_gt_atTop M)
  have hR := (tendsto_paramBarrier_right hn hx).eventually (eventually_gt_atTop M)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hL hR
  obtain ⟨ε₁, hε₁, hL⟩ := hL
  obtain ⟨ε₂, hε₂, hR⟩ := hR
  set δ₁ : ℝ := min (ε₁ / 2) (1 / 4)
  set δ₂ : ℝ := min (ε₂ / 2) (1 / 4)
  have hδ₁ : 0 < δ₁ := lt_min (half_pos hε₁) (by norm_num)
  have hδ₂ : 0 < δ₂ := lt_min (half_pos hε₂) (by norm_num)
  have hδ₁_le : δ₁ ≤ 1 / 4 := min_le_right _ _
  have hδ₂_le : δ₂ ≤ 1 / 4 := min_le_right _ _
  have hδ₁_lt : δ₁ < ε₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ₂_lt : δ₂ < ε₂ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨-2 * (n : ℝ) + δ₁, 1 - 2 * (n : ℝ) - δ₂, by linarith, by linarith, by linarith,
    fun a ha haM => ⟨?_, ?_⟩⟩
  · by_contra hlt
    push Not at hlt
    have hdist : dist a (-2 * (n : ℝ)) < ε₁ := by
      rw [Real.dist_eq, abs_of_pos (by linarith [ha.1])]; linarith
    linarith [hL hdist ha.1]
  · by_contra hgt
    push Not at hgt
    have hdist : dist a (1 - 2 * (n : ℝ)) < ε₂ := by
      rw [Real.dist_eq, abs_of_neg (by linarith [ha.2])]; linarith
    linarith [hR hdist ha.2]

private theorem exists_isMinOn_paramBarrier {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    ∃ a₀ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)),
      IsMinOn (paramBarrier x) (Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) a₀ ∧
      deriv (paramBarrier x) a₀ = 0 := by
  have haM : -2 * (n : ℝ) + 1 / 2 ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) :=
    ⟨by linarith, by linarith⟩
  obtain ⟨c, d, hc, hcd, hd, hsub⟩ :=
    exists_compact_sublevel_paramBarrier hn hx (paramBarrier x (-2 * (n : ℝ) + 1 / 2))
  have hIcc_sub : Icc c d ⊆ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) :=
    fun a ha => ⟨hc.trans_le ha.1, ha.2.trans_lt hd⟩
  have hcont : ContinuousOn (paramBarrier x) (Icc c d) := fun a ha =>
    (hasDerivAt_paramBarrier hn hx (hIcc_sub ha)).continuousAt.continuousWithinAt
  obtain ⟨a₀, ha₀_Icc, ha₀_min⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hcd.le) hcont
  have ha₀ : a₀ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) := hIcc_sub ha₀_Icc
  have ha₀_le_aM : paramBarrier x a₀ ≤ paramBarrier x (-2 * (n : ℝ) + 1 / 2) :=
    ha₀_min (hsub _ haM le_rfl)
  have hmin : IsMinOn (paramBarrier x) (Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) a₀ := by
    intro a ha
    rcases le_or_gt (paramBarrier x a) (paramBarrier x (-2 * (n : ℝ) + 1 / 2)) with hle | hgt
    · exact ha₀_min (hsub a ha hle)
    · exact ha₀_le_aM.trans hgt.le
  refine ⟨a₀, ha₀, hmin, (hmin.isLocalMin (isOpen_Ioo.mem_nhds ha₀)).deriv_eq_zero⟩

/-! ### Bridging zeros and derivatives between `γ*(·, x)` and `paramBarrier x` -/

private theorem tricomi_re_eq_of_paramBarrier {n : ℕ} (hn : 1 ≤ n) {x a : ℝ} (hx : 0 < x)
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) :
    (tricomiIncompleteGamma a x).re = x ^ (-a) * (1 - Real.exp (-paramBarrier x a)) := by
  have hΓ_pos := Gamma_pos_of_mem_evenBand hn ha
  have hU_pos := upperGammaMoment_zero_pos a hx
  have hid := Gamma_mul_one_sub_rpow_mul_tricomi_re (mem_evenBand_ne_neg_natCast hn ha) hx
  have hexp : Real.exp (-paramBarrier x a) = upperGammaMoment 0 a x / Real.Gamma a := by
    simp only [paramBarrier, neg_sub, Real.exp_sub, Real.exp_log hU_pos, Real.exp_log hΓ_pos]
  have h1 : 1 - x ^ a * (tricomiIncompleteGamma a x).re = Real.exp (-paramBarrier x a) := by
    rw [hexp, eq_div_iff hΓ_pos.ne', mul_comm, hid]
  have h2 : x ^ a * (tricomiIncompleteGamma a x).re = 1 - Real.exp (-paramBarrier x a) := by
    linarith
  have hcancel : x ^ (-a) * x ^ a = 1 := by
    rw [Real.rpow_neg hx.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hx a).ne']
  calc (tricomiIncompleteGamma a x).re
      = (x ^ (-a) * x ^ a) * (tricomiIncompleteGamma a x).re := by rw [hcancel, one_mul]
    _ = x ^ (-a) * (x ^ a * (tricomiIncompleteGamma a x).re) := by ring
    _ = x ^ (-a) * (1 - Real.exp (-paramBarrier x a)) := by rw [h2]

private theorem tricomi_eq_zero_iff_paramBarrier_eq_zero {n : ℕ} (hn : 1 ≤ n) {x a : ℝ}
    (hx : 0 < x) (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) :
    tricomiIncompleteGamma a x = 0 ↔ paramBarrier x a = 0 := by
  rw [tricomiIncompleteGamma_ofReal_eq_zero_iff, tricomi_re_eq_of_paramBarrier hn hx ha,
    mul_eq_zero, or_iff_right (Real.rpow_pos_of_pos hx (-a)).ne', sub_eq_zero, eq_comm,
    Real.exp_eq_one_iff, neg_eq_zero]

private theorem deriv_tricomi_re_of_mem_evenBand {n : ℕ} (hn : 1 ≤ n) {x a : ℝ} (hx : 0 < x)
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) :
    deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a =
      -Real.log x * (tricomiIncompleteGamma a x).re +
        x ^ (-a) * Real.exp (-paramBarrier x a) * deriv (paramBarrier x) a := by
  have heq : (fun b : ℝ => (tricomiIncompleteGamma b x).re) =ᶠ[𝓝 a]
      fun b => x ^ (-b) * (1 - Real.exp (-paramBarrier x b)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
    exact tricomi_re_eq_of_paramBarrier hn hx hb
  have h1 : HasDerivAt (fun b : ℝ => x ^ (-b)) (-Real.log x * x ^ (-a)) a := by
    have h := (hasDerivAt_neg a).const_rpow hx
    convert h using 1; ring
  have hH := hasDerivAt_paramBarrier hn hx ha
  have h2 : HasDerivAt (fun b : ℝ => 1 - Real.exp (-paramBarrier x b))
      (Real.exp (-paramBarrier x a) * deriv (paramBarrier x) a) a := by
    have hd := (hH.neg.exp).const_sub 1
    rw [← hH.deriv] at hd
    convert hd using 1
    simp only [Pi.neg_apply]; ring
  have hprod := h1.mul h2
  rw [(hprod.congr_of_eventuallyEq heq).deriv, tricomi_re_eq_of_paramBarrier hn hx ha]
  ring

private theorem deriv_tricomi_re_at_zero {n : ℕ} (hn : 1 ≤ n) {x a : ℝ} (hx : 0 < x)
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) (hz : paramBarrier x a = 0) :
    deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a =
      x ^ (-a) * deriv (paramBarrier x) a := by
  have hg0 : (tricomiIncompleteGamma a x).re = 0 := by
    rw [tricomi_re_eq_of_paramBarrier hn hx ha, hz, neg_zero, Real.exp_zero, sub_self, mul_zero]
  rw [deriv_tricomi_re_of_mem_evenBand hn hx ha, hg0, hz]
  simp

private theorem deriv_deriv_tricomi_re_at_double_zero {n : ℕ} (hn : 1 ≤ n) {x a : ℝ} (hx : 0 < x)
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) (hz : paramBarrier x a = 0)
    (hd : deriv (paramBarrier x) a = 0) :
    deriv (deriv fun b : ℝ => (tricomiIncompleteGamma b x).re) a =
      x ^ (-a) * deriv (deriv (paramBarrier x)) a := by
  have heq : deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) =ᶠ[𝓝 a]
      fun b => -Real.log x * (tricomiIncompleteGamma b x).re +
        (x ^ (-b) * Real.exp (-paramBarrier x b)) * deriv (paramBarrier x) b := by
    filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
    exact deriv_tricomi_re_of_mem_evenBand hn hx hb
  have hd1 : HasDerivAt (fun b : ℝ => -Real.log x * (tricomiIncompleteGamma b x).re) 0 a := by
    have h := (differentiable_tricomiIncompleteGamma_re x a).hasDerivAt.const_mul (-Real.log x)
    rw [deriv_tricomi_re_at_zero hn hx ha hz, hd, mul_zero, mul_zero] at h
    exact h
  have hpref : DifferentiableAt ℝ (fun b : ℝ => x ^ (-b) * Real.exp (-paramBarrier x b)) a :=
    ((hasDerivAt_neg a).const_rpow hx).differentiableAt.mul
      (hasDerivAt_paramBarrier hn hx ha).neg.exp.differentiableAt
  have hd2 : HasDerivAt
      (fun b : ℝ => (x ^ (-b) * Real.exp (-paramBarrier x b)) * deriv (paramBarrier x) b)
      (x ^ (-a) * deriv (deriv (paramBarrier x)) a) a := by
    have h : HasDerivAt
        (fun b : ℝ => (x ^ (-b) * Real.exp (-paramBarrier x b)) * deriv (paramBarrier x) b)
        (deriv (fun b : ℝ => x ^ (-b) * Real.exp (-paramBarrier x b)) a *
          deriv (paramBarrier x) a +
          (x ^ (-a) * Real.exp (-paramBarrier x a)) * deriv (deriv (paramBarrier x)) a) a := by
      have h' := hpref.hasDerivAt.mul (hasDerivAt_deriv_paramBarrier hn hx ha)
      rw [← (hasDerivAt_deriv_paramBarrier hn hx ha).deriv] at h'
      exact h'
    rw [hd, hz, neg_zero, Real.exp_zero, mul_one, mul_zero, zero_add] at h
    exact h
  have hsum := hd1.add hd2
  simpa only [zero_add] using (hsum.congr_of_eventuallyEq heq).deriv

private theorem strictMonoOn_deriv_paramBarrier {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    StrictMonoOn (deriv (paramBarrier x)) (Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) :=
  strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    (fun a ha => (hasDerivAt_deriv_paramBarrier hn hx ha).continuousAt.continuousWithinAt)
    (fun a ha => by
      rw [interior_Ioo] at ha
      linarith [deriv_deriv_paramBarrier_gt_six hn hx ha])

private theorem strictAntiOn_paramBarrier_left {n : ℕ} (hn : 1 ≤ n) {x a₀ : ℝ} (hx : 0 < x)
    (ha₀ : a₀ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) (hd₀ : deriv (paramBarrier x) a₀ = 0) :
    StrictAntiOn (paramBarrier x) (Ioc (-2 * (n : ℝ)) a₀) :=
  strictAntiOn_of_deriv_neg (convex_Ioc _ _)
    (fun a ha => (hasDerivAt_paramBarrier hn hx ⟨ha.1, ha.2.trans_lt ha₀.2⟩).continuousAt
      |>.continuousWithinAt)
    (fun a ha => by
      rw [interior_Ioc] at ha
      linarith [strictMonoOn_deriv_paramBarrier hn hx ⟨ha.1, ha.2.trans ha₀.2⟩ ha₀ ha.2])

private theorem strictMonoOn_paramBarrier_right {n : ℕ} (hn : 1 ≤ n) {x a₀ : ℝ} (hx : 0 < x)
    (ha₀ : a₀ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) (hd₀ : deriv (paramBarrier x) a₀ = 0) :
    StrictMonoOn (paramBarrier x) (Ico a₀ (1 - 2 * (n : ℝ))) :=
  strictMonoOn_of_deriv_pos (convex_Ico _ _)
    (fun a ha => (hasDerivAt_paramBarrier hn hx ⟨ha₀.1.trans_le ha.1, ha.2⟩).continuousAt
      |>.continuousWithinAt)
    (fun a ha => by
      rw [interior_Ico] at ha
      linarith [strictMonoOn_deriv_paramBarrier hn hx ha₀ ⟨ha₀.1.trans ha.1, ha.2⟩ ha.1])

private theorem paramBarrier_two_zeros_of_min_neg {n : ℕ} (hn : 1 ≤ n) {x a₀ : ℝ} (hx : 0 < x)
    (ha₀ : a₀ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)))
    (hd₀ : deriv (paramBarrier x) a₀ = 0) (hneg : paramBarrier x a₀ < 0) :
    ∃ a₁ a₂ : ℝ, a₁ < a₂ ∧
      Set.ofPred (fun a : ℝ => a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
        tricomiIncompleteGamma a x = 0) = {a₁, a₂} ∧
      deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₁ ≠ 0 ∧
      deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₂ ≠ 0 := by
  have hd_mono := strictMonoOn_deriv_paramBarrier hn hx
  have hanti := strictAntiOn_paramBarrier_left hn hx ha₀ hd₀
  have hmono := strictMonoOn_paramBarrier_right hn hx ha₀ hd₀
  have hL := (tendsto_paramBarrier_left hn hx).eventually (eventually_gt_atTop (0 : ℝ))
  have hR := (tendsto_paramBarrier_right hn hx).eventually (eventually_gt_atTop (0 : ℝ))
  obtain ⟨b₁, hb₁_pos, hb₁_mem⟩ := (hL.and (Ioo_mem_nhdsGT ha₀.1)).exists
  obtain ⟨b₂, hb₂_pos, hb₂_mem⟩ := (hR.and (Ioo_mem_nhdsLT ha₀.2)).exists
  have hcontL : ContinuousOn (paramBarrier x) (Icc b₁ a₀) := fun a ha =>
    (hasDerivAt_paramBarrier hn hx ⟨hb₁_mem.1.trans_le ha.1, ha.2.trans_lt ha₀.2⟩).continuousAt
      |>.continuousWithinAt
  have hcontR : ContinuousOn (paramBarrier x) (Icc a₀ b₂) := fun a ha =>
    (hasDerivAt_paramBarrier hn hx ⟨ha₀.1.trans_le ha.1, ha.2.trans_lt hb₂_mem.2⟩).continuousAt
      |>.continuousWithinAt
  obtain ⟨a₁, ha₁_Ioo, ha₁_zero⟩ := intermediate_value_Ioo' hb₁_mem.2.le hcontL ⟨hneg, hb₁_pos⟩
  obtain ⟨a₂, ha₂_Ioo, ha₂_zero⟩ := intermediate_value_Ioo hb₂_mem.1.le hcontR ⟨hneg, hb₂_pos⟩
  have ha₁ : a₁ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) :=
    ⟨hb₁_mem.1.trans ha₁_Ioo.1, ha₁_Ioo.2.trans ha₀.2⟩
  have ha₂ : a₂ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) :=
    ⟨ha₀.1.trans ha₂_Ioo.1, ha₂_Ioo.2.trans hb₂_mem.2⟩
  refine ⟨a₁, a₂, ha₁_Ioo.2.trans ha₂_Ioo.1, ?_, ?_, ?_⟩
  · ext a
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨ha, hza⟩
      have hHa := (tricomi_eq_zero_iff_paramBarrier_eq_zero hn hx ha).mp hza
      rcases lt_trichotomy a a₀ with hlt | rfl | hgt
      · exact Or.inl (hanti.injOn ⟨ha.1, hlt.le⟩ ⟨ha₁.1, ha₁_Ioo.2.le⟩ (hHa.trans ha₁_zero.symm))
      · linarith
      · exact Or.inr (hmono.injOn ⟨hgt.le, ha.2⟩ ⟨ha₂_Ioo.1.le, ha₂.2⟩ (hHa.trans ha₂_zero.symm))
    · rintro (rfl | rfl)
      · exact ⟨ha₁, (tricomi_eq_zero_iff_paramBarrier_eq_zero hn hx ha₁).mpr ha₁_zero⟩
      · exact ⟨ha₂, (tricomi_eq_zero_iff_paramBarrier_eq_zero hn hx ha₂).mpr ha₂_zero⟩
  · rw [deriv_tricomi_re_at_zero hn hx ha₁ ha₁_zero]
    exact mul_ne_zero (Real.rpow_pos_of_pos hx _).ne' (by linarith [hd_mono ha₁ ha₀ ha₁_Ioo.2])
  · rw [deriv_tricomi_re_at_zero hn hx ha₂ ha₂_zero]
    exact mul_ne_zero (Real.rpow_pos_of_pos hx _).ne' (by linarith [hd_mono ha₀ ha₂ ha₂_Ioo.1])

private theorem paramBarrier_double_zero_of_min_zero {n : ℕ} (hn : 1 ≤ n) {x a₀ : ℝ} (hx : 0 < x)
    (ha₀ : a₀ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)))
    (hd₀ : deriv (paramBarrier x) a₀ = 0) (hzero : paramBarrier x a₀ = 0) :
    ∃ a : ℝ,
      Set.ofPred (fun a : ℝ => a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
        tricomiIncompleteGamma a x = 0) = {a} ∧
      deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a = 0 ∧
      deriv (deriv fun b : ℝ => (tricomiIncompleteGamma b x).re) a ≠ 0 := by
  have hanti := strictAntiOn_paramBarrier_left hn hx ha₀ hd₀
  have hmono := strictMonoOn_paramBarrier_right hn hx ha₀ hd₀
  refine ⟨a₀, ?_, ?_, ?_⟩
  · ext a
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨ha, hza⟩
      have hHa := (tricomi_eq_zero_iff_paramBarrier_eq_zero hn hx ha).mp hza
      rcases lt_trichotomy a a₀ with hlt | rfl | hgt
      · exfalso; linarith [hanti ⟨ha.1, hlt.le⟩ ⟨ha₀.1, le_rfl⟩ hlt]
      · rfl
      · exfalso; linarith [hmono ⟨le_rfl, ha₀.2⟩ ⟨hgt.le, ha.2⟩ hgt]
    · rintro rfl
      exact ⟨ha₀, (tricomi_eq_zero_iff_paramBarrier_eq_zero hn hx ha₀).mpr hzero⟩
  · rw [deriv_tricomi_re_at_zero hn hx ha₀ hzero, hd₀, mul_zero]
  · rw [deriv_deriv_tricomi_re_at_double_zero hn hx ha₀ hzero hd₀]
    exact mul_ne_zero (Real.rpow_pos_of_pos hx _).ne'
      (by linarith [deriv_deriv_paramBarrier_gt_six hn hx ha₀])

private theorem paramBarrier_no_zeros_of_min_pos {n : ℕ} (hn : 1 ≤ n) {x a₀ : ℝ} (hx : 0 < x)
    (hmin : IsMinOn (paramBarrier x) (Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) a₀)
    (hpos : 0 < paramBarrier x a₀) :
    Set.ofPred (fun a : ℝ => a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
      tricomiIncompleteGamma a x = 0) = ∅ := by
  ext a
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro ha hza
  have hHa := (tricomi_eq_zero_iff_paramBarrier_eq_zero hn hx ha).mp hza
  have hle : paramBarrier x a₀ ≤ paramBarrier x a := hmin ha
  linarith

/-! ### Monotonicity, continuity, and crossing of the barrier minimum `m_n(x)` -/

/-- The minimum value `m_n(x) = inf_{a ∈ (-2n, 1 - 2n)} H_x(a)` of the logarithmic barrier on the
`n`-th positive-Gamma band. -/
private def paramBarrierMin (n : ℕ) (x : ℝ) : ℝ :=
  sInf (paramBarrier x '' Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)))

private theorem paramBarrierMin_eq_of_isMinOn {n : ℕ} {x a₀ : ℝ}
    (ha₀ : a₀ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)))
    (hmin : IsMinOn (paramBarrier x) (Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) a₀) :
    paramBarrierMin n x = paramBarrier x a₀ := by
  refine IsLeast.csInf_eq ⟨mem_image_of_mem _ ha₀, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact hmin ha

private theorem strictMonoOn_paramBarrierMin {n : ℕ} (hn : 1 ≤ n) :
    StrictMonoOn (paramBarrierMin n) (Ioi (0 : ℝ)) := by
  intro x₁ hx₁ x₂ hx₂ h12
  obtain ⟨a₁, ha₁, hmin₁, _⟩ := exists_isMinOn_paramBarrier hn hx₁
  obtain ⟨a₂, ha₂, hmin₂, _⟩ := exists_isMinOn_paramBarrier hn hx₂
  rw [paramBarrierMin_eq_of_isMinOn ha₁ hmin₁, paramBarrierMin_eq_of_isMinOn ha₂ hmin₂]
  have hU := upperGammaMoment_zero_strictAntiOn a₂ hx₁ hx₂ h12
  have hlog := Real.log_lt_log (upperGammaMoment_zero_pos a₂ hx₂) hU
  have hH : paramBarrier x₁ a₂ < paramBarrier x₂ a₂ := by
    simp only [paramBarrier]; linarith
  exact (hmin₁ ha₂).trans_lt hH

private theorem continuousAt_upperGammaMoment_right (a : ℝ) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ContinuousAt (fun x : ℝ => upperGammaMoment 0 a x) x₀ := by
  let f : ℝ → ℝ := fun t => t ^ (a - 1) * Real.exp (-t)
  have hcont_at : ContinuousAt f x₀ :=
    (continuousAt_id.rpow_const (Or.inl hx₀.ne')).mul
      (Real.continuous_exp.continuousAt.comp continuousAt_neg)
  have hcont_on : ContinuousOn f (Icc (x₀ / 2) x₀) := fun t ht =>
    ((continuousAt_id.rpow_const (Or.inl ((half_pos hx₀).trans_le ht.1).ne')).mul
      (Real.continuous_exp.continuousAt.comp continuousAt_neg)).continuousWithinAt
  have hderiv : HasDerivAt (fun x : ℝ => upperGammaMoment 0 a (x₀ / 2) - ∫ t in (x₀ / 2)..x, f t)
      (-f x₀) x₀ :=
    (intervalIntegral.integral_hasDerivAt_right (hcont_on.intervalIntegrable_of_Icc (by linarith))
      (((measurable_id.pow_const _).mul
        (Real.continuous_exp.measurable.comp measurable_neg)).stronglyMeasurable
          |>.stronglyMeasurableAtFilter)
      hcont_at).const_sub _
  refine hderiv.continuousAt.congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds (half_lt_self hx₀)] with x hx
  rw [intervalIntegral.integral_of_le (le_of_lt hx)]
  linarith [upperGammaMoment_zero_split a (half_pos hx₀) hx]

private theorem exists_lipschitz_left_paramBarrierMin {n : ℕ} (hn : 1 ≤ n) {x₀ : ℝ}
    (hx₀ : 0 < x₀) :
    ∃ L : ℝ, 0 < L ∧ ∀ x : ℝ, x₀ / 2 < x → x < x₀ →
      paramBarrierMin n x₀ - paramBarrierMin n x ≤ L * (x₀ - x) := by
  obtain ⟨a₀, ha₀, hmin₀, _⟩ := exists_isMinOn_paramBarrier hn hx₀
  set c : ℝ := -2 * (n : ℝ)
  set M : ℝ := max 1 ((x₀ / 2) ^ (c - 1))
  set δ : ℝ := (x₀ + 1) ^ (c - 1) * Real.exp (-(x₀ + 1))
  have hM_pos : 0 < M := lt_max_of_lt_left zero_lt_one
  have hδ_pos : 0 < δ := mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.exp_pos _)
  refine ⟨M / δ, div_pos hM_pos hδ_pos, fun x hx_lo hlt => ?_⟩
  have hx_pos : 0 < x := by linarith
  obtain ⟨ax, hax, hminx, _⟩ := exists_isMinOn_paramBarrier hn hx_pos
  have hax_lo : c < ax := hax.1
  have hax_neg : ax - 1 < 0 := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [hax.2]
  have hU_diff : upperGammaMoment 0 ax x - upperGammaMoment 0 ax x₀ ≤ (x₀ - x) * M := by
    rw [upperGammaMoment_zero_split ax hx_pos hlt, add_sub_cancel_right]
    refine integral_Ioc_upperGamma_le_mul hx_pos hlt.le fun t ht => ?_
    have ht0 : 0 < t := hx_pos.trans ht.1
    have hbase : t ^ (ax - 1) ≤ M := by
      rcases le_total 1 t with h1 | h1
      · exact (Real.rpow_le_one_of_one_le_of_nonpos h1 hax_neg.le).trans (le_max_left _ _)
      · have hx2_le_t : x₀ / 2 ≤ t := hx_lo.le.trans ht.1.le
        exact ((Real.rpow_le_rpow_of_nonpos (half_pos hx₀) hx2_le_t hax_neg.le).trans
          (Real.rpow_le_rpow_of_exponent_ge (half_pos hx₀) (hx2_le_t.trans h1)
            (by linarith))).trans (le_max_right _ _)
    have hexp1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [Real.rpow_pos_of_pos ht0 (ax - 1)]
  have hU_lo : δ ≤ upperGammaMoment 0 ax x₀ := by
    have h1 := mul_le_integral_Ioc_upperGamma (a := ax) (m := δ) hx₀ (by linarith : x₀ ≤ x₀ + 1)
      fun t ht => mul_le_mul
        ((Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)).trans
          (Real.rpow_le_rpow_of_nonpos (hx₀.trans ht.1) ht.2 hax_neg.le))
        (Real.exp_le_exp.mpr (by linarith [ht.2])) (Real.exp_pos _).le
        (Real.rpow_pos_of_pos (hx₀.trans ht.1) _).le
    linarith [integral_Ioc_le_upperGammaMoment_zero ax (x₂ := x₀ + 1) hx₀]
  have hUx := upperGammaMoment_zero_pos ax hx_pos
  have hUx₀ := upperGammaMoment_zero_pos ax hx₀
  have hlog_diff : Real.log (upperGammaMoment 0 ax x) - Real.log (upperGammaMoment 0 ax x₀) ≤
      M / δ * (x₀ - x) := by
    rw [← Real.log_div hUx.ne' hUx₀.ne']
    calc Real.log (upperGammaMoment 0 ax x / upperGammaMoment 0 ax x₀)
        ≤ upperGammaMoment 0 ax x / upperGammaMoment 0 ax x₀ - 1 :=
          Real.log_le_sub_one_of_pos (div_pos hUx hUx₀)
      _ = (upperGammaMoment 0 ax x - upperGammaMoment 0 ax x₀) / upperGammaMoment 0 ax x₀ := by
          field_simp
      _ ≤ (x₀ - x) * M / δ := div_le_div₀ (by positivity) hU_diff hδ_pos hU_lo
      _ = M / δ * (x₀ - x) := by ring
  rw [paramBarrierMin_eq_of_isMinOn ha₀ hmin₀, paramBarrierMin_eq_of_isMinOn hax hminx]
  have hle : paramBarrier x₀ a₀ ≤ paramBarrier x₀ ax := hmin₀ hax
  simp only [paramBarrier] at hle ⊢
  linarith

private theorem continuousOn_paramBarrierMin {n : ℕ} (hn : 1 ≤ n) :
    ContinuousOn (paramBarrierMin n) (Ioi (0 : ℝ)) := by
  intro x₀ hx₀
  have hx₀' : 0 < x₀ := hx₀
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨a₀, ha₀, hmin₀, _⟩ := exists_isMinOn_paramBarrier hn hx₀'
  have hm₀ : paramBarrierMin n x₀ = paramBarrier x₀ a₀ :=
    paramBarrierMin_eq_of_isMinOn ha₀ hmin₀
  obtain ⟨L, hL_pos, hlip⟩ := exists_lipschitz_left_paramBarrierMin hn hx₀'
  have hcont_a₀ : ContinuousAt (fun x : ℝ => paramBarrier x a₀) x₀ :=
    continuousAt_const.sub ((continuousAt_upperGammaMoment_right a₀ hx₀').log
      (upperGammaMoment_zero_pos a₀ hx₀').ne')
  rw [Metric.continuousAt_iff] at hcont_a₀ ⊢
  intro ε hε
  obtain ⟨η₁, hη₁, hup⟩ := hcont_a₀ ε hε
  refine ⟨min η₁ (min (x₀ / 2) (ε / (2 * L))),
    lt_min hη₁ (lt_min (half_pos hx₀') (by positivity)), fun x hx => ?_⟩
  rw [Real.dist_eq] at hx ⊢
  have hx_lt_η₁ : |x - x₀| < η₁ := hx.trans_le (min_le_left _ _)
  have hx_lo : x₀ / 2 < x := by
    linarith [(abs_lt.mp (hx.trans_le ((min_le_right _ _).trans (min_le_left _ _)))).1]
  have hx_pos : 0 < x := by linarith
  have hupper : paramBarrierMin n x < paramBarrierMin n x₀ + ε := by
    obtain ⟨ax, hax, hminx, _⟩ := exists_isMinOn_paramBarrier hn hx_pos
    have hle : paramBarrierMin n x ≤ paramBarrier x a₀ := by
      rw [paramBarrierMin_eq_of_isMinOn hax hminx]; exact hminx ha₀
    have hdist := hup (by rwa [Real.dist_eq])
    rw [Real.dist_eq, abs_lt] at hdist
    linarith
  have hlower : paramBarrierMin n x₀ - ε < paramBarrierMin n x := by
    rcases le_or_gt x₀ x with hge | hlt
    · linarith [(strictMonoOn_paramBarrierMin hn).monotoneOn hx₀ hx_pos hge]
    · have hdist_x : x₀ - x < ε / (2 * L) := by
        have h := hx.trans_le ((min_le_right _ _).trans (min_le_right _ _))
        rw [abs_of_neg (by linarith)] at h
        linarith
      have hmul : L * (x₀ - x) < ε / 2 := by
        have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * L)).mp hdist_x
        linarith
      linarith [hlip x hx_lo hlt]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

private theorem exists_paramBarrierMin_neg {n : ℕ} (hn : 1 ≤ n) :
    ∃ x : ℝ, 0 < x ∧ paramBarrierMin n x < 0 := by
  set aM : ℝ := -2 * (n : ℝ) + 1 / 2 with haM_eq
  have haM : aM ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) := ⟨by linarith, by linarith⟩
  have haM_le : aM ≤ -1 := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hG_pos : 0 < Real.Gamma aM := Gamma_pos_of_mem_evenBand hn haM
  set c₀ : ℝ := (2 : ℝ) ^ (aM - 1) * Real.exp (-1)
  have hc₀_pos : 0 < c₀ := mul_pos (Real.rpow_pos_of_pos two_pos _) (Real.exp_pos _)
  set x : ℝ := min (1 / 4) (c₀ / (2 * Real.Gamma aM))
  have hx_pos : 0 < x := lt_min (by norm_num) (by positivity)
  have hx_le1 : x ≤ 1 / 4 := min_le_left _ _
  have hx_le2 : x ≤ c₀ / (2 * Real.Gamma aM) := min_le_right _ _
  refine ⟨x, hx_pos, ?_⟩
  obtain ⟨a₀, ha₀, hmin₀, _⟩ := exists_isMinOn_paramBarrier hn hx_pos
  rw [paramBarrierMin_eq_of_isMinOn ha₀ hmin₀]
  have hle_aM : paramBarrier x a₀ ≤ paramBarrier x aM := hmin₀ haM
  set m : ℝ := (2 * x) ^ (aM - 1) * Real.exp (-1)
  have hle_sub := mul_le_integral_Ioc_upperGamma (a := aM) (m := m) hx_pos
    (by linarith : x ≤ 2 * x) fun t ht => mul_le_mul
      (Real.rpow_le_rpow_of_nonpos (hx_pos.trans ht.1) ht.2 (by linarith))
      (Real.exp_le_exp.mpr (by linarith [ht.2])) (Real.exp_pos _).le
      (Real.rpow_pos_of_pos (hx_pos.trans ht.1) _).le
  have hle_full := integral_Ioc_le_upperGammaMoment_zero aM (x₂ := 2 * x) hx_pos
  have hval : (2 * x - x) * m = c₀ * x ^ aM := by
    have hxa : x * x ^ (aM - 1) = x ^ aM := by
      simpa only [Real.rpow_one, add_sub_cancel] using (Real.rpow_add hx_pos 1 (aM - 1)).symm
    simp only [m, c₀]
    rw [Real.mul_rpow two_pos.le hx_pos.le]
    calc (2 * x - x) * (2 ^ (aM - 1) * x ^ (aM - 1) * Real.exp (-1))
        = 2 ^ (aM - 1) * Real.exp (-1) * (x * x ^ (aM - 1)) := by ring
      _ = 2 ^ (aM - 1) * Real.exp (-1) * x ^ aM := by rw [hxa]
  have hx_pow : x⁻¹ ≤ x ^ aM := by
    rw [← Real.rpow_neg_one x]
    exact Real.rpow_le_rpow_of_exponent_ge hx_pos (by linarith) haM_le
  have h2G : 2 * Real.Gamma aM ≤ c₀ * x⁻¹ := by
    rw [le_div_iff₀ (by positivity)] at hx_le2
    rw [← div_eq_mul_inv, le_div_iff₀ hx_pos]
    linarith
  have hU_gt : Real.Gamma aM < upperGammaMoment 0 aM x := by
    linarith [mul_le_mul_of_nonneg_left hx_pow hc₀_pos.le]
  have hH_neg : paramBarrier x aM < 0 := by
    simp only [paramBarrier]; linarith [Real.log_lt_log hG_pos hU_gt]
  linarith

private theorem exists_paramBarrierMin_pos {n : ℕ} (hn : 1 ≤ n) :
    ∃ x : ℝ, 0 < x ∧ 0 < paramBarrierMin n x := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Real.continuous_inv_Gamma.continuousOn (s := Icc (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))))
  set K : ℝ := max B 1
  have hK_pos : 0 < K := lt_max_of_lt_right zero_lt_one
  set x : ℝ := max 1 (Real.log K + 1)
  have hx_ge1 : 1 ≤ x := le_max_left _ _
  have hx_pos : 0 < x := by linarith
  refine ⟨x, hx_pos, ?_⟩
  obtain ⟨a₀, ha₀, hmin₀, _⟩ := exists_isMinOn_paramBarrier hn hx_pos
  rw [paramBarrierMin_eq_of_isMinOn ha₀ hmin₀]
  have hG_pos : 0 < Real.Gamma a₀ := Gamma_pos_of_mem_evenBand hn ha₀
  have hG_lo : K⁻¹ ≤ Real.Gamma a₀ := by
    have hnorm : |(Real.Gamma a₀)⁻¹| ≤ B := hB a₀ ⟨ha₀.1.le, ha₀.2.le⟩
    rw [abs_of_pos (inv_pos.mpr hG_pos)] at hnorm
    exact (inv_le_comm₀ hK_pos hG_pos).mpr (hnorm.trans (le_max_left _ _))
  have hU_hi : upperGammaMoment 0 a₀ x ≤ Real.exp (-x) := by
    have ha₀_neg : a₀ - 1 < 0 := by
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith [ha₀.2]
    have hrec := upperGammaMoment_zero_add_one (a₀ - 1) hx_pos
    rw [sub_add_cancel] at hrec
    have h1 : x ^ (a₀ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx_ge1 ha₀_neg.le
    nlinarith [upperGammaMoment_zero_pos (a₀ - 1) hx_pos, Real.exp_pos (-x)]
  have hexp_lt : Real.exp (-x) < K⁻¹ := by
    rw [Real.exp_neg, ← Real.exp_log hK_pos]
    exact inv_strictAnti₀ (Real.exp_pos _)
      (Real.exp_lt_exp.mpr (by linarith [le_max_right (1 : ℝ) (Real.log K + 1)]))
  have hlt : upperGammaMoment 0 a₀ x < Real.Gamma a₀ := (hU_hi.trans_lt hexp_lt).trans_le hG_lo
  simp only [paramBarrier]
  linarith [Real.log_lt_log (upperGammaMoment_zero_pos a₀ hx_pos) hlt]

/-! ### Main classification theorem for `x > 0` (DLMF §8.13(iii)(b)) -/

/-- **DLMF §8.13(iii)(b)**: for each `n ≥ 1`, there is `x*_n > 0` such that on the interval
`-2n < a < 1 - 2n`, Tricomi's function `a ↦ γ*(a, x)` has two simple real zeros for `0 < x < x*_n`,
one double real zero for `x = x*_n`, and no real zeros for `x > x*_n`. The derivatives are those
of the real-valued function `b ↦ Re γ*(b, x)`. -/
theorem tricomiIncompleteGamma_param_zeros {n : ℕ} (hn : 1 ≤ n) :
    ∃ xs : ℝ, 0 < xs ∧ ∀ x : ℝ, 0 < x →
      (x < xs → ∃ a₁ a₂ : ℝ, a₁ < a₂ ∧
        Set.ofPred (fun a : ℝ => a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
          tricomiIncompleteGamma a x = 0) = {a₁, a₂} ∧
        deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₁ ≠ 0 ∧
        deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₂ ≠ 0) ∧
      (x = xs → ∃ a₀ : ℝ,
        Set.ofPred (fun a : ℝ => a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
          tricomiIncompleteGamma a x = 0) = {a₀} ∧
        deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₀ = 0 ∧
        deriv (deriv fun b : ℝ => (tricomiIncompleteGamma b x).re) a₀ ≠ 0) ∧
      (xs < x →
        Set.ofPred (fun a : ℝ => a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
          tricomiIncompleteGamma a x = 0) = ∅) := by
  obtain ⟨x₁, hx₁_pos, hx₁_neg⟩ := exists_paramBarrierMin_neg hn
  obtain ⟨x₂, hx₂_pos, hx₂_pos'⟩ := exists_paramBarrierMin_pos hn
  have h12 : x₁ < x₂ := by
    by_contra hge
    push Not at hge
    have := (strictMonoOn_paramBarrierMin hn).monotoneOn hx₂_pos hx₁_pos hge
    linarith
  have hcont : ContinuousOn (paramBarrierMin n) (Icc x₁ x₂) :=
    (continuousOn_paramBarrierMin hn).mono fun x hx => hx₁_pos.trans_le hx.1
  obtain ⟨xs, hxs_Ioo, hxs_zero⟩ :=
    intermediate_value_Ioo h12.le hcont ⟨hx₁_neg, hx₂_pos'⟩
  have hxs_pos : 0 < xs := hx₁_pos.trans hxs_Ioo.1
  refine ⟨xs, hxs_pos, fun x hx => ?_⟩
  obtain ⟨a₀, ha₀, hmin₀, hd₀⟩ := exists_isMinOn_paramBarrier hn hx
  have hm_eq : paramBarrierMin n x = paramBarrier x a₀ :=
    paramBarrierMin_eq_of_isMinOn ha₀ hmin₀
  refine ⟨fun hlt => paramBarrier_two_zeros_of_min_neg hn hx ha₀ hd₀ ?_,
    fun heq => paramBarrier_double_zero_of_min_zero hn hx ha₀ hd₀ ?_,
    fun hgt => paramBarrier_no_zeros_of_min_pos hn hx hmin₀ ?_⟩
  · rw [← hm_eq, ← hxs_zero]
    exact strictMonoOn_paramBarrierMin hn hx hxs_pos hlt
  · rw [← hm_eq, heq, hxs_zero]
  · rw [← hm_eq, ← hxs_zero]
    exact strictMonoOn_paramBarrierMin hn hxs_pos hx hgt

end Complex

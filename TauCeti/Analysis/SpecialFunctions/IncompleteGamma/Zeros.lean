/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Tricomi
import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Complementary
import TauCeti.Analysis.SpecialFunctions.Gamma.Digamma.Real

/-!
# Zeros of Tricomi's function in its parameter

For a fixed real argument `x`, this file locates the real zeros of the parameter function
`a ↦ γ*(a, x)` of Tricomi's entire incomplete Gamma function (DLMF §8.13(iii)).

* At `x = 0`, `γ*(a, 0) = 1 / Γ(a + 1)` vanishes exactly at `a = −1, −2, …`; this holds for
  complex `a`.
* For `x < 0`, `γ*(·, x)` has exactly one real zero in each interval `−(k + 1) < a < −k`,
  `k ∈ ℕ`. Grouping these intervals in pairs gives DLMF §8.13(iii)(a): exactly two zeros in each
  interval `−2n < a < 2 − 2n`, `n ≥ 1`.
* For `x > 0`, on each band `-2n < a < 1 - 2n` (`n ≥ 1`) the function `a ↦ γ*(a, x)` is positive
  at both ends, where `γ*(-m, x) = xᵐ`, and its zeros in the band are governed by a threshold
  `x*ₙ > 0` (DLMF §8.13(iii)(b)): below `x*ₙ` there are exactly two zeros, both simple; at `x*ₙ`
  there is exactly one zero, which is double; above `x*ₙ` there is none.

For `x = −y < 0` and real `a ∉ −ℕ`, the series DLMF 8.7.1 reads
`Γ(a) γ*(a, x) = ∑ yᵏ / (k! (a + k))`, whose terms are real, positive multiples of `1 / (a + k)`.
On each interval `−(k + 1) < a < −k` every term is strictly decreasing in `a`, so the sum is
strictly decreasing there, which gives uniqueness. Existence follows from the intermediate value
theorem applied to `γ*(·, x)` on `[−(k + 1), −k]`, since `γ*(−n, x) = xⁿ` (DLMF 8.4.12) has
opposite signs at the two endpoints.

For real `a` and `x > 0`, the complementary relation `1 - x^a γ*(a, x) = Γ(a, x) / Γ(a)`
(DLMF 8.2.4–8.2.5, with the entire reciprocal of `Γ`) gives
`γ*(a, x) = x^{-a} (1 - Γ(a, x) / Γ(a))` with `Γ(a, x) = ∫_x^∞ t^{a-1} e^{-t} dt`. On the band
`Γ(a) > 0`, so the sign of `γ*(a, x)` is the sign of the log-gap `D(a, x) = log Γ(a) - log Γ(a, x)`,
which is strictly increasing in `x`.

The log-gap is strictly convex in `a` on the band. Indeed `(log Γ)'' = ψ'` and
`ψ'(a) ≥ 1/a² + 1/(a + 2n - 1)²` there, from the shifted recurrence of `ψ'`. On the other side,
`(log Γ(·, x))''` is the variance of `log t` under `t^{a-1} e^{-t} dt` on `(x, ∞)`; integrating
by parts shows that it is at most `2/a²` for `a < 0`. Since `|a + 2n - 1| < 1 < |a|`, the
difference is positive.

Strict convexity and the positive endpoint values give the two simple zeros wherever `D` takes a
negative value. The threshold is the supremum of the `x` at which `D(·, x)` takes one. A nested
compactness argument shows that at the threshold `D(·, x*ₙ) ≥ 0` vanishes somewhere, and there
its second derivative is positive.

## Main results

* `Complex.tricomiIncompleteGamma_zero_right_eq_zero_iff`: `γ*(a, 0) = 0` if and only if
  `a = −(n + 1)` for some `n : ℕ`.
* `Complex.existsUnique_tricomiIncompleteGamma_eq_zero_of_neg`: for `x < 0` and `k : ℕ`,
  `γ*(·, x)` has exactly one zero `a` with `−(k + 1) < a < −k`.
* `Complex.tricomiIncompleteGamma_param_zeros_of_neg`: for `x < 0` and `n ≥ 1`, the zeros of
  `γ*(·, x)` in `−2n < a < 2 − 2n` are exactly two points `a₁ < 1 − 2n < a₂`.
* `Complex.tricomiIncompleteGamma_param_zeros`: for `x > 0`, DLMF §8.13(iii)(b).

## References

* NIST Digital Library of Mathematical Functions, §8.13(iii), <https://dlmf.nist.gov/8.13>.
* K. S. Kölbig, *On the zeros of the incomplete gamma function*, Math. Comp. 26 (1972),
  751–755.
-/

public section

noncomputable section

open Set
open scoped Nat

namespace Complex

/-- Tricomi's function at `z = 0` vanishes exactly at the parameters `a = −1, −2, …`, the poles
of `Γ(a + 1)` (DLMF 8.4.2). -/
theorem tricomiIncompleteGamma_zero_right_eq_zero_iff {a : ℂ} :
    tricomiIncompleteGamma a 0 = 0 ↔ ∃ n : ℕ, a = -(n + 1) := by
  rw [tricomiIncompleteGamma_zero_right, inv_eq_zero, Gamma_eq_zero_iff]
  exact exists_congr fun n => ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩

/-- At a nonpositive integer `a = −n`, `γ*(a, x) = xⁿ` (DLMF 8.4.12) does not vanish for real
`x ≠ 0`. -/
private theorem tricomiIncompleteGamma_ofReal_ne_zero_of_eq_neg_natCast {x : ℝ} (hx : x ≠ 0)
    {a : ℝ} {n : ℕ} (ha : a = -n) : tricomiIncompleteGamma a x ≠ 0 := by
  rw [ha, ofReal_neg, ofReal_natCast, tricomiIncompleteGamma_neg_natCast]
  exact pow_ne_zero _ (ofReal_ne_zero.2 hx)

/-- For `x < 0`, the real sum `∑ (−x)ᵏ / (k! (a + k))` is strictly decreasing in `a` on each
interval `−(k + 1) < a < −k`: every term is a positive multiple of `1 / (a + j)`, and `a + j` keeps
its sign there. -/
private theorem hasSum_lt_of_mem_Ioo {x : ℝ} (hx : x < 0) {k : ℕ} {a b : ℝ}
    (ha : a ∈ Ioo (-(k + 1 : ℝ)) (-k)) (hb : b ∈ Ioo (-(k + 1 : ℝ)) (-k)) (hab : a < b)
    {sa sb : ℝ} (hsa : HasSum (fun j : ℕ => (-x) ^ j / (j ! * (a + j))) sa)
    (hsb : HasSum (fun j : ℕ => (-x) ^ j / (j ! * (b + j))) sb) : sb < sa := by
  have hlt : ∀ j : ℕ, (-x) ^ j / (j ! * (b + j)) < (-x) ^ j / (j ! * (a + j)) := fun j => by
    have hp : 0 < (a + j) * (b + j) := by
      rcases le_or_gt j k with hj | hj
      · have hj' : (j : ℝ) ≤ k := by exact_mod_cast hj
        exact mul_pos_of_neg_of_neg (by linarith [ha.2]) (by linarith [hb.2])
      · have hj' : (k : ℝ) + 1 ≤ j := by exact_mod_cast hj
        exact mul_pos (by linarith [ha.1]) (by linarith [hb.1])
    have hpow : 0 < (-x) ^ j := pow_pos (by linarith) j
    rw [← sub_neg, show (-x) ^ j / (j ! * (b + j)) - (-x) ^ j / (j ! * (a + j)) =
        (-x) ^ j / j ! * ((a - b) / ((a + j) * (b + j))) by
      field_simp [left_ne_zero_of_mul hp.ne', right_ne_zero_of_mul hp.ne']
      ring]
    exact mul_neg_of_pos_of_neg (by positivity) (div_neg_of_neg_of_pos (by linarith) hp)
  exact hasSum_lt (fun j => (hlt j).le) (hlt 0) hsb hsa

/-- `a ↦ Re γ*(a, x)` is continuous on `ℝ`. -/
private theorem continuous_re_tricomi_left (x : ℝ) :
    Continuous fun b : ℝ => (tricomiIncompleteGamma b x).re :=
  Complex.continuous_re.comp
    ((Complex.differentiable_tricomiIncompleteGamma_left x).continuous.comp
      Complex.continuous_ofReal)

/-- Existence of a zero of `γ*(·, x)` in `−(k + 1) < a < −k` for `x < 0`, by the intermediate
value theorem: `γ*(−n, x) = xⁿ` has opposite signs at the two endpoints. -/
private theorem exists_mem_Ioo_tricomiIncompleteGamma_eq_zero {x : ℝ} (hx : x < 0) (k : ℕ) :
    ∃ a ∈ Ioo (-(k + 1 : ℝ)) (-k), tricomiIncompleteGamma a x = 0 := by
  -- the real part of `γ*(·, x)` on the real line, which is `xⁿ` at `−n`
  set f : ℝ → ℝ := fun a => (tricomiIncompleteGamma a x).re with hf_def
  have hf : Continuous f := continuous_re_tricomi_left x
  have hval : ∀ n : ℕ, f (-n) = x ^ n := fun n => by
    simp [hf_def, ← ofReal_pow]
  have hx0 : x ≠ 0 := hx.ne
  have hsign : (0 : ℝ) ∈ uIcc (f (-(k + 1 : ℕ))) (f (-k)) := by
    rw [hval, hval, mem_uIcc, pow_succ]
    rcases Nat.even_or_odd k with hk | hk
    · have := hk.pow_pos hx0
      exact Or.inl ⟨by nlinarith, this.le⟩
    · have := hk.pow_neg hx
      exact Or.inr ⟨this.le, by nlinarith⟩
  obtain ⟨c, hc, hfc⟩ := intermediate_value_uIcc hf.continuousOn hsign
  -- `γ*(c, x)` is real, so the vanishing of its real part is enough
  have hre : (tricomiIncompleteGamma c x).re = 0 := hfc
  have hc0 : tricomiIncompleteGamma c x = 0 := by
    rw [← ofReal_tricomiIncompleteGamma_ofReal_re, hre, ofReal_zero]
  have hle : (-(k + 1 : ℕ) : ℝ) ≤ -k := by push_cast; linarith
  rw [uIcc_of_le hle] at hc
  refine ⟨c, ⟨lt_of_le_of_ne (by exact_mod_cast hc.1) ?_, lt_of_le_of_ne hc.2 ?_⟩, hc0⟩
  · rintro rfl
    exact tricomiIncompleteGamma_ofReal_ne_zero_of_eq_neg_natCast hx0 (n := k + 1)
      (by push_cast; ring) hc0
  · rintro rfl
    exact tricomiIncompleteGamma_ofReal_ne_zero_of_eq_neg_natCast hx0 rfl hc0

/-- Uniqueness of the zero of `γ*(·, x)` in `−(k + 1) < a < −k` for `x < 0`: there
`∑ (−x)ʲ / (j! (a + j)) = Γ(a) γ*(a, x)`, and the sum is strictly decreasing. -/
private theorem eq_of_tricomiIncompleteGamma_eq_zero_of_mem_Ioo {x : ℝ} (hx : x < 0) {k : ℕ}
    {a b : ℝ} (ha : a ∈ Ioo (-(k + 1 : ℝ)) (-k)) (hb : b ∈ Ioo (-(k + 1 : ℝ)) (-k))
    (ha0 : tricomiIncompleteGamma a x = 0) (hb0 : tricomiIncompleteGamma b x = 0) : a = b := by
  have hsum : ∀ c ∈ Ioo (-(k + 1 : ℝ)) (-k), tricomiIncompleteGamma c x = 0 →
      HasSum (fun j : ℕ => (-x) ^ j / (j ! * (c + j))) 0 := fun c hc hc0 => by
    have h :=
      hasSum_Gamma_mul_re_tricomiIncompleteGamma_ofReal (Real.ne_neg_natCast_of_mem_Ioo hc) x
    rwa [hc0, zero_re, mul_zero] at h
  rcases lt_trichotomy a b with h | h | h
  · exact absurd (hasSum_lt_of_mem_Ioo hx ha hb h (hsum a ha ha0) (hsum b hb hb0)) (lt_irrefl 0)
  · exact h
  · exact absurd (hasSum_lt_of_mem_Ioo hx hb ha h (hsum b hb hb0) (hsum a ha ha0)) (lt_irrefl 0)

/-- For `x < 0` and `k : ℕ`, Tricomi's function `γ*(·, x)` has exactly one zero in the interval
`−(k + 1) < a < −k`. -/
theorem existsUnique_tricomiIncompleteGamma_eq_zero_of_neg {x : ℝ} (hx : x < 0) (k : ℕ) :
    ∃! a : ℝ, a ∈ Ioo (-(k + 1 : ℝ)) (-k) ∧ tricomiIncompleteGamma a x = 0 := by
  obtain ⟨a, ha, ha0⟩ := exists_mem_Ioo_tricomiIncompleteGamma_eq_zero hx k
  exact ⟨a, ⟨ha, ha0⟩, fun b ⟨hb, hb0⟩ =>
    eq_of_tricomiIncompleteGamma_eq_zero_of_mem_Ioo hx hb ha hb0 ha0⟩

/-- DLMF §8.13(iii)(a): for `x < 0` and `n ≥ 1`, Tricomi's function `γ*(·, x)` has exactly two
zeros in the interval `−2n < a < 2 − 2n`, one on each side of `a = 1 − 2n`. -/
theorem tricomiIncompleteGamma_param_zeros_of_neg {x : ℝ} (hx : x < 0) {n : ℕ} (hn : 1 ≤ n) :
    ∃ a₁ a₂ : ℝ, a₁ < 1 - 2 * n ∧ 1 - 2 * n < a₂ ∧
      {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (2 - 2 * n) ∧ tricomiIncompleteGamma a x = 0} =
        {a₁, a₂} := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨a₁, ⟨ha₁, ha₁0⟩, hu₁⟩ :=
    existsUnique_tricomiIncompleteGamma_eq_zero_of_neg hx (2 * m + 1)
  obtain ⟨a₂, ⟨ha₂, ha₂0⟩, hu₂⟩ :=
    existsUnique_tricomiIncompleteGamma_eq_zero_of_neg hx (2 * m)
  push_cast at ha₁ ha₂ hu₁ hu₂
  refine ⟨a₁, a₂, by push_cast; linarith [ha₁.2], by push_cast; linarith [ha₂.1],
    Set.ext fun a => ⟨?_, ?_⟩⟩
  · rintro ⟨⟨h₁, h₂⟩, ha0⟩
    push_cast at h₁ h₂
    rcases lt_trichotomy a (-(2 * m + 1)) with h | h | h
    · exact Or.inl (hu₁ a ⟨⟨by linarith, by linarith⟩, ha0⟩)
    · exact absurd ha0 (tricomiIncompleteGamma_ofReal_ne_zero_of_eq_neg_natCast hx.ne
        (n := 2 * m + 1) (by rw [h]; push_cast; ring))
    · exact Or.inr (hu₂ a ⟨⟨by linarith, by linarith⟩, ha0⟩)
  · rintro (rfl | rfl)
    · exact ⟨⟨by push_cast; linarith [ha₁.1], by push_cast; linarith [ha₁.2]⟩, ha₁0⟩
    · exact ⟨⟨by push_cast; linarith [ha₂.1], by push_cast; linarith [ha₂.2]⟩, ha₂0⟩

end Complex

/-! ## The parameter zeros for a positive argument -/

open Filter Set MeasureTheory Asymptotics Real
open scoped Topology

namespace TauCeti

open Complex (tricomiIncompleteGamma)

/-! ### The logarithmic moments of the upper incomplete Gamma integral -/

/-- The integrand `(log t - log x)ᵏ t^{a-1} e^{-t}` of the `k`-th logarithmic moment of the upper
incomplete Gamma integral on `(x, ∞)`. -/
private def momentIntegrand (x : ℝ) (k : ℕ) (a t : ℝ) : ℝ :=
  (Real.log t - Real.log x) ^ k * (t ^ (a - 1) * Real.exp (-t))

/-- The moment `∫_x^∞ (log t - log x)ᵏ t^{a-1} e^{-t} dt`; for `k = 0` it is `Γ(a, x)`. -/
private def upperMoment (x : ℝ) (k : ℕ) (a : ℝ) : ℝ :=
  ∫ t in Ioi x, momentIntegrand x k a t

/-- The moment integrands decay like `e^{-t/2}`. -/
private theorem isBigO_momentIntegrand (x : ℝ) (k : ℕ) (a : ℝ) :
    momentIntegrand x k a =O[atTop] fun t => exp (-(1 / 2) * t) := by
  have hlog : (fun t : ℝ => log t - log x) =O[atTop] fun t => t :=
    ((isLittleO_log_rpow_atTop one_pos).isBigO.congr_right (fun t => rpow_one t)).sub
      (isLittleO_const_id_atTop _).isBigO
  have hpow : (fun t : ℝ => t ^ ((k : ℝ) + (a - 1)) * exp (-t)) =O[atTop]
      fun t => exp (-(1 / 2) * t) :=
    (Gamma_integrand_isLittleO _).isBigO.congr_left fun t => mul_comm _ _
  refine ((hlog.pow k).mul (isBigO_refl (fun t : ℝ => t ^ (a - 1) * exp (-t)) atTop)).trans ?_
  refine (hpow.congr' ?_ EventuallyEq.rfl)
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [rpow_add ht, rpow_natCast]
  ring

/-- The moment integrands are continuous on `[x, ∞)` for `x > 0`. -/
private theorem continuousOn_momentIntegrand {x : ℝ} (hx : 0 < x) (k : ℕ) (a : ℝ) :
    ContinuousOn (momentIntegrand x k a) (Ici x) := by
  intro t ht
  have ht0 : t ≠ 0 := (hx.trans_le ht).ne'
  exact (((continuousAt_log ht0).sub continuousAt_const).pow k |>.mul
    ((continuousAt_id.rpow_const (Or.inl ht0)).mul
      (continuous_exp.comp continuous_neg).continuousAt)).continuousWithinAt

/-- The moment integrands are integrable on `(x, ∞)` for `x > 0`. -/
private theorem integrableOn_momentIntegrand {x : ℝ} (hx : 0 < x) (k : ℕ) (a : ℝ) :
    IntegrableOn (momentIntegrand x k a) (Ioi x) :=
  integrable_of_isBigO_exp_neg (by norm_num) (continuousOn_momentIntegrand hx k a)
    (isBigO_momentIntegrand x k a)

/-- For `|a - a₀| < 1`, a moment integrand at `a` is dominated by the integrands at `a₀ ± 1`. -/
private theorem norm_momentIntegrand_le {x t : ℝ} (ht : 0 < t) (k : ℕ) {a a₀ : ℝ}
    (ha : |a - a₀| < 1) :
    ‖momentIntegrand x k a t‖ ≤
      ‖momentIntegrand x k (a₀ + 1) t‖ + ‖momentIntegrand x k (a₀ - 1) t‖ := by
  have hpow : t ^ (a - 1) ≤ t ^ (a₀ + 1 - 1) + t ^ (a₀ - 1 - 1) := by
    rw [abs_lt] at ha
    rcases le_or_gt 1 t with h1 | h1
    · have := rpow_le_rpow_of_exponent_le h1 (show a - 1 ≤ a₀ + 1 - 1 by linarith)
      linarith [rpow_nonneg ht.le (a₀ - 1 - 1)]
    · have := rpow_le_rpow_of_exponent_ge ht h1.le (show a₀ - 1 - 1 ≤ a - 1 by linarith)
      linarith [rpow_nonneg ht.le (a₀ + 1 - 1)]
  simp only [momentIntegrand, norm_mul, norm_pow, norm_of_nonneg (rpow_nonneg ht.le _),
    norm_of_nonneg (exp_pos _).le]
  have h0 : 0 ≤ ‖log t - log x‖ ^ k * rexp (-t) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hpow h0]

/-- The parameter derivative of a moment integrand: `∂ₐ t^{a-1} = log t · t^{a-1}`, with
`log t = (log t - log x) + log x`. -/
private theorem hasDerivAt_momentIntegrand {x t : ℝ} (ht : 0 < t) (k : ℕ) (a : ℝ) :
    HasDerivAt (fun b => momentIntegrand x k b t)
      (momentIntegrand x (k + 1) a t + log x * momentIntegrand x k a t) a := by
  have h := (((hasDerivAt_id a).sub_const 1).const_rpow ht).mul_const (exp (-t))
  convert h.const_mul ((log t - log x) ^ k) using 1
  · funext b
    simp only [momentIntegrand, id]
  · simp only [momentIntegrand, id]
    ring

/-- Differentiation under the integral sign: `∂ₐ Vₖ = Vₖ₊₁ + log x · Vₖ`. -/
private theorem hasDerivAt_upperMoment {x : ℝ} (hx : 0 < x) (k : ℕ) (a₀ : ℝ) :
    HasDerivAt (upperMoment x k)
      (upperMoment x (k + 1) a₀ + log x * upperMoment x k a₀) a₀ := by
  have hint := fun j b => integrableOn_momentIntegrand hx j b
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi x))
    (F := fun b t => momentIntegrand x k b t)
    (F' := fun b t => momentIntegrand x (k + 1) b t + log x * momentIntegrand x k b t)
    (bound := fun t => (‖momentIntegrand x (k + 1) (a₀ + 1) t‖ +
        ‖momentIntegrand x (k + 1) (a₀ - 1) t‖) + ‖log x‖ * (‖momentIntegrand x k (a₀ + 1) t‖ +
        ‖momentIntegrand x k (a₀ - 1) t‖))
    (x₀ := a₀) (Metric.ball_mem_nhds a₀ one_pos)
    (Eventually.of_forall fun b => (hint k b).aestronglyMeasurable) (hint k a₀)
    (((hint (k + 1) a₀).add ((hint k a₀).const_mul _)).aestronglyMeasurable) ?_ ?_ ?_
  · rw [integral_add (hint (k + 1) a₀) ((hint k a₀).const_mul _), integral_const_mul] at key
    exact key.2
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht b hb => ?_
    have ht0 : 0 < t := hx.trans ht
    rw [Metric.mem_ball, dist_eq_norm, norm_eq_abs] at hb
    refine (norm_add_le _ _).trans (add_le_add (norm_momentIntegrand_le ht0 _ hb) ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_momentIntegrand_le ht0 _ hb) (norm_nonneg _)
  · exact (((hint _ _).norm.add (hint _ _).norm).add
      (((hint _ _).norm.add (hint _ _).norm).const_mul _))
  · exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht b _ =>
      hasDerivAt_momentIntegrand (hx.trans ht) k b

/-- The moment integrands are nonnegative on `[x, ∞)`. -/
private theorem momentIntegrand_nonneg {x t : ℝ} (hx : 0 < x) (ht : x ≤ t) (k : ℕ) (a : ℝ) :
    0 ≤ momentIntegrand x k a t := by
  have := log_le_log hx ht
  have ht0 := hx.trans_le ht
  unfold momentIntegrand
  have : 0 ≤ log t - log x := by linarith
  positivity

/-- For `x ≥ 0` the upper incomplete Gamma function `Γ(a, x)` is the real zeroth moment. -/
private theorem upperIncompleteGamma_ofReal_eq {x : ℝ} (hx : 0 ≤ x) (a : ℝ) :
    Complex.upperIncompleteGamma a x = ((upperMoment x 0 a : ℝ) : ℂ) := by
  simp [Complex.upperIncompleteGamma_ofReal_eq_ofReal_integral a hx, upperMoment, momentIntegrand]

/-- For `x ≥ 0` the zeroth moment is the upper incomplete Gamma function `Γ(a, x)`. -/
private theorem re_upperIncompleteGamma_ofReal {x : ℝ} (hx : 0 ≤ x) (a : ℝ) :
    (Complex.upperIncompleteGamma a x).re = upperMoment x 0 a := by
  rw [upperIncompleteGamma_ofReal_eq hx, Complex.ofReal_re]

/-- The moments are nonnegative. -/
private theorem upperMoment_nonneg {x : ℝ} (hx : 0 < x) (k : ℕ) (a : ℝ) : 0 ≤ upperMoment x k a :=
  setIntegral_nonneg measurableSet_Ioi fun _ ht => momentIntegrand_nonneg hx (le_of_lt ht) k a

/-- `Complex.upperIncompleteGamma_ofReal_re_pos` for the zeroth moment. -/
private theorem upperMoment_zero_pos {x : ℝ} (hx : 0 < x) (a : ℝ) : 0 < upperMoment x 0 a :=
  re_upperIncompleteGamma_ofReal hx.le a ▸ Complex.upperIncompleteGamma_ofReal_re_pos a hx

/-- The moment integrands tend to `0` at infinity. -/
private theorem tendsto_momentIntegrand_atTop (x : ℝ) (k : ℕ) (a : ℝ) :
    Tendsto (momentIntegrand x k a) atTop (𝓝 0) :=
  (isBigO_momentIntegrand x k a).trans_tendsto <| tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1 / 2 : ℝ) < 0))

/-- Integration by parts of `d/dt ((log t - log x)^{j+1} t^a e^{-t})` over `(x, ∞)`:
`(j + 1) Vⱼ(a) + a Vⱼ₊₁(a) = Vⱼ₊₁(a + 1)`. -/
private theorem upperMoment_recurrence {x : ℝ} (hx : 0 < x) (j : ℕ) (a : ℝ) :
    (j + 1) * upperMoment x j a + a * upperMoment x (j + 1) a = upperMoment x (j + 1) (a + 1) := by
  have hint := fun k b => integrableOn_momentIntegrand hx k b
  have hderiv : ∀ t ∈ Ioi x, HasDerivAt (momentIntegrand x (j + 1) (a + 1))
      ((j + 1) * momentIntegrand x j a t + a * momentIntegrand x (j + 1) a t -
        momentIntegrand x (j + 1) (a + 1) t) t := by
    intro t ht
    have ht0 : 0 < t := hx.trans ht
    have h := ((((hasDerivAt_log ht0.ne').sub_const (log x)).pow (j + 1)).mul
      (hasDerivAt_rpow_const (p := a + 1 - 1) (Or.inl ht0.ne'))).mul (hasDerivAt_neg t).exp
    convert h using 1
    · funext s
      simp only [momentIntegrand, add_sub_cancel_right, Pi.mul_apply, Pi.pow_apply]
      ring
    · simp only [momentIntegrand, add_sub_cancel_right, Nat.cast_add, Nat.cast_one,
        Nat.add_sub_cancel, rpow_sub_one ht0.ne', Pi.mul_apply, Pi.pow_apply]
      field_simp
      ring
  have hi1 : IntegrableOn (fun t => (j + 1 : ℝ) * momentIntegrand x j a t) (Ioi x) :=
    (hint j a).const_mul _
  have hi2 : IntegrableOn (fun t => a * momentIntegrand x (j + 1) a t) (Ioi x) :=
    (hint (j + 1) a).const_mul _
  have hi12 : IntegrableOn (fun t => (j + 1 : ℝ) * momentIntegrand x j a t +
      a * momentIntegrand x (j + 1) a t) (Ioi x) := hi1.add hi2
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto
    ((continuousOn_momentIntegrand hx _ _).continuousWithinAt self_mem_Ici) hderiv
    (hi12.sub (hint (j + 1) (a + 1))) (tendsto_momentIntegrand_atTop x (j + 1) (a + 1))
  rw [integral_sub hi12 (hint (j + 1) (a + 1)), integral_add hi1 hi2,
    integral_const_mul, integral_const_mul] at hftc
  rw [show momentIntegrand x (j + 1) (a + 1) x = 0 by simp [momentIntegrand]] at hftc
  unfold upperMoment
  linarith

/-- The variance of `log t` under `t ^ (a - 1) e^{-t}` on `(x, ∞)` is at most `2 / a²` for
`a < 0`. -/
private theorem upperMoment_variance_le {x : ℝ} (hx : 0 < x) {a : ℝ} (ha : a < 0) :
    a ^ 2 * (upperMoment x 2 a * upperMoment x 0 a - upperMoment x 1 a ^ 2) ≤
      2 * upperMoment x 0 a ^ 2 := by
  have h0 := upperMoment_recurrence hx 0 a
  have h1 := upperMoment_recurrence hx 1 a
  push_cast at h0 h1
  -- the recurrence and `Vⱼ(a + 1) ≥ 0` give `-a V₁ ≤ V₀` and `-a V₂ ≤ 2 V₁`
  have e1 : -a * upperMoment x 1 a ≤ upperMoment x 0 a := by
    linarith [upperMoment_nonneg hx 1 (a + 1)]
  have e2 : -a * upperMoment x 2 a ≤ 2 * upperMoment x 1 a := by
    linarith [upperMoment_nonneg hx 2 (a + 1)]
  have e3 : a ^ 2 * upperMoment x 2 a ≤ 2 * upperMoment x 0 a := by
    nlinarith [mul_le_mul_of_nonneg_left e2 (neg_nonneg.2 ha.le)]
  nlinarith [sq_nonneg (a * upperMoment x 1 a), upperMoment_nonneg hx 0 a]

/-! ### The regularized function `P(a, x)` on the positive axis -/

open Complex in
/-- For real `a` and `x > 0`: `P(a, x) = 1 - Γ(a, x) / Γ(a)`, with the entire reciprocal of `Γ`;
hence `γ*(a, x) = x^{-a} (1 - Γ(a, x) / Γ(a))`. -/
private theorem tricomi_ofReal_eq (a : ℝ) {x : ℝ} (hx : 0 < x) :
    tricomiIncompleteGamma a x =
      ((x ^ (-a) * (1 - (Complex.upperIncompleteGamma a x).re * (Real.Gamma a)⁻¹) : ℝ) : ℂ) := by
  have hQ := regularizedGammaQ_eq_upperIncompleteGamma_div a (ofReal_mem_slitPlane.2 hx)
  rw [regularizedGammaQ_def, regularizedGamma_def, upperIncompleteGamma_ofReal_eq hx.le,
    Gamma_ofReal] at hQ
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have hpow : (x : ℂ) ^ (-(a : ℂ)) * (x : ℂ) ^ (a : ℂ) = 1 := by
    rw [cpow_neg, inv_mul_cancel₀ (cpow_ne_zero_iff.2 (Or.inl hx'))]
  rw [re_upperIncompleteGamma_ofReal hx.le, ofReal_mul, ofReal_cpow hx.le, ofReal_neg, ofReal_sub,
    ofReal_one, ofReal_mul, ofReal_inv]
  linear_combination -(x : ℂ) ^ (-(a : ℂ)) * hQ - tricomiIncompleteGamma a x * hpow

/-- The log-gap `D(a, x) = log Γ(a) - log Γ(a, x)`. On the band it has the sign of `γ*(a, x)`. -/
private def logGap (x a : ℝ) : ℝ :=
  Real.log (Real.Gamma a) - Real.log (Complex.upperIncompleteGamma a x).re

/-- The parameter derivative `ψ(a) - V₁/V₀ - log x` of the log-gap. -/
private def logGapDeriv (x a : ℝ) : ℝ :=
  Real.digamma a - upperMoment x 1 a / upperMoment x 0 a - Real.log x

/-- The second parameter derivative `ψ'(a) - (V₂ V₀ - V₁²)/V₀²` of the log-gap. -/
private def logGapDeriv2 (x a : ℝ) : ℝ :=
  deriv Real.digamma a -
    (upperMoment x 2 a * upperMoment x 0 a - upperMoment x 1 a ^ 2) / upperMoment x 0 a ^ 2

/-- The band `(-2n, 1 - 2n)` contains no pole of `Γ`: its shift by `-1` lies between the
consecutive poles `-(2n + 1)` and `-2n`. -/
private theorem ne_neg_natCast_of_mem_band {n : ℕ} {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n)) (m : ℕ) : a ≠ -(m : ℝ) := fun h =>
  Real.ne_neg_natCast_of_mem_Ioo (k := 2 * n) (a := a - 1)
    ⟨by push_cast; linarith [ha.1], by push_cast; linarith [ha.2]⟩ (m + 1) (by push_cast; linarith)

/-- The parameter derivative of the log-gap. -/
private theorem hasDerivAt_logGap {x : ℝ} (hx : 0 < x) {a : ℝ}
    (ha : ∀ m : ℕ, a ≠ -(m : ℝ)) :
    HasDerivAt (logGap x) (logGapDeriv x a) a := by
  have hV := upperMoment_zero_pos hx a
  have h := (Real.hasDerivAt_log_Gamma ha).sub
    ((hasDerivAt_upperMoment hx 0 a).log hV.ne')
  convert h using 1
  · funext b
    simp only [logGap, re_upperIncompleteGamma_ofReal hx.le, Pi.sub_apply, Function.comp_apply]
  · simp only [logGapDeriv, zero_add]
    field_simp
    ring

/-- The second parameter derivative of the log-gap. -/
private theorem hasDerivAt_logGapDeriv {x : ℝ} (hx : 0 < x) {a : ℝ}
    (ha : ∀ m : ℕ, a ≠ -(m : ℝ)) :
    HasDerivAt (logGapDeriv x) (logGapDeriv2 x a) a := by
  have hV := upperMoment_zero_pos hx a
  have hd := (Real.differentiableAt_digamma ha).hasDerivAt
  have h := (hd.sub ((hasDerivAt_upperMoment hx 1 a).div (hasDerivAt_upperMoment hx 0 a)
    hV.ne')).sub_const (Real.log x)
  convert h using 1
  · funext b
    simp only [logGapDeriv, Pi.sub_apply, Pi.div_apply]
  · simp only [logGapDeriv2]
    field_simp
    ring

/-- **The log-gap is strictly convex on the band**: `ψ'(a) ≥ 1/a² + 1/(a + 2n - 1)²`, the variance
term is at most `2/a²`, and `(a + 2n - 1)² < 1 < a²`. -/
private theorem logGapDeriv2_pos {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n)) : 0 < logGapDeriv2 x a := by
  have hV := upperMoment_zero_pos hx a
  -- `ψ'(a) = ψ'(a + 2n) + ∑_{k < 2n} 1 / (a + k)²` with `ψ'(a + 2n) ≥ 0`
  have hrec := Real.deriv_digamma_apply_add_nat (ne_neg_natCast_of_mem_band ha) (2 * n)
  have hψ := Real.deriv_digamma_pos (x := a + (2 * n : ℕ)) fun m h => by
    push_cast at h
    linarith [ha.1, (m.cast_nonneg : (0 : ℝ) ≤ m)]
  have ha0 : a < 0 := by linarith [ha.2, (show (1 : ℝ) ≤ n by exact_mod_cast hn)]
  have hvar := upperMoment_variance_le hx ha0
  -- the terms `k = 0` and `k = 2n - 1` of the sum
  obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 1 := ⟨2 * n - 1, by omega⟩
  have hm0 : m ≠ 0 := by omega
  have hsum : (a ^ 2)⁻¹ + ((a + m) ^ 2)⁻¹ ≤ ∑ k ∈ Finset.range (2 * n), ((a + k) ^ 2)⁻¹ := by
    have hsub : ({0, m} : Finset ℕ) ⊆ Finset.range (2 * n) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rw [Finset.mem_range]
      omega
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k : ℕ => ((a + k) ^ 2)⁻¹) hsub
      (fun k _ _ => by positivity)
    rwa [Finset.sum_pair (Ne.symm hm0), Nat.cast_zero, add_zero] at this
  have hmR : (m : ℝ) = 2 * n - 1 := by
    have : ((2 * n : ℕ) : ℝ) = m + 1 := by exact_mod_cast hm
    push_cast at this
    linarith
  -- `(a + 2n - 1)² < 1 < a²`
  have hlt : (a ^ 2)⁻¹ < ((a + m) ^ 2)⁻¹ := by
    have h1 : (a + m) ^ 2 < 1 := by
      rw [hmR]; nlinarith [ha.1, ha.2]
    have h2 : 1 < a ^ 2 := by
      nlinarith [ha.2, (show (1 : ℝ) ≤ n by exact_mod_cast hn)]
    have h3 : 0 < (a + m) ^ 2 := by
      have : a + m ≠ 0 := by rw [hmR]; intro h; linarith [ha.1, ha.2]
      exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 this))
    exact inv_strictAnti₀ h3 (h1.trans h2)
  have hfrac : (upperMoment x 2 a * upperMoment x 0 a - upperMoment x 1 a ^ 2) /
      upperMoment x 0 a ^ 2 ≤ 2 * (a ^ 2)⁻¹ := by
    have h2 : 0 < a ^ 2 := by nlinarith
    have hX : upperMoment x 2 a * upperMoment x 0 a - upperMoment x 1 a ^ 2 ≤
        2 * upperMoment x 0 a ^ 2 / a ^ 2 := by
      rw [le_div_iff₀ h2]
      linarith
    rw [div_le_iff₀ (pow_pos hV 2)]
    calc _ ≤ 2 * upperMoment x 0 a ^ 2 / a ^ 2 := hX
      _ = 2 * (a ^ 2)⁻¹ * upperMoment x 0 a ^ 2 := by ring
  simp only [logGapDeriv2]
  linarith

/-- The log-gap is strictly convex in `a` on the band. -/
private theorem strictConvexOn_logGap {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    StrictConvexOn ℝ (Ioo (-2 * (n : ℝ)) (1 - 2 * n)) (logGap x) := by
  refine strictConvexOn_of_deriv2_pos' (convex_Ioo _ _)
    (fun a ha => (hasDerivAt_logGap hx (ne_neg_natCast_of_mem_band ha)).continuousAt
      |>.continuousWithinAt) fun a ha => ?_
  have hd : deriv (logGap x) =ᶠ[𝓝 a] logGapDeriv x := by
    filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
    exact (hasDerivAt_logGap hx (ne_neg_natCast_of_mem_band hb)).deriv
  rw [Function.iterate_succ_apply, Function.iterate_one, hd.deriv_eq,
    (hasDerivAt_logGapDeriv hx (ne_neg_natCast_of_mem_band ha)).deriv]
  exact logGapDeriv2_pos hx hn ha

open Complex in
/-- On the band, `γ*(a, x) = x^{-a} (1 - e^{-D(a, x)})` for `x > 0`. -/
private theorem tricomi_eq_ofReal_logGap {x : ℝ} (hx : 0 < x) {n : ℕ} {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n)) :
    tricomiIncompleteGamma a x = ((x ^ (-a) * (1 - Real.exp (-logGap x a)) : ℝ) : ℂ) := by
  rw [tricomi_ofReal_eq a hx, logGap, re_upperIncompleteGamma_ofReal hx.le, neg_sub, Real.exp_sub,
    Real.exp_log (upperMoment_zero_pos hx a),
    Real.exp_log (Real.Gamma_pos_of_mem_Ioo ⟨ha.1, by linarith [ha.2]⟩), div_eq_mul_inv]

/-- The parameter derivative of `x^{-a} (1 - e^{-D(a, x)})`. -/
private theorem hasDerivAt_rpow_mul_logGap {x : ℝ} (hx : 0 < x) {a : ℝ}
    (ha : ∀ m : ℕ, a ≠ -(m : ℝ)) :
    HasDerivAt (fun b => x ^ (-b) * (1 - Real.exp (-logGap x b)))
      (x ^ (-a) * (logGapDeriv x a * Real.exp (-logGap x a) -
        Real.log x * (1 - Real.exp (-logGap x a)))) a := by
  have h := ((hasDerivAt_neg a).const_rpow hx).mul
    ((hasDerivAt_logGap hx ha).neg.exp.const_sub 1)
  convert h using 1
  simp only [Pi.neg_apply]
  ring

/-- At a point where `D` and `∂ₐD` vanish, the second parameter derivative of
`x^{-a} (1 - e^{-D(a, x)})` is `x^{-a} ∂ₐ²D`. -/
private theorem hasDerivAt_rpow_mul_logGapDeriv {x : ℝ} (hx : 0 < x) {a : ℝ}
    (ha : ∀ m : ℕ, a ≠ -(m : ℝ)) (h0 : logGap x a = 0)
    (h1 : logGapDeriv x a = 0) :
    HasDerivAt (fun b => x ^ (-b) * (logGapDeriv x b * Real.exp (-logGap x b) -
        Real.log x * (1 - Real.exp (-logGap x b))))
      (x ^ (-a) * logGapDeriv2 x a) a := by
  have hD := hasDerivAt_logGap hx ha
  have h := ((hasDerivAt_neg a).const_rpow hx).mul
    (((hasDerivAt_logGapDeriv hx ha).mul hD.neg.exp).sub
      ((hD.neg.exp.const_sub 1).const_mul (Real.log x)))
  convert h using 1
  simp only [Pi.neg_apply, Pi.mul_apply, Pi.sub_apply, h0, h1]
  simp

/-- On the band, `Re γ*(a, x) = x^{-a} (1 - e^{-D(a, x)})` for `x > 0`. -/
private theorem re_tricomi_eq {x : ℝ} (hx : 0 < x) {n : ℕ} {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n)) :
    (tricomiIncompleteGamma a x).re = x ^ (-a) * (1 - Real.exp (-logGap x a)) := by
  rw [tricomi_eq_ofReal_logGap hx ha, Complex.ofReal_re]

/-- On the band, `γ*(a, x)` vanishes exactly where the log-gap does. -/
private theorem tricomi_eq_zero_iff {x : ℝ} (hx : 0 < x) {n : ℕ} {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n)) :
    tricomiIncompleteGamma a x = 0 ↔ logGap x a = 0 := by
  rw [tricomi_eq_ofReal_logGap hx ha, Complex.ofReal_eq_zero,
    mul_eq_zero, sub_eq_zero, eq_comm (a := (1 : ℝ)), Real.exp_eq_one_iff, neg_eq_zero]
  exact or_iff_right (rpow_pos_of_pos hx _).ne'

/-- On the band, `γ*(a, x)` is negative exactly where the log-gap is. -/
private theorem re_tricomi_neg_iff {x : ℝ} (hx : 0 < x) {n : ℕ} {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n)) :
    (tricomiIncompleteGamma a x).re < 0 ↔ logGap x a < 0 := by
  have hp := rpow_pos_of_pos hx (-a)
  rw [re_tricomi_eq hx ha, mul_neg_iff, sub_neg, Real.one_lt_exp_iff, neg_pos]
  simp [hp, hp.not_gt]

/-- `x ↦ Re γ*(a, x)` is continuous on `ℝ`. -/
private theorem continuous_re_tricomi_right (a : ℝ) :
    Continuous fun y : ℝ => (tricomiIncompleteGamma a y).re :=
  Complex.continuous_re.comp
    ((Complex.differentiable_tricomiIncompleteGamma a).continuous.comp Complex.continuous_ofReal)

/-- `γ*(-m, x) = xᵐ > 0` for `x > 0`. -/
private theorem re_tricomi_neg_natCast (m : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < (tricomiIncompleteGamma (-(m : ℝ)) x).re := by
  rw [Complex.ofReal_natCast, Complex.tricomiIncompleteGamma_neg_natCast,
    ← Complex.ofReal_pow, Complex.ofReal_re]
  positivity

/-- The parameter derivative of `Re γ*(·, x)` on the band. -/
private theorem deriv_re_tricomi {x : ℝ} (hx : 0 < x) {n : ℕ} {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n)) :
    deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a =
      x ^ (-a) * (logGapDeriv x a * Real.exp (-logGap x a) -
        Real.log x * (1 - Real.exp (-logGap x a))) := by
  rw [← (hasDerivAt_rpow_mul_logGap hx (ne_neg_natCast_of_mem_band ha)).deriv]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
  exact re_tricomi_eq hx hb

/-- The second parameter derivative of `Re γ*(·, x)` at a common zero of `D` and `∂ₐD`. -/
private theorem deriv_deriv_re_tricomi {x : ℝ} (hx : 0 < x) {n : ℕ} {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n)) (h0 : logGap x a = 0)
    (h1 : logGapDeriv x a = 0) :
    deriv (deriv fun b : ℝ => (tricomiIncompleteGamma b x).re) a =
      x ^ (-a) * logGapDeriv2 x a := by
  rw [← (hasDerivAt_rpow_mul_logGapDeriv hx (ne_neg_natCast_of_mem_band ha) h0 h1).deriv]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
  exact deriv_re_tricomi hx hb

/-- The log-gap is strictly increasing in `x`. -/
private theorem logGap_lt_logGap {x y : ℝ} (hx : 0 < x) (hxy : x < y) (a : ℝ) :
    logGap x a < logGap y a := by
  rw [logGap, logGap]
  have := Real.log_lt_log (Complex.upperIncompleteGamma_ofReal_re_pos a (hx.trans hxy))
    (Complex.strictAntiOn_upperIncompleteGamma_ofReal_re a hx (hx.trans hxy) hxy)
  linarith

/-- On the band, `Re γ*(a, x)` vanishes exactly where the log-gap does. -/
private theorem re_tricomi_eq_zero_iff {x : ℝ} (hx : 0 < x) {n : ℕ} {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n)) :
    (tricomiIncompleteGamma a x).re = 0 ↔ logGap x a = 0 := by
  rw [← tricomi_eq_zero_iff hx ha, tricomi_eq_ofReal_logGap hx ha, Complex.ofReal_re,
    Complex.ofReal_eq_zero]

/-- By strict convexity, the log-gap is negative strictly between two points where it is `≤ 0`. -/
private theorem logGap_neg_of_lt_of_lt {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) {p r q : ℝ}
    (hp : p ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n)) (hq : q ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n))
    (hpr : p < r) (hrq : r < q) (hDp : logGap x p ≤ 0) (hDq : logGap x q ≤ 0) :
    logGap x r < 0 := by
  have h := (strictConvexOn_logGap hx hn).lt_on_openSegment hp hq (hpr.trans hrq).ne
    (by rw [openSegment_eq_Ioo (hpr.trans hrq)]; exact ⟨hpr, hrq⟩)
  exact h.trans_le (max_le hDp hDq)

/-- `γ*(-2n, x) = x^{2n} > 0` for `x > 0`. -/
private theorem re_tricomi_left_endpoint_pos (n : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < (tricomiIncompleteGamma ((-2 * n : ℝ) : ℂ) x).re := by
  have h := re_tricomi_neg_natCast (2 * n) hx
  have hc : -(((2 * n : ℕ) : ℝ) : ℂ) = ((-2 * n : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hc] at h
  exact h

/-- `γ*(1 - 2n, x) = x^{2n - 1} > 0` for `x > 0`. -/
private theorem re_tricomi_right_endpoint_pos {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    0 < (tricomiIncompleteGamma ((1 - 2 * n : ℝ) : ℂ) x).re := by
  have h := re_tricomi_neg_natCast (2 * n - 1) hx
  have hc : -(((2 * n - 1 : ℕ) : ℝ) : ℂ) = ((1 - 2 * n : ℝ) : ℂ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hc] at h
  exact h

/-- Two zeros on each side of a point where the log-gap is negative. -/
private theorem exists_zeros_of_logGap_neg {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n)) (hneg : logGap x a < 0) :
    ∃ a₁ a₂ : ℝ, a₁ ∈ Ioo (-2 * (n : ℝ)) a ∧ a₂ ∈ Ioo a (1 - 2 * n) ∧
      logGap x a₁ = 0 ∧ logGap x a₂ = 0 ∧ logGapDeriv x a₁ < 0 ∧ 0 < logGapDeriv x a₂ ∧
      (∀ b ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n), logGap x b ≤ 0 → b ∈ Icc a₁ a₂) ∧
      (∀ b ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n), logGap x b = 0 → b = a₁ ∨ b = a₂) := by
  set I := Ioo (-2 * (n : ℝ)) (1 - 2 * n)
  have hf := (Complex.continuous_re_tricomi_left x).continuousOn (s := Icc (-2 * (n : ℝ)) a)
  have hf' := (Complex.continuous_re_tricomi_left x).continuousOn (s := Icc a (1 - 2 * (n : ℝ)))
  have hfa := (re_tricomi_neg_iff hx ha).2 hneg
  obtain ⟨a₁, ha₁, hz₁⟩ := intermediate_value_Ioo' ha.1.le hf
    ⟨hfa, re_tricomi_left_endpoint_pos n hx⟩
  obtain ⟨a₂, ha₂, hz₂⟩ := intermediate_value_Ioo ha.2.le hf'
    ⟨hfa, re_tricomi_right_endpoint_pos hn hx⟩
  have ha₁I : a₁ ∈ I := ⟨ha₁.1, ha₁.2.trans ha.2⟩
  have ha₂I : a₂ ∈ I := ⟨ha.1.trans ha₂.1, ha₂.2⟩
  have hD₁ := (re_tricomi_eq_zero_iff hx ha₁I).1 hz₁
  have hD₂ := (re_tricomi_eq_zero_iff hx ha₂I).1 hz₂
  have hconv := (strictConvexOn_logGap hx hn).convexOn
  refine ⟨a₁, a₂, ha₁, ha₂, hD₁, hD₂, ?_, ?_, ?_, ?_⟩
  · have h := hconv.le_slope_of_hasDerivAt ha₁I ha ha₁.2
      (hasDerivAt_logGap hx (ne_neg_natCast_of_mem_band ha₁I))
    rw [slope_def_field, hD₁, sub_zero] at h
    exact h.trans_lt (div_neg_of_neg_of_pos hneg (sub_pos.2 ha₁.2))
  · have h := hconv.slope_le_of_hasDerivAt ha ha₂I ha₂.1
      (hasDerivAt_logGap hx (ne_neg_natCast_of_mem_band ha₂I))
    rw [slope_def_field, hD₂, zero_sub] at h
    exact (div_pos (neg_pos.2 hneg) (sub_pos.2 ha₂.1)).trans_le h
  · intro b hb hDb
    refine ⟨not_lt.1 fun hlt => ?_, not_lt.1 fun hlt => ?_⟩
    · exact (logGap_neg_of_lt_of_lt hx hn hb ha hlt ha₁.2 hDb hneg.le).ne hD₁
    · exact (logGap_neg_of_lt_of_lt hx hn ha hb ha₂.1 hlt hneg.le hDb).ne hD₂
  · intro b hb hDb
    rcases lt_trichotomy b a with hlt | rfl | hgt
    · left
      rcases lt_trichotomy b a₁ with h | h | h
      · exact absurd hD₁ (logGap_neg_of_lt_of_lt hx hn hb ha h ha₁.2 hDb.le hneg.le).ne
      · exact h
      · exact absurd hDb (logGap_neg_of_lt_of_lt hx hn ha₁I ha h hlt hD₁.le hneg.le).ne
    · exact absurd hDb hneg.ne
    · right
      rcases lt_trichotomy b a₂ with h | h | h
      · exact absurd hDb (logGap_neg_of_lt_of_lt hx hn ha ha₂I hgt h hneg.le hD₂.le).ne
      · exact h
      · exact absurd hD₂ (logGap_neg_of_lt_of_lt hx hn ha hb ha₂.1 h hneg.le hDb.le).ne

/-- Large `x` leaves no negative value of the log-gap. -/
private theorem exists_logGap_nonneg {n : ℕ} (hn : 1 ≤ n) :
    ∃ X : ℝ, 0 < X ∧ ∀ x, X ≤ x → ∀ a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n), 0 ≤ logGap x a := by
  refine ⟨max 1 (Real.log (2 * n).factorial), by positivity, fun x hx a ha => ?_⟩
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hfac : (0 : ℝ) < (2 * n).factorial := by positivity
  have ha1 : a ≤ 1 := by linarith [ha.2, (show (0 : ℝ) ≤ n by positivity)]
  have hV : (Complex.upperIncompleteGamma a x).re ≤ Real.exp (-x) :=
    (Complex.upperIncompleteGamma_ofReal_re_le_rpow_mul_exp_neg ha1 (by linarith)).trans
      (mul_le_of_le_one_left (Real.exp_pos _).le
        (rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)))
  have hexp : Real.exp (-x) ≤ 1 / ((2 * n).factorial : ℝ) := by
    rw [one_div, ← Real.exp_log hfac, ← Real.exp_neg]
    exact Real.exp_le_exp.2 (by linarith [le_max_right 1 (Real.log (2 * n).factorial)])
  have hπ : 1 / ((2 * n).factorial : ℝ) ≤ π / ((2 * n).factorial : ℝ) :=
    div_le_div_of_nonneg_right (by linarith [Real.two_le_pi]) hfac.le
  rw [logGap, sub_nonneg]
  exact Real.log_le_log (Complex.upperIncompleteGamma_ofReal_re_pos a (by linarith))
    (hV.trans (hexp.trans (hπ.trans
      (Real.pi_div_factorial_le_Gamma_of_mem_Ioo hn ⟨ha.1, by linarith [ha.2]⟩))))

/-- Small `x` gives a negative value of the log-gap. -/
private theorem exists_logGap_neg {n : ℕ} (hn : 1 ≤ n) :
    ∃ x : ℝ, 0 < x ∧ ∃ a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n), logGap x a < 0 := by
  set a : ℝ := 1 / 2 - 2 * n
  have ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n) := ⟨by simp only [a]; linarith,
    by simp only [a]; linarith⟩
  have h0 : (tricomiIncompleteGamma a (0 : ℝ)).re < 0 := by
    rw [Complex.ofReal_zero, Complex.tricomiIncompleteGamma_zero_right,
      show (a : ℂ) + 1 = ((a + 1 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
      ← Complex.ofReal_inv, Complex.ofReal_re, inv_lt_zero]
    refine Real.Gamma_neg_of_mem_Ioo (n := n - 1) ⟨?_, ?_⟩ <;>
      · rw [Nat.cast_sub hn]; push_cast; simp only [a]; linarith
  have hev := (continuous_re_tricomi_right a).continuousAt.eventually_lt continuousAt_const h0
  obtain ⟨x, hx, hx0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
  exact ⟨x, hx0, a, ha, (re_tricomi_neg_iff hx0 ha).1 hx⟩

/-- On the band, `γ*(a, x) ≤ 0` exactly where the log-gap is `≤ 0`. -/
private theorem re_tricomi_nonpos_iff {x : ℝ} (hx : 0 < x) {n : ℕ} {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n)) :
    (tricomiIncompleteGamma a x).re ≤ 0 ↔ logGap x a ≤ 0 := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, re_tricomi_neg_iff hx ha, re_tricomi_eq_zero_iff hx ha]

/-- The log-gap is monotone in `x`. -/
private theorem logGap_le_logGap {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (a : ℝ) :
    logGap x a ≤ logGap y a := by
  rcases hxy.lt_or_eq with h | rfl
  · exact (logGap_lt_logGap hx h a).le
  · exact le_rfl

/-- The arguments `x > 0` at which the log-gap takes a negative value on the band. -/
private def negSet (n : ℕ) : Set ℝ :=
  {x | 0 < x ∧ ∃ a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n), logGap x a < 0}

/-- The set of `x` with a negative log-gap value is bounded above. -/
private theorem bddAbove_negSet {n : ℕ} (hn : 1 ≤ n) : BddAbove (negSet n) := by
  obtain ⟨X, -, hX⟩ := exists_logGap_nonneg hn
  refine ⟨X, fun x ⟨_, a, ha, hD⟩ => ?_⟩
  by_contra h
  exact (hX x (not_le.1 h).le a ha).not_gt hD

/-- The threshold is positive. -/
private theorem sSup_negSet_pos {n : ℕ} (hn : 1 ≤ n) : 0 < sSup (negSet n) := by
  obtain ⟨x, hx, hmem⟩ := exists_logGap_neg hn
  exact hx.trans_le (le_csSup (bddAbove_negSet hn) ⟨hx, hmem⟩)

/-- Above the threshold the log-gap is positive on the band. -/
private theorem logGap_pos_of_sSup_lt {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : sSup (negSet n) < x)
    {a : ℝ} (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n)) : 0 < logGap x a := by
  by_contra h
  set y := (sSup (negSet n) + x) / 2
  have hy0 : 0 < y := by have := sSup_negSet_pos hn; simp only [y]; linarith
  have hyx : y < x := by simp only [y]; linarith
  have hmem : y ∈ negSet n := ⟨hy0, a, ha, (logGap_lt_logGap hy0 hyx a).trans_le (not_lt.1 h)⟩
  have := le_csSup (bddAbove_negSet hn) hmem
  simp only [y] at this
  linarith

/-- At the threshold the log-gap is nonnegative on the band. -/
private theorem logGap_sSup_nonneg {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n)) : 0 ≤ logGap (sSup (negSet n)) a := by
  set xs := sSup (negSet n)
  have hxs := sSup_negSet_pos hn
  by_contra h
  have hf := (re_tricomi_neg_iff hxs ha).2 (not_le.1 h)
  have hev := (continuous_re_tricomi_right a).continuousAt.eventually_lt continuousAt_const hf
  obtain ⟨y, hy, hxy⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Ioi xs))).exists
  have hy0 : 0 < y := hxs.trans hxy
  exact (le_csSup (bddAbove_negSet hn) ⟨hy0, a, ha, (re_tricomi_neg_iff hy0 ha).1 hy⟩).not_gt hxy

/-- At the threshold, the log-gap vanishes somewhere on the band. -/
private theorem exists_logGap_sSup_eq_zero {n : ℕ} (hn : 1 ≤ n) :
    ∃ a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n), logGap (sSup (negSet n)) a = 0 := by
  set I := Ioo (-2 * (n : ℝ)) (1 - 2 * n)
  set xs := sSup (negSet n)
  obtain ⟨s₀, hs₀, a, ha, hD⟩ := exists_logGap_neg hn
  have hmem₀ : s₀ ∈ negSet n := ⟨hs₀, a, ha, hD⟩
  have hs₀xs : s₀ < xs := (le_csSup (bddAbove_negSet hn) hmem₀).lt_of_ne
    fun h => (logGap_sSup_nonneg hn ha).not_gt (h ▸ hD)
  obtain ⟨a₁, a₂, ha₁, ha₂, -, -, -, -, hC, -⟩ := exists_zeros_of_logGap_neg hs₀ hn ha hD
  have hIcc : Icc a₁ a₂ ⊆ I := Icc_subset_Ioo ha₁.1 ha₂.2
  -- the nested compact sets `{b ∈ [a₁, a₂] | γ*(b, y) ≤ 0}` for `s₀ ≤ y < x*`
  let K : Ico s₀ xs → Set ℝ := fun y =>
    Icc a₁ a₂ ∩ (fun b : ℝ => (tricomiIncompleteGamma b (y : ℝ)).re) ⁻¹' Iic 0
  have hy0 : ∀ y : Ico s₀ xs, 0 < (y : ℝ) := fun y => hs₀.trans_le y.property.1
  have hKcl : ∀ y, IsClosed (K y) := fun y =>
    isClosed_Icc.inter (isClosed_Iic.preimage (Complex.continuous_re_tricomi_left _))
  have hKne : ∀ y, (K y).Nonempty := by
    intro y
    obtain ⟨s, ⟨-, b, hb, hDb⟩, hys⟩ := exists_lt_of_lt_csSup ⟨s₀, hmem₀⟩ y.property.2
    have hDy := (logGap_le_logGap (hy0 y) hys.le b).trans_lt hDb
    exact ⟨b, hC b hb ((logGap_le_logGap hs₀ y.property.1 b).trans hDy.le),
      ((re_tricomi_neg_iff (hy0 y) hb).2 hDy).le⟩
  have hKdir : Directed (· ⊇ ·) K := directed_of_isDirected_le fun i j hij b ⟨hb, hfb⟩ =>
    ⟨hb, (re_tricomi_nonpos_iff (hy0 i) (hIcc hb)).2 <| (logGap_le_logGap (hy0 i) hij b).trans
      ((re_tricomi_nonpos_iff (hy0 j) (hIcc hb)).1 hfb)⟩
  have : Nonempty (Ico s₀ xs) := ⟨⟨s₀, le_rfl, hs₀xs⟩⟩
  obtain ⟨a₀, ha₀⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed K hKdir
    hKne (fun y => isCompact_Icc.inter_right
      (isClosed_Iic.preimage (Complex.continuous_re_tricomi_left _))) hKcl
  rw [mem_iInter] at ha₀
  have ha₀I : a₀ ∈ I := hIcc (ha₀ ⟨s₀, le_rfl, hs₀xs⟩).1
  have hfxs : (tricomiIncompleteGamma a₀ xs).re ≤ 0 :=
    le_of_tendsto ((continuous_re_tricomi_right a₀).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds) (Filter.mem_of_superset (Ioo_mem_nhdsLT hs₀xs)
        fun y hy => (ha₀ ⟨y, hy.1.le, hy.2⟩).2)
  exact ⟨a₀, ha₀I, le_antisymm ((re_tricomi_nonpos_iff (sSup_negSet_pos hn) ha₀I).1 hfxs)
    (logGap_sSup_nonneg hn ha₀I)⟩

/-- Below the threshold there are exactly two zeros on the band, both simple. -/
private theorem param_zeros_of_lt_sSup {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x)
    (hlt : x < sSup (negSet n)) :
    ∃ a₁ a₂ : ℝ, a₁ < a₂ ∧
      {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧ tricomiIncompleteGamma a x = 0} =
        {a₁, a₂} ∧
      deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₁ ≠ 0 ∧
      deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₂ ≠ 0 := by
  obtain ⟨x₀, hx₀, hmem₀⟩ := exists_logGap_neg hn
  have hS : x₀ ∈ negSet n := ⟨hx₀, hmem₀⟩
  obtain ⟨s, ⟨-, a, ha, hD⟩, hxs⟩ := exists_lt_of_lt_csSup ⟨x₀, hS⟩ hlt
  obtain ⟨a₁, a₂, ha₁, ha₂, hD₁, hD₂, hd₁, hd₂, -, hZ⟩ :=
    exists_zeros_of_logGap_neg hx hn ha ((logGap_lt_logGap hx hxs a).trans hD)
  have ha₁I : a₁ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n) := ⟨ha₁.1, ha₁.2.trans ha.2⟩
  have ha₂I : a₂ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * n) := ⟨ha.1.trans ha₂.1, ha₂.2⟩
  refine ⟨a₁, a₂, ha₁.2.trans ha₂.1, ?_, ?_, ?_⟩
  · ext b
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hb, hzero⟩
      exact hZ b hb ((tricomi_eq_zero_iff hx hb).1 hzero)
    · rintro (rfl | rfl)
      · exact ⟨ha₁I, (tricomi_eq_zero_iff hx ha₁I).2 hD₁⟩
      · exact ⟨ha₂I, (tricomi_eq_zero_iff hx ha₂I).2 hD₂⟩
  · rw [deriv_re_tricomi hx ha₁I, hD₁]
    simpa using ⟨(rpow_pos_of_pos hx _).ne', hd₁.ne⟩
  · rw [deriv_re_tricomi hx ha₂I, hD₂]
    simpa using ⟨(rpow_pos_of_pos hx _).ne', hd₂.ne'⟩

/-- At the threshold there is exactly one zero on the band, and it is double. -/
private theorem param_zeros_sSup {n : ℕ} (hn : 1 ≤ n) :
    ∃ a₀ : ℝ,
      {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
        tricomiIncompleteGamma a (sSup (negSet n) : ℝ) = 0} = {a₀} ∧
      deriv (fun b : ℝ => (tricomiIncompleteGamma b (sSup (negSet n) : ℝ)).re) a₀ = 0 ∧
      deriv (deriv fun b : ℝ => (tricomiIncompleteGamma b (sSup (negSet n) : ℝ)).re) a₀ ≠ 0 := by
  have hx := sSup_negSet_pos hn
  obtain ⟨a₀, ha₀, hD₀⟩ := exists_logGap_sSup_eq_zero hn
  -- every zero of the nonnegative log-gap minimizes it on the band
  have hmin : ∀ b, logGap (sSup (negSet n)) b = 0 →
      IsMinOn (logGap (sSup (negSet n))) (Ioo (-2 * (n : ℝ)) (1 - 2 * n)) b :=
    fun b hb => isMinOn_iff.2 fun c hc => hb ▸ logGap_sSup_nonneg hn hc
  have hd₀ := ((hmin a₀ hD₀).isLocalMin (isOpen_Ioo.mem_nhds ha₀)).hasDerivAt_eq_zero
    (hasDerivAt_logGap hx (ne_neg_natCast_of_mem_band ha₀))
  refine ⟨a₀, ?_, ?_, ?_⟩
  · ext b
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    refine ⟨fun ⟨hb, hzero⟩ => ?_, fun h => h ▸ ⟨ha₀, (tricomi_eq_zero_iff hx ha₀).2 hD₀⟩⟩
    exact (strictConvexOn_logGap hx hn).eq_of_isMinOn
      (hmin b ((tricomi_eq_zero_iff hx hb).1 hzero)) (hmin a₀ hD₀) hb ha₀
  · rw [deriv_re_tricomi hx ha₀, hD₀, hd₀]
    simp
  · rw [deriv_deriv_re_tricomi hx ha₀ hD₀ hd₀]
    exact mul_ne_zero (rpow_pos_of_pos hx _).ne' (logGapDeriv2_pos hx hn ha₀).ne'

/-- **The zeros of `γ*(·, x)` on the band `-2n < a < 1 - 2n` for `x > 0`** (DLMF §8.13(iii)(b)).
There is a threshold `x*ₙ > 0` such that the zeros are exactly two, both simple (`γ*` has
nonzero parameter derivative there), for `0 < x < x*ₙ`; exactly one, which is double
(`∂ₐγ* = 0` and `∂ₐ²γ* ≠ 0` there), for `x = x*ₙ`; and none for `x > x*ₙ`. The derivatives are
those of the real function `b ↦ Re γ*(b, x)`. -/
theorem _root_.Complex.tricomiIncompleteGamma_param_zeros {n : ℕ} (hn : 1 ≤ n) :
    ∃ xs : ℝ, 0 < xs ∧ ∀ x : ℝ, 0 < x →
      (x < xs → ∃ a₁ a₂ : ℝ, a₁ < a₂ ∧
        {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
          tricomiIncompleteGamma a x = 0} = {a₁, a₂} ∧
        deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₁ ≠ 0 ∧
        deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₂ ≠ 0) ∧
      (x = xs → ∃ a₀ : ℝ,
        {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
          tricomiIncompleteGamma a x = 0} = {a₀} ∧
        deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₀ = 0 ∧
        deriv (deriv fun b : ℝ => (tricomiIncompleteGamma b x).re) a₀ ≠ 0) ∧
      (xs < x →
        {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
          tricomiIncompleteGamma a x = 0} = ∅) := by
  refine ⟨sSup (negSet n), sSup_negSet_pos hn, fun x hx =>
    ⟨param_zeros_of_lt_sSup hn hx, fun h => h ▸ param_zeros_sSup hn, fun hlt => ?_⟩⟩
  ext b
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun hb hzero =>
    (logGap_pos_of_sSup_lt hn hlt hb).ne' ((tricomi_eq_zero_iff hx hb).1 hzero)

end TauCeti

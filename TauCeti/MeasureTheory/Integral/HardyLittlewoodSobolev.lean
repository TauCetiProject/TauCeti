/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.MaximalFunction
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import TauCeti.Analysis.SpecialFunctions.Pow.Integral

/-!
# The Hardy–Littlewood–Sobolev inequality

Let `E` be a real normed space of finite dimension `n ≥ 1` with an additive Haar measure `μ`, and
let `ω = μ(B(0, 1))`. For `0 < κ < 1` the **Riesz potential** of order `n κ` of `f ≥ 0` is

`I f (x) = ∫ ‖x - y‖ ^ (n (κ - 1)) f(y) dy`,

the convolution of `f` with the Riesz kernel `‖·‖ ^ (n κ - n)`. This file proves the
**Hardy–Littlewood–Sobolev inequality**: for `1 < p < q < ∞` with `1/p - 1/q = κ`,

`‖I f‖_q ≤ C(n, κ, p, ω) ‖f‖_p`

(`TauCeti.eLpNorm_lintegral_enorm_sub_rpow_mul_le`). On a set of finite measure the potential maps
`Lᵖ` to `L^q` whenever `1 ≤ p ≤ q < ∞` and `1/p - 1/q < κ`, by Young's inequality
(`TauCeti.eLpNorm_setLIntegral_enorm_sub_rpow_mul_le`); on the whole space only the scale-invariant
exponent `1/p - 1/q = κ` can work, and there Young's inequality fails, because the kernel lies in
no Lebesgue space of the whole space. Fractional integration in time with the kernel
`|t - s| ^ (-σ)`, `0 < σ < 1`, on `ℝ` is the one-dimensional case, `κ = 1 - σ`.

## The proof

The proof is Hedberg's. Integrating `r ^ (s - 1)` over `r > ‖z‖` writes the kernel, for `s < 0`,
as a superposition of indicators of balls, and so the potential as a superposition of the
integrals of `f` over the balls about `x`
(`TauCeti.lintegral_enorm_sub_rpow_mul_eq`):

`∫ ‖x - y‖ ^ s f(y) dy = (-s) ∫₀^∞ r ^ (s - 1) (∫_{B(x, r)} f) dr`.

A small ball carries at most `μ(B(x, r)) M f(x)` of `f`, where `M f` is the Hardy–Littlewood
maximal function, and by Hölder's inequality a large one carries at most
`μ(B(x, r)) ^ (1 - 1/p) ‖f‖_p`. Splitting the `r`-integral at the radius `δ` that balances the two
bounds gives **Hedberg's inequality**
(`TauCeti.lintegral_enorm_sub_rpow_mul_le_maximalFunction`)

`I f (x) ≤ (1 - κ) (κ⁻¹ + q) ω ^ (1 - κ) M f(x) ^ (1 - p κ) ‖f‖_p ^ (p κ)`.

Since `(1 - p κ) q = p`, raising it to the power `q` and integrating leaves `∫ (M f) ^ p`, which
the strong type `(p, p)` maximal inequality `TauCeti.lintegral_rpow_maximalFunction_le` bounds by
`∫ f ^ p`.

## Main declarations

* `TauCeti.lintegral_enorm_sub_rpow_mul_eq`: the Riesz potential as a superposition of the
  integrals of `f` over balls.
* `TauCeti.lintegral_enorm_sub_rpow_mul_le_maximalFunction`: Hedberg's pointwise inequality.
* `TauCeti.eLpNorm_lintegral_enorm_sub_rpow_mul_le`: the Hardy–Littlewood–Sobolev inequality.

## References

* L. I. Hedberg, *On certain convolution inequalities*, Proc. Amer. Math. Soc. 36 (1972),
  505–510.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V,
  §1.2, Theorem 1.
* L. Grafakos, *Modern Fourier Analysis*, Theorem 1.2.3.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set Module
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **The Riesz potential as a superposition of ball integrals.** For `s < 0`,

`∫ ‖x - y‖ ^ s f(y) dy = (-s) ∫₀^∞ r ^ (s - 1) (∫_{B(x, r)} f) dr`,

since `‖z‖ ^ s = (-s) ∫_{‖z‖}^∞ r ^ (s - 1) dr` for `z ≠ 0`. -/
theorem lintegral_enorm_sub_rpow_mul_eq {s : ℝ} (hs : s < 0) {f : E → ℝ≥0∞}
    (hf : AEMeasurable f μ) (x : E) :
    ∫⁻ y, ‖x - y‖ₑ ^ s * f y ∂μ =
      ENNReal.ofReal (-s) *
        ∫⁻ r in Ioi 0, ENNReal.ofReal (r ^ (s - 1)) * ∫⁻ y in ball x r, f y ∂μ := by
  -- The integrand in the variables `(y, r)`.
  set H : E → ℝ → ℝ≥0∞ := fun y r => ENNReal.ofReal (r ^ (s - 1)) * (ball x r).indicator f y
  -- Away from the pole, the kernel is the `r`-integral of `H`, up to the factor `-s`.
  have hpt : ∀ y, y ≠ x → ‖x - y‖ₑ ^ s * f y = ENNReal.ofReal (-s) * ∫⁻ r in Ioi 0, H y r := by
    intro y hy
    have hd : 0 < dist y x := dist_pos.2 hy
    have hH : ∀ r, H y r =
        (Ioi (dist y x)).indicator (fun r => ENNReal.ofReal (r ^ (s - 1)) * f y) r := by
      intro r
      by_cases h : dist y x < r
      · simp [H, indicator_of_mem (mem_ball.2 h), indicator_of_mem (mem_Ioi.2 h)]
      · simp [H, indicator_of_notMem (mt mem_ball.1 h), indicator_of_notMem (mt mem_Ioi.1 h)]
    simp_rw [hH]
    rw [setLIntegral_indicator measurableSet_Ioi, inter_eq_left.2 (Ioi_subset_Ioi hd.le),
      lintegral_mul_const _ (by fun_prop),
      lintegral_ofReal_rpow_Ioi_of_lt (by linarith) hd, sub_add_cancel, ← mul_assoc,
      ← ENNReal.ofReal_mul (by linarith), show ‖x - y‖ₑ = ENNReal.ofReal (dist y x) by
        rw [dist_comm, dist_eq_norm, ofReal_norm], ENNReal.ofReal_rpow_of_pos hd]
    congr 2
    field_simp [hs.ne]
  have hmeas : AEMeasurable (Function.uncurry H) (μ.prod (volume.restrict (Ioi 0))) := by
    have hind : Function.uncurry H = fun z : E × ℝ => ENNReal.ofReal (z.2 ^ (s - 1)) *
        {z : E × ℝ | dist z.1 x < z.2}.indicator (fun z => f z.1) z := by
      ext ⟨y, r⟩
      by_cases h : dist y x < r <;> simp [H, mem_ball, h]
    rw [hind]
    have hk : Measurable fun z : E × ℝ => ENNReal.ofReal (z.2 ^ (s - 1)) := by fun_prop
    exact hk.aemeasurable.mul
      (hf.comp_fst.indicator (measurableSet_lt (by fun_prop) measurable_snd))
  calc
    ∫⁻ y, ‖x - y‖ₑ ^ s * f y ∂μ = ∫⁻ y, ENNReal.ofReal (-s) * (∫⁻ r in Ioi 0, H y r) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [compl_mem_ae_iff.2 (measure_singleton (μ := μ) x)] with y hy
      exact hpt y hy
    _ = ENNReal.ofReal (-s) * ∫⁻ r in Ioi 0, ∫⁻ y, H y r ∂μ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_lintegral_swap hmeas]
    _ = _ := by
      congr 1
      refine setLIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_ball]

omit [Nontrivial E] in
/-- The measure of a ball, `μ(B(x, r)) = rⁿ ω` for `r > 0`, with a real exponent. -/
private theorem addHaar_ball_eq_ofReal_rpow_mul (x : E) {r : ℝ} (hr : 0 < r) :
    μ (ball x r) = ENNReal.ofReal (r ^ (finrank ℝ E : ℝ)) * ENNReal.ofReal (μ.real (ball 0 1)) := by
  rw [Measure.addHaar_ball_of_pos μ x hr, ofReal_measureReal measure_ball_lt_top.ne,
    Real.rpow_natCast]

/-- The balls of radius below `δ` contribute to the potential at most what the maximal function
allows: `∫_{B(x, r)} f ≤ ω rⁿ M f(x)`. -/
private theorem setLIntegral_Ioo_mul_setLIntegral_ball_le {κ : ℝ} (hκ : 0 < κ) (f : E → ℝ≥0∞)
    (x : E) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∫⁻ r in Ioo 0 δ, ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) * (κ - 1) - 1)) *
        ∫⁻ y in ball x r, f y ∂μ ≤
      ENNReal.ofReal (δ ^ ((finrank ℝ E : ℝ) * κ) / ((finrank ℝ E : ℝ) * κ)) *
        (ENNReal.ofReal (μ.real (ball 0 1)) * maximalFunction μ f x) := by
  have hn : 0 < (finrank ℝ E : ℝ) := by exact_mod_cast finrank_pos
  calc
    _ ≤ ∫⁻ r in Ioo 0 δ, ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) * κ - 1)) *
          (ENNReal.ofReal (μ.real (ball 0 1)) * maximalFunction μ f x) := by
      refine setLIntegral_mono_ae' measurableSet_Ioo (.of_forall fun r hr => ?_)
      calc
        _ ≤ ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) * (κ - 1) - 1)) *
              (μ (ball x r) * maximalFunction μ f x) := by
          gcongr
          simpa only [enorm_eq_self] using
            setLIntegral_ball_le_measure_mul_maximalFunction μ f x hr.1 measure_ball_lt_top.ne
        _ = _ := by
          rw [addHaar_ball_eq_ofReal_rpow_mul x hr.1,
            show (finrank ℝ E : ℝ) * κ - 1 = (finrank ℝ E : ℝ) * (κ - 1) - 1 + finrank ℝ E by
              ring, Real.rpow_add hr.1, ENNReal.ofReal_mul (Real.rpow_nonneg hr.1.le _)]
          ring
    _ = _ := by
      rw [lintegral_mul_const _ (by fun_prop), lintegral_ofReal_rpow_Ioo (by nlinarith) hδ,
        sub_add_cancel]

/-- The balls of radius above `δ` contribute to the potential at most what Hölder's inequality
allows: `∫_{B(x, r)} f ≤ ‖f‖_p (ω rⁿ) ^ (1 - 1/p)`. -/
private theorem setLIntegral_Ioi_mul_setLIntegral_ball_le {p : ℝ≥0} {κ : ℝ} (hp : 1 ≤ p)
    (hκp : κ < (p : ℝ)⁻¹) {f : E → ℝ≥0∞} (hf : AEMeasurable f μ) (x : E) {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ r in Ioi δ, ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) * (κ - 1) - 1)) *
        ∫⁻ y in ball x r, f y ∂μ ≤
      ENNReal.ofReal (-δ ^ ((finrank ℝ E : ℝ) * κ - finrank ℝ E * (p : ℝ)⁻¹) /
          ((finrank ℝ E : ℝ) * κ - finrank ℝ E * (p : ℝ)⁻¹)) *
        (ENNReal.ofReal (μ.real (ball 0 1) ^ (1 - (p : ℝ)⁻¹)) * eLpNorm f p μ) := by
  set n : ℝ := (finrank ℝ E : ℝ)
  set ω := μ.real (ball (0 : E) 1)
  have hn : 0 < n := by simp only [n]; exact_mod_cast finrank_pos
  have hω : 0 ≤ ω := measureReal_nonneg
  have hp1 : 0 ≤ 1 - (p : ℝ)⁻¹ := sub_nonneg.2 (inv_le_one_of_one_le₀ (by exact_mod_cast hp))
  -- Hölder's inequality on a ball.
  have hholder : ∀ r, ∫⁻ y in ball x r, f y ∂μ ≤
      eLpNorm f p μ * μ (ball x r) ^ (1 - (p : ℝ)⁻¹) := fun r => by
    have hfm : AEStronglyMeasurable f (μ.restrict (ball x r)) := hf.restrict.aestronglyMeasurable
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := (p : ℝ≥0∞))
      (by exact_mod_cast hp) hfm
    rw [eLpNorm_one_eq_lintegral_enorm hfm, Measure.restrict_apply_univ] at h
    simp only [enorm_eq_self, ENNReal.toReal_one, div_one, ENNReal.coe_toReal, one_div] at h
    exact h.trans (by gcongr; exact Measure.restrict_le_self)
  calc
    _ ≤ ∫⁻ r in Ioi δ, ENNReal.ofReal (r ^ (n * κ - n * (p : ℝ)⁻¹ - 1)) *
          (ENNReal.ofReal (ω ^ (1 - (p : ℝ)⁻¹)) * eLpNorm f p μ) := by
      refine setLIntegral_mono_ae' measurableSet_Ioi (.of_forall fun r hr => ?_)
      have hr0 : 0 < r := hδ.trans hr
      have key : r ^ (n * (κ - 1) - 1) * (r ^ n * ω) ^ (1 - (p : ℝ)⁻¹) =
          r ^ (n * κ - n * (p : ℝ)⁻¹ - 1) * ω ^ (1 - (p : ℝ)⁻¹) := by
        rw [Real.mul_rpow (by positivity) hω, ← Real.rpow_mul hr0.le, ← mul_assoc,
          ← Real.rpow_add hr0]
        congr 2
        ring
      calc
        _ ≤ ENNReal.ofReal (r ^ (n * (κ - 1) - 1)) *
              (eLpNorm f p μ * μ (ball x r) ^ (1 - (p : ℝ)⁻¹)) := by
          gcongr
          exact hholder r
        _ = _ := by
          rw [addHaar_ball_eq_ofReal_rpow_mul x hr0, ← ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_rpow_of_nonneg (by positivity) hp1, mul_comm (eLpNorm f p μ),
            ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), key,
            ENNReal.ofReal_mul (by positivity)]
          ring
    _ = _ := by
      rw [lintegral_mul_const _ (by fun_prop),
        lintegral_ofReal_rpow_Ioi_of_lt (by nlinarith) hδ, sub_add_cancel]

/-- Hedberg's inequality before the choice of the splitting radius: for every `δ > 0` the
potential is bounded by the contributions of the balls of radius below `δ`, controlled by the
maximal function, and of those of radius above `δ`, controlled by `‖f‖_p`. -/
private theorem lintegral_enorm_sub_rpow_mul_le_add {p : ℝ≥0} {κ : ℝ} (hp : 1 ≤ p) (hκ : 0 < κ)
    (hκp : κ < (p : ℝ)⁻¹) {f : E → ℝ≥0∞} (hf : AEMeasurable f μ) (x : E) {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ y, ‖x - y‖ₑ ^ ((finrank ℝ E : ℝ) * (κ - 1)) * f y ∂μ ≤
      ENNReal.ofReal (-((finrank ℝ E : ℝ) * (κ - 1))) *
        (ENNReal.ofReal (δ ^ ((finrank ℝ E : ℝ) * κ) / ((finrank ℝ E : ℝ) * κ)) *
            (ENNReal.ofReal (μ.real (ball 0 1)) * maximalFunction μ f x) +
          ENNReal.ofReal (-δ ^ ((finrank ℝ E : ℝ) * κ - finrank ℝ E * (p : ℝ)⁻¹) /
              ((finrank ℝ E : ℝ) * κ - finrank ℝ E * (p : ℝ)⁻¹)) *
            (ENNReal.ofReal (μ.real (ball 0 1) ^ (1 - (p : ℝ)⁻¹)) * eLpNorm f p μ)) := by
  have hn : 0 < (finrank ℝ E : ℝ) := by exact_mod_cast finrank_pos
  have hκ1 : κ < 1 := hκp.trans_le (inv_le_one_of_one_le₀ (by exact_mod_cast hp))
  rw [lintegral_enorm_sub_rpow_mul_eq (by nlinarith) hf x]
  gcongr
  -- Split `(0, ∞)` at `δ`.
  refine (lintegral_mono_set (Ioi_subset_Ioo_union_Ici (b := δ))).trans
    ((lintegral_union_le _ _ _).trans (add_le_add
      (setLIntegral_Ioo_mul_setLIntegral_ball_le hκ f x hδ.le) ?_))
  rw [← setLIntegral_congr Ioi_ae_eq_Ici]
  exact setLIntegral_Ioi_mul_setLIntegral_ball_le hp hκp hf x hδ

/-- The choice of the splitting radius in Hedberg's inequality: for positive `ω`, `m` and `ν`
there is a radius `δ > 0`, with `ω δⁿ = (ν / m) ^ p`, at which the two bounds of
`lintegral_enorm_sub_rpow_mul_le_add` add up to `(1 - κ) (κ⁻¹ + (1/p - κ)⁻¹) ω ^ (1 - κ)`
times `m ^ (1 - p κ) ν ^ (p κ)`. -/
private theorem exists_pos_hedberg_eq {n p κ : ℝ} (hn : 0 < n) (hp : 0 < p) (hκ : 0 < κ)
    (hκp : κ < p⁻¹) {ω m ν : ℝ} (hω : 0 < ω) (hm : 0 < m) (hν : 0 < ν) :
    ∃ δ > 0, -(n * (κ - 1)) * (δ ^ (n * κ) / (n * κ) * (ω * m) +
        -δ ^ (n * κ - n * p⁻¹) / (n * κ - n * p⁻¹) * (ω ^ (1 - p⁻¹) * ν)) =
      (1 - κ) * (κ⁻¹ + (p⁻¹ - κ)⁻¹) * ω ^ (1 - κ) * m ^ (1 - p * κ) * ν ^ (p * κ) := by
  -- Work with the logarithms `a`, `b`, `c` of `ω`, `m`, `ν`.
  obtain ⟨a, rfl⟩ : ∃ a, ω = Real.exp a := ⟨_, (Real.exp_log hω).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b, m = Real.exp b := ⟨_, (Real.exp_log hm).symm⟩
  obtain ⟨c, rfl⟩ : ∃ c, ν = Real.exp c := ⟨_, (Real.exp_log hν).symm⟩
  set L := a * (1 - κ) + b * (1 - p * κ) + c * (p * κ)
  set δ := Real.exp ((p * (c - b) - a) / n)
  have hpκ : p * κ < 1 := by
    calc p * κ < p * p⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hp.ne'
  have h1 : δ ^ (n * κ) * (Real.exp a * Real.exp b) = Real.exp L := by
    simp only [δ, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have h2 : δ ^ (n * κ - n * p⁻¹) * (Real.exp a ^ (1 - p⁻¹) * Real.exp c) = Real.exp L := by
    simp only [δ, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have h3 : Real.exp a ^ (1 - κ) * Real.exp b ^ (1 - p * κ) * Real.exp c ^ (p * κ) =
      Real.exp L := by
    simp only [← Real.exp_mul, ← Real.exp_add]
    rfl
  refine ⟨δ, Real.exp_pos _, ?_⟩
  have hb : n * κ - n * p⁻¹ ≠ 0 := by nlinarith
  have hc : p⁻¹ - κ ≠ 0 := by linarith
  calc
    _ = -(n * (κ - 1)) * (δ ^ (n * κ) * (Real.exp a * Real.exp b) / (n * κ) -
          δ ^ (n * κ - n * p⁻¹) * (Real.exp a ^ (1 - p⁻¹) * Real.exp c) /
            (n * κ - n * p⁻¹)) := by ring
    _ = (1 - κ) * (κ⁻¹ + (p⁻¹ - κ)⁻¹) * Real.exp L := by
      rw [h1, h2, show n * κ - n * p⁻¹ = -(n * (p⁻¹ - κ)) by ring]
      generalize p⁻¹ - κ = q at hc ⊢
      field_simp
      ring
    _ = _ := by rw [← h3]; ring

/-- The potential vanishes at `x` if `M f(x) = 0`, since then `f` carries no mass on the balls
about `x`, and everywhere if `‖f‖_p = 0`, since then `f = 0` almost everywhere. -/
private theorem lintegral_enorm_sub_rpow_mul_eq_zero {p : ℝ≥0} (hp : p ≠ 0) {s : ℝ} (hs : s < 0)
    {f : E → ℝ≥0∞} (hf : AEMeasurable f μ) (x : E)
    (h0 : maximalFunction μ f x = 0 ∨ eLpNorm f p μ = 0) :
    ∫⁻ y, ‖x - y‖ₑ ^ s * f y ∂μ = 0 := by
  rcases h0 with h0 | h0
  · rw [lintegral_enorm_sub_rpow_mul_eq hs hf x]
    refine mul_eq_zero_of_right _ ((setLIntegral_congr_fun measurableSet_Ioi
      fun r hr => ?_).trans lintegral_zero)
    have h := setLIntegral_ball_le_measure_mul_maximalFunction μ f x hr measure_ball_lt_top.ne
    simp only [enorm_eq_self, h0, mul_zero, nonpos_iff_eq_zero] at h
    rw [h, mul_zero]
  · have hf0 : f =ᵐ[μ] 0 := (eLpNorm_eq_zero_iff (by exact_mod_cast hp)).1 h0
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hf0] with y hy
    rw [hy, Pi.zero_apply, mul_zero]

/-- **Hedberg's inequality.** For `1 ≤ p` and `0 < κ < 1/p`, the Riesz potential of order `n κ`
of `f ≥ 0` is bounded pointwise by a geometric mean of the Hardy–Littlewood maximal function of
`f` and the `Lᵖ` norm of `f`:

`∫ ‖x - y‖ ^ (n (κ - 1)) f(y) dy ≤ C M f(x) ^ (1 - p κ) ‖f‖_p ^ (p κ)`,

with `C = (1 - κ) (κ⁻¹ + (1/p - κ)⁻¹) ω ^ (1 - κ)`, where `n` is the dimension and
`ω = μ(B(0, 1))`. -/
theorem lintegral_enorm_sub_rpow_mul_le_maximalFunction {p : ℝ≥0} {κ : ℝ} (hp : 1 ≤ p)
    (hκ : 0 < κ) (hκp : κ < (p : ℝ)⁻¹) {f : E → ℝ≥0∞} (hf : AEMeasurable f μ) (x : E) :
    ∫⁻ y, ‖x - y‖ₑ ^ ((finrank ℝ E : ℝ) * (κ - 1)) * f y ∂μ ≤
      ENNReal.ofReal ((1 - κ) * (κ⁻¹ + ((p : ℝ)⁻¹ - κ)⁻¹) * μ.real (ball 0 1) ^ (1 - κ)) *
        maximalFunction μ f x ^ (1 - p * κ) * eLpNorm f p μ ^ (p * κ) := by
  have hn : 0 < (finrank ℝ E : ℝ) := by exact_mod_cast finrank_pos
  have hω : 0 < μ.real (ball (0 : E) 1) := ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne'
    measure_ball_lt_top.ne
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp)
  have hκ1 : κ < 1 := hκp.trans_le (inv_le_one_of_one_le₀ (by exact_mod_cast hp))
  have hpκ : 0 < 1 - p * κ := by
    have : (p : ℝ) * κ < p * (p : ℝ)⁻¹ := by gcongr
    rw [mul_inv_cancel₀ hp0.ne'] at this
    linarith
  have hpκ' : 0 < (p : ℝ) * κ := by positivity
  have hC : 0 < (1 - κ) * (κ⁻¹ + ((p : ℝ)⁻¹ - κ)⁻¹) * μ.real (ball (0 : E) 1) ^ (1 - κ) := by
    have : 0 < 1 - κ := by linarith
    have : 0 < (p : ℝ)⁻¹ - κ := by linarith
    positivity
  have hC' := (ENNReal.ofReal_pos.2 hC).ne'
  -- If `M f(x) = 0` or `‖f‖_p = 0`, the potential vanishes at `x`.
  by_cases h0 : maximalFunction μ f x = 0 ∨ eLpNorm f p μ = 0
  · exact le_of_eq_of_le (lintegral_enorm_sub_rpow_mul_eq_zero (by exact_mod_cast hp0.ne')
      (by nlinarith) hf x h0) zero_le
  simp only [not_or] at h0
  -- If `M f(x) = ∞` or `‖f‖_p = ∞`, the right-hand side is infinite.
  by_cases htop : maximalFunction μ f x = ∞ ∨ eLpNorm f p μ = ∞
  · refine le_top.trans_eq ?_
    rcases htop with h | h
    · rw [h, ENNReal.top_rpow_of_pos hpκ, ENNReal.mul_top hC',
        ENNReal.top_mul (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 h0.2) hpκ'.le).ne']
    · rw [h, ENNReal.top_rpow_of_pos hpκ', ENNReal.mul_top (mul_ne_zero hC'
        (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 h0.1) hpκ.le).ne')]
  simp only [not_or] at htop
  -- Otherwise split at the radius chosen by `exists_pos_hedberg_eq`.
  obtain ⟨m, hm, hM⟩ : ∃ m, 0 < m ∧ maximalFunction μ f x = ENNReal.ofReal m :=
    ⟨_, ENNReal.toReal_pos h0.1 htop.1, (ENNReal.ofReal_toReal htop.1).symm⟩
  obtain ⟨ν, hν, hN⟩ : ∃ ν, 0 < ν ∧ eLpNorm f p μ = ENNReal.ofReal ν :=
    ⟨_, ENNReal.toReal_pos h0.2 htop.2, (ENNReal.ofReal_toReal htop.2).symm⟩
  obtain ⟨δ, hδ, hid⟩ := exists_pos_hedberg_eq hn hp0 hκ hκp hω hm hν
  have hb : (finrank ℝ E : ℝ) * κ - finrank ℝ E * (p : ℝ)⁻¹ < 0 := by nlinarith
  have h1 : 0 ≤ δ ^ ((finrank ℝ E : ℝ) * κ) / ((finrank ℝ E : ℝ) * κ) := by positivity
  have h2 : 0 ≤ -δ ^ ((finrank ℝ E : ℝ) * κ - finrank ℝ E * (p : ℝ)⁻¹) /
      ((finrank ℝ E : ℝ) * κ - finrank ℝ E * (p : ℝ)⁻¹) :=
    div_nonneg_of_nonpos (neg_nonpos.2 (Real.rpow_nonneg hδ.le _)) hb.le
  have h3 : 0 ≤ μ.real (ball (0 : E) 1) ^ (1 - (p : ℝ)⁻¹) := Real.rpow_nonneg hω.le _
  refine (lintegral_enorm_sub_rpow_mul_le_add hp hκ hκp hf x hδ).trans_eq ?_
  rw [hM, hN, ← ENNReal.ofReal_mul hω.le, ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h3,
    ← ENNReal.ofReal_mul h2, ← ENNReal.ofReal_add (by positivity) (mul_nonneg h2 (by positivity)),
    ← ENNReal.ofReal_mul (by nlinarith), hid, ENNReal.ofReal_rpow_of_pos hm,
    ENNReal.ofReal_rpow_of_pos hν, ← ENNReal.ofReal_mul hC.le,
    ← ENNReal.ofReal_mul (by positivity)]

/-- The exponent bookkeeping in raising Hedberg's inequality to the power `q`: since
`(1 - p κ) q = p`, the `q`-th power of `C M ^ (1 - p κ) (J ^ (1/p)) ^ (p κ)` is
`C ^ q J ^ (κ q) M ^ p`. -/
private theorem mul_rpow_mul_rpow_rpow_eq {C M J : ℝ≥0∞} {p q κ : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpq : p⁻¹ - q⁻¹ = κ) :
    (C * M ^ (1 - p * κ) * (J ^ p⁻¹) ^ (p * κ)) ^ q = C ^ q * J ^ (κ * q) * M ^ p := by
  have he1 : (1 - p * κ) * q = p := by
    rw [← hpq]
    field_simp
    ring
  have he2 : p⁻¹ * (p * κ * q) = κ * q := by field_simp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ENNReal.mul_rpow_of_nonneg _ _ hq.le,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, he1, he2]
  ring

/-- The exponent bookkeeping at the end of the Hardy–Littlewood–Sobolev inequality:
`(C ^ q J ^ (κ q) K J) ^ (1/q) = C K ^ (1/q) J ^ (κ + 1/q)`. -/
private theorem rpow_mul_rpow_mul_mul_rpow_eq {C K J : ℝ≥0∞} {κ q r : ℝ} (hq : 0 < q)
    (hκ : 0 ≤ κ) (hr : (κ * q + 1) * (1 / q) = r) :
    (C ^ q * J ^ (κ * q) * (K * J)) ^ (1 / q) = C * K ^ q⁻¹ * J ^ r := by
  rw [show C ^ q * J ^ (κ * q) * (K * J) = C ^ q * K * J ^ (κ * q + 1) by
      rw [ENNReal.rpow_add_of_nonneg _ _ (by positivity) zero_le_one, ENNReal.rpow_one]
      ring,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hr, mul_one_div_cancel hq.ne', ENNReal.rpow_one,
    one_div]

/-- **The Hardy–Littlewood–Sobolev inequality.** For `1 < p`, `0 < κ` and
`1/p - 1/q = κ`, the Riesz potential of order `n κ` maps `Lᵖ` to `L^q`:

`‖∫ ‖· - y‖ ^ (n (κ - 1)) f(y) dy‖_q ≤ C K ^ (1/q) ‖f‖_p`,

where `n` is the dimension, `C = (1 - κ) (κ⁻¹ + q) ω ^ (1 - κ)` with `ω = μ(B(0, 1))` is the
constant of Hedberg's inequality `TauCeti.lintegral_enorm_sub_rpow_mul_le_maximalFunction`, and
`K = 2 p 2 ^ (p - 1) / (p - 1) 4ⁿ` is that of the maximal inequality
`TauCeti.lintegral_rpow_maximalFunction_le`. When `q = 0`, which in `ℝ≥0` encodes the excluded
endpoint `κ = 1/p`, the left-hand side is the trivial seminorm `0`. -/
theorem eLpNorm_lintegral_enorm_sub_rpow_mul_le {p q : ℝ≥0} {κ : ℝ} (hp : 1 < p) (hκ : 0 < κ)
    (hpq : (p : ℝ)⁻¹ - (q : ℝ)⁻¹ = κ) {f : E → ℝ≥0∞} (hf : AEMeasurable f μ) :
    eLpNorm (fun x => ∫⁻ y, ‖x - y‖ₑ ^ ((finrank ℝ E : ℝ) * (κ - 1)) * f y ∂μ) q μ ≤
      ENNReal.ofReal ((1 - κ) * (κ⁻¹ + q) * μ.real (ball 0 1) ^ (1 - κ)) *
        (ENNReal.ofReal (2 * p * 2 ^ ((p : ℝ) - 1) / (p - 1)) * 4 ^ finrank ℝ E) ^ (q : ℝ)⁻¹ *
          eLpNorm f p μ := by
  have hI : AEMeasurable (fun x => ∫⁻ y, ‖x - y‖ₑ ^ ((finrank ℝ E : ℝ) * (κ - 1)) * f y ∂μ) μ :=
    ((by fun_prop : Measurable (Function.uncurry fun x y : E =>
      ‖x - y‖ₑ ^ ((finrank ℝ E : ℝ) * (κ - 1)))).aemeasurable.mul
        hf.comp_snd).lintegral_prod_right'
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [ENNReal.coe_zero, eLpNorm_exponent_zero hI.aestronglyMeasurable]
    exact zero_le
  have hq : (0 : ℝ) < q := by positivity
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans (by exact_mod_cast hp)
  have hκp : κ < (p : ℝ)⁻¹ := by
    have : 0 < (q : ℝ)⁻¹ := inv_pos.2 hq
    linarith
  have hqinv : ((p : ℝ)⁻¹ - κ)⁻¹ = q := by rw [← hpq, sub_sub_cancel, inv_inv]
  set C := ENNReal.ofReal ((1 - κ) * (κ⁻¹ + q) * μ.real (ball (0 : E) 1) ^ (1 - κ))
  set K := ENNReal.ofReal (2 * p * 2 ^ ((p : ℝ) - 1) / (p - 1)) * 4 ^ finrank ℝ E
  set J := ∫⁻ y, f y ^ (p : ℝ) ∂μ
  have hH : ∀ x, ∫⁻ y, ‖x - y‖ₑ ^ ((finrank ℝ E : ℝ) * (κ - 1)) * f y ∂μ ≤
      C * maximalFunction μ f x ^ (1 - p * κ) * eLpNorm f p μ ^ (p * κ) := fun x => by
    simpa only [hqinv] using
      lintegral_enorm_sub_rpow_mul_le_maximalFunction hp.le hκ hκp hf x
  have hN : eLpNorm f p μ = J ^ (p : ℝ)⁻¹ := by
    rw [eLpNorm_nnreal_eq_lintegral (by positivity) hf.aestronglyMeasurable]
    simp only [enorm_eq_self, one_div, J]
  have hMJ : ∫⁻ x, maximalFunction μ f x ^ (p : ℝ) ∂μ ≤ K * J := by
    simpa only [enorm_eq_self] using lintegral_rpow_maximalFunction_le μ
      (f := f) (by simpa only [enorm_eq_self] using hf) (by exact_mod_cast hp)
  rw [eLpNorm_nnreal_eq_lintegral hq0 hI.aestronglyMeasurable]
  simp only [enorm_eq_self]
  calc
    _ ≤ (∫⁻ x, (C * maximalFunction μ f x ^ (1 - p * κ) * eLpNorm f p μ ^ (p * κ)) ^ (q : ℝ)
          ∂μ) ^ (1 / (q : ℝ)) := by
      gcongr with x
      exact hH x
    _ ≤ (C ^ (q : ℝ) * J ^ (κ * q) * (K * J)) ^ (1 / (q : ℝ)) := by
      -- Raising Hedberg's inequality to the power `q` leaves `(M f) ^ p`.
      simp_rw [hN, mul_rpow_mul_rpow_rpow_eq hp0 hq hpq]
      rw [lintegral_const_mul _ ((measurable_maximalFunction μ f).pow_const _)]
      gcongr
    _ = C * K ^ (q : ℝ)⁻¹ * eLpNorm f p μ := by
      rw [hN]
      refine rpow_mul_rpow_mul_mul_rpow_eq hq (by positivity) ?_
      rw [← hpq]
      field_simp
      ring

end TauCeti

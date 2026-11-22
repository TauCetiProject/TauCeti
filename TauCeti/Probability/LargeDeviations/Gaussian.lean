/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import TauCeti.Probability.LargeDeviations.Weak
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import TauCeti.Data.EReal.Operations
import TauCeti.Probability.Concentration.SubgaussianTail
import TauCeti.Probability.Distributions.Gaussian.PDF
import TauCeti.Probability.Distributions.Gaussian.Sum
import TauCeti.Probability.Independence.ConvolutionPower
import TauCeti.Probability.Moments.SubGaussian

/-!
# Large deviations of Gaussian laws with vanishing variance

The Gaussian laws `gaussianReal m (ε i * v)`, with `v ≠ 0` and an eventually positive speed `ε i`
tending to `0`, satisfy a large deviation principle at speed `ε` with the good rate function
`x ↦ (x - m)² / (2v)`. They are exponentially tight at every eventually positive and eventually
bounded speed.

In particular, the sample means `(X 0 + ⋯ + X (n - 1)) / n` of independent random variables with
common law `gaussianReal m v`, `v ≠ 0`, whose law is `gaussianReal m (v / n)` for `n ≥ 1`, satisfy
the large deviation principle at speed `1 / n` with rate `x ↦ (x - m)² / (2v)`. This is Cramér's
theorem for Gaussian laws; for standard Gaussians the rate is `x ↦ x² / 2`.

## Main results

* `TauCeti.Probability.hasLDP_gaussianReal`: the large deviation principle for
  `gaussianReal m (ε i * v)`.
* `TauCeti.Probability.isExponentiallyTight_gaussianReal`: these laws are exponentially tight at
  every eventually positive and eventually bounded speed.
* `TauCeti.Probability.isGoodRateFunction_ofReal_sq_sub_div`: the rate function is good.
* `ProbabilityTheory.iIndepFun.hasLDP_map_sum_range_div_of_hasLaw_gaussianReal`: the large
  deviation principle for the sample means of independent Gaussians with a common law.

## References

* A. Dembo, O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed., Springer
  (1998), §2.2.
-/

public section

open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Real

namespace TauCeti.Probability

variable {ι : Type*} {l : Filter ι} {ε : ι → ℝ≥0}

/-- At a positive speed `e`, a set at distance at least `√(2vs)` from the mean has Gaussian
measure decaying at rate `s`: `e log (gaussianReal m (e * v) A) ≤ e log 2 - s`. -/
private theorem coe_mul_log_gaussianReal_le (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {e : ℝ≥0}
    (he : 0 < e) {s : ℝ} (hs : 0 ≤ s) {A : Set ℝ} (hA : A ⊆ {x | √(2 * v * s) ≤ |x - m|}) :
    ((e : ℝ) : EReal) * ENNReal.log (gaussianReal m (e * v) A) ≤
      ((e * Real.log 2 - s : ℝ) : EReal) := by
  have hlaw : HasLaw (fun x => x - m) (gaussianReal 0 (e * v)) (gaussianReal m (e * v)) :=
    ⟨by fun_prop, by rw [gaussianReal_map_sub_const, sub_self]⟩
  have htail := hlaw.hasSubgaussianMGF.measureReal_abs_ge_le (Real.sqrt_nonneg (2 * v * s))
  have hexp : -√(2 * v * s) ^ 2 / (2 * ((e * v : ℝ≥0) : ℝ)) = -s / e := by
    rw [Real.sq_sqrt (by positivity), NNReal.coe_mul]
    field_simp
  rw [hexp] at htail
  have hμ : gaussianReal m (e * v) A ≤ ENNReal.ofReal (2 * Real.exp (-s / e)) :=
    (measure_mono hA).trans <| by
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal htail
  calc ((e : ℝ) : EReal) * ENNReal.log (gaussianReal m (e * v) A)
      ≤ ((e : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (2 * Real.exp (-s / e))) :=
        monotone_coe_mul_log e hμ
    _ = ((e * Real.log 2 - s : ℝ) : EReal) := by
      rw [ENNReal.log_ofReal_of_pos (by positivity), ← EReal.coe_mul, Real.log_mul two_ne_zero
        (Real.exp_pos _).ne', Real.log_exp]
      congr 1
      field_simp
      ring

/-- The Gaussian upper bound at speed `ε` holds for every set `A`, closed or not. -/
private theorem limsup_coe_mul_log_gaussianReal_le [l.NeBot] (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (hε : Tendsto ε l (𝓝 0)) (hpos : ∀ᶠ i in l, 0 < ε i) (A : Set ℝ) :
    limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (gaussianReal m (ε i * v) A)) l ≤
      -((⨅ x ∈ A, ENNReal.ofReal ((x - m) ^ 2 / (2 * v)) : ℝ≥0∞) : EReal) := by
  refine EReal.le_neg_coe_ennreal_of_forall_ofReal_le fun s hs => ?_
  rcases le_or_gt s 0 with hs0 | hs0
  · -- Probabilities have nonpositive logarithms.
    refine (limsup_le_of_le (a := (0 : EReal)) (by isBoundedDefault)
      (.of_forall fun i => ?_)).trans (by exact_mod_cast neg_nonneg.2 hs0)
    exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast (ε i).coe_nonneg)
      (ENNReal.log_le_zero_iff.2 prob_le_one)
  have hA : A ⊆ {x | √(2 * v * s) ≤ |x - m|} := fun x hx => by
    have hle : s ≤ (x - m) ^ 2 / (2 * v) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (hs.trans (biInf_le _ hx))
    rw [le_div_iff₀ (by positivity)] at hle
    exact Real.sqrt_le_sqrt (by linarith) |>.trans_eq (Real.sqrt_sq_eq_abs _)
  have hlim : Tendsto (fun i => ((ε i * Real.log 2 - s : ℝ) : EReal)) l (𝓝 ((-s : ℝ) : EReal)) := by
    refine (continuous_coe_real_ereal.tendsto _).comp ?_
    simpa using ((NNReal.tendsto_coe.2 hε).mul_const (Real.log 2)).sub_const s
  calc limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (gaussianReal m (ε i * v) A)) l
      ≤ limsup (fun i => ((ε i * Real.log 2 - s : ℝ) : EReal)) l :=
        limsup_le_limsup (hpos.mono fun i hi => coe_mul_log_gaussianReal_le m hv hi hs0.le hA)
    _ = -(s : EReal) := by rw [hlim.limsup_eq, EReal.coe_neg]

/-- The Gaussian lower bound near `x`, up to the radius `δ` of the interval used. -/
private theorem coe_le_liminf_coe_mul_log_gaussianReal [l.NeBot] (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (hε : Tendsto ε l (𝓝 0)) (hpos : ∀ᶠ i in l, 0 < ε i) {x δ : ℝ} (hδ : 0 < δ) {U : Set ℝ}
    (hU : Icc (x - δ) (x + δ) ⊆ U) :
    ((-(|x - m| + δ) ^ 2 / (2 * v) : ℝ) : EReal) ≤
      liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (gaussianReal m (ε i * v) U)) l := by
  -- The logarithm of the density bound, as a continuous function of the speed.
  let g : ℝ → ℝ := fun e => e * Real.log (2 * δ) - e * Real.log (2 * π * v) / 2 -
    e * Real.log e / 2 - (|x - m| + δ) ^ 2 / (2 * v)
  have hg : Continuous g := by
    have := Real.continuous_mul_log
    fun_prop
  have hlow : ∀ᶠ i in l, ((g (ε i) : ℝ) : EReal) ≤
      ((ε i : ℝ) : EReal) * ENNReal.log (gaussianReal m (ε i * v) U) := by
    filter_upwards [hpos] with i hi
    have hi' : (0 : ℝ) < ε i := hi
    have hc : 0 < (√(2 * π * ((ε i * v : ℝ≥0) : ℝ)))⁻¹ *
        Real.exp (-(|x - m| + δ) ^ 2 / (2 * ((ε i * v : ℝ≥0) : ℝ))) * (2 * δ) := by positivity
    -- Isolate the speed as a factor, so that `Real.log_mul` splits off `log (ε i)`.
    have hvar : 2 * π * ((ε i : ℝ) * v) = (2 * π * v) * ε i := by ring
    have hlog : Real.log ((√(2 * π * ((ε i * v : ℝ≥0) : ℝ)))⁻¹ *
        Real.exp (-(|x - m| + δ) ^ 2 / (2 * ((ε i * v : ℝ≥0) : ℝ))) * (2 * δ)) =
        -((Real.log (2 * π * v) + Real.log (ε i)) / 2) +
          -(|x - m| + δ) ^ 2 / (2 * (ε i * v)) + Real.log (2 * δ) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
        (by positivity), Real.log_inv, Real.log_sqrt (by positivity), Real.log_exp,
        NNReal.coe_mul, hvar, Real.log_mul (by positivity) hi'.ne']
    calc ((g (ε i) : ℝ) : EReal)
        = ((ε i : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal
            ((√(2 * π * ((ε i * v : ℝ≥0) : ℝ)))⁻¹ *
              Real.exp (-(|x - m| + δ) ^ 2 / (2 * ((ε i * v : ℝ≥0) : ℝ))) * (2 * δ))) := by
          rw [ENNReal.log_ofReal_of_pos hc, ← EReal.coe_mul, EReal.coe_eq_coe_iff, hlog]
          simp only [g]
          field_simp
          ring
      _ ≤ ((ε i : ℝ) : EReal) * ENNReal.log (gaussianReal m (ε i * v) U) :=
          monotone_coe_mul_log (ε i)
            ((ofReal_mul_le_gaussianReal_Icc m x (ε i * v) δ).trans (measure_mono hU))
  have hlim : Tendsto (fun i => ((g (ε i) : ℝ) : EReal)) l
      (𝓝 ((-(|x - m| + δ) ^ 2 / (2 * v) : ℝ) : EReal)) := by
    refine (continuous_coe_real_ereal.tendsto _).comp ?_
    simpa [g, neg_div, Function.comp_def] using (hg.tendsto 0).comp (NNReal.tendsto_coe.2 hε)
  rw [← hlim.liminf_eq]
  exact liminf_le_liminf hlow

/-- The Gaussian lower bound: every neighbourhood of `x` has liminf rate at least
`-(x - m)² / (2v)`. -/
private theorem neg_le_liminf_coe_mul_log_gaussianReal [l.NeBot] (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (hε : Tendsto ε l (𝓝 0)) (hpos : ∀ᶠ i in l, 0 < ε i) {x : ℝ} {U : Set ℝ} (hU : U ∈ 𝓝 x) :
    -(ENNReal.ofReal ((x - m) ^ 2 / (2 * v)) : EReal) ≤
      liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (gaussianReal m (ε i * v) U)) l := by
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.mem_nhds_iff.1 hU
  -- Let the radius of the interval tend to `0`.
  have hlim : Tendsto (fun δ : ℝ => ((-(|x - m| + δ) ^ 2 / (2 * v) : ℝ) : EReal)) (𝓝[>] 0)
      (𝓝 ((-(x - m) ^ 2 / (2 * v) : ℝ) : EReal)) := by
    refine (continuous_coe_real_ereal.tendsto _).comp (tendsto_nhdsWithin_of_tendsto_nhds ?_)
    have : Continuous fun δ : ℝ => -(|x - m| + δ) ^ 2 / (2 * v) := by fun_prop
    simpa [sq_abs] using this.tendsto 0
  rw [EReal.coe_ennreal_ofReal, max_eq_left (by positivity), ← EReal.coe_neg, ← neg_div]
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ
  refine coe_le_liminf_coe_mul_log_gaussianReal m hv hε hpos hδ.1 fun y hy => hball ?_
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hy.1, hy.2, hδ.2]

/-- **Large deviations of Gaussian laws.** At an eventually positive speed `ε` tending to `0`,
the Gaussian laws `gaussianReal m (ε i * v)`, `v ≠ 0`, satisfy a large deviation principle with
rate function `x ↦ (x - m)² / (2v)`. -/
theorem hasLDP_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (hε : Tendsto ε l (𝓝 0))
    (hpos : ∀ᶠ i in l, 0 < ε i) :
    HasLDP l ε (fun i => gaussianReal m (ε i * v))
      (fun x => ENNReal.ofReal ((x - m) ^ 2 / (2 * v))) := by
  have hcont : Continuous fun x : ℝ => ENNReal.ofReal ((x - m) ^ 2 / (2 * v)) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  rcases l.eq_or_neBot with rfl | hl
  · exact ⟨hcont.lowerSemicontinuous, fun _ _ => by simp, fun _ _ => by simp⟩
  exact ⟨hcont.lowerSemicontinuous, fun G hG => EReal.neg_coe_ennreal_biInf_le_iff.2 fun x hx =>
    neg_le_liminf_coe_mul_log_gaussianReal m hv hε hpos (hG.mem_nhds hx),
    fun F _ => limsup_coe_mul_log_gaussianReal_le m hv hε hpos F⟩

/-- At an eventually positive and eventually bounded speed `ε`, the Gaussian laws
`gaussianReal m (ε i * v)` are exponentially tight. -/
theorem isExponentiallyTight_gaussianReal (m : ℝ) (v : ℝ≥0) (hε : IsBoundedUnder (· ≤ ·) l ε)
    (hpos : ∀ᶠ i in l, 0 < ε i) :
    IsExponentiallyTight l ε (fun i => gaussianReal m (ε i * v)) := by
  refine isExponentiallyTight_iff.2 fun L => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · -- Dirac masses at `m` are carried by `{m}`.
    refine ⟨{m}, isCompact_singleton, (limsup_congr ?_).trans_le
      (limsup_const_bot.trans_le bot_le)⟩
    filter_upwards [hpos] with i hi
    simpa using EReal.mul_bot_of_pos (by exact_mod_cast hi)
  obtain ⟨B, hB⟩ := hε
  -- Outside a ball of radius `√(2vs)`, with `s ≥ L + B log 2`, the rate is below `-L`.
  set s := max (L + B * Real.log 2) 0
  refine ⟨Metric.closedBall m √(2 * v * s), isCompact_closedBall _ _,
    limsup_le_of_le (by isBoundedDefault) ?_⟩
  filter_upwards [hpos, hB] with i hi hBi
  have hBi' : (ε i : ℝ) ≤ B := hBi
  have hsub : (Metric.closedBall m √(2 * v * s))ᶜ ⊆ {x | √(2 * v * s) ≤ |x - m|} := fun x hx => by
    rw [mem_compl_iff, Metric.mem_closedBall, not_le, Real.dist_eq] at hx
    exact hx.le
  refine (coe_mul_log_gaussianReal_le m hv hi (le_max_right _ _) hsub).trans ?_
  rw [← EReal.coe_neg, EReal.coe_le_coe_iff]
  nlinarith [le_max_left (L + B * Real.log 2) 0, Real.log_pos one_lt_two]

/-- The Gaussian rate function `x ↦ (x - m)² / (2v)`, `v ≠ 0`, is a good rate function. -/
theorem isGoodRateFunction_ofReal_sq_sub_div (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    IsGoodRateFunction fun x => ENNReal.ofReal ((x - m) ^ 2 / (2 * v)) := by
  have hε : Tendsto (fun n : ℕ => (n : ℝ≥0)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ≥0)⁻¹ :=
    (eventually_gt_atTop 0).mono fun n hn => by positivity
  have h := hasLDP_gaussianReal m hv hε hpos
  exact (isExponentiallyTight_gaussianReal m v hε.isBoundedUnder_le hpos).isGoodRateFunction
    h.lowerSemicontinuous h.lower_bound

end TauCeti.Probability

namespace ProbabilityTheory.iIndepFun

open TauCeti.Probability

/-- **Cramér's theorem for Gaussian laws.** The sample means `(X 0 + ⋯ + X (n - 1)) / n` of
independent random variables with common law `gaussianReal m v`, `v ≠ 0`, satisfy a large
deviation principle at speed `1 / n` with rate function `x ↦ (x - m)² / (2v)`. -/
theorem hasLDP_map_sum_range_div_of_hasLaw_gaussianReal {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℕ → Ω → ℝ} (hind : iIndepFun X P) {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX : ∀ i, HasLaw (X i) (gaussianReal m v) P) :
    HasLDP atTop (fun n : ℕ => (n : ℝ≥0)⁻¹)
      (fun n => P.map fun ω => (∑ i ∈ Finset.range n, X i ω) / n)
      (fun x => ENNReal.ofReal ((x - m) ^ 2 / (2 * v))) := by
  -- For `n ≥ 1` the sample mean has law `gaussianReal m (v / n)`; at `n = 0` it is the constant
  -- `0`, so the laws agree only eventually.
  have hlaw : ∀ᶠ n : ℕ in atTop, P.map (fun ω => (∑ i ∈ Finset.range n, X i ω) / n) =
      gaussianReal m ((n : ℝ≥0)⁻¹ * v) := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hsum := hind.hasLaw_finset_sum_convolutionPower hX (Finset.range n)
    rw [Finset.card_range, gaussianReal_convolutionPower] at hsum
    have hmean := gaussianReal_div_const hsum n
    simp only [Finset.sum_apply] at hmean
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
    rw [hmean.map_eq]
    congr 1
    · field_simp
    · ext
      simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_mul, NNReal.coe_inv,
        NNReal.coe_natCast]
      field_simp
  have hε : Tendsto (fun n : ℕ => (n : ℝ≥0)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ≥0)⁻¹ :=
    (eventually_gt_atTop 0).mono fun n hn => by positivity
  have h := hasLDP_gaussianReal m hv hε hpos
  refine ⟨h.lowerSemicontinuous, fun G hG => (h.lower_bound G hG).trans_eq (liminf_congr ?_),
    fun F hF => (limsup_congr ?_).trans_le (h.upper_bound F hF)⟩ <;>
  · filter_upwards [hlaw] with n hn
    rw [hn]

end ProbabilityTheory.iIndepFun

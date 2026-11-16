/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Concentration.Poincare.LogSobolev
public import Mathlib.Probability.Moments.SubGaussian
import TauCeti.Analysis.Calculus.BumpFunction.SmoothApprox
import TauCeti.MeasureTheory.Measure.Tail
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Herbst's argument and sub-Gaussian concentration for Lipschitz functions

If a probability measure `μ` on a finite-dimensional real normed space satisfies
`MeasureTheory.Measure.LogSobolevInequality μ C` with `C : ℝ≥0`, then every `K`-Lipschitz function
`f : E → ℝ` is exponentially integrable, integrable, and centered sub-Gaussian with sharp variance
proxy `C * K ^ 2`, giving the two-sided tail bound
`μ.real {x | t ≤ |f x - ∫ y, f y ∂μ|} ≤ 2 * exp (-t² / (2 * C * K²))` for `0 ≤ t`. No prior
integrability hypothesis on `f` is assumed, and `μ` need not have a density.

The proof proceeds in two stages:
1. **Herbst's differential inequality** for smooth bounded functions `g` with `∫ g ∂μ = 0` and
   `‖fderiv ℝ g‖ ≤ K`: applying `LogSobolevInequality` to `x ↦ exp (t * g x / 2)` bounds the
   derivative of `t ↦ log (∫ exp (t * g) ∂μ) / t` on `(0, ∞)` by `C * K² / 2`, while vanishing of
   the mean makes the difference quotient continuous at `0`.
2. **Truncation and smooth Lipschitz approximation**: truncating `f` to `[-(n + 1), n + 1]` and
   convolving via `LipschitzOnWith.exists_contDiff_lipschitzWith_mem_Icc_dist_lt` yields smooth
   bounded `K`-Lipschitz approximants `g n → f` with `|g n x| ≤ |f x| + 1`. Symmetrizing on
   `μ.prod μ` cancels the means `∫ g n ∂μ` so Fatou's lemma yields exponential integrability of `f`
   first; dominated convergence then passes Herbst's bound to `f - ∫ f ∂μ` without loss in the
   constant.

## Main results

* `MeasureTheory.Measure.LogSobolevInequality.integrable_exp_mul_of_lipschitzWith`: `exp (t * f)`
  is `μ`-integrable for every `K`-Lipschitz `f` and `t : ℝ`.
* `MeasureTheory.Measure.LogSobolevInequality.integrable_of_lipschitzWith`: every Lipschitz
  function is `μ`-integrable.
* `MeasureTheory.Measure.LogSobolevInequality.hasSubgaussianMGF_sub_integral_of_lipschitzWith`:
  `f - ∫ f ∂μ` satisfies `HasSubgaussianMGF` with variance proxy `C * K ^ 2`.
* `MeasureTheory.Measure.LogSobolevInequality.measureReal_abs_sub_integral_ge_le_of_lipschitzWith`:
  two-sided Gaussian tail bound `2 * exp (-t² / (2 * C * K²))` for `0 ≤ t`.

## References

* I. Herbst, unpublished letter to L. Gross (1975); see E. B. Davies and B. Simon,
  *Ultracontractivity and the heat kernel for Schrödinger operators and Dirichlet forms*,
  J. Funct. Anal. **59** (1984), 335–395.
* M. Ledoux, *The Concentration of Measure Phenomenon*, AMS, 2001, §5.1 (Proposition 5.3).
* S. Boucheron, G. Lugosi, and P. Massart, *Concentration Inequalities*, Oxford University Press,
  2013, §5.3 (Theorem 5.5).
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real
open scoped ContDiff ENNReal NNReal Topology

namespace MeasureTheory.Measure

section SmoothBounded

variable {E : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E] [OpensMeasurableSpace E]
  {μ : Measure E} [IsProbabilityMeasure μ] {C K : ℝ≥0} {g : E → ℝ} {M : ℝ}

private theorem integrable_exp_mul_of_abs_le (hg : Continuous g) (hM : ∀ x, |g x| ≤ M) (t : ℝ) :
    Integrable (fun x ↦ exp (t * g x)) μ := by
  refine Integrable.of_bound (continuous_exp.comp (continuous_const.mul hg)).aestronglyMeasurable
    (exp (|t| * M)) (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  refine exp_le_exp.2 ?_
  calc t * g x ≤ |t * g x| := le_abs_self _
    _ = |t| * |g x| := abs_mul t (g x)
    _ ≤ |t| * M := mul_le_mul_of_nonneg_left (hM x) (abs_nonneg t)

private theorem integral_exp_mul_pos_of_abs_le (hg : Continuous g) (hM : ∀ x, |g x| ≤ M) (t : ℝ) :
    0 < ∫ x, exp (t * g x) ∂μ := by
  have hlo : exp (-(|t| * M)) ≤ ∫ x, exp (t * g x) ∂μ := by
    have hmono := integral_mono (integrable_const (μ := μ) (exp (-(|t| * M))))
      (integrable_exp_mul_of_abs_le hg hM t) fun x ↦ by
      refine exp_le_exp.2 ?_
      have habs : |t * g x| ≤ |t| * M := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg t)
      exact neg_le_of_abs_le habs
    simpa using hmono
  exact (exp_pos _).trans_le hlo

private theorem hasDerivAt_integral_exp_mul (hg : Continuous g) (hM : ∀ x, |g x| ≤ M) (t : ℝ) :
    HasDerivAt (fun s ↦ ∫ x, exp (s * g x) ∂μ) (∫ x, g x * exp (t * g x) ∂μ) t := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x ↦ exp (s * g x))
    (F' := fun s x ↦ g x * exp (s * g x))
    (x₀ := t) (bound := fun _ ↦ M * exp ((|t| + 1) * M))
    (s := Metric.ball t 1) (Metric.ball_mem_nhds t zero_lt_one)
    ?_ (integrable_exp_mul_of_abs_le hg hM t) ?_ ?_ (integrable_const _) ?_).2
  · exact Eventually.of_forall fun s ↦
      (continuous_exp.comp (continuous_const.mul hg)).aestronglyMeasurable
  · exact (hg.mul (continuous_exp.comp (continuous_const.mul hg))).aestronglyMeasurable
  · refine ae_of_all _ fun x s hs ↦ ?_
    have hs_abs : |s| ≤ |t| + 1 := by
      have hd : |s - t| < 1 := by simpa [Real.dist_eq] using Metric.mem_ball.1 hs
      linarith [abs_sub_abs_le_abs_sub s t]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
    refine mul_le_mul (hM x) (exp_le_exp.2 ?_) (exp_pos _).le hM0
    calc s * g x ≤ |s * g x| := le_abs_self _
      _ = |s| * |g x| := abs_mul s (g x)
      _ ≤ (|t| + 1) * M := mul_le_mul hs_abs (hM x) (abs_nonneg _) (by positivity)
  · refine ae_of_all _ fun x s _ ↦ ?_
    exact (((hasDerivAt_id s).mul_const (g x)).exp).congr_deriv (by simp only [id_eq]; ring)

variable [NormedSpace ℝ E]

/-- Applying `LogSobolevInequality` to `x ↦ exp (t * g x / 2)` for `t > 0` yields Herbst's
differential inequality for `Z t = ∫ exp (t * g) ∂μ`. -/
private theorem entropy_exp_half_sq_le (hLSI : LogSobolevInequality μ C)
    (hg : ContDiff ℝ ∞ g) (hM : ∀ x, |g x| ≤ M) (hK : ∀ x, ‖fderiv ℝ g x‖ ≤ K)
    {t : ℝ} (ht : 0 < t) :
    t * (∫ x, g x * exp (t * g x) ∂μ) -
        (∫ x, exp (t * g x) ∂μ) * log (∫ x, exp (t * g x) ∂μ) ≤
      ((C : ℝ) * (K : ℝ) ^ 2 / 2) * t ^ 2 * ∫ x, exp (t * g x) ∂μ := by
  let u : E → ℝ := fun x ↦ exp ((t / 2) * g x)
  have hu : ContDiff ℝ ∞ u := Real.contDiff_exp.comp (contDiff_const.mul hg)
  have hu_sq (x : E) : u x ^ 2 = exp (t * g x) := by
    dsimp only [u]
    rw [sq, ← exp_add]
    ring_nf
  have hu_fderiv (x : E) :
      ‖fderiv ℝ u x‖ = (t / 2) * exp ((t / 2) * g x) * ‖fderiv ℝ g x‖ := by
    have hsc := ((hg.differentiable (by simp) x).hasFDerivAt.const_mul (t / 2)).exp
    rw [hsc.fderiv, norm_smul, norm_smul, Real.norm_of_nonneg (exp_pos _).le,
      Real.norm_of_nonneg (by positivity : 0 ≤ t / 2)]
    ring
  have hdu : MemLp (fun x ↦ ‖fderiv ℝ u x‖) 2 μ := by
    refine MemLp.of_bound ((hu.continuous_fderiv (by simp)).norm).aestronglyMeasurable
      ((t / 2) * K * exp (|(t / 2)| * M)) (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _), hu_fderiv]
    have hexp_le : exp ((t / 2) * g x) ≤ exp (|(t / 2)| * M) := by
      refine exp_le_exp.2 ((le_abs_self _).trans ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg _)
    calc (t / 2) * exp ((t / 2) * g x) * ‖fderiv ℝ g x‖
        ≤ (t / 2) * exp (|(t / 2)| * M) * K :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp_le (by positivity)) (hK x)
            (norm_nonneg _) (by positivity)
      _ = (t / 2) * K * exp (|(t / 2)| * M) := by ring
  have hu2 : Integrable (fun x ↦ u x ^ 2) μ := by
    simp_rw [hu_sq]
    exact integrable_exp_mul_of_abs_le hg.continuous hM t
  have hgexp_int : Integrable (fun x ↦ g x * exp (t * g x)) μ := by
    refine ((integrable_exp_mul_of_abs_le hg.continuous hM t).const_mul M).mono'
      (hg.continuous.mul
        (continuous_exp.comp (continuous_const.mul hg.continuous))).aestronglyMeasurable
      (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hM x) (exp_pos _).le
  have hu2log_eq (x : E) : u x ^ 2 * log (u x ^ 2) = t * (g x * exp (t * g x)) := by
    rw [hu_sq, log_exp]
    ring
  have hu2log : Integrable (fun x ↦ u x ^ 2 * log (u x ^ 2)) μ := by
    simp_rw [hu2log_eq]
    exact hgexp_int.const_mul t
  have hlsi := hLSI.apply u hu hdu hu2 hu2log
  rw [entropy_def] at hlsi
  simp_rw [hu2log_eq, hu_sq] at hlsi
  rw [integral_const_mul] at hlsi
  have henergy : ∫ x, ‖fderiv ℝ u x‖ ^ 2 ∂μ ≤
      (t ^ 2 * (K : ℝ) ^ 2 / 4) * ∫ x, exp (t * g x) ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono hdu.integrable_sq
      ((integrable_exp_mul_of_abs_le hg.continuous hM t).const_mul _) fun x ↦ ?_
    dsimp only
    rw [hu_fderiv, mul_pow, mul_pow, ← hu_sq]
    dsimp only [u]
    have hKsq : ‖fderiv ℝ g x‖ ^ 2 ≤ (K : ℝ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hK x) 2
    have hpos : 0 ≤ (t / 2) ^ 2 * exp ((t / 2) * g x) ^ 2 := by positivity
    calc (t / 2) ^ 2 * exp ((t / 2) * g x) ^ 2 * ‖fderiv ℝ g x‖ ^ 2
        ≤ (t / 2) ^ 2 * exp ((t / 2) * g x) ^ 2 * (K : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hKsq hpos
      _ = (t ^ 2 * (K : ℝ) ^ 2 / 4) * exp ((t / 2) * g x) ^ 2 := by ring
  nlinarith [C.coe_nonneg]

/-- Herbst's MGF bound for `0 < t` and smooth bounded mean-zero `g`. -/
private theorem integral_exp_mul_le_of_pos (hLSI : LogSobolevInequality μ C)
    (hg : ContDiff ℝ ∞ g) (hM : ∀ x, |g x| ≤ M) (hK : ∀ x, ‖fderiv ℝ g x‖ ≤ K)
    (hmean : ∫ x, g x ∂μ = 0) {t : ℝ} (ht : 0 < t) :
    ∫ x, exp (t * g x) ∂μ ≤ exp ((C : ℝ) * (K : ℝ) ^ 2 * t ^ 2 / 2) := by
  classical
  let Z : ℝ → ℝ := fun s ↦ ∫ x, exp (s * g x) ∂μ
  let Z' : ℝ → ℝ := fun s ↦ ∫ x, g x * exp (s * g x) ∂μ
  let Λ : ℝ → ℝ := fun s ↦ log (Z s)
  have hZ_pos (s : ℝ) : 0 < Z s := integral_exp_mul_pos_of_abs_le hg.continuous hM s
  have hZ_deriv (s : ℝ) : HasDerivAt Z (Z' s) s :=
    hasDerivAt_integral_exp_mul hg.continuous hM s
  have hΛ_deriv (s : ℝ) : HasDerivAt Λ (Z' s / Z s) s :=
    (hZ_deriv s).log (hZ_pos s).ne'
  have hΛ0 : Λ 0 = 0 := by simp [Λ, Z]
  have hZ'0 : Z' 0 = 0 := by simpa [Z'] using hmean
  have hΛ_deriv0 : HasDerivAt Λ 0 0 := by
    simpa [hZ'0] using hΛ_deriv 0
  let H : ℝ → ℝ := Function.update (fun s ↦ (Λ s - Λ 0) / (s - 0)) 0 0
  have hH_pos {s : ℝ} (hs : 0 < s) : H s = Λ s / s := by
    simp [H, hs.ne', hΛ0]
  have hH_deriv {s : ℝ} (hs : 0 < s) :
      HasDerivAt H ((s * Z' s - Z s * Λ s) / (s ^ 2 * Z s)) s := by
    have hdiv : HasDerivAt (fun r ↦ Λ r / r)
        ((Z' s / Z s * s - Λ s * 1) / s ^ 2) s :=
      (hΛ_deriv s).div (hasDerivAt_id s) hs.ne'
    have heq : (fun r ↦ Λ r / r) =ᶠ[𝓝 s] H := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
      exact (hH_pos hr).symm
    refine (hdiv.congr_of_eventuallyEq heq.symm).congr_deriv ?_
    have hZs : Z s ≠ 0 := (hZ_pos s).ne'
    have hss : s ≠ 0 := hs.ne'
    field_simp
  let c := (C : ℝ) * (K : ℝ) ^ 2 / 2
  let φ : ℝ → ℝ := fun s ↦ c * s - H s
  have hφ_deriv {s : ℝ} (hs : 0 < s) :
      HasDerivAt φ (c - (s * Z' s - Z s * Λ s) / (s ^ 2 * Z s)) s :=
    (((hasDerivAt_id s).const_mul c).fun_sub (hH_deriv hs)).congr_deriv (by ring)
  have hφ_cont : ContinuousOn φ (Set.Ici 0) := by
    intro s hs
    rcases (Set.mem_Ici.1 hs).eq_or_lt with rfl | hs_pos
    · exact ((continuousAt_const.mul continuousAt_id).sub
        hΛ_deriv0.continuousAt_div).continuousWithinAt
    · exact (hφ_deriv hs_pos).continuousAt.continuousWithinAt
  have hφ_diff : DifferentiableOn ℝ φ (interior (Set.Ici 0)) := by
    rw [interior_Ici]
    intro s hs
    exact (hφ_deriv hs).differentiableAt.differentiableWithinAt
  have hφ_deriv_nonneg : ∀ s ∈ interior (Set.Ici 0), 0 ≤ deriv φ s := by
    rw [interior_Ici]
    intro s hs
    rw [(hφ_deriv hs).deriv, sub_nonneg, div_le_iff₀ (mul_pos (sq_pos_of_pos hs) (hZ_pos s))]
    simpa only [c, Z, Z', Λ, mul_assoc] using entropy_exp_half_sq_le hLSI hg hM hK hs
  have hmono := monotoneOn_of_deriv_nonneg (convex_Ici 0) hφ_cont hφ_diff hφ_deriv_nonneg
    (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht.le) ht.le
  have hφ0 : φ 0 = 0 := by simp [φ, H]
  rw [hφ0] at hmono
  have hle : Λ t / t ≤ c * t := by
    dsimp only [φ] at hmono
    rw [hH_pos ht] at hmono
    linarith
  have hlog_le : log (Z t) ≤ (C : ℝ) * (K : ℝ) ^ 2 * t ^ 2 / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hle ht.le
    rw [div_mul_cancel₀ _ ht.ne'] at hmul
    exact hmul.trans_eq (by dsimp only [c]; ring)
  rw [← exp_log (integral_exp_mul_pos_of_abs_le hg.continuous hM t)]
  exact exp_le_exp.2 hlog_le

/-- Herbst's MGF bound for all `t : ℝ` and smooth bounded mean-zero `g`. -/
private theorem integral_exp_mul_le_of_contDiff_of_abs_le (hLSI : LogSobolevInequality μ C)
    (hg : ContDiff ℝ ∞ g) (hM : ∀ x, |g x| ≤ M) (hK : ∀ x, ‖fderiv ℝ g x‖ ≤ K)
    (hmean : ∫ x, g x ∂μ = 0) (t : ℝ) :
    ∫ x, exp (t * g x) ∂μ ≤ exp ((C : ℝ) * (K : ℝ) ^ 2 * t ^ 2 / 2) := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hneg_pos : 0 < -t := neg_pos.2 ht
    have hneg_mean : ∫ x, (-g) x ∂μ = 0 := by simp [integral_neg, hmean]
    have hneg_K (x : E) : ‖fderiv ℝ (-g) x‖ ≤ K := by
      rw [fderiv_neg, norm_neg]
      exact hK x
    have hneg_M (x : E) : |(-g) x| ≤ M := by simp [hM x]
    have h := integral_exp_mul_le_of_pos hLSI hg.neg hneg_M hneg_K hneg_mean hneg_pos
    simpa only [Pi.neg_apply, mul_neg, neg_mul, neg_neg, neg_sq] using h
  · simp
  · exact integral_exp_mul_le_of_pos hLSI hg hM hK hmean ht

/-- Centered Herbst MGF bound for a smooth bounded `K`-Lipschitz function. -/
private theorem integral_exp_mul_sub_integral_le_of_contDiff_of_abs_le
    (hLSI : LogSobolevInequality μ C)
    (hg : ContDiff ℝ ∞ g) (hgK : LipschitzWith K g) (hM : ∀ x, |g x| ≤ M) (t : ℝ) :
    ∫ x, exp (t * (g x - ∫ y, g y ∂μ)) ∂μ ≤ exp ((C : ℝ) * (K : ℝ) ^ 2 * t ^ 2 / 2) := by
  have hg_int : Integrable g μ :=
    Integrable.of_bound hg.continuous.aestronglyMeasurable M
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hM x)
  let m := ∫ y, g y ∂μ
  have hm_le : |m| ≤ M := by
    calc |m| ≤ ∫ y, ‖g y‖ ∂μ := by rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
      _ ≤ ∫ _, M ∂μ := integral_mono hg_int.norm (integrable_const M)
          (fun y ↦ by simpa only [Real.norm_eq_abs] using hM y)
      _ = M := by simp
  have hmean : ∫ x, (g x - m) ∂μ = 0 := by
    rw [integral_sub hg_int (integrable_const m), integral_const]
    simp [m]
  have hbd (x : E) : |g x - m| ≤ 2 * M := by
    linarith [abs_sub (g x) m, hM x, hm_le]
  have hgrad (x : E) : ‖fderiv ℝ (fun y ↦ g y - m) x‖ ≤ K := by
    rw [fderiv_sub_const]
    exact norm_fderiv_le_of_lipschitz ℝ hgK
  exact integral_exp_mul_le_of_contDiff_of_abs_le hLSI (hg.sub contDiff_const) hbd hgrad hmean t

end SmoothBounded

section Lipschitz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsProbabilityMeasure μ] {C K : ℝ≥0} {f : E → ℝ}

/-- Under a logarithmic Sobolev inequality on a finite-dimensional real normed space, every
Lipschitz function is exponentially integrable with respect to `μ`. -/
theorem LogSobolevInequality.integrable_exp_mul_of_lipschitzWith
    (hLSI : LogSobolevInequality μ C) (hf : LipschitzWith K f) (t : ℝ) :
    Integrable (fun x ↦ exp (t * f x)) μ := by
  -- Symmetrize smooth bounded approximants `g n` on `μ.prod μ` to cancel `∫ g n ∂μ` before Fatou.
  obtain ⟨g, hgs, hgK, hgbdd, _, hg_lim⟩ := hf.exists_contDiff_lipschitzWith_abs_le_tendsto
  let B := exp ((C : ℝ) * (K : ℝ) ^ 2 * t ^ 2)
  have hprod_le (n : ℕ) :
      ∫⁻ p, ENNReal.ofReal (exp (t * (g n p.2 - g n p.1))) ∂(μ.prod μ) ≤ ENNReal.ofReal B := by
    obtain ⟨M, hM⟩ := hgbdd n
    let m := ∫ y, g n y ∂μ
    have hpos := integral_exp_mul_sub_integral_le_of_contDiff_of_abs_le hLSI (hgs n) (hgK n) hM t
    have hneg :=
      integral_exp_mul_sub_integral_le_of_contDiff_of_abs_le hLSI (hgs n) (hgK n) hM (-t)
    simp only [neg_sq] at hneg
    have hmul : (∫ x, exp ((-t) * (g n x - m)) ∂μ) * (∫ y, exp (t * (g n y - m)) ∂μ) ≤ B := by
      calc (∫ x, exp ((-t) * (g n x - m)) ∂μ) * (∫ y, exp (t * (g n y - m)) ∂μ)
          ≤ exp ((C : ℝ) * (K : ℝ) ^ 2 * t ^ 2 / 2) *
              exp ((C : ℝ) * (K : ℝ) ^ 2 * t ^ 2 / 2) :=
            mul_le_mul hneg hpos (integral_nonneg fun _ ↦ (exp_pos _).le) (exp_pos _).le
        _ = B := by rw [← exp_add]; dsimp only [B]; ring_nf
    rw [← integral_prod_mul (μ := μ) (ν := μ)] at hmul
    have heq (p : E × E) :
        exp ((-t) * (g n p.1 - m)) * exp (t * (g n p.2 - m)) = exp (t * (g n p.2 - g n p.1)) := by
      rw [← exp_add]
      ring_nf
    simp_rw [heq] at hmul
    have hint : Integrable (fun p : E × E ↦ exp (t * (g n p.2 - g n p.1))) (μ.prod μ) := by
      have hgc : Continuous (g n) := (hgs n).continuous
      refine Integrable.of_bound
        (by fun_prop : Continuous fun p : E × E ↦
          exp (t * (g n p.2 - g n p.1))).aestronglyMeasurable
        (exp (|t| * (2 * M))) (ae_of_all _ fun p ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      refine exp_le_exp.2 ((le_abs_self _).trans ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (by linarith [abs_sub (g n p.2) (g n p.1), hM p.2, hM p.1]) (abs_nonneg t)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ (exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hmul
  have hlim_pt (p : E × E) :
      liminf (fun n ↦ ENNReal.ofReal (exp (t * (g n p.2 - g n p.1)))) atTop =
        ENNReal.ofReal (exp (t * (f p.2 - f p.1))) :=
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (continuous_exp.continuousAt.tendsto.comp
        (((hg_lim p.2).sub (hg_lim p.1)).const_mul t))).liminf_eq
  have hfatou :
      ∫⁻ p, ENNReal.ofReal (exp (t * (f p.2 - f p.1))) ∂(μ.prod μ) ≤ ENNReal.ofReal B := by
    calc ∫⁻ p, ENNReal.ofReal (exp (t * (f p.2 - f p.1))) ∂(μ.prod μ)
        = ∫⁻ p, liminf (fun n ↦ ENNReal.ofReal (exp (t * (g n p.2 - g n p.1)))) atTop ∂(μ.prod μ) :=
          by simp_rw [hlim_pt]
      _ ≤ liminf (fun n ↦
            ∫⁻ p, ENNReal.ofReal (exp (t * (g n p.2 - g n p.1))) ∂(μ.prod μ)) atTop := by
          refine lintegral_liminf_le fun n ↦ ?_
          have hgc : Continuous (g n) := (hgs n).continuous
          exact (ENNReal.continuous_ofReal.comp
            (by fun_prop : Continuous fun p : E × E ↦ exp (t * (g n p.2 - g n p.1)))).measurable
      _ ≤ ENNReal.ofReal B := liminf_le_of_frequently_le' (Frequently.of_forall hprod_le)
  have hf_cont : Continuous f := hf.continuous
  have hmeas_prod : Measurable fun p : E × E ↦ ENNReal.ofReal (exp (t * (f p.2 - f p.1))) :=
    (ENNReal.continuous_ofReal.comp
      (by fun_prop : Continuous fun p : E × E ↦ exp (t * (f p.2 - f p.1)))).measurable
  -- Pick a basepoint `x₀` with finite slice integral by Tonelli's theorem.
  rw [lintegral_prod _ hmeas_prod.aemeasurable] at hfatou
  have hae : ∀ᵐ x ∂μ, (∫⁻ y, ENNReal.ofReal (exp (t * (f y - f x))) ∂μ) < ⊤ :=
    ae_lt_top hmeas_prod.lintegral_prod_right' (hfatou.trans_lt ENNReal.ofReal_lt_top).ne
  have : (ae μ).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero μ)
  obtain ⟨x₀, hx₀⟩ := hae.exists
  refine ⟨(by fun_prop : Continuous fun y ↦ exp (t * f y)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ (exp_pos _).le)]
  have hsplit : (∫⁻ y, ENNReal.ofReal (exp (t * f y)) ∂μ) =
      ∫⁻ y, ENNReal.ofReal (exp (t * f x₀)) * ENNReal.ofReal (exp (t * (f y - f x₀))) ∂μ := by
    refine lintegral_congr fun y ↦ ?_
    rw [← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
    ring_nf
  rw [hsplit, lintegral_const_mul _
    (by fun_prop : Continuous fun y ↦ exp (t * (f y - f x₀))).measurable.ennreal_ofReal]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hx₀

/-- Under a logarithmic Sobolev inequality on a finite-dimensional real normed space, every
Lipschitz function is integrable with respect to `μ`. -/
theorem LogSobolevInequality.integrable_of_lipschitzWith
    (hLSI : LogSobolevInequality μ C) (hf : LipschitzWith K f) :
    Integrable f μ := by
  have h1 := hLSI.integrable_exp_mul_of_lipschitzWith hf 1
  have h2 := hLSI.integrable_exp_mul_of_lipschitzWith hf (-1)
  refine (h1.add h2).mono' hf.continuous.aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, Pi.add_apply, one_mul, neg_one_mul]
  rcases le_total 0 (f x) with hx | hx
  · rw [abs_of_nonneg hx]
    linarith [add_one_le_exp (f x), exp_pos (-f x)]
  · rw [abs_of_nonpos hx]
    linarith [add_one_le_exp (-f x), exp_pos (f x)]

/-- **Herbst's sub-Gaussian concentration theorem**: under `LogSobolevInequality μ C` on a
finite-dimensional real normed space, `f - ∫ f ∂μ` is sub-Gaussian with variance proxy `C * K ^ 2`
for every `K`-Lipschitz function `f : E → ℝ`. -/
theorem LogSobolevInequality.hasSubgaussianMGF_sub_integral_of_lipschitzWith
    (hLSI : LogSobolevInequality μ C) (hf : LipschitzWith K f) :
    HasSubgaussianMGF (fun x ↦ f x - ∫ y, f y ∂μ) (C * K ^ 2) μ := by
  let m := ∫ y, f y ∂μ
  refine ⟨fun t ↦ ?_, fun t ↦ ?_⟩
  · have hexp := hLSI.integrable_exp_mul_of_lipschitzWith hf t
    have hrew (x : E) :
        exp (t * (f x - ∫ y, f y ∂μ)) = exp (-t * m) * exp (t * f x) := by
      dsimp only [m]
      rw [← exp_add]
      ring_nf
    simp_rw [hrew]
    exact hexp.const_mul (exp (-t * m))
  · rw [mgf]
    -- Pass the smooth bounded MGF bound to `f - m` by dominated convergence using `exp (|t| * f)`.
    obtain ⟨g, hgs, hgK, hgbdd, hg_dom, hg_lim⟩ := hf.exists_contDiff_lipschitzWith_abs_le_tendsto
    have hf_int : Integrable f μ := hLSI.integrable_of_lipschitzWith hf
    have hm_lim : Tendsto (fun n ↦ ∫ y, g n y ∂μ) atTop (𝓝 m) :=
      tendsto_integral_of_dominated_convergence (fun x ↦ |f x| + 1)
        (fun n ↦ (hgs n).continuous.aestronglyMeasurable)
        (hf_int.abs.add (integrable_const 1))
        (fun n ↦ ae_of_all _ fun x ↦ (Real.norm_eq_abs (g n x)).trans_le (hg_dom n x))
        (ae_of_all _ hg_lim)
    have hm_ev : ∀ᶠ n in atTop, |∫ y, g n y ∂μ| ≤ |m| + 1 := by
      filter_upwards [(tendsto_iff_dist_tendsto_zero.1 hm_lim).eventually
        (gt_mem_nhds zero_lt_one)] with n hn
      rw [Real.dist_eq] at hn
      linarith [abs_sub_abs_le_abs_sub (∫ y, g n y ∂μ) m]
    let dom : E → ℝ := fun x ↦
      exp (|t| * (|m| + 2)) * (exp (|t| * f x) + exp ((-|t|) * f x))
    have hdom_int : Integrable dom μ :=
      ((hLSI.integrable_exp_mul_of_lipschitzWith hf |t|).add
        (hLSI.integrable_exp_mul_of_lipschitzWith hf (-|t|))).const_mul _
    have hmgf_lim :
        Tendsto (fun n ↦ ∫ x, exp (t * (g n x - ∫ y, g n y ∂μ)) ∂μ) atTop
          (𝓝 (∫ x, exp (t * (f x - m)) ∂μ)) := by
      refine tendsto_integral_filter_of_dominated_convergence dom
        (Eventually.of_forall fun n ↦ ?_) ?_ hdom_int (ae_of_all _ fun x ↦ ?_)
      · have hgc : Continuous (g n) := (hgs n).continuous
        exact (by fun_prop : Continuous _).aestronglyMeasurable
      · filter_upwards [hm_ev] with n hmn
        refine ae_of_all _ fun x ↦ ?_
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        have hexp_le : exp (t * (g n x - ∫ y, g n y ∂μ)) ≤
            exp (|t| * (|m| + 2)) * exp (|t| * |f x|) := by
          rw [← exp_add]
          refine exp_le_exp.2 ?_
          have h1 : t * (g n x - ∫ y, g n y ∂μ) ≤ |t| * |g n x - ∫ y, g n y ∂μ| := by
            rw [← abs_mul]; exact le_abs_self _
          have h2 : |g n x - ∫ y, g n y ∂μ| ≤ |f x| + (|m| + 2) := by
            linarith [abs_sub (g n x) (∫ y, g n y ∂μ), hg_dom n x, hmn]
          calc t * (g n x - ∫ y, g n y ∂μ)
              ≤ |t| * (|f x| + (|m| + 2)) :=
                h1.trans (mul_le_mul_of_nonneg_left h2 (abs_nonneg t))
            _ = |t| * (|m| + 2) + |t| * |f x| := by ring
        refine hexp_le.trans (mul_le_mul_of_nonneg_left ?_ (exp_pos _).le)
        rcases le_total 0 (f x) with hfx | hfx
        · rw [abs_of_nonneg hfx]
          linarith [exp_pos ((-|t|) * f x)]
        · rw [abs_of_nonpos hfx, mul_neg, ← neg_mul]
          linarith [exp_pos (|t| * f x)]
      · exact continuous_exp.continuousAt.tendsto.comp
          (((hg_lim x).sub hm_lim).const_mul t)
    have hbd_n (n : ℕ) : ∫ x, exp (t * (g n x - ∫ y, g n y ∂μ)) ∂μ ≤
        exp ((C : ℝ) * (K : ℝ) ^ 2 * t ^ 2 / 2) := by
      obtain ⟨M, hM⟩ := hgbdd n
      exact integral_exp_mul_sub_integral_le_of_contDiff_of_abs_le hLSI (hgs n) (hgK n) hM t
    exact le_of_tendsto hmgf_lim (Eventually.of_forall hbd_n)

/-- Two-sided Gaussian tail concentration around the mean for `K`-Lipschitz functions under
`LogSobolevInequality μ C`. -/
theorem LogSobolevInequality.measureReal_abs_sub_integral_ge_le_of_lipschitzWith
    (hLSI : LogSobolevInequality μ C) (hf : LipschitzWith K f) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {x | t ≤ |f x - ∫ y, f y ∂μ|} ≤
      2 * exp (-t ^ 2 / (2 * (C : ℝ) * (K : ℝ) ^ 2)) := by
  have hsub := hLSI.hasSubgaussianMGF_sub_integral_of_lipschitzWith hf
  have htail₁ := hsub.measure_ge_le ht
  have htail₂ := hsub.neg.measure_ge_le ht
  calc μ.real {x | t ≤ |f x - ∫ y, f y ∂μ|}
      ≤ μ.real {x | t ≤ f x - ∫ y, f y ∂μ} + μ.real {x | t ≤ -(f x - ∫ y, f y ∂μ)} :=
        TauCeti.measureReal_le_abs_le_add (f := fun x ↦ f x - ∫ y, f y ∂μ)
    _ ≤ exp (-t ^ 2 / (2 * ((C * K ^ 2 : ℝ≥0) : ℝ))) +
          exp (-t ^ 2 / (2 * ((C * K ^ 2 : ℝ≥0) : ℝ))) :=
        add_le_add htail₁ htail₂
    _ = 2 * exp (-t ^ 2 / (2 * (C : ℝ) * (K : ℝ) ^ 2)) := by
        push_cast
        ring_nf

end Lipschitz

end MeasureTheory.Measure

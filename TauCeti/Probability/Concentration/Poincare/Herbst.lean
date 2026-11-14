/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Concentration.Poincare.LogSobolev
public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.MGFAnalytic
import TauCeti.Analysis.Calculus.BumpFunction.SmoothApprox
import TauCeti.MeasureTheory.Integral.Bochner.Fatou
import TauCeti.Probability.Concentration.SubgaussianTail

/-!
# Herbst's argument: Lipschitz concentration under a logarithmic Sobolev inequality

Let `μ` be a probability measure on a finite-dimensional real normed space satisfying the
logarithmic Sobolev inequality `Ent_μ(f²) ≤ 2 C ∫ ‖∇f‖² dμ`
(`MeasureTheory.Measure.LogSobolevInequality`). Then every `K`-Lipschitz function `f` is
sub-Gaussian about its mean with variance proxy `C K²`:
`∫ exp (t (f - ∫ f dμ)) dμ ≤ exp (C K² t² / 2)` for every real `t`. In particular `f` has
exponential moments of every order, and it deviates from its mean by at least `t ≥ 0` with
probability at most `2 exp (-t² / (2 C K²))`. The bound depends on the dimension only through `C`,
so a logarithmic Sobolev inequality with a dimension-free constant gives dimension-free Gaussian
concentration of Lipschitz statistics.

## Main results

* `MeasureTheory.Measure.LogSobolevInequality.hasSubgaussianMGF_of_lipschitzWith`: a `K`-Lipschitz
  function is sub-Gaussian about its mean with variance proxy `C K²`.
* `MeasureTheory.Measure.LogSobolevInequality.measureReal_abs_sub_integral_ge_le_of_lipschitzWith`:
  the two-sided tail bound `2 exp (-t² / (2 C K²))`.

## Implementation notes

For a smooth function `G` with values in `[-M, M]` and `‖∇G‖ ≤ K`, the inequality applied to
`exp (t G / 2)` gives Herbst's differential inequality
`t H'(t) - H(t) log H(t) ≤ (C K² t² / 2) H(t)` for `H t = ∫ exp (t G) dμ`. Hence
`t ↦ log H(t) / t - C K² t / 2` is antitone on `(0, ∞)`, and its limit at `0⁺` is `∫ G dμ`.
A general Lipschitz function is a pointwise limit of such functions with the same Lipschitz
constant; their means stay bounded, and Fatou's lemma passes the bound to the limit, with no
integrability assumption on `f`.

## References

* G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, §2.3.2,
  Lemma 2.3.3.
* M. Ledoux, *The Concentration of Measure Phenomenon*, Chapter 5.
-/

public section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped ContDiff Topology NNReal

namespace MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ] {K : ℝ≥0}

section Bounded

variable {C : ℝ≥0} {G : E → ℝ} {M : ℝ}

/-- **Herbst's differential inequality.** For a smooth `G` with values in `[-M, M]` and gradient
bounded by `K`, the logarithmic Sobolev inequality applied to `exp (t G / 2)` gives
`t ∫ G exp (t G) dμ - H log H ≤ (C K² t² / 2) H`, where `H = ∫ exp (t G) dμ`. -/
private lemma LogSobolevInequality.mul_integral_mul_exp_sub_mgf_mul_log_le
    (h : LogSobolevInequality μ C) (hG : ContDiff ℝ ∞ G) (hGM : ∀ x, |G x| ≤ M)
    (hGK : ∀ x, ‖fderiv ℝ G x‖ ≤ K) (t : ℝ) :
    t * ∫ x, G x * exp (t * G x) ∂μ - mgf G μ t * log (mgf G μ t) ≤
      C * K ^ 2 * t ^ 2 / 2 * mgf G μ t := by
  let u : E → ℝ := fun y ↦ exp (t / 2 * G y)
  have hu : ContDiff ℝ ∞ u := (contDiff_const.mul hG).exp
  have hu2 (y : E) : u y ^ 2 = exp (t * G y) := by
    rw [← exp_nat_mul]; congr 1; push_cast; ring
  have hdu (y : E) : ‖fderiv ℝ u y‖ = exp (t / 2 * G y) * (|t / 2| * ‖fderiv ℝ G y‖) := by
    rw [(((hG.differentiable (by simp) y).hasFDerivAt.const_mul (t / 2)).exp).fderiv, norm_smul,
      norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  have hdu_sq (y : E) : ‖fderiv ℝ u y‖ ^ 2 ≤ K ^ 2 * t ^ 2 / 4 * exp (t * G y) := by
    have hK : ‖fderiv ℝ G y‖ ^ 2 ≤ (K : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hGK y) 2
    calc ‖fderiv ℝ u y‖ ^ 2 = t ^ 2 / 4 * ‖fderiv ℝ G y‖ ^ 2 * u y ^ 2 := by
          rw [hdu, mul_pow, mul_pow, sq_abs]; ring
      _ ≤ t ^ 2 / 4 * K ^ 2 * u y ^ 2 := by gcongr
      _ = K ^ 2 * t ^ 2 / 4 * exp (t * G y) := by rw [hu2]; ring
  have hint : Integrable (fun x ↦ exp (t * G x)) μ :=
    integrable_exp_mul_of_mem_Icc hG.continuous.aemeasurable (.of_forall fun x ↦ abs_le.1 (hGM x))
  have hGexp : Integrable (fun x ↦ G x * exp (t * G x)) μ :=
    hint.bdd_mul hG.continuous.aestronglyMeasurable (.of_forall fun x ↦ by
      rw [Real.norm_eq_abs]; exact hGM x)
  have hdf : MemLp (fun x ↦ ‖fderiv ℝ u x‖) 2 μ :=
    .of_bound (hu.continuous_fderiv (by simp)).norm.aestronglyMeasurable
      (exp (|t / 2| * M) * (|t / 2| * K)) (.of_forall fun y ↦ by
        have he : exp (t / 2 * G y) ≤ exp (|t / 2| * M) := exp_le_exp.2 <|
          (le_abs_self _).trans (by rw [abs_mul]; gcongr; exact hGM y)
        rw [norm_norm, hdu]
        exact mul_le_mul he (mul_le_mul_of_nonneg_left (hGK y) (abs_nonneg _)) (by positivity)
          (by positivity))
  have hf2log : Integrable (fun x ↦ u x ^ 2 * log (u x ^ 2)) μ := by
    simp_rw [hu2, log_exp]
    exact (hGexp.const_mul t).congr (.of_forall fun x ↦ by ring)
  have hent : entropy μ (fun x ↦ u x ^ 2) =
      t * ∫ x, G x * exp (t * G x) ∂μ - mgf G μ t * log (mgf G μ t) := by
    simp_rw [entropy_def, hu2, log_exp, mgf, ← integral_const_mul]
    congr 2 with x
    ring
  have hgrad : ∫ x, ‖fderiv ℝ u x‖ ^ 2 ∂μ ≤ K ^ 2 * t ^ 2 / 4 * mgf G μ t := by
    rw [mgf, ← integral_const_mul]
    exact integral_mono hdf.integrable_sq (hint.const_mul _) hdu_sq
  calc _ = entropy μ (fun x ↦ u x ^ 2) := hent.symm
    _ ≤ 2 * C * ∫ x, ‖fderiv ℝ u x‖ ^ 2 ∂μ :=
        h.apply u hu hdf (by simpa only [hu2] using hint) hf2log
    _ ≤ 2 * C * (K ^ 2 * t ^ 2 / 4 * mgf G μ t) := by gcongr
    _ = C * K ^ 2 * t ^ 2 / 2 * mgf G μ t := by ring

/-- **Herbst's argument** at positive parameters, for a smooth `G` with values in `[-M, M]` and
gradient bounded by `K`: `∫ exp (t G) dμ ≤ exp (t ∫ G dμ + C K² t² / 2)` for `t > 0`. -/
private lemma LogSobolevInequality.mgf_le_of_pos (h : LogSobolevInequality μ C)
    (hG : ContDiff ℝ ∞ G) (hGM : ∀ x, |G x| ≤ M) (hGK : ∀ x, ‖fderiv ℝ G x‖ ≤ K) {t : ℝ}
    (ht : 0 < t) : mgf G μ t ≤ exp (t * ∫ x, G x ∂μ + C * K ^ 2 * t ^ 2 / 2) := by
  have hint (s : ℝ) : Integrable (fun x ↦ exp (s * G x)) μ :=
    integrable_exp_mul_of_mem_Icc hG.continuous.aemeasurable (.of_forall fun x ↦ abs_le.1 (hGM x))
  have hpos (s : ℝ) : 0 < mgf G μ s := mgf_pos (hint s)
  have hset : integrableExpSet G μ = univ := eq_univ_of_forall hint
  have hΛ (s : ℝ) : HasDerivAt (fun r ↦ log (mgf G μ r))
      ((∫ x, G x * exp (s * G x) ∂μ) / mgf G μ s) s :=
    (hasDerivAt_mgf (by simp [hset])).log (hpos s).ne'
  -- The function `φ s = log H(s) / s - C K² s / 2`, with `H = mgf G μ`.
  let φ : ℝ → ℝ := fun s ↦ log (mgf G μ s) / s - C * K ^ 2 / 2 * s
  have hφ (s : ℝ) (hs : s ≠ 0) : HasDerivAt φ (((∫ x, G x * exp (s * G x) ∂μ) / mgf G μ s * s -
      log (mgf G μ s) * 1) / s ^ 2 - C * K ^ 2 / 2 * 1) s :=
    ((hΛ s).div (hasDerivAt_id' s) hs).sub ((hasDerivAt_id' s).const_mul _)
  -- Herbst's differential inequality says that `φ` is antitone on `(0, ∞)`.
  have hanti : AntitoneOn φ (Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0)
      (fun s hs ↦ (hφ s (ne_of_gt hs)).continuousAt.continuousWithinAt) ?_ ?_ <;>
      rw [interior_Ioi]
    · exact fun s hs ↦ (hφ s (ne_of_gt hs)).differentiableAt.differentiableWithinAt
    · intro s (hs : 0 < s)
      have key := h.mul_integral_mul_exp_sub_mgf_mul_log_le hG hGM hGK s
      rw [(hφ s hs.ne').deriv]
      set I := ∫ x, G x * exp (s * G x) ∂μ
      set m := mgf G μ s
      rw [mul_one, mul_one, sub_nonpos, div_le_iff₀ (by positivity), div_mul_eq_mul_div,
        sub_le_iff_le_add, div_le_iff₀ (hpos s)]
      linear_combination key
  -- At `0⁺`, `φ` tends to the derivative of `log H` at `0`, which is `∫ G dμ`.
  have hlim : Tendsto φ (𝓝[>] 0) (𝓝 (∫ x, G x ∂μ)) := by
    have h0 := (hΛ 0).tendsto_slope_zero_right
    simp only [zero_add, mgf_zero, log_one, sub_zero, zero_mul, exp_zero, mul_one, div_one,
      smul_eq_mul] at h0
    have hlin : Tendsto (fun s : ℝ ↦ C * K ^ 2 / 2 * s) (𝓝[>] 0) (𝓝 0) :=
      ((continuous_const_mul _).tendsto' 0 0 (mul_zero _)).mono_left nhdsWithin_le_nhds
    simpa [φ, div_eq_inv_mul] using h0.sub hlin
  have hle : φ t ≤ ∫ x, G x ∂μ := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT ht] with s hs
    exact hanti hs.1 ht hs.2.le
  have hlog : log (mgf G μ t) ≤ t * ∫ x, G x ∂μ + C * K ^ 2 * t ^ 2 / 2 := by
    have h1 : log (mgf G μ t) / t ≤ ∫ x, G x ∂μ + C * K ^ 2 / 2 * t := by
      simp only [φ] at hle; linarith
    rw [div_le_iff₀ ht] at h1
    linarith
  calc mgf G μ t = exp (log (mgf G μ t)) := (exp_log (hpos t)).symm
    _ ≤ _ := exp_le_exp.2 hlog

/-- **Herbst's argument** for a smooth `G` with values in `[-M, M]` and gradient bounded by
`K`: `∫ exp (t G) dμ ≤ exp (t ∫ G dμ + C K² t² / 2)` for every `t`. -/
private lemma LogSobolevInequality.mgf_le (h : LogSobolevInequality μ C) (hG : ContDiff ℝ ∞ G)
    (hGM : ∀ x, |G x| ≤ M) (hGK : ∀ x, ‖fderiv ℝ G x‖ ≤ K) (t : ℝ) :
    mgf G μ t ≤ exp (t * ∫ x, G x ∂μ + C * K ^ 2 * t ^ 2 / 2) := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · -- Apply the positive case to `-G` at `-t`.
    have hneg := h.mgf_le_of_pos hG.neg (G := -G) (by simpa using hGM)
      (by simpa [fderiv_neg] using hGK) (neg_pos.2 ht)
    rw [mgf_neg, neg_neg, Pi.neg_def, integral_neg] at hneg
    convert hneg using 2
    ring
  · simp
  · exact h.mgf_le_of_pos hG hGM hGK ht

/-- **Herbst's argument** for a smooth `G` with values in `[-M, M]` and gradient bounded by `K`:
`G` is sub-Gaussian about its mean with variance proxy `C K²`. -/
private lemma LogSobolevInequality.hasSubgaussianMGF_of_contDiff (h : LogSobolevInequality μ C)
    (hG : ContDiff ℝ ∞ G) (hGM : ∀ x, |G x| ≤ M) (hGK : ∀ x, ‖fderiv ℝ G x‖ ≤ K) :
    HasSubgaussianMGF (fun x ↦ G x - ∫ y, G y ∂μ) (C * K ^ 2) μ where
  integrable_exp_mul t := by
    simp_rw [mul_sub, exp_sub]
    exact (integrable_exp_mul_of_mem_Icc hG.continuous.aemeasurable
      (.of_forall fun x ↦ abs_le.1 (hGM x))).div_const _
  mgf_le t := by
    simp_rw [sub_eq_add_neg]
    rw [mgf_add_const]
    calc mgf G μ t * exp (t * -∫ y, G y ∂μ)
        ≤ exp (t * ∫ x, G x ∂μ + C * K ^ 2 * t ^ 2 / 2) * exp (t * -∫ y, G y ∂μ) := by
          gcongr; exact h.mgf_le hG hGM hGK t
      _ = exp (↑(C * K ^ 2) * t ^ 2 / 2) := by
          rw [← exp_add]; push_cast; ring_nf

end Bounded

section Lipschitz

variable [FiniteDimensional ℝ E] {C : ℝ} {f : E → ℝ}

/-- **Herbst's argument.** Under the logarithmic Sobolev inequality with nonnegative constant `C`,
every `K`-Lipschitz function `f` is sub-Gaussian about its mean with variance proxy `C K²`:
`∫ exp (t (f - ∫ f dμ)) dμ ≤ exp (C K² t² / 2)` for every `t`, and each of these exponential
moments is finite. -/
theorem LogSobolevInequality.hasSubgaussianMGF_of_lipschitzWith (h : LogSobolevInequality μ C)
    (hC : 0 ≤ C) (hf : LipschitzWith K f) :
    HasSubgaussianMGF (fun x ↦ f x - ∫ y, f y ∂μ) (C.toNNReal * K ^ 2) μ := by
  lift C to ℝ≥0 using hC
  simp only [Real.toNNReal_coe]
  obtain ⟨g, hgs, hgn, hgK, hgf, hlim⟩ := hf.exists_seq_contDiff_tendsto
  have hsub (n : ℕ) := h.hasSubgaussianMGF_of_contDiff (hgs n) (hgn n) (hgK n)
  obtain ⟨B, hB⟩ := hf.continuous.measurable.exists_forall_abs_integral_le_of_hasSubgaussianMGF
    hgf hsub
  -- Fatou's lemma gives every exponential moment of `f`.
  have hexp (t : ℝ) : Integrable (fun x ↦ exp (t * f x)) μ := by
    refine TauCeti.integrable_of_tendsto_of_integral_le
      (D := exp (|t| * B + C * K ^ 2 * t ^ 2 / 2))
      (.of_forall fun n ↦ integrable_exp_mul_of_mem_Icc (hgs n).continuous.aemeasurable
        (.of_forall fun x ↦ abs_le.1 (hgn n x)))
      (.of_forall fun _ ↦ .of_forall fun _ ↦ (exp_pos _).le)
      (.of_forall fun x ↦ ((hlim x).const_mul t).rexp) (.of_forall fun n ↦ ?_)
    refine (h.mgf_le (hgs n) (hgn n) (hgK n) t).trans (exp_le_exp.2 ?_)
    have : t * ∫ y, g n y ∂μ ≤ |t| * B :=
      (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB n) (abs_nonneg t))
    linarith
  have hset : integrableExpSet f μ = univ := eq_univ_of_forall hexp
  have hfint : Integrable f μ := integrable_of_mem_interior_integrableExpSet (by simp [hset])
  -- Dominated convergence identifies the limit of the means.
  have hm : Tendsto (fun n ↦ ∫ y, g n y ∂μ) atTop (𝓝 (∫ y, f y ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x ↦ |f x| + 1)
      (fun n ↦ (hgs n).continuous.aestronglyMeasurable) (hfint.abs.add (integrable_const 1))
      (fun n ↦ .of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hgf n x) (.of_forall hlim)
  -- Fatou's lemma passes the centred bounds of the approximants to `f`.
  have hcent (t : ℝ) : ∀ᵐ x ∂μ, Tendsto (fun n ↦ exp (t * (g n x - ∫ y, g n y ∂μ))) atTop
      (𝓝 (exp (t * (f x - ∫ y, f y ∂μ)))) :=
    .of_forall fun x ↦ (((hlim x).sub hm).const_mul t).rexp
  have hpos (t : ℝ) (n : ℕ) : 0 ≤ᵐ[μ] fun x ↦ exp (t * (g n x - ∫ y, g n y ∂μ)) :=
    .of_forall fun _ ↦ (exp_pos _).le
  exact ⟨fun t ↦ TauCeti.integrable_of_tendsto_of_integral_le
      (.of_forall fun n ↦ (hsub n).integrable_exp_mul t) (.of_forall (hpos t)) (hcent t)
      (.of_forall fun n ↦ (hsub n).mgf_le t),
    fun t ↦ TauCeti.integral_le_of_tendsto_of_integral_le
      (.of_forall fun n ↦ (hsub n).integrable_exp_mul t) (.of_forall (hpos t)) (hcent t)
      (.of_forall fun n ↦ (hsub n).mgf_le t)⟩

/-- **Gaussian concentration of Lipschitz functions** under a logarithmic Sobolev inequality with
nonnegative constant `C`: a `K`-Lipschitz function `f` deviates from its mean by at least `t ≥ 0`
with probability at most `2 exp (-t² / (2 C K²))`. -/
theorem LogSobolevInequality.measureReal_abs_sub_integral_ge_le_of_lipschitzWith
    (h : LogSobolevInequality μ C) (hC : 0 ≤ C) (hf : LipschitzWith K f) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {x | t ≤ |f x - ∫ y, f y ∂μ|} ≤ 2 * exp (-t ^ 2 / (2 * (C * (K : ℝ) ^ 2))) := by
  simpa only [NNReal.coe_mul, NNReal.coe_pow, Real.coe_toNNReal C hC] using
    (h.hasSubgaussianMGF_of_lipschitzWith hC hf).measureReal_abs_ge_le ht

end Lipschitz

end MeasureTheory.Measure

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Entropy.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
import TauCeti.Analysis.SpecialFunctions.Log.MulLog
import TauCeti.Probability.Distributions.Gaussian.IntegrationByParts.Basic
import TauCeti.Probability.Distributions.Gaussian.Symmetry
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.HasLaw

/-!
# The scalar Gaussian logarithmic Sobolev inequality for bounded test functions

This file proves Gross's logarithmic Sobolev inequality `Ent_γ(f²) ≤ 2 E[(f')²]` for the standard
Gaussian law `γ = gaussianReal 0 1` on `ℝ`, for continuously differentiable functions `f : ℝ → ℝ`
with bounded values and bounded derivative. The companion module
`TauCeti.Probability.Concentration.Poincare.Gaussian.LogSobolev.Basic` removes the boundedness
assumptions via compactly supported cutoffs and lifts the inequality to finite-dimensional real
inner product spaces by tensorization and isometric transport.

The proof adapts the trigonometric Ornstein–Uhlenbeck interpolation on `[0, π / 2]` from
`TauCeti.Probability.Distributions.Gaussian.Poincare` to the regularized functional
`g x = f x ^ 2 + ε` (`ε > 0`), differentiating `ψ θ = ∫ x, P θ x * log (P θ x) ∂γ` where
`P θ x = ∫ y, g (cos θ * x + sin θ * y) ∂γ` so no `1 / sin θ` singularity arises at `θ = 0`.

## Main result

* `TauCeti.Probability.entropy_sq_le_two_mul_integral_deriv_sq_gaussianReal`: for `ContDiff ℝ 1 f`
  with bounded `f` and `deriv f`, `(gaussianReal 0 1).entropy (fun x ↦ f x ^ 2) ≤
  2 * ∫ x, deriv f x ^ 2 ∂(gaussianReal 0 1)`.

## References

* L. Gross, *Logarithmic Sobolev inequalities*, Amer. J. Math. **97** (1975), 1061–1083.
* C. Houdré and V. Pérez-Abreu, *Covariance identities and inequalities for functionals on Wiener
  and Poisson spaces*, Ann. Probab. **23** (1995), 400–419.
* M. Ledoux, *The Concentration of Measure Phenomenon*, AMS, 2001, §5.1.
* D. Bakry, I. Gentil, and M. Ledoux, *Analysis and Geometry of Markov Diffusion Operators*,
  Springer, 2014, §5.5.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real
open scoped NNReal Topology

namespace TauCeti.Probability

local notation "γ" => gaussianReal 0 1

section Interpolation

variable {g : ℝ → ℝ} {ε M L : ℝ}

/-- Trigonometric Gaussian interpolation `P θ x = E[g(cos θ · x + sin θ · Y)]` for `Y ~ N(0, 1)`. -/
private def gaussianInterp (g : ℝ → ℝ) (θ x : ℝ) : ℝ :=
  ∫ y, g (cos θ * x + sin θ * y) ∂γ

/-- Angle derivative `∂_θ P θ x` of `gaussianInterp`. -/
private def gaussianInterpDerivTheta (g : ℝ → ℝ) (θ x : ℝ) : ℝ :=
  ∫ y, deriv g (cos θ * x + sin θ * y) * (-sin θ * x + cos θ * y) ∂γ

private theorem sq_le_of_abs_le {x A : ℝ} (h : |x| ≤ A) : x ^ 2 ≤ A ^ 2 := by
  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2

private theorem integrable_of_abs_le {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {h : α → ℝ} {C : ℝ}
    (hc : Continuous h) (hb : ∀ x, |h x| ≤ C) : Integrable h μ :=
  Integrable.of_bound hc.aestronglyMeasurable C <|
    ae_of_all _ fun x ↦ (Real.norm_eq_abs _).trans_le (hb x)

private theorem abs_deriv_mul_le (hdg : ∀ x, |deriv g x| ≤ L) (t x y : ℝ) :
    |deriv g (cos t * x + sin t * y) * (-sin t * x + cos t * y)| ≤ L * (|x| + |y|) := by
  rw [abs_mul]
  refine mul_le_mul (hdg _) ((abs_add_le _ _).trans ?_) (abs_nonneg _)
    ((abs_nonneg _).trans (hdg 0))
  rw [abs_mul, abs_mul, abs_neg]
  nlinarith [abs_sin_le_one t, abs_cos_le_one t, abs_nonneg x, abs_nonneg y]

private theorem abs_two_mul_deriv_le {f : ℝ → ℝ} {A B : ℝ}
    (hA : ∀ x, |f x| ≤ A) (hB : ∀ x, |deriv f x| ≤ B) (x : ℝ) :
    |2 * f x * deriv f x| ≤ 2 * A * B := by
  rw [abs_mul, abs_mul, abs_of_nonneg zero_le_two]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hA x) zero_le_two) (hB x)
    (abs_nonneg _) (by have := (abs_nonneg _).trans (hA 0); positivity)

private theorem integrable_comp_gaussianInterp (hg : ContDiff ℝ 1 g)
    (hε : 0 < ε) (hlo : ∀ x, ε ≤ g x) (hhi : ∀ x, g x ≤ M) (θ x : ℝ) :
    Integrable (fun y ↦ g (cos θ * x + sin θ * y)) γ :=
  have := hg.continuous
  integrable_of_abs_le (by fun_prop) fun _ ↦ by
    rw [abs_of_pos (hε.trans_le (hlo _))]; exact hhi _

private theorem gaussianInterp_mem_Icc (hg : ContDiff ℝ 1 g)
    (hε : 0 < ε) (hlo : ∀ x, ε ≤ g x) (hhi : ∀ x, g x ≤ M) (θ x : ℝ) :
    ε ≤ gaussianInterp g θ x ∧ gaussianInterp g θ x ≤ M := by
  have hint := integrable_comp_gaussianInterp hg hε hlo hhi θ x
  exact ⟨by simpa [gaussianInterp] using integral_mono (integrable_const ε) hint fun _ ↦ hlo _,
    by simpa [gaussianInterp] using integral_mono hint (integrable_const M) fun _ ↦ hhi _⟩

private theorem hasDerivAt_gaussianInterp_x (hg : ContDiff ℝ 1 g)
    (hε : 0 < ε) (hlo : ∀ x, ε ≤ g x) (hhi : ∀ x, g x ≤ M) (hdg : ∀ x, |deriv g x| ≤ L)
    (θ x : ℝ) :
    HasDerivAt (gaussianInterp g θ)
      (cos θ * ∫ y, deriv g (cos θ * x + sin θ * y) ∂γ) x := by
  have := hg.continuous
  rw [← integral_const_mul]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z y ↦ g (cos θ * z + sin θ * y))
    (F' := fun z y ↦ cos θ * deriv g (cos θ * z + sin θ * y))
    (x₀ := x) (bound := fun _ ↦ L) (s := Set.univ) Filter.univ_mem
    (.of_forall fun _ ↦ (by fun_prop : Continuous _).aestronglyMeasurable)
    (integrable_comp_gaussianInterp hg hε hlo hhi θ x)
    (by fun_prop : Continuous _).aestronglyMeasurable
    (ae_of_all _ fun _ _ _ ↦ by
      rw [Real.norm_eq_abs, abs_mul]
      simpa only [one_mul] using mul_le_mul (abs_cos_le_one θ) (hdg _) (abs_nonneg _) zero_le_one)
    (integrable_const L) (ae_of_all _ fun y z _ ↦
      ((hg.differentiable one_ne_zero _).hasDerivAt.comp z <| by
        simpa using ((hasDerivAt_id z).const_mul (cos θ)).add_const (sin θ * y)).congr_deriv
        (mul_comm _ _))).2

private theorem contDiff_gaussianInterp_x (hg : ContDiff ℝ 1 g)
    (hε : 0 < ε) (hlo : ∀ x, ε ≤ g x) (hhi : ∀ x, g x ≤ M) (hdg : ∀ x, |deriv g x| ≤ L)
    (θ : ℝ) : ContDiff ℝ 1 (gaussianInterp g θ) := by
  have hd := hasDerivAt_gaussianInterp_x hg hε hlo hhi hdg θ
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x ↦ (hd x).differentiableAt, ?_⟩
  rw [show deriv (gaussianInterp g θ) = _ from funext fun x ↦ (hd x).deriv]
  exact continuous_const.mul <| continuous_of_dominated
    (fun _ ↦ (by fun_prop : Continuous _).aestronglyMeasurable)
    (fun _ ↦ ae_of_all _ fun _ ↦ (Real.norm_eq_abs _).trans_le (hdg _))
    (integrable_const L) (ae_of_all _ fun _ ↦ by fun_prop)

private theorem hasDerivAt_gaussianInterp_theta (hg : ContDiff ℝ 1 g)
    (hε : 0 < ε) (hlo : ∀ x, ε ≤ g x) (hhi : ∀ x, g x ≤ M) (hdg : ∀ x, |deriv g x| ≤ L)
    (θ x : ℝ) :
    HasDerivAt (fun t ↦ gaussianInterp g t x) (gaussianInterpDerivTheta g θ x) θ := by
  have := hg.continuous
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t y ↦ g (cos t * x + sin t * y))
    (F' := fun t y ↦ deriv g (cos t * x + sin t * y) * (-sin t * x + cos t * y))
    (x₀ := θ) (bound := fun y ↦ L * (|x| + |y|)) (s := Set.univ) Filter.univ_mem
    (.of_forall fun _ ↦ (by fun_prop : Continuous _).aestronglyMeasurable)
    (integrable_comp_gaussianInterp hg hε hlo hhi θ x)
    (by fun_prop : Continuous _).aestronglyMeasurable
    (ae_of_all _ fun y t _ ↦ (Real.norm_eq_abs _).trans_le (abs_deriv_mul_le hdg t x y))
    (((integrable_const |x|).add (integrable_abs_gaussianReal 0 1)).const_mul L)
    (ae_of_all _ fun y t _ ↦ (hg.differentiable one_ne_zero _).hasDerivAt.comp t <|
      ((hasDerivAt_cos t).mul_const x).add ((hasDerivAt_sin t).mul_const y))).2

private theorem abs_log_add_one_le_of_mem_Icc {u : ℝ} (hε : 0 < ε) (hlo : ε ≤ u) (hhi : u ≤ M) :
    |log u + 1| ≤ |log ε| + |log M| + 1 :=
  abs_le.2 ⟨by linarith [log_le_log hε hlo, neg_abs_le (log ε), abs_nonneg (log M)],
    by linarith [log_le_log (hε.trans_le hlo) hhi, le_abs_self (log M), abs_nonneg (log ε)]⟩

private theorem abs_gaussianInterpDerivTheta_le (hg : ContDiff ℝ 1 g)
    (hdg : ∀ x, |deriv g x| ≤ L) (t x : ℝ) :
    |gaussianInterpDerivTheta g t x| ≤ L * (|x| + ∫ y, |y| ∂γ) := by
  have hb_int : Integrable (fun y ↦ L * (|x| + |y|)) γ :=
    ((integrable_const |x|).add (integrable_abs_gaussianReal 0 1)).const_mul L
  calc |gaussianInterpDerivTheta g t x|
      ≤ ∫ y, ‖deriv g (cos t * x + sin t * y) * (-sin t * x + cos t * y)‖ ∂γ := by
        rw [gaussianInterpDerivTheta, ← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    _ ≤ ∫ y, L * (|x| + |y|) ∂γ := integral_mono
        (hb_int.mono' (by have := hg.continuous_deriv le_rfl; fun_prop)
          (ae_of_all _ fun y ↦ by
            rw [norm_norm, Real.norm_eq_abs]; exact abs_deriv_mul_le hdg t x y))
        hb_int fun y ↦ (Real.norm_eq_abs _).trans_le (abs_deriv_mul_le hdg t x y)
    _ = L * (|x| + ∫ y, |y| ∂γ) := by
        rw [integral_const_mul,
          integral_add (integrable_const |x|) (integrable_abs_gaussianReal 0 1)]; simp

private theorem hasDerivAt_integral_gaussianInterp_mul_log (hg : ContDiff ℝ 1 g)
    (hε : 0 < ε) (hlo : ∀ x, ε ≤ g x) (hhi : ∀ x, g x ≤ M) (hdg : ∀ x, |deriv g x| ≤ L)
    (θ : ℝ) :
    HasDerivAt (fun t ↦ ∫ x, gaussianInterp g t x * log (gaussianInterp g t x) ∂γ)
      (∫ p, (log (gaussianInterp g θ p.1) + 1) *
        (deriv g (cos θ * p.1 + sin θ * p.2) * (-sin θ * p.1 + cos θ * p.2))
        ∂(Measure.prod γ γ)) θ := by
  have := hg.continuous_deriv le_rfl
  let CΦ := |log ε| + |log M| + 1
  let Φ : ℝ → ℝ → ℝ := fun t x ↦ log (gaussianInterp g t x) + 1
  have hP_pos (t x : ℝ) : 0 < gaussianInterp g t x :=
    hε.trans_le (gaussianInterp_mem_Icc hg hε hlo hhi t x).1
  have hP_cont (t : ℝ) : Continuous (gaussianInterp g t) :=
    (contDiff_gaussianInterp_x hg hε hlo hhi hdg t).continuous
  have hΦ_le (t x : ℝ) : |Φ t x| ≤ CΦ :=
    abs_log_add_one_le_of_mem_Icc hε (gaussianInterp_mem_Icc hg hε hlo hhi t x).1
      (gaussianInterp_mem_Icc hg hε hlo hhi t x).2
  have hprod_int : Integrable (fun p : ℝ × ℝ ↦
      Φ θ p.1 * (deriv g (cos θ * p.1 + sin θ * p.2) * (-sin θ * p.1 + cos θ * p.2)))
      (Measure.prod γ γ) := by
    have hΦc : Continuous (Φ θ) :=
      ((hP_cont θ).log fun x ↦ (hP_pos θ x).ne').add continuous_const
    refine ((integrable_abs_add_abs_gaussianReal 0 0 1 1).const_mul (CΦ * L)).mono'
      ((hΦc.comp continuous_fst).mul (by fun_prop)).aestronglyMeasurable (ae_of_all _ fun p ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, mul_assoc]
    exact mul_le_mul (hΦ_le θ p.1) (abs_deriv_mul_le hdg θ p.1 p.2) (abs_nonneg _) (by positivity)
  have hfub_pt (x : ℝ) :
      ∫ y, Φ θ x * (deriv g (cos θ * x + sin θ * y) * (-sin θ * x + cos θ * y)) ∂γ =
        Φ θ x * gaussianInterpDerivTheta g θ x := integral_const_mul _ _
  rw [integral_prod _ hprod_int, integral_congr_ae (ae_of_all _ hfub_pt)]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x ↦ gaussianInterp g t x * log (gaussianInterp g t x))
    (F' := fun t x ↦ Φ t x * gaussianInterpDerivTheta g t x)
    (x₀ := θ) (bound := fun x ↦ CΦ * (L * (|x| + ∫ y, |y| ∂γ))) (s := Set.univ) Filter.univ_mem
    (.of_forall fun t ↦ (Real.continuous_mul_log.comp (hP_cont t)).aestronglyMeasurable)
    (integrable_of_abs_le (Real.continuous_mul_log.comp (hP_cont θ)) fun x ↦
      TauCeti.abs_mul_log_le_one_add_abs_mul_log (hP_pos θ x).le
        (gaussianInterp_mem_Icc hg hε hlo hhi θ x).2)
    (hprod_int.integral_prod_left.aestronglyMeasurable.congr (ae_of_all _ hfub_pt))
    (ae_of_all _ fun x t _ ↦ by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hΦ_le t x) (abs_gaussianInterpDerivTheta_le hg hdg t x)
        (abs_nonneg _) (by positivity))
    ((((integrable_abs_gaussianReal 0 1).add (integrable_const _)).const_mul L).const_mul CΦ)
    (ae_of_all _ fun x t _ ↦ by
      exact (Real.hasDerivAt_mul_log (hP_pos t x).ne').comp t
        (hasDerivAt_gaussianInterp_theta hg hε hlo hhi hdg t x))).2

/-- Planar reflection symmetry and Gaussian integration by parts rewrite the cross derivative
against `Φ` as `-sin θ * ∫ x, Φ' x * (∫ y, g'(cos θ · x + sin θ · y) ∂γ) ∂γ`. -/
private theorem integral_mul_interp_deriv {Φ g : ℝ → ℝ} {A₁ B₁ B₂ : ℝ}
    (hΦ : ContDiff ℝ 1 Φ) (hA₁ : ∀ x, |Φ x| ≤ A₁) (hB₁ : ∀ x, |deriv Φ x| ≤ B₁)
    (hg : ContDiff ℝ 1 g) (hB₂ : ∀ x, |deriv g x| ≤ B₂) (θ : ℝ) :
    ∫ p, Φ p.1 * (deriv g (cos θ * p.1 + sin θ * p.2) * (-sin θ * p.1 + cos θ * p.2))
        ∂(Measure.prod γ γ) =
      -sin θ * ∫ x, deriv Φ x * (∫ y, deriv g (cos θ * x + sin θ * y) ∂γ) ∂γ := by
  have := hΦ.continuous
  have hB₂0 : 0 ≤ B₂ := (abs_nonneg _).trans (hB₂ 0)
  have hmp := measurePreserving_reflection_gaussianReal θ
  set c := cos θ; set s := sin θ
  have hrot (p : ℝ × ℝ) : c * (c * p.1 + s * p.2) + s * (s * p.1 - c * p.2) = p.1 := by
    linear_combination p.1 * cos_sq_add_sin_sq θ
  let H : ℝ × ℝ → ℝ := fun q ↦ Φ (c * q.1 + s * q.2) * (deriv g q.1 * (-q.2))
  have hHc : Continuous H := by fun_prop
  have hHint : Integrable H (Measure.prod γ γ) :=
    ((integrable_abs_add_abs_gaussianReal 0 0 1 1).const_mul (A₁ * B₂)).mono'
      hHc.aestronglyMeasurable <| ae_of_all _ fun q ↦ by
        simp only [H, Real.norm_eq_abs, abs_mul, abs_neg, mul_assoc]
        exact mul_le_mul (hA₁ _) (mul_le_mul (hB₂ _) (le_add_of_nonneg_left (abs_nonneg _))
          (abs_nonneg _) hB₂0) (by positivity) ((abs_nonneg _).trans (hA₁ 0))
  have hch1 := hmp.hasLaw.integral_comp hHc.aestronglyMeasurable
  simp only [Function.comp_def] at hch1
  rw [show (fun p : ℝ × ℝ ↦ Φ p.1 * (deriv g (c * p.1 + s * p.2) * (-s * p.1 + c * p.2))) =
      fun p ↦ H (c * p.1 + s * p.2, s * p.1 - c * p.2) from
        funext fun p ↦ by simp only [H, hrot p]; ring, hch1, integral_prod _ hHint]
  have hinner (u : ℝ) : ∫ v, H (u, v) ∂γ = -s * (deriv g u * ∫ v, deriv Φ (c * u + s * v) ∂γ) := by
    simp_rw [show ∀ v, H (u, v) = -(deriv g u) * (v * Φ (c * u + s * v)) from
      fun _ ↦ by simp only [H]; ring]
    rw [integral_const_mul, integral_mul_comp_affine_gaussianReal hΦ hA₁ hB₁]; ring
  simp_rw [hinner, integral_const_mul]; congr 1
  let K : ℝ × ℝ → ℝ := fun q ↦ deriv g q.1 * deriv Φ (c * q.1 + s * q.2)
  let K' : ℝ × ℝ → ℝ := fun p ↦ deriv Φ p.1 * deriv g (c * p.1 + s * p.2)
  have hKc : Continuous K := by fun_prop
  have hKint : Integrable K (Measure.prod γ γ) := integrable_of_abs_le hKc fun _ ↦ by
    simpa only [K, abs_mul] using mul_le_mul (hB₂ _) (hB₁ _) (abs_nonneg _) hB₂0
  have hK'int : Integrable K' (Measure.prod γ γ) := integrable_of_abs_le (by fun_prop) fun _ ↦ by
    simpa only [K', abs_mul] using
      mul_le_mul (hB₁ _) (hB₂ _) (abs_nonneg _) ((abs_nonneg _).trans (hB₁ 0))
  have hch2 := hmp.hasLaw.integral_comp hKc.aestronglyMeasurable
  simp only [Function.comp_def, show (fun p : ℝ × ℝ ↦ K (c * p.1 + s * p.2, s * p.1 - c * p.2)) =
    K' from funext fun p ↦ by simp only [K, K', hrot p]; ring] at hch2
  rw [show (∫ u, deriv g u * (∫ v, deriv Φ (c * u + s * v) ∂γ) ∂γ) = ∫ q, K q ∂(Measure.prod γ γ) by
    rw [integral_prod _ hKint]
    exact integral_congr_ae (.of_forall fun _ ↦ (integral_const_mul _ _).symm),
    ← hch2, integral_prod _ hK'int]
  exact integral_congr_ae (.of_forall fun _ ↦ by dsimp only [K']; exact integral_const_mul _ _)

end Interpolation

/-- Elementary quadratic Cauchy–Schwarz bound: `(E[2 u v])² / E[u² + ε] ≤ 4 E[v²]`. -/
private theorem sq_integral_two_mul_div_le {u v : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hu : Integrable (fun y ↦ u y ^ 2 + ε) γ) (huv : Integrable (fun y ↦ 2 * u y * v y) γ)
    (hv : Integrable (fun y ↦ v y ^ 2) γ) :
    (∫ y, 2 * u y * v y ∂γ) ^ 2 / (∫ y, (u y ^ 2 + ε) ∂γ) ≤ 4 * ∫ y, v y ^ 2 ∂γ := by
  let P := ∫ y, (u y ^ 2 + ε) ∂γ
  let G := ∫ y, 2 * u y * v y ∂γ
  let D := ∫ y, v y ^ 2 ∂γ
  have hP : 0 < P := hε.trans_le <| by
    simpa using integral_mono (integrable_const ε) hu fun _ ↦ le_add_of_nonneg_left (sq_nonneg _)
  let t := G / (2 * P)
  have hu₁₂ : Integrable (fun y ↦ t ^ 2 * (u y ^ 2 + ε) - t * (2 * u y * v y)) γ :=
    (hu.const_mul (t ^ 2)).sub (huv.const_mul t)
  have h0 : 0 ≤ ∫ y, ((t ^ 2 * (u y ^ 2 + ε) - t * (2 * u y * v y)) + v y ^ 2) ∂γ :=
    integral_nonneg fun y ↦ by
      simp only [Pi.zero_apply]
      nlinarith [sq_nonneg (t * u y - v y), mul_nonneg (sq_nonneg t) hε.le]
  rw [integral_add hu₁₂ hv, integral_sub (hu.const_mul _) (huv.const_mul _),
    integral_const_mul, integral_const_mul] at h0
  have htP : t * (2 * P) = G := div_mul_cancel₀ G (by positivity)
  change 0 ≤ t ^ 2 * P - t * G + D at h0; change G ^ 2 / P ≤ 4 * D
  rw [div_le_iff₀ hP, ← htP]; rw [← htP] at h0
  nlinarith [mul_nonneg h0 hP.le]

/-- Integrated Fisher-information bound along the Gaussian interpolation. -/
private theorem integral_sq_deriv_div_gaussianInterp_le
    {f : ℝ → ℝ} {A B ε : ℝ} (hf : ContDiff ℝ 1 f) (hA : ∀ x, |f x| ≤ A)
    (hB : ∀ x, |deriv f x| ≤ B) (hε : 0 < ε) (θ : ℝ) :
    (∫ x, (∫ y, 2 * f (cos θ * x + sin θ * y) * deriv f (cos θ * x + sin θ * y) ∂γ) ^ 2 /
        gaussianInterp (fun z ↦ f z ^ 2 + ε) θ x ∂γ) ≤
      4 * ∫ x, deriv f x ^ 2 ∂γ := by
  have := hf.continuous
  let g : ℝ → ℝ := fun z ↦ f z ^ 2 + ε
  have hg : ContDiff ℝ 1 g := (hf.pow 2).add contDiff_const
  have hg_lo (z : ℝ) : ε ≤ g z := le_add_of_nonneg_left (sq_nonneg _)
  have hg_hi (z : ℝ) : g z ≤ A ^ 2 + ε := add_le_add_left (sq_le_of_abs_le (hA z)) ε
  have hP_pos (x : ℝ) : 0 < gaussianInterp g θ x :=
    hε.trans_le (gaussianInterp_mem_Icc hg hε hg_lo hg_hi θ x).1
  have hpt (x : ℝ) :
      (∫ y, 2 * f (cos θ * x + sin θ * y) * deriv f (cos θ * x + sin θ * y) ∂γ) ^ 2 /
          gaussianInterp g θ x ≤
        4 * ∫ y, deriv f (cos θ * x + sin θ * y) ^ 2 ∂γ :=
    sq_integral_two_mul_div_le hε (integrable_comp_gaussianInterp hg hε hg_lo hg_hi θ x)
      (integrable_of_abs_le (by fun_prop) fun _ ↦ abs_two_mul_deriv_le hA hB _)
      (integrable_of_abs_le (by fun_prop) fun _ ↦ by
        rw [abs_of_nonneg (sq_nonneg _)]; exact sq_le_of_abs_le (hB _))
  have hmp := (measurePreserving_fst (μ := γ) (ν := γ)).comp
    (measurePreserving_reflection_gaussianReal θ)
  have hrot_int : Integrable (fun p : ℝ × ℝ ↦ deriv f (cos θ * p.1 + sin θ * p.2) ^ 2)
      (Measure.prod γ γ) :=
    hmp.integrable_comp_of_integrable <|
      integrable_of_abs_le (h := fun x ↦ deriv f x ^ 2) (by fun_prop) fun _ ↦ by
        rw [abs_of_nonneg (sq_nonneg _)]; exact sq_le_of_abs_le (hB _)
  have hnum_cont : Continuous fun x ↦
      ∫ y, 2 * f (cos θ * x + sin θ * y) * deriv f (cos θ * x + sin θ * y) ∂γ :=
    continuous_of_dominated (fun _ ↦ (by fun_prop : Continuous _).aestronglyMeasurable)
      (fun _ ↦ ae_of_all _ fun _ ↦ (Real.norm_eq_abs _).trans_le (abs_two_mul_deriv_le hA hB _))
      (integrable_const (2 * A * B)) (ae_of_all _ fun _ ↦ by fun_prop)
  have hden_cont : Continuous (gaussianInterp g θ) :=
    continuous_of_dominated (fun _ ↦ (by fun_prop : Continuous _).aestronglyMeasurable)
      (fun _ ↦ ae_of_all _ fun _ ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (hε.trans_le (hg_lo _))]; exact hg_hi _)
      (integrable_const (A ^ 2 + ε)) (ae_of_all _ fun _ ↦ by fun_prop)
  have hI_int : Integrable (fun x ↦
      (∫ y, 2 * f (cos θ * x + sin θ * y) * deriv f (cos θ * x + sin θ * y) ∂γ) ^ 2 /
        gaussianInterp g θ x) γ :=
    (hrot_int.integral_prod_left.const_mul 4).mono'
      ((hnum_cont.pow 2).div hden_cont fun x ↦ (hP_pos x).ne').aestronglyMeasurable
      (ae_of_all _ fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (hP_pos x).le)]; exact hpt x)
  calc _ ≤ ∫ x, (4 * ∫ y, deriv f (cos θ * x + sin θ * y) ^ 2 ∂γ) ∂γ :=
          integral_mono hI_int (hrot_int.integral_prod_left.const_mul 4) hpt
    _ = 4 * ∫ x, deriv f x ^ 2 ∂γ := by
        rw [integral_const_mul, ← integral_prod _ hrot_int]
        exact congrArg (4 * ·) <| hmp.hasLaw.integral_comp
          (by fun_prop : Continuous fun x ↦ deriv f x ^ 2).aestronglyMeasurable

/-- Exact Fisher-information formula for `∂_θ ∫ P θ log (P θ) ∂γ`. -/
private theorem hasDerivAt_integral_gaussianInterp_mul_log_fisher
    {g : ℝ → ℝ} {ε M L : ℝ} (hg : ContDiff ℝ 1 g) (hε : 0 < ε)
    (hlo : ∀ x, ε ≤ g x) (hhi : ∀ x, g x ≤ M) (hdg : ∀ x, |deriv g x| ≤ L) (θ : ℝ) :
    HasDerivAt (fun t ↦ ∫ x, gaussianInterp g t x * log (gaussianInterp g t x) ∂γ)
      (-sin θ * cos θ *
        ∫ x, (∫ y, deriv g (cos θ * x + sin θ * y) ∂γ) ^ 2 / gaussianInterp g θ x ∂γ) θ := by
  let Φ : ℝ → ℝ := fun x ↦ log (gaussianInterp g θ x) + 1
  have hP_pos (x : ℝ) : 0 < gaussianInterp g θ x :=
    hε.trans_le (gaussianInterp_mem_Icc hg hε hlo hhi θ x).1
  have hΦ_deriv (x : ℝ) :
      deriv Φ x = (cos θ * ∫ y, deriv g (cos θ * x + sin θ * y) ∂γ) / gaussianInterp g θ x :=
    (((hasDerivAt_gaussianInterp_x hg hε hlo hhi hdg θ x).log (hP_pos x).ne').add_const 1).deriv
  have hΦ_db (x : ℝ) : |deriv Φ x| ≤ L / ε := by
    rw [hΦ_deriv, abs_div, abs_of_pos (hP_pos x), abs_mul]
    have hint_le : |∫ y, deriv g (cos θ * x + sin θ * y) ∂γ| ≤ L := by
      have hi : Integrable (fun y ↦ ‖deriv g (cos θ * x + sin θ * y)‖) γ :=
        (integrable_of_abs_le (by have := hg.continuous_deriv le_rfl; fun_prop) fun _ ↦ hdg _).norm
      simpa using (norm_integral_le_integral_norm _).trans <|
        integral_mono hi (integrable_const L) fun _ ↦ (Real.norm_eq_abs _).trans_le (hdg _)
    exact (div_le_div_of_nonneg_right (by
        simpa only [one_mul] using
          mul_le_mul (abs_cos_le_one θ) hint_le (abs_nonneg _) zero_le_one) (hP_pos x).le).trans <|
      div_le_div_of_nonneg_left ((abs_nonneg _).trans (hdg 0)) hε
        (gaussianInterp_mem_Icc hg hε hlo hhi θ x).1
  have hraw := hasDerivAt_integral_gaussianInterp_mul_log hg hε hlo hhi hdg θ
  rw [integral_mul_interp_deriv
    (((contDiff_gaussianInterp_x hg hε hlo hhi hdg θ).log fun x ↦ (hP_pos x).ne').add
      contDiff_const)
    (fun x ↦ abs_log_add_one_le_of_mem_Icc hε (gaussianInterp_mem_Icc hg hε hlo hhi θ x).1
      (gaussianInterp_mem_Icc hg hε hlo hhi θ x).2) hΦ_db hg hdg θ] at hraw
  refine hraw.congr_deriv ?_
  rw [show (∫ x, deriv Φ x * (∫ y, deriv g (cos θ * x + sin θ * y) ∂γ) ∂γ) =
      cos θ * ∫ x, (∫ y, deriv g (cos θ * x + sin θ * y) ∂γ) ^ 2 / gaussianInterp g θ x ∂γ by
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall fun x ↦ by dsimp only; rw [hΦ_deriv]; ring)]
  ring

/-- Regularized Gaussian logarithmic Sobolev inequality on `ℝ` for `f² + ε` with `0 < ε`. -/
private theorem entropy_add_pos_le_two_mul_integral_deriv_sq_gaussianReal
    {f : ℝ → ℝ} {A B ε : ℝ} (hf : ContDiff ℝ 1 f) (hA : ∀ x, |f x| ≤ A)
    (hB : ∀ x, |deriv f x| ≤ B) (hε : 0 < ε) :
    Measure.entropy γ (fun x ↦ f x ^ 2 + ε) ≤ 2 * ∫ x, deriv f x ^ 2 ∂γ := by
  let g : ℝ → ℝ := fun x ↦ f x ^ 2 + ε
  have hg : ContDiff ℝ 1 g := (hf.pow 2).add contDiff_const
  have hg_lo (x : ℝ) : ε ≤ g x := le_add_of_nonneg_left (sq_nonneg _)
  have hg_hi (x : ℝ) : g x ≤ A ^ 2 + ε := add_le_add_left (sq_le_of_abs_le (hA x)) ε
  have hderiv_g (x : ℝ) : deriv g x = 2 * f x * deriv f x :=
    let hdf := (hf.differentiable one_ne_zero x).hasDerivAt
    ((((hdf.mul hdf).add_const ε).congr_of_eventuallyEq
      (.of_forall fun _ ↦ by simp [g, sq])).congr_deriv (by ring)).deriv
  have hdg (x : ℝ) : |deriv g x| ≤ 2 * A * B := by
    rw [hderiv_g]; exact abs_two_mul_deriv_le hA hB x
  let D := ∫ x, deriv f x ^ 2 ∂γ
  let ψ : ℝ → ℝ := fun θ ↦ ∫ x, gaussianInterp g θ x * log (gaussianInterp g θ x) ∂γ
  let I : ℝ → ℝ := fun θ ↦
    ∫ x, (∫ y, deriv g (cos θ * x + sin θ * y) ∂γ) ^ 2 / gaussianInterp g θ x ∂γ
  have hmono : MonotoneOn (fun θ ↦ ψ θ + 2 * sin θ ^ 2 * D) (Set.Icc 0 (π / 2)) := by
    have hd (θ : ℝ) : HasDerivAt (fun t ↦ ψ t + 2 * sin t ^ 2 * D)
        (sin θ * cos θ * (4 * D - I θ)) θ :=
      ((hasDerivAt_integral_gaussianInterp_mul_log_fisher hg hε hg_lo hg_hi hdg θ).add
        ((((hasDerivAt_sin θ).pow 2).const_mul 2).mul_const D)).congr_deriv (by
          simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun θ _ ↦ (hd θ).continuousAt.continuousWithinAt)
      (fun θ _ ↦ (hd θ).differentiableAt.differentiableWithinAt) fun θ hθ ↦ ?_
    rw [(hd θ).deriv]; rw [interior_Icc] at hθ
    exact mul_nonneg (mul_nonneg
      (sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2, pi_pos]))
      (cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, pi_pos], hθ.2.le⟩))
      (sub_nonneg.2 <| by
        simpa only [I, D, hderiv_g] using integral_sq_deriv_div_gaussianInterp_le hf hA hB hε θ)
  have hle := hmono ⟨le_rfl, by linarith [pi_pos]⟩ ⟨by linarith [pi_pos], le_rfl⟩
    (by linarith [pi_pos])
  simp only [sin_zero, sin_pi_div_two, ψ, gaussianInterp, cos_zero, one_mul, zero_mul, add_zero,
    cos_pi_div_two, zero_add, sin_pi_div_two, one_mul, integral_const, probReal_univ,
    one_smul] at hle
  rw [Measure.entropy_def]; linarith

/-- **Gross's Gaussian logarithmic Sobolev inequality on `ℝ`** for bounded `C¹` test functions:
if `f : ℝ → ℝ` is continuously differentiable with bounded values and bounded derivative, then
`(gaussianReal 0 1).entropy (fun x ↦ f x ^ 2) ≤ 2 * ∫ x, deriv f x ^ 2 ∂(gaussianReal 0 1)`. -/
theorem entropy_sq_le_two_mul_integral_deriv_sq_gaussianReal {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfb : ∃ A, ∀ x, |f x| ≤ A) (hdb : ∃ B, ∀ x, |deriv f x| ≤ B) :
    (gaussianReal 0 1).entropy (fun x ↦ f x ^ 2) ≤ 2 * ∫ x, deriv f x ^ 2 ∂(gaussianReal 0 1) := by
  obtain ⟨A, hA⟩ := hfb; obtain ⟨B, hB⟩ := hdb
  let g : ℕ → ℝ → ℝ := fun n x ↦ f x ^ 2 + ((n : ℝ) + 1)⁻¹
  have hg_pos (n : ℕ) : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
  have hg_le (n : ℕ) (x : ℝ) : g n x ≤ A ^ 2 + 1 :=
    add_le_add (sq_le_of_abs_le (hA x))
      (inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]))
  have hgpt (x : ℝ) : Tendsto (fun n ↦ g n x) atTop (𝓝 (f x ^ 2)) := by
    simpa only [g, one_div, add_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add (f x ^ 2)
  have hlim_sq : Tendsto (fun n ↦ ∫ x, g n x ∂γ) atTop (𝓝 (∫ x, f x ^ 2 ∂γ)) :=
    tendsto_integral_of_dominated_convergence (fun _ ↦ A ^ 2 + 1)
      (fun _ ↦ ((hf.continuous.pow 2).add continuous_const).aestronglyMeasurable)
      (integrable_const _) (fun n ↦ ae_of_all _ fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (sq_nonneg _) (hg_pos n).le)]
        exact hg_le n x) (ae_of_all _ hgpt)
  have hlim_mul_log : Tendsto (fun n ↦ ∫ x, g n x * log (g n x) ∂γ) atTop
      (𝓝 (∫ x, f x ^ 2 * log (f x ^ 2) ∂γ)) :=
    tendsto_integral_of_dominated_convergence (fun _ ↦ 1 + |(A ^ 2 + 1) * log (A ^ 2 + 1)|)
      (fun _ ↦ (Real.continuous_mul_log.comp
        ((hf.continuous.pow 2).add continuous_const)).aestronglyMeasurable)
      (integrable_const _) (fun n ↦ ae_of_all _ fun x ↦ (Real.norm_eq_abs _).trans_le <|
        TauCeti.abs_mul_log_le_one_add_abs_mul_log (add_nonneg (sq_nonneg _) (hg_pos n).le)
          (hg_le n x))
      (ae_of_all _ fun x ↦ Real.continuous_mul_log.continuousAt.tendsto.comp (hgpt x))
  have hent : Tendsto (fun n ↦ Measure.entropy γ (g n)) atTop
      (𝓝 ((gaussianReal 0 1).entropy (fun x ↦ f x ^ 2))) := by
    simp_rw [Measure.entropy_def]
    exact hlim_mul_log.sub (Real.continuous_mul_log.continuousAt.tendsto.comp hlim_sq)
  exact le_of_tendsto hent (.of_forall fun n ↦
    entropy_add_pos_le_two_mul_integral_deriv_sq_gaussianReal hf hA hB (hg_pos n))

end TauCeti.Probability

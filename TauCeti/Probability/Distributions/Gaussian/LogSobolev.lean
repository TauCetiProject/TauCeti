/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Entropy.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
import TauCeti.Analysis.SpecialFunctions.Log.MulLog
import TauCeti.Probability.Distributions.Gaussian.IntegrationByParts
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

private theorem abs_neg_sin_mul_add_cos_mul_le (t x y : ℝ) :
    |-sin t * x + cos t * y| ≤ |x| + |y| := by
  calc |-sin t * x + cos t * y|
      ≤ |-sin t * x| + |cos t * y| := abs_add_le _ _
    _ = |sin t| * |x| + |cos t| * |y| := by rw [abs_mul, abs_mul, abs_neg]
    _ ≤ 1 * |x| + 1 * |y| := by gcongr; exacts [abs_sin_le_one t, abs_cos_le_one t]
    _ = |x| + |y| := by ring

private theorem integrable_comp_gaussianInterp (hg : ContDiff ℝ 1 g)
    (hε : 0 < ε) (hlo : ∀ x, ε ≤ g x) (hhi : ∀ x, g x ≤ M) (θ x : ℝ) :
    Integrable (fun y ↦ g (cos θ * x + sin θ * y)) γ := by
  have hc : Continuous g := hg.continuous
  refine Integrable.of_bound (by fun_prop) M (ae_of_all _ fun y ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_pos (hε.trans_le (hlo _))]
  exact hhi _

private theorem gaussianInterp_mem_Icc (hg : ContDiff ℝ 1 g)
    (hε : 0 < ε) (hlo : ∀ x, ε ≤ g x) (hhi : ∀ x, g x ≤ M) (θ x : ℝ) :
    ε ≤ gaussianInterp g θ x ∧ gaussianInterp g θ x ≤ M := by
  have hint := integrable_comp_gaussianInterp hg hε hlo hhi θ x
  refine ⟨?_, ?_⟩
  · simpa [gaussianInterp] using integral_mono (integrable_const ε) hint fun y ↦ hlo _
  · simpa [gaussianInterp] using integral_mono hint (integrable_const M) fun y ↦ hhi _

private theorem hasDerivAt_gaussianInterp_x (hg : ContDiff ℝ 1 g)
    (hε : 0 < ε) (hlo : ∀ x, ε ≤ g x) (hhi : ∀ x, g x ≤ M) (hdg : ∀ x, |deriv g x| ≤ L)
    (θ x : ℝ) :
    HasDerivAt (gaussianInterp g θ)
      (cos θ * ∫ y, deriv g (cos θ * x + sin θ * y) ∂γ) x := by
  have hc : Continuous g := hg.continuous
  have hderiv_eq : cos θ * ∫ y, deriv g (cos θ * x + sin θ * y) ∂γ =
      ∫ y, deriv g (cos θ * x + sin θ * y) * cos θ ∂γ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun y ↦ mul_comm _ _)
  rw [hderiv_eq]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z y ↦ g (cos θ * z + sin θ * y))
    (F' := fun z y ↦ deriv g (cos θ * z + sin θ * y) * cos θ)
    (x₀ := x) (bound := fun _ ↦ L) (s := Set.univ) Filter.univ_mem
    ?_ (integrable_comp_gaussianInterp hg hε hlo hhi θ x) ?_ ?_ (integrable_const L) ?_).2
  · exact Eventually.of_forall fun z ↦ (by fun_prop : Continuous _).aestronglyMeasurable
  · exact (by fun_prop : Continuous _).aestronglyMeasurable
  · refine ae_of_all _ fun y z _ ↦ ?_
    rw [Real.norm_eq_abs, abs_mul]
    calc |deriv g (cos θ * z + sin θ * y)| * |cos θ|
        ≤ L * 1 := mul_le_mul (hdg _) (abs_cos_le_one θ) (abs_nonneg _)
          ((abs_nonneg _).trans (hdg 0))
      _ = L := mul_one L
  · refine ae_of_all _ fun y z _ ↦ ?_
    have h1 : HasDerivAt (fun z : ℝ ↦ cos θ * z + sin θ * y) (cos θ) z := by
      simpa using ((hasDerivAt_id z).const_mul (cos θ)).add_const (sin θ * y)
    exact (hg.differentiable one_ne_zero _).hasDerivAt.comp z h1

private theorem contDiff_gaussianInterp_x (hg : ContDiff ℝ 1 g)
    (hε : 0 < ε) (hlo : ∀ x, ε ≤ g x) (hhi : ∀ x, g x ≤ M) (hdg : ∀ x, |deriv g x| ≤ L)
    (θ : ℝ) :
    ContDiff ℝ 1 (gaussianInterp g θ) := by
  have hd := hasDerivAt_gaussianInterp_x hg hε hlo hhi hdg θ
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x ↦ (hd x).differentiableAt, ?_⟩
  have hder : deriv (gaussianInterp g θ) =
      fun x ↦ cos θ * ∫ y, deriv g (cos θ * x + sin θ * y) ∂γ :=
    funext fun x ↦ (hd x).deriv
  rw [hder]
  refine continuous_const.mul (continuous_of_dominated
    (fun x ↦ (by fun_prop : Continuous _).aestronglyMeasurable)
    (fun x ↦ ae_of_all _ fun y ↦ by simpa only [Real.norm_eq_abs] using hdg _)
    (integrable_const L)
    (ae_of_all _ fun y ↦ by fun_prop))

private theorem hasDerivAt_gaussianInterp_theta (hg : ContDiff ℝ 1 g)
    (hε : 0 < ε) (hlo : ∀ x, ε ≤ g x) (hhi : ∀ x, g x ≤ M) (hdg : ∀ x, |deriv g x| ≤ L)
    (θ x : ℝ) :
    HasDerivAt (fun t ↦ gaussianInterp g t x) (gaussianInterpDerivTheta g θ x) θ := by
  have hc : Continuous g := hg.continuous
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hdg 0)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t y ↦ g (cos t * x + sin t * y))
    (F' := fun t y ↦ deriv g (cos t * x + sin t * y) * (-sin t * x + cos t * y))
    (x₀ := θ) (bound := fun y ↦ L * (|x| + |y|)) (s := Set.univ) Filter.univ_mem
    ?_ (integrable_comp_gaussianInterp hg hε hlo hhi θ x) ?_ ?_
    (((integrable_const |x|).add (integrable_abs_gaussianReal 0 1)).const_mul L) ?_).2
  · exact Eventually.of_forall fun t ↦ (by fun_prop : Continuous _).aestronglyMeasurable
  · exact (by fun_prop : Continuous _).aestronglyMeasurable
  · refine ae_of_all _ fun y t _ ↦ ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hdg _) (abs_neg_sin_mul_add_cos_mul_le t x y) (abs_nonneg _) hL0
  · refine ae_of_all _ fun y t _ ↦ ?_
    have h1 : HasDerivAt (fun t : ℝ ↦ cos t * x + sin t * y) (-sin t * x + cos t * y) t :=
      ((hasDerivAt_cos t).mul_const x).add ((hasDerivAt_sin t).mul_const y)
    exact (hg.differentiable one_ne_zero _).hasDerivAt.comp t h1

private theorem abs_log_add_one_le_of_mem_Icc {u : ℝ} (hε : 0 < ε) (hlo : ε ≤ u) (hhi : u ≤ M) :
    |log u + 1| ≤ |log ε| + |log M| + 1 := by
  have h1 : log ε ≤ log u := log_le_log hε hlo
  have h2 : log u ≤ log M := log_le_log (hε.trans_le hlo) hhi
  rw [abs_le]
  constructor <;>
    linarith [neg_abs_le (log ε), le_abs_self (log M), abs_nonneg (log ε), abs_nonneg (log M)]

private theorem abs_gaussianInterpDerivTheta_le (hg : ContDiff ℝ 1 g)
    (hdg : ∀ x, |deriv g x| ≤ L) (t x : ℝ) :
    |gaussianInterpDerivTheta g t x| ≤ L * (|x| + ∫ y, |y| ∂γ) := by
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hdg 0)
  have hb_int : Integrable (fun y ↦ L * (|x| + |y|)) γ :=
    ((integrable_const |x|).add (integrable_abs_gaussianReal 0 1)).const_mul L
  calc |gaussianInterpDerivTheta g t x|
      ≤ ∫ y, ‖deriv g (cos t * x + sin t * y) * (-sin t * x + cos t * y)‖ ∂γ := by
        rw [gaussianInterpDerivTheta, ← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ y, L * (|x| + |y|) ∂γ := by
        refine integral_mono ?_ hb_int fun y ↦ ?_
        · refine hb_int.mono' (by have := hg.continuous_deriv le_rfl; fun_prop)
            (ae_of_all _ fun y ↦ ?_)
          rw [Real.norm_eq_abs, abs_norm, Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hdg _) (abs_neg_sin_mul_add_cos_mul_le t x y) (abs_nonneg _) hL0
        · rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hdg _) (abs_neg_sin_mul_add_cos_mul_le t x y) (abs_nonneg _) hL0
    _ = L * (|x| + ∫ y, |y| ∂γ) := by
        rw [integral_const_mul,
          integral_add (integrable_const |x|) (integrable_abs_gaussianReal 0 1)]
        simp

private theorem hasDerivAt_integral_gaussianInterp_mul_log (hg : ContDiff ℝ 1 g)
    (hε : 0 < ε) (hlo : ∀ x, ε ≤ g x) (hhi : ∀ x, g x ≤ M) (hdg : ∀ x, |deriv g x| ≤ L)
    (θ : ℝ) :
    HasDerivAt (fun t ↦ ∫ x, gaussianInterp g t x * log (gaussianInterp g t x) ∂γ)
      (∫ p, (log (gaussianInterp g θ p.1) + 1) *
        (deriv g (cos θ * p.1 + sin θ * p.2) * (-sin θ * p.1 + cos θ * p.2))
        ∂(Measure.prod γ γ)) θ := by
  have := hg.continuous_deriv le_rfl
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hdg 0)
  let CΦ := |log ε| + |log M| + 1
  have hCΦ0 : 0 ≤ CΦ := by positivity
  let Φ : ℝ → ℝ → ℝ := fun t x ↦ log (gaussianInterp g t x) + 1
  have hP_pos (t x : ℝ) : 0 < gaussianInterp g t x :=
    hε.trans_le (gaussianInterp_mem_Icc hg hε hlo hhi t x).1
  have hP_cont (t : ℝ) : Continuous (gaussianInterp g t) :=
    (contDiff_gaussianInterp_x hg hε hlo hhi hdg t).continuous
  have hΦ_le (t x : ℝ) : |Φ t x| ≤ CΦ :=
    abs_log_add_one_le_of_mem_Icc hε (gaussianInterp_mem_Icc hg hε hlo hhi t x).1
      (gaussianInterp_mem_Icc hg hε hlo hhi t x).2
  have hΦ_cont : Continuous (Φ θ) :=
    ((hP_cont θ).log fun x ↦ (hP_pos θ x).ne').add continuous_const
  have hprod_cont : Continuous fun p : ℝ × ℝ ↦
      Φ θ p.1 * (deriv g (cos θ * p.1 + sin θ * p.2) * (-sin θ * p.1 + cos θ * p.2)) :=
    (hΦ_cont.comp continuous_fst).mul (by fun_prop)
  have hprod_int : Integrable (fun p : ℝ × ℝ ↦
      Φ θ p.1 * (deriv g (cos θ * p.1 + sin θ * p.2) * (-sin θ * p.1 + cos θ * p.2)))
      (Measure.prod γ γ) := by
    refine ((integrable_abs_add_abs_gaussianReal 0 0 1 1).const_mul (CΦ * L)).mono'
      hprod_cont.aestronglyMeasurable (ae_of_all _ fun p ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |Φ θ p.1| * (|deriv g (cos θ * p.1 + sin θ * p.2)| * |-sin θ * p.1 + cos θ * p.2|)
        ≤ CΦ * (L * (|p.1| + |p.2|)) :=
          mul_le_mul (hΦ_le θ p.1)
            (mul_le_mul (hdg _) (abs_neg_sin_mul_add_cos_mul_le θ p.1 p.2) (abs_nonneg _) hL0)
            (by positivity) hCΦ0
      _ = CΦ * L * (|p.1| + |p.2|) := by ring
  have hfub_pt (x : ℝ) :
      ∫ y, Φ θ x * (deriv g (cos θ * x + sin θ * y) * (-sin θ * x + cos θ * y)) ∂γ =
        Φ θ x * gaussianInterpDerivTheta g θ x :=
    integral_const_mul (Φ θ x) _
  have hfub : ∫ p, Φ θ p.1 *
      (deriv g (cos θ * p.1 + sin θ * p.2) * (-sin θ * p.1 + cos θ * p.2)) ∂(Measure.prod γ γ) =
      ∫ x, Φ θ x * gaussianInterpDerivTheta g θ x ∂γ := by
    rw [integral_prod _ hprod_int]
    exact integral_congr_ae (ae_of_all _ hfub_pt)
  rw [hfub]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x ↦ gaussianInterp g t x * log (gaussianInterp g t x))
    (F' := fun t x ↦ Φ t x * gaussianInterpDerivTheta g t x)
    (x₀ := θ) (bound := fun x ↦ CΦ * (L * (|x| + ∫ y, |y| ∂γ))) (s := Set.univ) Filter.univ_mem
    ?_ ?_ ?_ ?_
    ((((integrable_abs_gaussianReal 0 1).add (integrable_const _)).const_mul L).const_mul CΦ) ?_).2
  · exact Eventually.of_forall fun t ↦
      (Real.continuous_mul_log.comp (hP_cont t)).aestronglyMeasurable
  · refine Integrable.of_bound
      (Real.continuous_mul_log.comp (hP_cont θ)).aestronglyMeasurable
      (1 + |M * log M|) (ae_of_all _ fun x ↦ ?_)
    simpa only [Real.norm_eq_abs, Function.comp_apply] using
      TauCeti.abs_mul_log_le_one_add_abs_mul_log (hP_pos θ x).le
        (gaussianInterp_mem_Icc hg hε hlo hhi θ x).2
  · exact hprod_int.integral_prod_left.aestronglyMeasurable.congr (ae_of_all _ hfub_pt)
  · refine ae_of_all _ fun x t _ ↦ ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hΦ_le t x) (abs_gaussianInterpDerivTheta_le hg hdg t x) (abs_nonneg _) hCΦ0
  · refine ae_of_all _ fun x t _ ↦ ?_
    exact (Real.hasDerivAt_mul_log (hP_pos t x).ne').comp t
      (hasDerivAt_gaussianInterp_theta hg hε hlo hhi hdg t x)

/-- Planar reflection symmetry and Gaussian integration by parts rewrite the cross derivative
against `Φ` as `-sin θ * ∫ x, Φ' x * (∫ y, g'(cos θ · x + sin θ · y) ∂γ) ∂γ`. -/
private theorem integral_mul_interp_deriv {Φ g : ℝ → ℝ} {A₁ B₁ B₂ : ℝ}
    (hΦ : ContDiff ℝ 1 Φ) (hA₁ : ∀ x, |Φ x| ≤ A₁) (hB₁ : ∀ x, |deriv Φ x| ≤ B₁)
    (hg : ContDiff ℝ 1 g) (hB₂ : ∀ x, |deriv g x| ≤ B₂) (θ : ℝ) :
    ∫ p, Φ p.1 * (deriv g (cos θ * p.1 + sin θ * p.2) * (-sin θ * p.1 + cos θ * p.2))
        ∂(Measure.prod γ γ) =
      -sin θ * ∫ x, deriv Φ x * (∫ y, deriv g (cos θ * x + sin θ * y) ∂γ) ∂γ := by
  have hcΦ : Continuous Φ := hΦ.continuous
  have hA₁0 : 0 ≤ A₁ := (abs_nonneg _).trans (hA₁ 0)
  have hB₁0 : 0 ≤ B₁ := (abs_nonneg _).trans (hB₁ 0)
  have hB₂0 : 0 ≤ B₂ := (abs_nonneg _).trans (hB₂ 0)
  obtain ⟨c, hcdef⟩ : ∃ c, c = cos θ := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s, s = sin θ := ⟨_, rfl⟩
  rw [← hcdef, ← hsdef]
  have hcs : c ^ 2 + s ^ 2 = 1 := by rw [hcdef, hsdef]; exact cos_sq_add_sin_sq θ
  have hmp := measurePreserving_reflection_gaussianReal θ
  rw [← hcdef, ← hsdef] at hmp
  let H : ℝ × ℝ → ℝ := fun q ↦ Φ (c * q.1 + s * q.2) * (deriv g q.1 * (-q.2))
  have hHc : Continuous H := by fun_prop
  have hHint : Integrable H (Measure.prod γ γ) := by
    refine ((integrable_abs_add_abs_gaussianReal 0 0 1 1).const_mul (A₁ * B₂)).mono'
      hHc.aestronglyMeasurable (ae_of_all _ fun q ↦ ?_)
    rw [Real.norm_eq_abs]
    simp only [H, abs_mul, abs_neg]
    calc |Φ (c * q.1 + s * q.2)| * (|deriv g q.1| * |q.2|)
        ≤ A₁ * (B₂ * (|q.1| + |q.2|)) :=
          mul_le_mul (hA₁ _)
            (mul_le_mul (hB₂ _) (le_add_of_nonneg_left (abs_nonneg _)) (abs_nonneg _) hB₂0)
            (by positivity) hA₁0
      _ = A₁ * B₂ * (|q.1| + |q.2|) := by ring
  have hrot (p : ℝ × ℝ) : c * (c * p.1 + s * p.2) + s * (s * p.1 - c * p.2) = p.1 := by
    linear_combination p.1 * hcs
  have e1 : (fun p : ℝ × ℝ ↦ Φ p.1 * (deriv g (c * p.1 + s * p.2) * (-s * p.1 + c * p.2))) =
      fun p ↦ H (c * p.1 + s * p.2, s * p.1 - c * p.2) := by
    funext p
    simp only [H, hrot p]
    ring
  have hchange := hmp.hasLaw.integral_comp hHc.aestronglyMeasurable
  simp only [Function.comp_def] at hchange
  rw [e1, hchange, integral_prod _ hHint]
  have hinner (u : ℝ) : ∫ v, H (u, v) ∂γ = -s * (deriv g u * ∫ v, deriv Φ (c * u + s * v) ∂γ) := by
    have hrew (v : ℝ) : H (u, v) = -(deriv g u) * (v * Φ (c * u + s * v)) := by
      simp only [H]; ring
    simp_rw [hrew]
    rw [integral_const_mul, integral_mul_comp_affine_gaussianReal hΦ hA₁ hB₁]
    ring
  simp_rw [hinner]
  rw [integral_const_mul]
  congr 1
  let K : ℝ × ℝ → ℝ := fun q ↦ deriv g q.1 * deriv Φ (c * q.1 + s * q.2)
  have hKc : Continuous K := by fun_prop
  let K' : ℝ × ℝ → ℝ := fun p ↦ deriv Φ p.1 * deriv g (c * p.1 + s * p.2)
  have hK'int : Integrable K' (Measure.prod γ γ) :=
    Integrable.of_bound (by fun_prop : Continuous K').aestronglyMeasurable (B₁ * B₂)
      (ae_of_all _ fun p ↦ by
        simpa only [K', Real.norm_eq_abs, abs_mul] using
          mul_le_mul (hB₁ _) (hB₂ _) (abs_nonneg _) hB₁0)
  have hK_fub : (∫ u, deriv g u * (∫ v, deriv Φ (c * u + s * v) ∂γ) ∂γ) =
      ∫ q, K q ∂(Measure.prod γ γ) := by
    have hKint : Integrable K (Measure.prod γ γ) :=
      Integrable.of_bound hKc.aestronglyMeasurable (B₂ * B₁)
        (ae_of_all _ fun q ↦ by
          simpa only [K, Real.norm_eq_abs, abs_mul] using
            mul_le_mul (hB₂ _) (hB₁ _) (abs_nonneg _) hB₂0)
    rw [integral_prod _ hKint]
    exact integral_congr_ae (ae_of_all _ fun u ↦ (integral_const_mul _ _).symm)
  have e2 : (fun p : ℝ × ℝ ↦ K (c * p.1 + s * p.2, s * p.1 - c * p.2)) = K' := by
    funext p
    simp only [K, K', hrot p]
    ring
  have hchange2 := hmp.hasLaw.integral_comp hKc.aestronglyMeasurable
  simp only [Function.comp_def, e2] at hchange2
  rw [hK_fub, ← hchange2, integral_prod _ hK'int]
  exact integral_congr_ae (ae_of_all _ fun x ↦ by dsimp only [K']; exact integral_const_mul _ _)

end Interpolation

/-- Elementary quadratic Cauchy–Schwarz bound for `g = f² + ε` along the Gaussian interpolation:
`(E_y[2 f f'])² / E_y[f² + ε] ≤ 4 E_y[(f')²]`. -/
private theorem sq_integral_two_mul_deriv_div_le {f : ℝ → ℝ} {A B ε : ℝ}
    (hf : ContDiff ℝ 1 f) (hA : ∀ x, |f x| ≤ A) (hB : ∀ x, |deriv f x| ≤ B) (hε : 0 < ε)
    (θ x : ℝ) :
    (∫ y, 2 * f (cos θ * x + sin θ * y) * deriv f (cos θ * x + sin θ * y) ∂γ) ^ 2 /
        gaussianInterp (fun z ↦ f z ^ 2 + ε) θ x ≤
      4 * ∫ y, deriv f (cos θ * x + sin θ * y) ^ 2 ∂γ := by
  have hc : Continuous f := hf.continuous
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  let g : ℝ → ℝ := fun z ↦ f z ^ 2 + ε
  have hg : ContDiff ℝ 1 g := (hf.pow 2).add contDiff_const
  have hg_lo (z : ℝ) : ε ≤ g z := le_add_of_nonneg_left (sq_nonneg _)
  have hg_hi (z : ℝ) : g z ≤ A ^ 2 + ε := by
    have hsq : f z ^ 2 ≤ A ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hA z) 2
    linarith
  let P := gaussianInterp g θ x
  let G := ∫ y, 2 * f (cos θ * x + sin θ * y) * deriv f (cos θ * x + sin θ * y) ∂γ
  let D := ∫ y, deriv f (cos θ * x + sin θ * y) ^ 2 ∂γ
  have hP : 0 < P := hε.trans_le (gaussianInterp_mem_Icc hg hε hg_lo hg_hi θ x).1
  let t := G / (2 * P)
  have hu₁ : Integrable (fun y ↦ t ^ 2 * g (cos θ * x + sin θ * y)) γ :=
    (integrable_comp_gaussianInterp hg hε hg_lo hg_hi θ x).const_mul (t ^ 2)
  have hu₂_base : Integrable (fun y ↦ 2 * f (cos θ * x + sin θ * y) *
      deriv f (cos θ * x + sin θ * y)) γ :=
    Integrable.of_bound (by fun_prop : Continuous _).aestronglyMeasurable (2 * A * B)
      (ae_of_all _ fun y ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg zero_le_two]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hA _) zero_le_two) (hB _)
          (abs_nonneg _) (by positivity))
  have hu₂ : Integrable (fun y ↦ t * (2 * f (cos θ * x + sin θ * y) *
      deriv f (cos θ * x + sin θ * y))) γ := hu₂_base.const_mul t
  have hu₁₂ : Integrable (fun y ↦ t ^ 2 * g (cos θ * x + sin θ * y) -
      t * (2 * f (cos θ * x + sin θ * y) * deriv f (cos θ * x + sin θ * y))) γ := hu₁.sub hu₂
  have hu₃ : Integrable (fun y ↦ deriv f (cos θ * x + sin θ * y) ^ 2) γ :=
    Integrable.of_bound (by fun_prop : Continuous _).aestronglyMeasurable (B ^ 2)
      (ae_of_all _ fun y ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2)
  have hnonneg : 0 ≤ ∫ y, ((t ^ 2 * g (cos θ * x + sin θ * y) -
      t * (2 * f (cos θ * x + sin θ * y) * deriv f (cos θ * x + sin θ * y))) +
      deriv f (cos θ * x + sin θ * y) ^ 2) ∂γ := by
    refine integral_nonneg fun y ↦ ?_
    simp only [Pi.zero_apply, g]
    nlinarith [sq_nonneg (t * f (cos θ * x + sin θ * y) - deriv f (cos θ * x + sin θ * y)),
      mul_nonneg (sq_nonneg t) hε.le]
  rw [integral_add hu₁₂ hu₃, integral_sub hu₁ hu₂, integral_const_mul, integral_const_mul]
    at hnonneg
  have hquad : 0 ≤ (t ^ 2 * P - t * G + D) * (4 * P) := mul_nonneg hnonneg (by positivity)
  have htP : t * (2 * P) = G := div_mul_cancel₀ G (by positivity)
  have halg : (t ^ 2 * P - t * G + D) * (4 * P) = 4 * D * P - G ^ 2 :=
    calc (t ^ 2 * P - t * G + D) * (4 * P)
        = (t * (2 * P)) ^ 2 - 2 * (t * (2 * P)) * G + 4 * D * P := by ring
      _ = G ^ 2 - 2 * G * G + 4 * D * P := by rw [htP]
      _ = 4 * D * P - G ^ 2 := by ring
  rw [div_le_iff₀ hP]
  linarith

/-- Integrated Fisher-information bound along the Gaussian interpolation. -/
private theorem integral_sq_deriv_div_gaussianInterp_le
    {f : ℝ → ℝ} {A B ε : ℝ} (hf : ContDiff ℝ 1 f) (hA : ∀ x, |f x| ≤ A)
    (hB : ∀ x, |deriv f x| ≤ B) (hε : 0 < ε) (θ : ℝ) :
    (∫ x, (∫ y, 2 * f (cos θ * x + sin θ * y) * deriv f (cos θ * x + sin θ * y) ∂γ) ^ 2 /
        gaussianInterp (fun z ↦ f z ^ 2 + ε) θ x ∂γ) ≤
      4 * ∫ x, deriv f x ^ 2 ∂γ := by
  have hc : Continuous f := hf.continuous
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  let g : ℝ → ℝ := fun z ↦ f z ^ 2 + ε
  have hg : ContDiff ℝ 1 g := (hf.pow 2).add contDiff_const
  have hg_lo (z : ℝ) : ε ≤ g z := le_add_of_nonneg_left (sq_nonneg _)
  have hg_hi (z : ℝ) : g z ≤ A ^ 2 + ε := by
    have hsq : f z ^ 2 ≤ A ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hA z) 2
    linarith
  have hmp := measurePreserving_reflection_gaussianReal θ
  have hrot_int : Integrable (fun p : ℝ × ℝ ↦ deriv f (cos θ * p.1 + sin θ * p.2) ^ 2)
      (Measure.prod γ γ) :=
    ((measurePreserving_fst (μ := γ) (ν := γ)).comp hmp).integrable_comp_of_integrable
      (Integrable.of_bound (by fun_prop : Continuous fun x ↦ deriv f x ^ 2).aestronglyMeasurable
        (B ^ 2) (ae_of_all _ fun x ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2))
  have hrot_eq : ∫ x, (∫ y, deriv f (cos θ * x + sin θ * y) ^ 2 ∂γ) ∂γ =
      ∫ x, deriv f x ^ 2 ∂γ := by
    rw [← integral_prod _ hrot_int]
    exact ((measurePreserving_fst (μ := γ) (ν := γ)).comp hmp).hasLaw.integral_comp
      (by fun_prop : Continuous fun x ↦ deriv f x ^ 2).aestronglyMeasurable
  have hnum_cont : Continuous fun x ↦
      ∫ y, 2 * f (cos θ * x + sin θ * y) * deriv f (cos θ * x + sin θ * y) ∂γ :=
    continuous_of_dominated (fun x ↦ (by fun_prop : Continuous _).aestronglyMeasurable)
      (fun x ↦ ae_of_all _ fun y ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg zero_le_two]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hA _) zero_le_two) (hB _)
          (abs_nonneg _) (by positivity))
      (integrable_const (2 * A * B)) (ae_of_all _ fun y ↦ by fun_prop)
  have hden_cont : Continuous (gaussianInterp g θ) := by
    refine continuous_of_dominated (fun x ↦ (by fun_prop : Continuous _).aestronglyMeasurable)
      (fun x ↦ ae_of_all _ fun y ↦ ?_) (integrable_const (A ^ 2 + ε))
      (ae_of_all _ fun y ↦ by fun_prop)
    rw [Real.norm_eq_abs, abs_of_pos (hε.trans_le (hg_lo _))]
    exact hg_hi _
  have hI_int : Integrable (fun x ↦
      (∫ y, 2 * f (cos θ * x + sin θ * y) * deriv f (cos θ * x + sin θ * y) ∂γ) ^ 2 /
        gaussianInterp g θ x) γ := by
    refine Integrable.of_bound
      ((hnum_cont.pow 2).div hden_cont fun x ↦
        (hε.trans_le (gaussianInterp_mem_Icc hg hε hg_lo hg_hi θ x).1).ne').aestronglyMeasurable
      (4 * B ^ 2) (ae_of_all _ fun x ↦ ?_)
    have hpos : 0 ≤ (∫ y, 2 * f (cos θ * x + sin θ * y) * deriv f (cos θ * x + sin θ * y) ∂γ) ^ 2 /
        gaussianInterp g θ x :=
      div_nonneg (sq_nonneg _)
        (hε.trans_le (gaussianInterp_mem_Icc hg hε hg_lo hg_hi θ x).1).le
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    refine (sq_integral_two_mul_deriv_div_le hf hA hB hε θ x).trans ?_
    have hy_int : Integrable (fun y ↦ deriv f (cos θ * x + sin θ * y) ^ 2) γ :=
      Integrable.of_bound
        (by fun_prop : Continuous fun y ↦ deriv f (cos θ * x + sin θ * y) ^ 2).aestronglyMeasurable
        (B ^ 2) (ae_of_all _ fun y ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2)
    have hle : ∫ y, deriv f (cos θ * x + sin θ * y) ^ 2 ∂γ ≤ B ^ 2 := by
      simpa using integral_mono hy_int (integrable_const (B ^ 2)) fun y ↦ by
        dsimp only
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2
    linarith
  calc (∫ x, (∫ y, 2 * f (cos θ * x + sin θ * y) * deriv f (cos θ * x + sin θ * y) ∂γ) ^ 2 /
          gaussianInterp g θ x ∂γ)
      ≤ ∫ x, (4 * ∫ y, deriv f (cos θ * x + sin θ * y) ^ 2 ∂γ) ∂γ :=
        integral_mono hI_int (hrot_int.integral_prod_left.const_mul 4) fun x ↦
          sq_integral_two_mul_deriv_div_le hf hA hB hε θ x
    _ = 4 * ∫ x, deriv f x ^ 2 ∂γ := by rw [integral_const_mul, hrot_eq]

/-- Exact Fisher-information formula for `∂_θ ∫ P θ log (P θ) ∂γ`. -/
private theorem hasDerivAt_integral_gaussianInterp_mul_log_fisher
    {g : ℝ → ℝ} {ε M L : ℝ} (hg : ContDiff ℝ 1 g) (hε : 0 < ε)
    (hlo : ∀ x, ε ≤ g x) (hhi : ∀ x, g x ≤ M) (hdg : ∀ x, |deriv g x| ≤ L) (θ : ℝ) :
    HasDerivAt (fun t ↦ ∫ x, gaussianInterp g t x * log (gaussianInterp g t x) ∂γ)
      (-sin θ * cos θ *
        ∫ x, (∫ y, deriv g (cos θ * x + sin θ * y) ∂γ) ^ 2 / gaussianInterp g θ x ∂γ) θ := by
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hdg 0)
  let Φ : ℝ → ℝ := fun x ↦ log (gaussianInterp g θ x) + 1
  have hP_pos (x : ℝ) : 0 < gaussianInterp g θ x :=
    hε.trans_le (gaussianInterp_mem_Icc hg hε hlo hhi θ x).1
  have hP_cd : ContDiff ℝ 1 (gaussianInterp g θ) :=
    contDiff_gaussianInterp_x hg hε hlo hhi hdg θ
  have hΦ_cd : ContDiff ℝ 1 Φ := (hP_cd.log fun x ↦ (hP_pos x).ne').add contDiff_const
  have hΦ_bd (x : ℝ) : |Φ x| ≤ |log ε| + |log M| + 1 :=
    abs_log_add_one_le_of_mem_Icc hε (gaussianInterp_mem_Icc hg hε hlo hhi θ x).1
      (gaussianInterp_mem_Icc hg hε hlo hhi θ x).2
  have hΦ_deriv (x : ℝ) :
      deriv Φ x = (cos θ * ∫ y, deriv g (cos θ * x + sin θ * y) ∂γ) / gaussianInterp g θ x := by
    have hdP := hasDerivAt_gaussianInterp_x hg hε hlo hhi hdg θ x
    exact ((hdP.log (hP_pos x).ne').add_const 1).deriv
  have hΦ_db (x : ℝ) : |deriv Φ x| ≤ L / ε := by
    rw [hΦ_deriv, abs_div, abs_of_pos (hP_pos x), abs_mul]
    have hnum : |cos θ| * |∫ y, deriv g (cos θ * x + sin θ * y) ∂γ| ≤ L := by
      have hint_le : |∫ y, deriv g (cos θ * x + sin θ * y) ∂γ| ≤ L := by
        calc |∫ y, deriv g (cos θ * x + sin θ * y) ∂γ|
            ≤ ∫ y, ‖deriv g (cos θ * x + sin θ * y)‖ ∂γ := by
              rw [← Real.norm_eq_abs]
              exact norm_integral_le_integral_norm _
          _ ≤ ∫ _, L ∂γ := integral_mono
              (Integrable.of_bound (by have := hg.continuous_deriv le_rfl; fun_prop) L
                (ae_of_all _ fun y ↦ by simpa using hdg _))
              (integrable_const L) (fun y ↦ by simpa only [Real.norm_eq_abs] using hdg _)
          _ = L := by simp
      calc |cos θ| * |∫ y, deriv g (cos θ * x + sin θ * y) ∂γ|
          ≤ 1 * L := mul_le_mul (abs_cos_le_one θ) hint_le (abs_nonneg _) zero_le_one
        _ = L := one_mul L
    exact (div_le_div_of_nonneg_right hnum (hP_pos x).le).trans
      (div_le_div_of_nonneg_left hL0 hε
        (gaussianInterp_mem_Icc hg hε hlo hhi θ x).1)
  have hraw := hasDerivAt_integral_gaussianInterp_mul_log hg hε hlo hhi hdg θ
  rw [integral_mul_interp_deriv hΦ_cd hΦ_bd hΦ_db hg hdg θ] at hraw
  refine hraw.congr_deriv ?_
  have hcongr : (∫ x, deriv Φ x * (∫ y, deriv g (cos θ * x + sin θ * y) ∂γ) ∂γ) =
      cos θ * ∫ x, (∫ y, deriv g (cos θ * x + sin θ * y) ∂γ) ^ 2 / gaussianInterp g θ x ∂γ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    dsimp only
    rw [hΦ_deriv]
    ring
  rw [hcongr]
  ring

/-- Regularized Gaussian logarithmic Sobolev inequality on `ℝ` for `f² + ε` with `0 < ε`. -/
private theorem entropy_add_pos_le_two_mul_integral_deriv_sq_gaussianReal
    {f : ℝ → ℝ} {A B ε : ℝ} (hf : ContDiff ℝ 1 f) (hA : ∀ x, |f x| ≤ A)
    (hB : ∀ x, |deriv f x| ≤ B) (hε : 0 < ε) :
    Measure.entropy γ (fun x ↦ f x ^ 2 + ε) ≤ 2 * ∫ x, deriv f x ^ 2 ∂γ := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  let g : ℝ → ℝ := fun x ↦ f x ^ 2 + ε
  let M := A ^ 2 + ε
  let L := 2 * A * B
  have hg : ContDiff ℝ 1 g := (hf.pow 2).add contDiff_const
  have hg_lo (x : ℝ) : ε ≤ g x := le_add_of_nonneg_left (sq_nonneg _)
  have hg_hi (x : ℝ) : g x ≤ M := by
    have hsq : f x ^ 2 ≤ A ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hA x) 2
    linarith
  have hderiv_g (x : ℝ) : deriv g x = 2 * f x * deriv f x := by
    have hdf := (hf.differentiable one_ne_zero x).hasDerivAt
    have hmul := (hdf.mul hdf).add_const ε
    exact ((hmul.congr_of_eventuallyEq (.of_forall fun z ↦ by simp [g, sq])).congr_deriv
      (by ring)).deriv
  have hdg (x : ℝ) : |deriv g x| ≤ L := by
    rw [hderiv_g, abs_mul, abs_mul, abs_of_nonneg zero_le_two]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hA x) zero_le_two) (hB x)
      (abs_nonneg _) (by positivity)
  let D := ∫ x, deriv f x ^ 2 ∂γ
  let ψ : ℝ → ℝ := fun θ ↦ ∫ x, gaussianInterp g θ x * log (gaussianInterp g θ x) ∂γ
  let I : ℝ → ℝ := fun θ ↦
    ∫ x, (∫ y, deriv g (cos θ * x + sin θ * y) ∂γ) ^ 2 / gaussianInterp g θ x ∂γ
  have hI_le (θ : ℝ) : I θ ≤ 4 * D := by
    dsimp only [I, D]
    simp_rw [hderiv_g]
    exact integral_sq_deriv_div_gaussianInterp_le hf hA hB hε θ
  have hmono : MonotoneOn (fun θ ↦ ψ θ + 2 * sin θ ^ 2 * D) (Set.Icc 0 (π / 2)) := by
    have hd (θ : ℝ) : HasDerivAt (fun t ↦ ψ t + 2 * sin t ^ 2 * D)
        (sin θ * cos θ * (4 * D - I θ)) θ := by
      have hψ := hasDerivAt_integral_gaussianInterp_mul_log_fisher hg hε hg_lo hg_hi hdg θ
      have hsin2 : HasDerivAt (fun t ↦ 2 * sin t ^ 2 * D) (4 * sin θ * cos θ * D) θ := by
        have hs := (((hasDerivAt_sin θ).mul (hasDerivAt_sin θ)).const_mul 2).mul_const D
        exact (hs.congr_of_eventuallyEq (.of_forall fun t ↦ by simp [sq])).congr_deriv (by ring)
      exact (hψ.add hsin2).congr_deriv (by ring)
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun θ _ ↦ (hd θ).continuousAt.continuousWithinAt)
      (fun θ _ ↦ (hd θ).differentiableAt.differentiableWithinAt) fun θ hθ ↦ ?_
    rw [(hd θ).deriv]
    rw [interior_Icc] at hθ
    have hsin : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2, pi_pos])
    have hcos : 0 ≤ cos θ := cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, pi_pos], hθ.2.le⟩
    exact mul_nonneg (mul_nonneg hsin hcos) (sub_nonneg.2 (hI_le θ))
  have h0 : ψ 0 = ∫ x, g x * log (g x) ∂γ := by
    dsimp only [ψ]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    dsimp only
    have hP0 : gaussianInterp g 0 x = g x := by simp [gaussianInterp]
    rw [hP0]
  have hpi : ψ (π / 2) = (∫ y, g y ∂γ) * log (∫ y, g y ∂γ) := by
    have hPpi (x : ℝ) : gaussianInterp g (π / 2) x = ∫ y, g y ∂γ := by simp [gaussianInterp]
    simp [ψ, hPpi]
  have hle := hmono ⟨le_rfl, by linarith [pi_pos]⟩ ⟨by linarith [pi_pos], le_rfl⟩
    (by linarith [pi_pos])
  simp only [sin_zero, sin_pi_div_two, h0, hpi] at hle
  rw [Measure.entropy_def]
  linarith

/-- **Gross's Gaussian logarithmic Sobolev inequality on `ℝ`** for bounded `C¹` test functions:
if `f : ℝ → ℝ` is continuously differentiable with bounded values and bounded derivative, then
`(gaussianReal 0 1).entropy (fun x ↦ f x ^ 2) ≤ 2 * ∫ x, deriv f x ^ 2 ∂(gaussianReal 0 1)`. -/
theorem entropy_sq_le_two_mul_integral_deriv_sq_gaussianReal {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfb : ∃ A, ∀ x, |f x| ≤ A) (hdb : ∃ B, ∀ x, |deriv f x| ≤ B) :
    (gaussianReal 0 1).entropy (fun x ↦ f x ^ 2) ≤ 2 * ∫ x, deriv f x ^ 2 ∂(gaussianReal 0 1) := by
  obtain ⟨A, hA⟩ := hfb
  obtain ⟨B, hB⟩ := hdb
  let g : ℕ → ℝ → ℝ := fun n x ↦ f x ^ 2 + ((n : ℝ) + 1)⁻¹
  have hg_pos (n : ℕ) : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
  have hg_le (n : ℕ) (x : ℝ) : g n x ≤ A ^ 2 + 1 := by
    have hsq : f x ^ 2 ≤ A ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hA x) 2
    have hinv : ((n : ℝ) + 1)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
    dsimp only [g]
    linarith
  have hgpt (x : ℝ) : Tendsto (fun n ↦ g n x) atTop (𝓝 (f x ^ 2)) := by
    simpa only [g, one_div, add_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add (f x ^ 2)
  have hlim_sq : Tendsto (fun n ↦ ∫ x, g n x ∂γ) atTop (𝓝 (∫ x, f x ^ 2 ∂γ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ A ^ 2 + 1)
      (fun n ↦ ((hf.continuous.pow 2).add continuous_const).aestronglyMeasurable)
      (integrable_const _) (fun n ↦ ae_of_all _ fun x ↦ ?_) (ae_of_all _ hgpt)
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (sq_nonneg _) (hg_pos n).le)]
    exact hg_le n x
  have hlim_mul_log : Tendsto (fun n ↦ ∫ x, g n x * log (g n x) ∂γ) atTop
      (𝓝 (∫ x, f x ^ 2 * log (f x ^ 2) ∂γ)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun _ ↦ 1 + |(A ^ 2 + 1) * log (A ^ 2 + 1)|)
      (fun n ↦ (Real.continuous_mul_log.comp
        ((hf.continuous.pow 2).add continuous_const)).aestronglyMeasurable)
      (integrable_const _) (fun n ↦ ae_of_all _ fun x ↦ ?_)
      (ae_of_all _ fun x ↦ Real.continuous_mul_log.continuousAt.tendsto.comp (hgpt x))
    simpa only [Real.norm_eq_abs] using
      TauCeti.abs_mul_log_le_one_add_abs_mul_log (add_nonneg (sq_nonneg _) (hg_pos n).le)
        (hg_le n x)
  have hent : Tendsto (fun n ↦ Measure.entropy γ (g n)) atTop
      (𝓝 ((gaussianReal 0 1).entropy (fun x ↦ f x ^ 2))) := by
    simp_rw [Measure.entropy_def]
    exact hlim_mul_log.sub (Real.continuous_mul_log.continuousAt.tendsto.comp hlim_sq)
  exact le_of_tendsto hent (Eventually.of_forall fun n ↦
    entropy_add_pos_le_two_mul_integral_deriv_sq_gaussianReal hf hA hB (hg_pos n))

end TauCeti.Probability

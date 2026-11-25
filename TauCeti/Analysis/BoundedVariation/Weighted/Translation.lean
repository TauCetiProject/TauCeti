/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.GaussGreen
public import TauCeti.Analysis.BoundedVariation.Weighted.Gaussian
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Probability.Distributions.Gaussian.Fernique
import TauCeti.MeasureTheory.Integral.Bochner.WithDensity

/-!
# The derivative of the Gaussian measure of a translated set

Let `E` be a finite-dimensional real inner product space of dimension `n ≥ 2`, with standard
Gaussian measure `γ` and Gaussian weight `W`, so that `γ = e^{−W} · volume`. For a
Lebesgue-measurable set `U` of finite Gaussian perimeter and a vector `w`, the function
`t ↦ γ(U + t w)` is differentiable at `0`, with derivative the flux of `w` through the reduced
boundary:

`d/dt γ(U + t w) |_{t = 0} = ∫_{∂*U} ⟨w, ν_U⟩ e^{−W} dHⁿ⁻¹`

(`TauCeti.hasDerivAt_measureReal_stdGaussian_smul_vadd`).

The route: by translation invariance of `volume`, `γ(U + t w) = ∫_U e^{−W(y + t w)} dy`, and
`e^{−W(y + t w)} = e^{−t ⟨y, w⟩ − t² ‖w‖² / 2} e^{−W(y)}`. Differentiating under the integral,
which is justified by Fernique's theorem (`e^{c ‖y‖²}` is `γ`-integrable for some `c > 0`),
the derivative at `0` is `∫_U (−⟨y, w⟩) e^{−W(y)} dy`. This is the left side of the weighted
Gauss–Green formula for bounded fields
(`TauCeti.integral_weightedDivergence_eq_integral_reducedBoundary_of_bounded`) applied to the
constant field `w`, whose Gaussian divergence is `−⟨x, w⟩`.

The first step is `TauCeti.measureReal_stdGaussian_vadd`; the derivative `⟨x, ·⟩` of the
Gaussian weight is `TauCeti.fderiv_gaussianWeight`.

## References

* E. Milman, J. Neeman, *The Gaussian double-bubble and multi-bubble conjectures*, Ann. of Math.
  (2022), equation (3.3).
-/

public section

noncomputable section

open MeasureTheory Set Module Filter ProbabilityTheory
open scoped Topology ENNReal RealInnerProductSpace Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- An elementary bound: for `|t| ≤ 1`,
`|⟨y + t w, w⟩| e^{−t ⟨y, w⟩ − t² ‖w‖² / 2} ≤ ‖w‖ (1 + ‖w‖) e^{(‖w‖ + 1)² / (4c)} e^{c ‖y‖²}`. -/
private theorem abs_inner_mul_exp_le {c : ℝ} (hc : 0 < c) (y w : E) {t : ℝ} (ht : |t| ≤ 1) :
    |⟪y + t • w, w⟫| * Real.exp (-(t * ⟪y, w⟫ + t ^ 2 * ‖w‖ ^ 2 / 2)) ≤
      ‖w‖ * (1 + ‖w‖) * Real.exp ((‖w‖ + 1) ^ 2 / (4 * c)) * Real.exp (c * ‖y‖ ^ 2) := by
  set r := ‖y‖
  set a := ‖w‖
  have hr : 0 ≤ r := norm_nonneg _
  have ha : 0 ≤ a := norm_nonneg _
  have hinner : |⟪y + t • w, w⟫| ≤ (r + a) * a := by
    refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ ha)
    refine (norm_add_le _ _).trans ?_
    gcongr
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left ha ht
  have hexp : -(t * ⟪y, w⟫ + t ^ 2 * ‖w‖ ^ 2 / 2) ≤ r * a := by
    have h1 : |t * ⟪y, w⟫| ≤ r * a := by
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) ht).trans (abs_real_inner_le_norm _ _)
    have h2 : 0 ≤ t ^ 2 * ‖w‖ ^ 2 / 2 := by positivity
    linarith [neg_abs_le (t * ⟪y, w⟫)]
  have hra : r + a ≤ (1 + a) * Real.exp r := by
    nlinarith [Real.add_one_le_exp r, Real.one_le_exp hr]
  have hquad : (a + 1) * r ≤ (a + 1) ^ 2 / (4 * c) + c * r ^ 2 := by
    rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * c * r - (a + 1))]
  calc |⟪y + t • w, w⟫| * Real.exp (-(t * ⟪y, w⟫ + t ^ 2 * ‖w‖ ^ 2 / 2))
      ≤ (r + a) * a * Real.exp (r * a) := by gcongr
    _ ≤ (1 + a) * Real.exp r * a * Real.exp (r * a) := by gcongr
    _ = a * (1 + a) * Real.exp ((a + 1) * r) := by
      rw [show (a + 1) * r = r + r * a by ring, Real.exp_add]; ring
    _ ≤ a * (1 + a) * Real.exp ((a + 1) ^ 2 / (4 * c) + c * r ^ 2) := by gcongr
    _ = a * (1 + a) * Real.exp ((a + 1) ^ 2 / (4 * c)) * Real.exp (c * r ^ 2) := by
      rw [Real.exp_add]; ring

/-- By Fernique's theorem, the `t`-derivatives of `e^{−t ⟨y, w⟩ − t² ‖w‖² / 2} e^{−W(y)}` for
`|t| ≤ 1` have a common Lebesgue-integrable bound. -/
private theorem exists_integrable_bound (w : E) :
    ∃ bound : E → ℝ, Integrable bound ∧ ∀ t : ℝ, |t| ≤ 1 → ∀ y : E,
      |⟪y + t • w, w⟫| * Real.exp (-(t * ⟪y, w⟫ + t ^ 2 * ‖w‖ ^ 2 / 2)) *
        Real.exp (-gaussianWeight E y) ≤ bound y := by
  obtain ⟨c, hc, hci⟩ := IsGaussian.exists_integrable_exp_sq (stdGaussian E)
  rw [← withDensity_exp_neg_gaussianWeight, MeasureTheory.integrable_withDensity_ofReal_iff
    continuous_exp_neg_gaussianWeight.aemeasurable
    (ae_of_all _ fun _ => (Real.exp_pos _).le)] at hci
  refine ⟨fun y => ‖w‖ * (1 + ‖w‖) * Real.exp ((‖w‖ + 1) ^ 2 / (4 * c)) *
    Real.exp (c * ‖y‖ ^ 2) * Real.exp (-gaussianWeight E y),
    (hci.const_mul (‖w‖ * (1 + ‖w‖) * Real.exp ((‖w‖ + 1) ^ 2 / (4 * c)))).congr
      (ae_of_all _ fun y => by simp only [smul_eq_mul]; ring), fun t ht y => ?_⟩
  exact mul_le_mul_of_nonneg_right (abs_inner_mul_exp_le hc y w ht) (Real.exp_pos _).le

/-- Differentiation under the integral sign of `t ↦ ∫_s e^{−t ⟨y, w⟩ − t² ‖w‖² / 2} e^{−W(y)} dy`
at `0`. -/
private theorem hasDerivAt_setIntegral_exp (s : Set E) (w : E) :
    HasDerivAt (fun t : ℝ => ∫ y in s,
        Real.exp (-(t * ⟪y, w⟫ + t ^ 2 * ‖w‖ ^ 2 / 2)) * Real.exp (-gaussianWeight E y))
      (∫ y in s, -⟪y, w⟫ * Real.exp (-gaussianWeight E y)) 0 := by
  obtain ⟨bound, hbound, hle⟩ := exists_integrable_bound w
  -- `fun_prop` uses this for the continuity side goals below
  have hφc := continuous_exp_neg_gaussianWeight (E := E)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict s)
    (x₀ := (0 : ℝ)) (bound := bound)
    (F := fun t y => Real.exp (-(t * ⟪y, w⟫ + t ^ 2 * ‖w‖ ^ 2 / 2)) *
      Real.exp (-gaussianWeight E y))
    (F' := fun t y => Real.exp (-(t * ⟪y, w⟫ + t ^ 2 * ‖w‖ ^ 2 / 2)) * (-⟪y + t • w, w⟫) *
      Real.exp (-gaussianWeight E y)) (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t => (by fun_prop : Continuous _).aestronglyMeasurable)
    (by simpa using (integrable_exp_neg_gaussianWeight.integrableOn (s := s)).integrable)
    ((by fun_prop : Continuous _).aestronglyMeasurable)
    (Eventually.of_forall fun y t ht => by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
      refine le_trans (le_of_eq ?_) (hle t ht.le y)
      simp only [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
      ring)
    hbound.integrableOn
    (Eventually.of_forall fun y t _ => by
      have h := ((hasDerivAt_id' t).mul_const ⟪y, w⟫).add
        ((hasDerivAt_pow 2 t).mul_const (‖w‖ ^ 2 / 2))
      have h1 : HasDerivAt (fun t : ℝ => -(t * ⟪y, w⟫ + t ^ 2 * ‖w‖ ^ 2 / 2))
          (-(⟪y, w⟫ + t * ‖w‖ ^ 2)) t := by
        convert h.neg using 1
        · funext x; simp only [Pi.neg_apply, Pi.add_apply]; ring
        · push_cast; ring
      convert h1.exp.mul_const (Real.exp (-gaussianWeight E y)) using 1
      simp only [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq,
        RCLike.conj_to_real])
  simpa using hd.2

/-- **The derivative of the Gaussian measure of a translate.** In dimension `n ≥ 2`, for a
Lebesgue-measurable set `s` of finite Gaussian perimeter and a vector `w`, the function
`t ↦ γ(s + t w)` has derivative `∫_{∂*s} ⟨w, ν_s⟩ e^{−W} dHⁿ⁻¹` at `0`, where `W` is the
Gaussian weight and `ν_s` the outer normal. -/
theorem hasDerivAt_measureReal_stdGaussian_smul_vadd (hn : 2 ≤ finrank ℝ E) {s : Set E}
    (hs : NullMeasurableSet s) (hP : gaussianPerimeter s ≠ ∞) (w : E) :
    HasDerivAt (fun t : ℝ => (stdGaussian E).real ((t • w) +ᵥ s))
      (∫ x in reducedBoundary volume ⊤ s,
        ⟪w, outerNormal volume ⊤ s x⟫ * Real.exp (-gaussianWeight E x)
          ∂μHE[finrank ℝ E - 1]) 0 := by
  have hFeq : (fun t : ℝ => (stdGaussian E).real ((t • w) +ᵥ s)) = fun t => ∫ y in s,
      Real.exp (-(t * ⟪y, w⟫ + t ^ 2 * ‖w‖ ^ 2 / 2)) * Real.exp (-gaussianWeight E y) := by
    funext t
    rw [measureReal_stdGaussian_vadd _ hs]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hFeq]
  convert hasDerivAt_setIntegral_exp s w using 1
  -- identify the derivative with the weighted Gauss–Green flux of the constant field `w`
  have hWX : Integrable fun x =>
      fderiv ℝ (gaussianWeight E) x w * Real.exp (-gaussianWeight E x) := by
    obtain ⟨bound, hbound, hle⟩ := exists_integrable_bound w
    refine hbound.mono' (by
      simp only [fderiv_gaussianWeight, innerSL_apply_apply]
      exact ((continuous_id.inner continuous_const).mul
        continuous_exp_neg_gaussianWeight).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    simpa [abs_mul, abs_of_pos (Real.exp_pos _)] using hle 0 (by simp) x
  rw [← integral_weightedDivergence_eq_integral_reducedBoundary_of_bounded
    (W := gaussianWeight E) (X := fun _ => w) contDiff_gaussianWeight hn
    integrable_exp_neg_gaussianWeight hs
    (gaussianPerimeter_def (s := s) ▸ hP) contDiff_const (C := ‖w‖) (C' := 0)
    (fun _ => le_rfl) (fun x => by simp) hWX, ← integral_indicator₀ hs]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ s <;> simp [hx]

end TauCeti

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

Along the way: the derivative `⟨x, ·⟩` of the Gaussian weight
(`TauCeti.hasFDerivAt_gaussianWeight`), the translation rule
`e^{−W(y + v)} = e^{−⟨y, v⟩ − ‖v‖² / 2} e^{−W(y)}` (`TauCeti.exp_neg_gaussianWeight_add`), and
integrability against `γ` as Lebesgue integrability after multiplication by `e^{−W}`
(`TauCeti.integrable_stdGaussian_iff`).

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
/-- The Gaussian weight has derivative `⟨x, ·⟩` at `x`. -/
theorem hasFDerivAt_gaussianWeight (x : E) :
    HasFDerivAt (gaussianWeight E) (innerSL ℝ x) x := by
  have h : gaussianWeight E = fun x =>
      ‖x‖ ^ 2 / 2 + (Module.finrank ℝ E : ℝ) / 2 * Real.log (2 * Real.pi) :=
    funext gaussianWeight_def
  rw [h]
  have h2 : HasFDerivAt (fun x : E => ‖x‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  convert (h2.mul_const (1 / 2 : ℝ)).add_const
    ((Module.finrank ℝ E : ℝ) / 2 * Real.log (2 * Real.pi)) using 1
  · funext y; ring
  · ext v; simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Translating the argument of the Gaussian density by `v` multiplies it by
`e^{−⟨y, v⟩ − ‖v‖² / 2}`. -/
theorem exp_neg_gaussianWeight_add (y v : E) :
    Real.exp (-gaussianWeight E (y + v)) =
      Real.exp (-(⟪y, v⟫ + ‖v‖ ^ 2 / 2)) * Real.exp (-gaussianWeight E y) := by
  rw [← Real.exp_add, gaussianWeight_def, gaussianWeight_def, norm_add_sq_real]
  congr 1
  ring

/-- The Gaussian measure of a set as the Lebesgue integral of the Gaussian density over it. -/
private theorem measureReal_stdGaussian_eq_setIntegral (A : Set E) :
    (stdGaussian E).real A = ∫ x in A, Real.exp (-gaussianWeight E x) := by
  have hm : Measurable fun x : E => ENNReal.ofReal (Real.exp (-gaussianWeight E x)) :=
    (contDiff_gaussianWeight (n := 0)).continuous.neg.rexp.measurable.ennreal_ofReal
  rw [← mul_one ((stdGaussian E).real A), ← smul_eq_mul, ← setIntegral_const,
    ← withDensity_exp_neg_gaussianWeight,
    setIntegral_withDensity_eq_setIntegral_toReal_smul₀' A hm.aemeasurable
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- The Gaussian measure of a translate `v + A`, as an integral over `A`. -/
private theorem measureReal_stdGaussian_vadd (v : E) (A : Set E) :
    (stdGaussian E).real (v +ᵥ A) =
      ∫ y in A, Real.exp (-(⟪y, v⟫ + ‖v‖ ^ 2 / 2)) * Real.exp (-gaussianWeight E y) := by
  rw [measureReal_stdGaussian_eq_setIntegral]
  have hpre : (fun y : E => y + v) ⁻¹' (v +ᵥ A) = A := by
    ext y
    simp [Set.mem_vadd_set, add_comm]
  rw [← (measurePreserving_add_right volume v).setIntegral_preimage_emb
    (MeasurableEquiv.addRight v).measurableEmbedding, hpre]
  exact integral_congr_ae (Eventually.of_forall fun y => exp_neg_gaussianWeight_add y v)

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

/-- Integrability against the standard Gaussian measure is Lebesgue integrability after
multiplication by the Gaussian density `e^{−W}`. -/
theorem integrable_stdGaussian_iff {g : E → ℝ} :
    Integrable g (stdGaussian E) ↔ Integrable fun x => g x * Real.exp (-gaussianWeight E x) := by
  have hm : Measurable fun x : E => ENNReal.ofReal (Real.exp (-gaussianWeight E x)) :=
    (contDiff_gaussianWeight (n := 0)).continuous.neg.rexp.measurable.ennreal_ofReal
  rw [← withDensity_exp_neg_gaussianWeight, integrable_withDensity_iff hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- By Fernique's theorem, the `t`-derivatives of `e^{−t ⟨y, w⟩ − t² ‖w‖² / 2} e^{−W(y)}` for
`|t| ≤ 1` have a common Lebesgue-integrable bound. -/
private theorem exists_integrable_bound (w : E) :
    ∃ bound : E → ℝ, Integrable bound ∧ ∀ t : ℝ, |t| ≤ 1 → ∀ y : E,
      |⟪y + t • w, w⟫| * Real.exp (-(t * ⟪y, w⟫ + t ^ 2 * ‖w‖ ^ 2 / 2)) *
        Real.exp (-gaussianWeight E y) ≤ bound y := by
  obtain ⟨c, hc, hci⟩ := IsGaussian.exists_integrable_exp_sq (stdGaussian E)
  refine ⟨fun y => ‖w‖ * (1 + ‖w‖) * Real.exp ((‖w‖ + 1) ^ 2 / (4 * c)) *
    Real.exp (c * ‖y‖ ^ 2) * Real.exp (-gaussianWeight E y),
    integrable_stdGaussian_iff.1 (hci.const_mul _), fun t ht y => ?_⟩
  exact mul_le_mul_of_nonneg_right (abs_inner_mul_exp_le hc y w ht) (Real.exp_pos _).le

/-- Differentiation under the integral sign of `t ↦ ∫_s e^{−t ⟨y, w⟩ − t² ‖w‖² / 2} e^{−W(y)} dy`
at `0`. -/
private theorem hasDerivAt_setIntegral_exp (s : Set E) (w : E) :
    HasDerivAt (fun t : ℝ => ∫ y in s,
        Real.exp (-(t * ⟪y, w⟫ + t ^ 2 * ‖w‖ ^ 2 / 2)) * Real.exp (-gaussianWeight E y))
      (∫ y in s, -⟪y, w⟫ * Real.exp (-gaussianWeight E y)) 0 := by
  obtain ⟨bound, hbound, hle⟩ := exists_integrable_bound w
  have hφc : Continuous fun y => Real.exp (-gaussianWeight E y) :=
    (contDiff_gaussianWeight (n := 0)).continuous.neg.rexp
  have hφi : Integrable fun y => Real.exp (-gaussianWeight E y) := by
    simpa using integrable_stdGaussian_iff.1 (integrable_const (1 : ℝ))
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict s)
    (x₀ := (0 : ℝ)) (bound := bound)
    (F := fun t y => Real.exp (-(t * ⟪y, w⟫ + t ^ 2 * ‖w‖ ^ 2 / 2)) *
      Real.exp (-gaussianWeight E y))
    (F' := fun t y => Real.exp (-(t * ⟪y, w⟫ + t ^ 2 * ‖w‖ ^ 2 / 2)) * (-⟪y + t • w, w⟫) *
      Real.exp (-gaussianWeight E y)) (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t => (by fun_prop : Continuous _).aestronglyMeasurable)
    (by simpa using (hφi.integrableOn (s := s)).integrable)
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
    rw [measureReal_stdGaussian_vadd]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hFeq]
  convert hasDerivAt_setIntegral_exp s w using 1
  -- identify the derivative with the weighted Gauss–Green flux of the constant field `w`
  have hfd (x : E) : fderiv ℝ (gaussianWeight E) x w = ⟪x, w⟫ := by
    simp [(hasFDerivAt_gaussianWeight x).fderiv]
  have hWX : Integrable fun x =>
      fderiv ℝ (gaussianWeight E) x w * Real.exp (-gaussianWeight E x) := by
    obtain ⟨bound, hbound, hle⟩ := exists_integrable_bound w
    have hφc : Continuous fun y => Real.exp (-gaussianWeight E y) :=
      (contDiff_gaussianWeight (n := 0)).continuous.neg.rexp
    refine hbound.mono' (by
      simp_rw [hfd]
      exact ((continuous_id.inner continuous_const).mul hφc).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    simpa [hfd, abs_mul, abs_of_pos (Real.exp_pos _)] using hle 0 (by simp) x
  rw [← integral_weightedDivergence_eq_integral_reducedBoundary_of_bounded
    (W := gaussianWeight E) (X := fun _ => w) contDiff_gaussianWeight hn
    (by simpa using integrable_stdGaussian_iff.1 (integrable_const (1 : ℝ))) hs
    (gaussianPerimeter_def (s := s) ▸ hP) contDiff_const (C := ‖w‖) (C' := 0)
    (fun _ => le_rfl) (fun x => by simp) hWX, ← integral_indicator₀ hs]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ s <;> simp [hx, hfd]

end TauCeti

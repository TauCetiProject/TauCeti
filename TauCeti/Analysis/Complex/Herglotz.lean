/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Poisson
public import Mathlib.MeasureTheory.Group.Circle
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Normed.Module.Connected
import TauCeti.MeasureTheory.Measure.Prokhorov

/-!
# The Herglotz representation of holomorphic functions with nonnegative real part

A function `F` holomorphic on the unit disc with `0 ≤ re F` is the **Herglotz transform** of a
finite positive measure `μ` on the unit circle, up to an imaginary constant:

`F w = ∫ (z + w) / (z - w) dμ(z) + (im F(0)) i`,

and conversely every such transform is holomorphic on the disc with nonnegative real part.
The representation is the basic structure theorem for holomorphic functions of positive real
part (Carathéodory functions). Through a Cayley transform it gives the Nevanlinna representation
of Pick functions, which in turn underlies the analytic characterizations of Stieltjes and
complete Bernstein functions.

The proof has two steps.
* **Finite radius.** For `f` holomorphic on a disc and continuous up to its boundary, the
  Herglotz–Riesz integral of the boundary values of `re f` is holomorphic, and by Mathlib's
  Poisson formula (`DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul`) it has the same real
  part as `f`. By the open mapping theorem the two differ by an imaginary constant, which
  evaluation at the centre identifies.
* **Weak limit.** Applied to the dilations `w ↦ F (r * w)`, `r < 1`, this represents each dilation
  by the measure with density `re F (r z)` against normalized arc length. These measures all have
  mass `re F(0)`; since the circle is compact, Prokhorov's theorem gives a weak cluster point `μ`
  as `r → 1`, and the kernel `z ↦ (z + w) / (z - w)` is continuous on the circle, so the
  representation passes to the limit.

## Main results

* `DiffContOnCl.circleAverage_herglotzRieszKernel_smul_re_add`: the Herglotz formula on a disc,
  recovering a holomorphic function from the boundary values of its real part.
* `TauCeti.differentiableOn_integral_add_div_sub` and `TauCeti.re_integral_add_div_sub_nonneg`:
  the Herglotz transform of a finite measure on the circle is holomorphic on the disc with
  nonnegative real part.
* `TauCeti.exists_isFiniteMeasure_eq_integral_add_div_sub`: **the Herglotz representation
  theorem**.
* `TauCeti.differentiableOn_and_re_nonneg_iff_exists_eq_integral_add_div_sub`: the resulting
  characterization of holomorphic functions on the disc with nonnegative real part.

## References

* G. Herglotz, *Über Potenzreihen mit positivem, reellem Teil im Einheitskreis*, Ber. Verh.
  Sächs. Akad. Wiss. Leipzig **63** (1911), 501–511.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Chapter 11 (positive harmonic functions and
  the Herglotz representation).
* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*, 2nd ed.,
  Chapter 6 (the Nevanlinna–Pick representation, via the Herglotz theorem).
-/

public section

noncomputable section

open Complex MeasureTheory Metric Real Set Filter Topology
open scoped NNReal ENNReal

namespace TauCeti

variable {f : ℂ → ℂ} {c w : ℂ} {R : ℝ}

/-- The centre-zero case of `DiffContOnCl.circleAverage_herglotzRieszKernel_smul_re_add`;
the general case is obtained by translation. -/
private lemma circleAverage_herglotzRieszKernel_smul_re_add_of_center_zero
    (hf : DiffContOnCl ℂ f (ball 0 R)) (hw : w ∈ ball 0 R) :
    circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • ((f ζ).re : ℂ)) 0 R + (f 0).im * I =
      f w := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hcont : ContinuousOn f (sphere 0 |R|) := by
    refine hf.2.mono ?_
    rw [abs_of_pos hR, closure_ball 0 hR.ne']
    exact sphere_subset_closedBall
  have hre : CircleIntegrable (fun ζ ↦ (f ζ).re) 0 R :=
    (continuous_re.comp_continuousOn hcont).circleIntegrable'
  have hreC : CircleIntegrable (fun ζ ↦ ((f ζ).re : ℂ)) 0 R :=
    (continuous_ofReal.comp_continuousOn (continuous_re.comp_continuousOn hcont)).circleIntegrable'
  have hball : ball (0 : ℂ) R ⊆ (sphere 0 |R|)ᶜ := by
    intro z hz hzs
    rw [abs_of_pos hR, mem_sphere_zero_iff_norm] at hzs
    exact (mem_ball_zero_iff.1 hz).ne hzs
  -- `G` is the Herglotz–Riesz integral of the real part of `f`; it is holomorphic on the disc.
  set G : ℂ → ℂ := fun z ↦
    circleAverage (fun ζ ↦ herglotzRieszKernel 0 z ζ • ((f ζ).re : ℂ)) 0 R with hG_def
  have hG : AnalyticOnNhd ℂ G (ball 0 R) :=
    (analyticOnNhd_circleAverage_herglotzRieszKernel_smul hreC).mono hball
  have hF : AnalyticOnNhd ℂ f (ball 0 R) := hf.1.analyticOnNhd isOpen_ball
  -- By the Poisson formula, `G` and `f` have the same real part on the disc.
  have hreeq : ∀ z ∈ ball (0 : ℂ) R, ((G - f) z).re = 0 := by
    intro z hz
    have hint : CircleIntegrable ((re ∘ herglotzRieszKernel 0 z) • f) 0 R :=
      ((continuous_re.comp_continuousOn
        (continuousOn_herglotzRieszKernel_sphere (hball hz))).smul hcont).circleIntegrable'
    have h₁ := re_circleAverage_herglotzRieszKernel_smul hre (hball hz)
    have h₂ := reCLM.circleAverage_comp_comm hint
    rw [hf.circleAverage_re_herglotzRieszKernel_smul hz, reCLM_apply] at h₂
    rw [Pi.sub_apply, sub_re, hG_def, h₁, ← h₂, sub_eq_zero]
    congr 1
    ext ζ
    simp
  obtain ⟨k, hk⟩ := (hG.sub hF).eq_const_of_re_eq_const hreeq isOpen_ball (isConnected_ball hR)
  -- Evaluating at the centre identifies the constant as `-(f 0).im * I`.
  have hG₀ : G 0 = ((f 0).re : ℂ) := by
    have hsphere : EqOn (fun ζ ↦ herglotzRieszKernel 0 0 ζ • ((f ζ).re : ℂ))
        ((ofRealCLM.comp reCLM) ∘ f) (sphere 0 |R|) := by
      intro ζ hζ
      have hζ₀ : ζ ≠ 0 := ne_of_mem_sphere hζ (abs_pos.2 hR.ne').ne'
      simp [herglotzRieszKernel_def, hζ₀]
    have hf' : DiffContOnCl ℂ f (ball 0 |R|) := by rwa [abs_of_pos hR]
    rw [hG_def]
    dsimp only
    rw [circleAverage_congr_sphere hsphere,
      (ofRealCLM.comp reCLM).circleAverage_comp_comm hcont.circleIntegrable', hf'.circleAverage]
    simp
  have e₁ := hk w hw
  have e₀ := hk 0 (mem_ball_self hR)
  simp only [Pi.sub_apply] at e₁ e₀
  linear_combination e₁ - e₀ + hG₀ + re_add_im (f 0)

/-- **The Herglotz formula** on a disc: a function holomorphic on a disc and continuous up to its
boundary is the Herglotz–Riesz integral of its boundary real part, plus the imaginary constant
`(f c).im * I`. Unlike the Poisson formula, which recovers `f` from all of its boundary values,
this recovers `f` from the boundary values of its real part alone. -/
theorem _root_.DiffContOnCl.circleAverage_herglotzRieszKernel_smul_re_add
    (hf : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    circleAverage (fun ζ ↦ herglotzRieszKernel c w ζ • ((f ζ).re : ℂ)) c R + (f c).im * I =
      f w := by
  have hg : DiffContOnCl ℂ (fun z ↦ f (z + c)) (ball 0 R) :=
    hf.comp (DifferentiableOn.diffContOnCl <| by fun_prop) (by intro; aesop)
  have hw' : w - c ∈ ball 0 R := by simpa using mem_ball_iff_norm.1 hw
  have h := circleAverage_herglotzRieszKernel_smul_re_add_of_center_zero hg hw'
  simp only [zero_add, sub_add_cancel] at h
  rw [← circleAverage_map_add_const]
  simpa [herglotzRieszKernel_add_const] using h

/-! ### Boundary measures with a continuous density -/

/-- The measure on `Circle` with density `φ` with respect to normalized arc length. -/
private def circleDensityMeasure (φ : ℂ → ℝ) : Measure Circle :=
  ((volume.restrict (Ioc 0 (2 * π))).withDensity
    fun θ ↦ ENNReal.ofReal ((2 * π)⁻¹ * φ (circleMap 0 1 θ))).map Circle.exp

private lemma continuous_comp_circleMap {φ : ℂ → ℝ} (hφ : ContinuousOn φ (sphere 0 1)) :
    Continuous fun θ ↦ φ (circleMap 0 1 θ) :=
  hφ.comp_continuous (continuous_circleMap 0 1) fun θ ↦ circleMap_mem_sphere 0 zero_le_one θ

private lemma isFiniteMeasure_circleDensityMeasure {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ (sphere 0 1)) : IsFiniteMeasure (circleDensityMeasure φ) := by
  have hint : IntegrableOn (fun θ ↦ (2 * π)⁻¹ * φ (circleMap 0 1 θ)) (Ioc 0 (2 * π)) :=
    ((continuous_const.mul (continuous_comp_circleMap hφ)).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have := isFiniteMeasure_withDensity_ofReal hint.hasFiniteIntegral
  unfold circleDensityMeasure
  infer_instance

private lemma integral_circleDensityMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {φ : ℂ → ℝ} (hφ : ContinuousOn φ (sphere 0 1))
    (hφ₀ : ∀ z ∈ sphere (0 : ℂ) 1, 0 ≤ φ z) {g : ℂ → E} (hg : ContinuousOn g (sphere 0 1)) :
    ∫ z : Circle, g z ∂circleDensityMeasure φ = circleAverage (fun ζ ↦ φ ζ • g ζ) 0 1 := by
  have hgc : Continuous fun z : Circle ↦ g z :=
    hg.comp_continuous continuous_subtype_val fun z ↦ by simp
  have hexp : ∀ θ : ℝ, (Circle.exp θ : ℂ) = circleMap 0 1 θ := fun θ ↦ by
    simp [Circle.coe_exp, circleMap]
  have hmeas : Measurable fun θ ↦ ENNReal.ofReal ((2 * π)⁻¹ * φ (circleMap 0 1 θ)) :=
    (continuous_const.mul (continuous_comp_circleMap hφ)).measurable.ennreal_ofReal
  rw [circleDensityMeasure, integral_map Circle.exp.continuous.aemeasurable
    hgc.aestronglyMeasurable, integral_withDensity_eq_integral_toReal_smul hmeas
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top), circleAverage_def,
    intervalIntegral.integral_of_le (by positivity), ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun θ ↦ ?_)
  have h₀ : 0 ≤ (2 * π)⁻¹ * φ (circleMap 0 1 θ) :=
    mul_nonneg (by positivity) (hφ₀ _ (circleMap_mem_sphere 0 zero_le_one θ))
  simp only [hexp, ENNReal.toReal_ofReal h₀, smul_smul]

/-! ### The Herglotz transform of a measure on the circle -/

private lemma coe_sub_ne_zero (hw : w ∈ ball (0 : ℂ) 1) (z : Circle) : (z : ℂ) - w ≠ 0 := by
  rw [sub_ne_zero]
  rintro rfl
  simp at hw

private lemma continuous_add_div_sub (hw : w ∈ ball (0 : ℂ) 1) :
    Continuous fun z : Circle ↦ ((z : ℂ) + w) / ((z : ℂ) - w) :=
  (continuous_subtype_val.add continuous_const).div (continuous_subtype_val.sub continuous_const)
    (coe_sub_ne_zero hw)

/-- The Herglotz transform `w ↦ ∫ (z + w) / (z - w) dμ(z)` of a finite measure on the unit
circle is holomorphic on the unit disc. -/
theorem differentiableOn_integral_add_div_sub (μ : Measure Circle) [IsFiniteMeasure μ] :
    DifferentiableOn ℂ (fun w ↦ ∫ z : Circle, ((z : ℂ) + w) / ((z : ℂ) - w) ∂μ) (ball 0 1) := by
  intro w₀ hw₀
  have hw₀' : ‖w₀‖ < 1 := mem_ball_zero_iff.1 hw₀
  set ε : ℝ := (1 - ‖w₀‖) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  -- On `ball w₀ ε` the pole `w` stays at distance at least `ε` from the circle.
  have hball : ball w₀ ε ⊆ ball 0 1 := by
    intro w hw
    rw [mem_ball_zero_iff]
    linarith [norm_le_norm_add_norm_sub' w w₀, (mem_ball_iff_norm.1 hw)]
  have hdist : ∀ w ∈ ball w₀ ε, ∀ z : Circle, ε ≤ ‖(z : ℂ) - w‖ := by
    intro w hw z
    have h₁ := mem_ball_iff_norm.1 hw
    have h₂ := norm_sub_norm_le (z : ℂ) w
    have h₃ := norm_le_norm_add_norm_sub' w w₀
    rw [Circle.norm_coe] at h₂
    linarith
  have hderiv : ∀ z : Circle, ∀ w ∈ ball w₀ ε, HasDerivAt (fun w ↦ ((z : ℂ) + w) / ((z : ℂ) - w))
      (2 * z / ((z : ℂ) - w) ^ 2) w := by
    intro z w hw
    have hne := coe_sub_ne_zero (hball hw) z
    exact (((hasDerivAt_id' w).const_add (z : ℂ)).div
      ((hasDerivAt_id' w).const_sub (z : ℂ)) hne).congr_deriv (by ring)
  have hF' : Continuous fun z : Circle ↦ 2 * (z : ℂ) / ((z : ℂ) - w₀) ^ 2 :=
    (continuous_const.mul continuous_subtype_val).div
      ((continuous_subtype_val.sub continuous_const).pow 2)
      fun z ↦ pow_ne_zero 2 (coe_sub_ne_zero hw₀ z)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ ↦ 2 / ε ^ 2)
    (ball_mem_nhds w₀ hε) ?_ ((continuous_add_div_sub hw₀).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) hF'.aestronglyMeasurable ?_ (integrable_const _)
    (ae_of_all _ hderiv)).2.differentiableAt.differentiableWithinAt
  · filter_upwards [ball_mem_nhds w₀ hε] with w hw
    exact (continuous_add_div_sub (hball hw)).aestronglyMeasurable
  · refine ae_of_all _ fun z w hw ↦ ?_
    rw [norm_div, norm_mul, norm_pow, Circle.norm_coe, Complex.norm_ofNat, mul_one]
    gcongr
    exact hdist w hw z

/-- The Herglotz transform of a measure on the unit circle has nonnegative real part on the unit
disc. -/
theorem re_integral_add_div_sub_nonneg (μ : Measure Circle) (hw : w ∈ ball (0 : ℂ) 1) :
    0 ≤ (∫ z : Circle, ((z : ℂ) + w) / ((z : ℂ) - w) ∂μ).re := by
  by_cases hint : Integrable (fun z : Circle ↦ ((z : ℂ) + w) / ((z : ℂ) - w)) μ
  swap
  · simp [integral_undef hint]
  rw [← reCLM_apply, ← reCLM.integral_comp_comm hint]
  refine integral_nonneg fun z ↦ ?_
  have h := congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := 0) (w := w)) z
  simp only [Function.comp_apply, poissonKernel_def, herglotzRieszKernel_def, sub_zero,
    Circle.norm_coe] at h
  rw [reCLM_apply, ← h]
  have : ‖w‖ ^ 2 ≤ 1 := by
    have := mem_ball_zero_iff.1 hw
    nlinarith [norm_nonneg w]
  rw [Pi.zero_apply]
  exact div_nonneg (by rw [one_pow]; linarith) (sq_nonneg _)

/-! ### The Herglotz representation -/

/-- The dilations `w ↦ F (r * w)`, `0 ≤ r < 1`, of a holomorphic function on the unit disc with
nonnegative real part are Herglotz transforms: the representing measure has density
`(F (r * z)).re` with respect to normalized arc length on the circle. -/
private lemma exists_isFiniteMeasure_comp_mul_eq_integral_add_div_sub
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1))
    (hre : ∀ w ∈ ball (0 : ℂ) 1, 0 ≤ (F w).re) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    ∃ ν : Measure Circle, IsFiniteMeasure ν ∧ ∀ w ∈ ball (0 : ℂ) 1,
      F (r * w) = ∫ z : Circle, ((z : ℂ) + w) / ((z : ℂ) - w) ∂ν + (F 0).im * I := by
  have hmaps : MapsTo (fun z : ℂ ↦ (r : ℂ) * z) (closedBall 0 1) (ball 0 1) := fun z hz ↦ by
    rw [mem_closedBall_zero_iff] at hz
    rw [mem_ball_zero_iff, norm_mul, norm_real, Real.norm_of_nonneg hr₀]
    nlinarith [norm_nonneg z]
  have hdiff : DifferentiableOn ℂ (fun z ↦ F (r * z)) (closedBall 0 1) :=
    hF.comp (by fun_prop) hmaps
  have hφc : ContinuousOn (fun ζ ↦ (F (r * ζ)).re) (sphere 0 1) :=
    continuous_re.comp_continuousOn (hdiff.continuousOn.mono sphere_subset_closedBall)
  have hφ₀ : ∀ z ∈ sphere (0 : ℂ) 1, 0 ≤ (F (r * z)).re := fun z hz ↦
    hre _ (hmaps (sphere_subset_closedBall hz))
  refine ⟨circleDensityMeasure fun ζ ↦ (F (r * ζ)).re,
    isFiniteMeasure_circleDensityMeasure hφc, fun w hw ↦ ?_⟩
  have hK : ContinuousOn (fun ζ : ℂ ↦ (ζ + w) / (ζ - w)) (sphere 0 1) := by
    have hw' : w ∉ sphere (0 : ℂ) |1| := by
      rw [abs_one, mem_sphere_zero_iff_norm]
      exact (mem_ball_zero_iff.1 hw).ne
    simpa [herglotzRieszKernel_fun_def] using continuousOn_herglotzRieszKernel_sphere hw'
  have hcl : DiffContOnCl ℂ (fun z ↦ F (r * z)) (ball 0 1) :=
    DifferentiableOn.diffContOnCl (by rwa [closure_ball 0 one_ne_zero])
  have h := hcl.circleAverage_herglotzRieszKernel_smul_re_add hw
  rw [mul_zero] at h
  rw [← h, integral_circleDensityMeasure hφc hφ₀ hK]
  congr 2
  ext ζ
  simp [herglotzRieszKernel_def, Complex.real_smul, mul_comm]

/-- **The Herglotz representation theorem.** A function holomorphic on the unit disc with
nonnegative real part is the Herglotz transform `∫ (z + w) / (z - w) dμ(z)` of a finite positive
measure `μ` on the unit circle, plus the imaginary constant `(F 0).im * I`. -/
theorem exists_isFiniteMeasure_eq_integral_add_div_sub
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1))
    (hre : ∀ w ∈ ball (0 : ℂ) 1, 0 ≤ (F w).re) :
    ∃ μ : Measure Circle, IsFiniteMeasure μ ∧ ∀ w ∈ ball (0 : ℂ) 1,
      F w = ∫ z : Circle, ((z : ℂ) + w) / ((z : ℂ) - w) ∂μ + (F 0).im * I := by
  -- Represent the dilations `w ↦ F (r n * w)` along radii `r n = 1 - 1 / (n + 1) ↑ 1`.
  set r : ℕ → ℝ := fun n ↦ 1 - 1 / ((n : ℝ) + 1) with hr_def
  have hr_lim : Tendsto r atTop (𝓝 1) := by
    simpa [hr_def] using (tendsto_const_nhds (x := (1 : ℝ))).sub
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hdil : ∀ n, ∃ ν : Measure Circle, IsFiniteMeasure ν ∧ ∀ w ∈ ball (0 : ℂ) 1,
      F (r n * w) = ∫ z : Circle, ((z : ℂ) + w) / ((z : ℂ) - w) ∂ν + (F 0).im * I := fun n ↦
    exists_isFiniteMeasure_comp_mul_eq_integral_add_div_sub hF hre
      (by simp only [hr_def, sub_nonneg]
          exact div_le_one_of_le₀ (by linarith [n.cast_nonneg (α := ℝ)]) (by positivity))
      (by simp only [hr_def]; linarith [show 0 < 1 / ((n : ℝ) + 1) by positivity])
  choose μs hμs hrep using hdil
  -- Evaluating at the centre shows that every `μs n` has mass `(F 0).re`.
  have hre₀ : 0 ≤ (F 0).re := hre 0 (mem_ball_self one_pos)
  let C : ℝ≥0 := ⟨(F 0).re, hre₀⟩
  have hmass : ∀ n, μs n univ ≤ C := fun n ↦ by
    have h := congrArg re (hrep n 0 (mem_ball_self one_pos))
    simp only [mul_zero, add_zero, sub_zero, ne_eq, Circle.coe_ne_zero, not_false_eq_true,
      div_self, integral_const, real_smul, mul_one, add_re, ofReal_re, mul_re, I_re, ofReal_im,
      I_im, sub_self] at h
    rw [← ofReal_measureReal (measure_ne_top _ _), ← h, ENNReal.ofReal_eq_coe_nnreal hre₀]
    exact le_rfl
  -- By Prokhorov compactness, the `μs n` converge weakly along an ultrafilter `U ≤ atTop`.
  obtain ⟨μ, U, hU, hμ, -, hlim⟩ :=
    finite_measure_cluster_limit μs _ hmass IsTightMeasureSet.of_compactSpace
  refine ⟨μ, hμ, fun w hw ↦ ?_⟩
  let μf : ℕ → FiniteMeasure Circle := fun n ↦ ⟨μs n, hμs n⟩
  let μf₀ : FiniteMeasure Circle := ⟨μ, hμ⟩
  have hweak : Tendsto μf U (𝓝 μf₀) := FiniteMeasure.tendsto_iff_forall_integral_tendsto.2 hlim
  -- Pass to the limit along `U` on both sides of the dilated Herglotz formulas.
  have hconv := (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hweak
    (.mkOfCompact ⟨_, continuous_add_div_sub hw⟩)
  have hFlim : Tendsto (fun n ↦ F (r n * w)) U (𝓝 (F w)) := by
    have h : Tendsto (fun n ↦ (r n : ℂ) * w) atTop (𝓝 w) := by
      simpa using ((continuous_ofReal.tendsto 1).comp hr_lim).mul_const w
    exact ((hF.continuousOn.continuousAt (isOpen_ball.mem_nhds hw)).tendsto.comp h).mono_left hU
  exact tendsto_nhds_unique hFlim ((hconv.add_const _).congr fun n ↦ (hrep n w hw).symm)

/-- **The Herglotz representation theorem**, as a characterization: a function on the unit disc
is holomorphic with nonnegative real part if and only if it is the Herglotz transform of a finite
positive measure on the unit circle plus an imaginary constant. -/
theorem differentiableOn_and_re_nonneg_iff_exists_eq_integral_add_div_sub {F : ℂ → ℂ} :
    (DifferentiableOn ℂ F (ball 0 1) ∧ ∀ w ∈ ball (0 : ℂ) 1, 0 ≤ (F w).re) ↔
      ∃ (μ : Measure Circle) (b : ℝ), IsFiniteMeasure μ ∧ ∀ w ∈ ball (0 : ℂ) 1,
        F w = ∫ z : Circle, ((z : ℂ) + w) / ((z : ℂ) - w) ∂μ + b * I := by
  refine ⟨fun ⟨hF, hre⟩ ↦ ?_, fun ⟨μ, b, hμ, hrep⟩ ↦ ⟨?_, fun w hw ↦ ?_⟩⟩
  · obtain ⟨μ, hμ, hrep⟩ := exists_isFiniteMeasure_eq_integral_add_div_sub hF hre
    exact ⟨μ, (F 0).im, hμ, hrep⟩
  · exact ((differentiableOn_integral_add_div_sub μ).add_const _).congr hrep
  · rw [hrep w hw, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
    simpa using re_integral_add_div_sub_nonneg μ hw

end TauCeti

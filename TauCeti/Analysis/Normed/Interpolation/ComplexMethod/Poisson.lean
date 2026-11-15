/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Poisson.Strip
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Calderón's log-convexity and Poisson integral bounds for `[X₀, X₁]_θ`

Pulling the Herglotz–Riesz integral on `ball 0 1` back along `TauCeti.stripToUnitDisc` refines the
three-lines bound on `[X₀, X₁]_θ` to Calderón's log-convexity inequality (Bergh–Löfström,
Lemma 4.3.2): for `0 < θ < 1` and `ε > 0`,
`‖u‖ ≤ exp (∫ μ₀(θ, t) log (max ‖g₀ t‖ ε) dt + ∫ μ₁(θ, t) log (max ‖g₁ t‖ ε) dt)`.
Applying Jensen's inequality (`ConvexOn.map_integral_le` for `Real.exp`) to `stripPoissonMeasure₀ θ`
and `stripPoissonMeasure₁ θ` and letting `ε → 0⁺` yields `(L^{p₀}, L^{p₁})` and mixed `(L^∞, L^p)`
bounds on `[X₀, X₁]_θ` without completeness, density of the intersection, or duality.

## Main results

* `TauCeti.CompatibleCouple.ComplexMethodSpace.norm_le_exp_integral_stripPoissonKernel`:
  Calderón's log-convexity bound for `[X₀, X₁]_θ`.
* `TauCeti.CompatibleCouple.ComplexMethodSpace.norm_le_rpow_integral_stripPoissonMeasure`,
  `norm_le_norm_fst_rpow_mul_rpow_integral_stripPoissonMeasure`,
  `norm_le_rpow_integral_stripPoissonMeasure_mul_norm_snd_rpow`, and
  `norm_le_rpow_integral_stripPoissonKernel`: `(L^{p₀}, L^{p₁})`, mixed, and `L¹` strip Poisson
  bounds.

## References

* I. I. Hirschman, *A convexity theorem for certain groups of transformations*, J. Analyse Math.
  **2** (1952), 209–218.
* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. **24**
  (1964), 113–190, §9.4.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Springer, 1976, Lemma 4.3.2.
-/

public noncomputable section

open Complex Complex.HadamardThreeLines TauCeti.Complex.HadamardThreeLines
open Filter MeasureTheory Metric Real Set
open scoped ENNReal Topology ZeroAtInfty

namespace TauCeti

/-! ### Regularized Jensen inequalities for `C₀(ℝ, X)` traces -/

private theorem integrable_log_max_of_zeroAtInfty {X : Type*} [NormedAddCommGroup X]
    {μ : Measure ℝ} [IsFiniteMeasure μ] (f : C₀(ℝ, X)) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun t ↦ Real.log (max ‖f t‖ ε)) μ :=
  Integrable.of_mem_Icc (Real.log ε) (Real.log (max ‖f‖ ε))
    (((continuous_norm.comp f.continuous).max continuous_const).log
      fun _ ↦ (lt_max_of_lt_right hε).ne').aemeasurable
    (Eventually.of_forall fun t ↦ ⟨Real.log_le_log hε (le_max_right _ _),
      Real.log_le_log (lt_max_of_lt_right hε)
        (max_le_max_right ε (ZeroAtInftyContinuousMap.norm_coe_le_norm f t))⟩)

private theorem exp_mul_integral_log_max_le {X : Type*} [NormedAddCommGroup X]
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (f : C₀(ℝ, X)) {α p ε : ℝ}
    (hα : 0 ≤ α) (hp : 0 < p) (hε : 0 < ε) :
    Real.exp (α * ∫ t, Real.log (max ‖f t‖ ε) ∂μ) ≤
      ((∫ t, ‖f t‖ ^ p ∂μ) + ε ^ p) ^ (α / p) := by
  set w : ℝ → ℝ := fun t ↦ p * Real.log (max ‖f t‖ ε)
  have hmax_pos (t : ℝ) : 0 < max ‖f t‖ ε := lt_max_of_lt_right hε
  have hw_int : Integrable w μ := (integrable_log_max_of_zeroAtInfty f hε).const_mul p
  have hexp_eq : Real.exp ∘ w = fun t ↦ (max ‖f t‖ ε) ^ p := by
    ext t; simp only [Function.comp_apply, w, Real.rpow_def_of_pos (hmax_pos t), mul_comm p]
  have hbnd {g : ℝ → ℝ} (hg : Continuous g) {M : ℝ} (h0 : ∀ t, 0 ≤ g t) (hM : ∀ t, g t ≤ M) :
      Integrable (fun t ↦ g t ^ p) μ :=
    Integrable.of_mem_Icc 0 (M ^ p) (hg.rpow_const fun _ ↦ Or.inr hp.le).aemeasurable
      (Eventually.of_forall fun t ↦
        ⟨Real.rpow_nonneg (h0 t) _, Real.rpow_le_rpow (h0 t) (hM t) hp.le⟩)
  have hexp_int : Integrable (Real.exp ∘ w) μ := hexp_eq ▸ hbnd
    ((continuous_norm.comp f.continuous).max continuous_const) (fun t ↦ (hmax_pos t).le)
    fun t ↦ max_le_max_right ε (ZeroAtInftyContinuousMap.norm_coe_le_norm f t)
  have hf_int : Integrable (fun t ↦ ‖f t‖ ^ p) μ := hbnd (continuous_norm.comp f.continuous)
    (fun _ ↦ norm_nonneg _) (ZeroAtInftyContinuousMap.norm_coe_le_norm f)
  have hjensen : Real.exp (∫ t, w t ∂μ) ≤ (∫ t, ‖f t‖ ^ p ∂μ) + ε ^ p := by
    have hpt (t : ℝ) : (Real.exp ∘ w) t ≤ ‖f t‖ ^ p + ε ^ p := by
      rw [hexp_eq]; dsimp only
      rcases le_total ‖f t‖ ε with hle | hle
      · rw [max_eq_right hle]; exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)
      · rw [max_eq_left hle]; exact le_add_of_nonneg_right (Real.rpow_nonneg hε.le _)
    refine (convexOn_exp.map_integral_le continuousOn_exp isClosed_univ
      (Eventually.of_forall fun _ ↦ mem_univ _) hw_int hexp_int).trans <|
      (integral_mono hexp_int (hf_int.add (integrable_const (ε ^ p))) hpt).trans_eq ?_
    rw [Pi.add_def, integral_add hf_int (integrable_const (ε ^ p)), integral_const, probReal_univ,
      one_smul]
  have hpow := Real.rpow_le_rpow (Real.exp_nonneg _) hjensen (div_nonneg hα hp.le)
  rw [← Real.exp_mul] at hpow
  have harg : (∫ t, w t ∂μ) * (α / p) = α * ∫ t, Real.log (max ‖f t‖ ε) ∂μ := by
    simp only [w, integral_const_mul]; field_simp [hp.ne']
  rwa [harg] at hpow

private theorem exp_mul_integral_log_max_le_norm {X : Type*} [NormedAddCommGroup X]
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (f : C₀(ℝ, X)) {α ε : ℝ}
    (hα : 0 ≤ α) (hε : 0 < ε) :
    Real.exp (α * ∫ t, Real.log (max ‖f t‖ ε) ∂μ) ≤ (max ‖f‖ ε) ^ α := by
  have hle : ∫ t, Real.log (max ‖f t‖ ε) ∂μ ≤ Real.log (max ‖f‖ ε) := by
    refine (integral_mono (integrable_log_max_of_zeroAtInfty f hε) (integrable_const _) fun t ↦
      Real.log_le_log (lt_max_of_lt_right hε)
        (max_le_max_right ε (ZeroAtInftyContinuousMap.norm_coe_le_norm f t))).trans_eq ?_
    rw [integral_const, probReal_univ, one_smul]
  rw [Real.rpow_def_of_pos (lt_max_of_lt_right hε), mul_comm _ α]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hle hα)

/-! ### Herglotz–Riesz multipliers and Calderón's log-convexity inequality -/

namespace CompatibleCouple.ComplexMethodSpace

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  {C : CompatibleCouple ℂ X₀ X₁ V}

private theorem exists_herglotz_multiplier {θ δ : ℝ} (hθ : θ ∈ Ioo 0 1) (hδ : 0 < δ)
    {ψ : ℂ → ℝ} (hψ : ContinuousOn ψ (sphere 0 1)) :
    ∃ (r : ℝ) (c : ℂ → ℂ) (K : ℝ), r ∈ Ioo 0 1 ∧
      DiffContOnCl ℂ c (verticalStrip 0 1) ∧
      (∀ z ∈ verticalClosedStrip 0 1, ‖c z‖ ≤ K) ∧
      c θ = 1 ∧
      (∀ ζ ∈ sphere 0 |1|, |ψ ζ - planarPoissonIntegral ψ 0 1 ((r : ℂ) * ζ)| < δ) ∧
      ∀ z ∈ verticalClosedStrip 0 1,
        ‖c z‖ = Real.exp (circleAverage ψ 0 1 -
          planarPoissonIntegral ψ 0 1 ((r : ℂ) * stripToUnitDisc θ z)) := by
  have hψ' : ContinuousOn ψ (sphere 0 |1|) := by simpa using hψ
  have hψi : CircleIntegrable ψ 0 1 := hψ'.circleIntegrable'
  have hψic : CircleIntegrable (fun ζ ↦ (ψ ζ : ℂ)) 0 1 := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hψi ⊢
    exact Complex.ofRealCLM.integrable_comp hψi
  let H : ℂ → ℂ := fun w ↦ circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • (ψ ζ : ℂ)) 0 1
  have hH_re {w : ℂ} (hw : w ∈ ball 0 1) : (H w).re = planarPoissonIntegral ψ 0 1 w := by
    rw [planarPoissonIntegral_def, poissonKernel_eq_re_herglotzRieszKernel]
    exact re_circleAverage_herglotzRieszKernel_smul hψi (by simpa using (mem_ball_zero_iff.1 hw).ne)
  have hH0 : (H 0).re = circleAverage ψ 0 1 := by
    rw [hH_re (mem_ball_self zero_lt_one), planarPoissonIntegral_def]
    exact circleAverage_congr_sphere fun ζ hζ ↦ by
      have hζ1 : ‖ζ‖ = 1 := by simpa using hζ
      simp [poissonKernel_def, hζ1]
  obtain ⟨r, hr_dist, hr_mem⟩ := ((Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_planarPoissonIntegral_smul one_ne_zero hψ') δ hδ).and
    (Ioo_mem_nhdsLT zero_lt_one)).exists
  let c : ℂ → ℂ := fun z ↦ exp (H 0 - H ((r : ℂ) * stripToUnitDisc θ z))
  have hc_ball {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
      (r : ℂ) * stripToUnitDisc θ z ∈ closedBall 0 r := by
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_of_nonneg hr_mem.1.le]
    exact mul_le_of_le_one_right hr_mem.1.le (norm_stripToUnitDisc_le_one hθ hz)
  have hcb_sub : closedBall (0 : ℂ) r ⊆ (sphere 0 |1|)ᶜ := fun w hw ↦ by
    simp only [mem_compl_iff, mem_sphere_zero_iff_norm, abs_one]
    exact ((mem_closedBall_zero_iff.1 hw).trans_lt hr_mem.2).ne
  have hc_diff : DifferentiableOn ℂ c (verticalClosedStrip 0 1) := fun z hz ↦
    ((differentiableAt_const _).sub
      ((hasDerivAt_circleAverage_herglotzRieszKernel_smul hψic
        (hcb_sub (hc_ball hz))).differentiableAt.comp z
        ((differentiableAt_stripToUnitDisc hθ hz).const_mul (r : ℂ)))).cexp.differentiableWithinAt
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    (continuous_exp.comp_continuousOn (continuousOn_const.sub
      ((differentiableOn_circleAverage_herglotzRieszKernel_smul hψic).continuousOn.mono hcb_sub)))
  refine ⟨r, c, K, hr_mem,
    ⟨hc_diff.mono (verticalStrip_subset_verticalClosedStrip 0 1),
      hc_diff.continuousOn.mono (closure_verticalStrip_subset 0 1)⟩,
    fun _ hz ↦ hK _ (hc_ball hz), by simp [c],
    fun ζ hζ ↦ by simpa [Real.dist_eq, Complex.real_smul] using hr_dist ζ hζ, fun z hz ↦ ?_⟩
  rw [Complex.norm_exp, sub_re, hH0, hH_re (closedBall_subset_ball hr_mem.2 (hc_ball hz))]

private theorem norm_le_exp_circleAverage_add {θ ε δ : ℝ} (hθ : θ ∈ Ioo 0 1) (hε : 0 < ε)
    (hδ : 0 < δ) {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace}
    {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g) (hu : toSum u = F θ)
    {ψ : ℂ → ℝ} (hψ : ContinuousOn ψ (sphere 0 1))
    (hψ₀ : ∀ t, Real.log (max ‖g.1 t‖ ε) ≤ ψ (stripToUnitDisc θ (t * I)))
    (hψ₁ : ∀ t, Real.log (max ‖g.2 t‖ ε) ≤ ψ (stripToUnitDisc θ (1 + t * I))) :
    ‖u‖ ≤ Real.exp (circleAverage ψ 0 1 + δ) := by
  obtain ⟨r, c, K, _, hc_diff, hK, hcθ, hr_dist, hc_norm⟩ := exists_herglotz_multiplier hθ hδ hψ
  obtain ⟨g', hsmul, hg'₀, hg'₁⟩ := hF.exists_smul_of_diffContOnCl hc_diff hK
  have hpt {x a p : ℝ} (hx : 0 ≤ x) (hd : |a - p| < δ) (hlog : Real.log (max x ε) ≤ a) :
      Real.exp (circleAverage ψ 0 1 - p) * x ≤ Real.exp (circleAverage ψ 0 1 + δ) :=
    (mul_le_mul (b := Real.exp (circleAverage ψ 0 1 + δ - Real.log (max x ε)))
      (Real.exp_le_exp.2 (by linarith [(abs_lt.1 hd).2])) (le_max_left x ε) hx
      (Real.exp_nonneg _)).trans_eq <| by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg, Real.exp_log (lt_max_of_lt_right hε),
          inv_mul_cancel_right₀ (lt_max_of_lt_right hε).ne']
  refine (norm_le_of_toSum_eq ⟨hθ.1.le, hθ.2.le⟩ hsmul (by simp [hcθ, hu])).trans <|
    norm_prod_le_iff.2 ⟨(ZeroAtInftyContinuousMap.norm_le (Real.exp_nonneg _)).2 fun t ↦ ?_,
      (ZeroAtInftyContinuousMap.norm_le (Real.exp_nonneg _)).2 fun t ↦ ?_⟩
  · rw [hg'₀, norm_smul, hc_norm _ (by simp [mem_verticalClosedStrip_iff])]
    exact hpt (norm_nonneg _) (hr_dist _ (by simpa using stripToUnitDisc_mul_I_mem_sphere hθ t))
      (hψ₀ t)
  · rw [hg'₁, norm_smul, hc_norm _ (by simp [mem_verticalClosedStrip_iff])]
    exact hpt (norm_nonneg _)
      (hr_dist _ (by simpa using stripToUnitDisc_one_add_mul_I_mem_sphere hθ t)) (hψ₁ t)

private theorem continuous_and_tendsto_log_max {X : Type*} [NormedAddCommGroup X]
    (f : C₀(ℝ, X)) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun t ↦ Real.log (max ‖f t‖ ε)) ∧
      Tendsto (fun t ↦ Real.log (max ‖f t‖ ε)) (cocompact ℝ) (𝓝 (Real.log ε)) :=
  ⟨((continuous_norm.comp f.continuous).max continuous_const).log
    fun _ ↦ (lt_max_of_lt_right hε).ne',
    (Real.continuousAt_log hε.ne').tendsto.comp
      (by simpa [max_eq_right hε.le] using
        (tendsto_norm_zero.comp (zero_at_infty f)).max (tendsto_const_nhds (x := ε)))⟩

/-- **Calderón's log-convexity inequality (Bergh–Löfström, Lemma 4.3.2).**
For `0 < θ < 1`, `ε > 0`, and any admissible strip function `F` with boundary traces `g` and
`toSum u = F θ`, the norm in `[X₀, X₁]_θ` is bounded by the exponential of the sum of the two
boundary integrals against `stripPoissonKernel₀ θ` and `stripPoissonKernel₁ θ`. -/
theorem norm_le_exp_integral_stripPoissonKernel {θ ε : ℝ} (hθ : θ ∈ Ioo 0 1) (hε : 0 < ε)
    {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)}
    (hF : C.IsStripFunction F g) (hu : toSum u = F θ) :
    ‖u‖ ≤ Real.exp ((∫ t, stripPoissonKernel₀ θ t * Real.log (max ‖g.1 t‖ ε)) +
      ∫ t, stripPoissonKernel₁ θ t * Real.log (max ‖g.2 t‖ ε)) := by
  have hl₀ := continuous_and_tendsto_log_max g.1 hε
  have hl₁ := continuous_and_tendsto_log_max g.2 hε
  obtain ⟨ψ, hψ, hψ₀, hψ₁⟩ := exists_continuousOn_sphere_comp_stripToUnitDisc hθ
    hl₀.1 hl₁.1 (hl₀.2.mono_left atBot_le_cocompact) (hl₁.2.mono_left atBot_le_cocompact)
    (hl₀.2.mono_left atTop_le_cocompact) (hl₁.2.mono_left atTop_le_cocompact)
  have hψi : CircleIntegrable ψ 0 1 :=
    (by simpa using hψ : ContinuousOn ψ (sphere 0 |1|)).circleIntegrable'
  have hca : circleAverage ψ 0 1 =
      (∫ t, stripPoissonKernel₀ θ t * Real.log (max ‖g.1 t‖ ε)) +
        ∫ t, stripPoissonKernel₁ θ t * Real.log (max ‖g.2 t‖ ε) := by
    rw [circleAverage_eq_stripPoissonKernel hθ hψi]
    simp_rw [smul_eq_mul, hψ₀, hψ₁]
  rw [← hca]
  have hcont : Continuous (fun δ : ℝ ↦ Real.exp (circleAverage ψ 0 1 + δ)) := by fun_prop
  exact ge_of_tendsto
    (by simpa using (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0)))
    (eventually_nhdsWithin_of_forall fun δ hδ ↦
      norm_le_exp_circleAverage_add hθ hε hδ hF hu hψ (fun t ↦ (hψ₀ t).ge) (fun t ↦ (hψ₁ t).ge))

/-- Calderón's log-convexity inequality applied to `mk θ g`. -/
theorem norm_mk_le_exp_integral_stripPoissonKernel {θ ε : ℝ} (hθ : θ ∈ Ioo 0 1) (hε : 0 < ε)
    (g : C.stripTraces) :
    ‖mk θ g‖ ≤ Real.exp ((∫ t, stripPoissonKernel₀ θ t * Real.log (max ‖g.1.1 t‖ ε)) +
      ∫ t, stripPoissonKernel₁ θ t * Real.log (max ‖g.1.2 t‖ ε)) :=
  norm_le_exp_integral_stripPoissonKernel hθ hε (C.isStripFunction_stripFunction g)
    (by simp [stripEval_apply])

private theorem norm_le_of_stripPoissonMeasure {θ b₀ b₁ : ℝ} (hθ : θ ∈ Ioo 0 1)
    {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)}
    (hF : C.IsStripFunction F g) (hu : toSum u = F θ) {φ₀ φ₁ : ℝ → ℝ}
    (ht₀ : Tendsto φ₀ (𝓝[>] 0) (𝓝 b₀)) (ht₁ : Tendsto φ₁ (𝓝[>] 0) (𝓝 b₁))
    (h₀ : [IsProbabilityMeasure (stripPoissonMeasure₀ θ)] → ∀ ε > 0,
      Real.exp ((1 - θ) * ∫ t, Real.log (max ‖g.1 t‖ ε) ∂stripPoissonMeasure₀ θ) ≤ φ₀ ε)
    (h₁ : [IsProbabilityMeasure (stripPoissonMeasure₁ θ)] → ∀ ε > 0,
      Real.exp (θ * ∫ t, Real.log (max ‖g.2 t‖ ε) ∂stripPoissonMeasure₁ θ) ≤ φ₁ ε) :
    ‖u‖ ≤ b₀ * b₁ :=
  have := isProbabilityMeasure_stripPoissonMeasure₀ hθ
  have := isProbabilityMeasure_stripPoissonMeasure₁ hθ
  ge_of_tendsto (ht₀.mul ht₁) <| eventually_nhdsWithin_of_forall fun ε hε ↦ by
    refine ((norm_le_exp_integral_stripPoissonKernel hθ hε hF hu).trans_eq ?_).trans
      (mul_le_mul (h₀ ε hε) (h₁ ε hε) (Real.exp_nonneg _) ((Real.exp_nonneg _).trans (h₀ ε hε)))
    rw [Real.exp_add, integral_stripPoissonMeasure₀ hθ, integral_stripPoissonMeasure₁ hθ]
    simp_rw [smul_eq_mul]
    rw [mul_inv_cancel_left₀ (sub_pos.2 hθ.2).ne', mul_inv_cancel_left₀ hθ.1.ne']

private theorem tendsto_add_rpow_nhdsGT (a : ℝ) {p α : ℝ} (hp : 0 < p) (hα : 0 ≤ α) :
    Tendsto (fun ε : ℝ ↦ (a + ε ^ p) ^ (α / p)) (𝓝[>] 0) (𝓝 (a ^ (α / p))) := by
  have hc : Continuous fun ε : ℝ ↦ (a + ε ^ p) ^ (α / p) :=
    (continuous_const.add (Real.continuous_rpow_const hp.le)).rpow_const
      fun _ ↦ Or.inr (div_nonneg hα hp.le)
  simpa [Real.zero_rpow hp.ne'] using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))

private theorem tendsto_max_rpow_nhdsGT {a α : ℝ} (ha : 0 ≤ a) (hα : 0 ≤ α) :
    Tendsto (fun ε : ℝ ↦ (max a ε) ^ α) (𝓝[>] 0) (𝓝 (a ^ α)) := by
  have hc : Continuous fun ε : ℝ ↦ (max a ε) ^ α :=
    (continuous_const.max continuous_id).rpow_const fun _ ↦ Or.inr hα
  simpa [max_eq_left ha] using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))

/-- **`(L^{p₀}, L^{p₁})` strip Poisson bound for `[X₀, X₁]_θ`.** -/
theorem norm_le_rpow_integral_stripPoissonMeasure {θ p₀ p₁ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace}
    {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g) (hu : toSum u = F θ) :
    ‖u‖ ≤ (∫ t, ‖g.1 t‖ ^ p₀ ∂stripPoissonMeasure₀ θ) ^ ((1 - θ) / p₀) *
      (∫ t, ‖g.2 t‖ ^ p₁ ∂stripPoissonMeasure₁ θ) ^ (θ / p₁) :=
  norm_le_of_stripPoissonMeasure hθ hF hu
    (tendsto_add_rpow_nhdsGT _ hp₀ (sub_nonneg.2 hθ.2.le)) (tendsto_add_rpow_nhdsGT _ hp₁ hθ.1.le)
    (fun _ ↦ exp_mul_integral_log_max_le g.1 (sub_nonneg.2 hθ.2.le) hp₀)
    (fun _ ↦ exp_mul_integral_log_max_le g.2 hθ.1.le hp₁)

/-- `(L^{p₀}, L^{p₁})` strip Poisson bound applied to `mk θ g`. -/
theorem norm_mk_le_rpow_integral_stripPoissonMeasure {θ p₀ p₁ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (g : C.stripTraces) :
    ‖mk θ g‖ ≤ (∫ t, ‖g.1.1 t‖ ^ p₀ ∂stripPoissonMeasure₀ θ) ^ ((1 - θ) / p₀) *
      (∫ t, ‖g.1.2 t‖ ^ p₁ ∂stripPoissonMeasure₁ θ) ^ (θ / p₁) :=
  norm_le_rpow_integral_stripPoissonMeasure hθ hp₀ hp₁ (C.isStripFunction_stripFunction g)
    (by simp [stripEval_apply])

/-- **Mixed `(L^∞, L^{p₁})` strip Poisson bound for `[X₀, X₁]_θ`.** -/
theorem norm_le_norm_fst_rpow_mul_rpow_integral_stripPoissonMeasure {θ p₁ : ℝ}
    (hθ : θ ∈ Ioo 0 1) (hp₁ : 0 < p₁) {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace}
    {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g) (hu : toSum u = F θ) :
    ‖u‖ ≤ ‖g.1‖ ^ (1 - θ) * (∫ t, ‖g.2 t‖ ^ p₁ ∂stripPoissonMeasure₁ θ) ^ (θ / p₁) :=
  norm_le_of_stripPoissonMeasure hθ hF hu
    (tendsto_max_rpow_nhdsGT (norm_nonneg g.1) (sub_nonneg.2 hθ.2.le))
    (tendsto_add_rpow_nhdsGT _ hp₁ hθ.1.le)
    (fun _ ↦ exp_mul_integral_log_max_le_norm g.1 (sub_nonneg.2 hθ.2.le))
    (fun _ ↦ exp_mul_integral_log_max_le g.2 hθ.1.le hp₁)

/-- **Mixed `(L^{p₀}, L^∞)` strip Poisson bound for `[X₀, X₁]_θ`.** -/
theorem norm_le_rpow_integral_stripPoissonMeasure_mul_norm_snd_rpow {θ p₀ : ℝ}
    (hθ : θ ∈ Ioo 0 1) (hp₀ : 0 < p₀) {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace}
    {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g) (hu : toSum u = F θ) :
    ‖u‖ ≤ (∫ t, ‖g.1 t‖ ^ p₀ ∂stripPoissonMeasure₀ θ) ^ ((1 - θ) / p₀) * ‖g.2‖ ^ θ :=
  norm_le_of_stripPoissonMeasure hθ hF hu
    (tendsto_add_rpow_nhdsGT _ hp₀ (sub_nonneg.2 hθ.2.le))
    (tendsto_max_rpow_nhdsGT (norm_nonneg g.2) hθ.1.le)
    (fun _ ↦ exp_mul_integral_log_max_le g.1 (sub_nonneg.2 hθ.2.le) hp₀)
    (fun _ ↦ exp_mul_integral_log_max_le_norm g.2 hθ.1.le)

/-- **`L¹` strip Poisson bound (Calderón–Hirschman).** -/
theorem norm_le_rpow_integral_stripPoissonKernel {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)}
    (hF : C.IsStripFunction F g) (hu : toSum u = F θ) :
    ‖u‖ ≤ ((1 - θ)⁻¹ * ∫ t, stripPoissonKernel₀ θ t * ‖g.1 t‖) ^ (1 - θ) *
      (θ⁻¹ * ∫ t, stripPoissonKernel₁ θ t * ‖g.2 t‖) ^ θ := by
  simpa [div_one, Real.rpow_one, integral_stripPoissonMeasure₀ hθ,
    integral_stripPoissonMeasure₁ hθ, smul_eq_mul] using
    norm_le_rpow_integral_stripPoissonMeasure hθ one_pos one_pos hF hu

end CompatibleCouple.ComplexMethodSpace

end TauCeti

end

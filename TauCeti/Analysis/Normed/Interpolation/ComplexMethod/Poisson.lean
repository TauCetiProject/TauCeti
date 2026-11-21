/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Poisson.Strip
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.MeanInequalities

/-!
# Calderón's log-convexity and Poisson integral bounds for `[X₀, X₁]_θ`

Pulling the Herglotz–Riesz integral on `ball 0 1` back along `TauCeti.stripToUnitDisc` refines the
three-lines bound on `[X₀, X₁]_θ` to Calderón's log-convexity inequality (Bergh–Löfström,
Lemma 4.3.2): for `0 < θ < 1` and `ε > 0`,
`‖u‖ ≤ exp (∫ μ₀(θ, t) log (max ‖g₀ t‖ ε) dt + ∫ μ₁(θ, t) log (max ‖g₁ t‖ ε) dt)`.
Applying the regularized geometric–`Lᵖ` mean inequality
(`TauCeti.exp_mul_integral_log_max_le_rpow_integral_rpow_add`) to `stripPoissonMeasure₀ θ` and
`stripPoissonMeasure₁ θ` and letting `ε → 0⁺` yields `(L^{p₀}, L^{p₁})` and mixed `(L^∞, L^p)`
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
open scoped Topology ZeroAtInfty

namespace TauCeti

/-! ### Herglotz–Riesz multipliers and Calderón's log-convexity inequality -/

namespace CompatibleCouple.IsStripFunction

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  {C : CompatibleCouple ℂ X₀ X₁ V} {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)}

private def smulBoundary {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    {c : ℂ → ℂ} (hcc : ContinuousOn c (verticalClosedStrip 0 1))
    {K : ℝ} (hK : ∀ z ∈ verticalClosedStrip 0 1, ‖c z‖ ≤ K)
    (γ : ℝ → ℂ) (hγ_cont : Continuous γ) (hγ_mem : ∀ t, γ t ∈ verticalClosedStrip 0 1) :
    C₀(ℝ, Y) → C₀(ℝ, Y) :=
  ZeroAtInftyContinuousMap.compLeftFamily
    (fun t : ℝ => c (γ t) • ContinuousLinearMap.id ℂ Y)
    (fun x => by
      have hcont : Continuous fun t : ℝ => c (γ t) := hcc.comp_continuous hγ_cont hγ_mem
      simpa only [smul_apply, ContinuousLinearMap.id_apply] using
        hcont.fun_smul (continuous_const (y := x)))
    ⟨K, fun t x => by
      rw [smul_apply, ContinuousLinearMap.id_apply, norm_smul]
      exact mul_le_mul_of_nonneg_right (hK (γ t) (hγ_mem t)) (norm_nonneg x)⟩

@[simp]
private theorem smulBoundary_apply {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    {c : ℂ → ℂ} (hcc : ContinuousOn c (verticalClosedStrip 0 1))
    {K : ℝ} (hK : ∀ z ∈ verticalClosedStrip 0 1, ‖c z‖ ≤ K)
    {γ : ℝ → ℂ} {hγ_cont : Continuous γ} {hγ_mem : ∀ t, γ t ∈ verticalClosedStrip 0 1}
    (f : C₀(ℝ, Y)) (t : ℝ) :
    smulBoundary hcc hK γ hγ_cont hγ_mem f t = c (γ t) • f t := by
  simp [smulBoundary]

/-- Multiplying an admissible function by a scalar function `c`, holomorphic on the open strip,
continuous up to its boundary, and bounded on the closed strip, gives an admissible function with
boundary traces `(t ↦ c (t * I) • g₀ t, t ↦ c (1 + t * I) • g₁ t)`. -/
theorem exists_smul_of_diffContOnCl (hF : C.IsStripFunction F g) {c : ℂ → ℂ}
    (hc : DiffContOnCl ℂ c (verticalStrip 0 1))
    {K : ℝ} (hK : ∀ z ∈ verticalClosedStrip 0 1, ‖c z‖ ≤ K) :
    ∃ g' : C₀(ℝ, X₀) × C₀(ℝ, X₁), C.IsStripFunction (fun z => c z • F z) g' ∧
      (∀ t, g'.1 t = c (t * I) • g.1 t) ∧ ∀ t, g'.2 t = c (1 + t * I) • g.2 t := by
  have hcc : ContinuousOn c (verticalClosedStrip 0 1) :=
    hc.continuousOn_verticalClosedStrip zero_lt_one
  let g'₀ := smulBoundary hcc hK (fun t : ℝ => t * I) (by fun_prop)
    (fun _ => by simp [mem_verticalClosedStrip_iff]) g.1
  let g'₁ := smulBoundary hcc hK (fun t : ℝ => 1 + t * I) (by fun_prop)
    (fun _ => by simp [mem_verticalClosedStrip_iff]) g.2
  exact ⟨(g'₀, g'₁),
    hF.smul hc hK (fun _ => by simp only [g'₀, smulBoundary_apply])
      (fun _ => by simp only [g'₁, smulBoundary_apply]),
    fun _ => by simp only [g'₀, smulBoundary_apply],
    fun _ => by simp only [g'₁, smulBoundary_apply]⟩

end CompatibleCouple.IsStripFunction

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
  have hψic : CircleIntegrable (fun ζ ↦ (ψ ζ : ℂ)) 0 1 :=
    (Complex.continuous_ofReal.comp_continuousOn hψ').circleIntegrable'
  let H : ℂ → ℂ := fun w ↦ circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • (ψ ζ : ℂ)) 0 1
  have hH_re {w : ℂ} (hw : w ∈ ball 0 1) : (H w).re = planarPoissonIntegral ψ 0 1 w := by
    rw [planarPoissonIntegral_def, poissonKernel_eq_re_herglotzRieszKernel]
    exact re_circleAverage_herglotzRieszKernel_smul hψi (by simpa using (mem_ball_zero_iff.1 hw).ne)
  have hH0 : (H 0).re = circleAverage ψ 0 1 := by
    rw [hH_re (mem_ball_self zero_lt_one), planarPoissonIntegral_def]
    exact circleAverage_congr_sphere fun ζ hζ ↦ by
      simp [poissonKernel_def, (by simpa using hζ : ‖ζ‖ = 1)]
  obtain ⟨r, hr_dist, hr_mem⟩ := ((Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_planarPoissonIntegral_smul one_ne_zero hψ') δ hδ).and
    (Ioo_mem_nhdsLT zero_lt_one)).exists
  let c : ℂ → ℂ := fun z ↦ exp (H 0 - H ((r : ℂ) * stripToUnitDisc θ z))
  have hc_ball {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
      (r : ℂ) * stripToUnitDisc θ z ∈ closedBall 0 r := by
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_of_nonneg hr_mem.1.le]
    exact mul_le_of_le_one_right hr_mem.1.le (norm_stripToUnitDisc_le_one hθ hz)
  have hcb_sub : closedBall (0 : ℂ) r ⊆ (sphere 0 |1|)ᶜ := fun w hw ↦ by
    simpa only [mem_compl_iff, mem_sphere_zero_iff_norm, abs_one] using
      ((mem_closedBall_zero_iff.1 hw).trans_lt hr_mem.2).ne
  have hc_diff : DifferentiableOn ℂ c (verticalClosedStrip 0 1) := fun z hz ↦
    ((differentiableAt_const _).sub ((hasDerivAt_circleAverage_herglotzRieszKernel_smul hψic
      (hcb_sub (hc_ball hz))).differentiableAt.comp z
      ((differentiableAt_stripToUnitDisc hθ hz).const_mul (r : ℂ)))).cexp.differentiableWithinAt
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    (continuous_exp.comp_continuousOn (continuousOn_const.sub
      ((differentiableOn_circleAverage_herglotzRieszKernel_smul hψic).continuousOn.mono hcb_sub)))
  exact ⟨r, c, K, hr_mem,
    ⟨hc_diff.mono (verticalStrip_subset_verticalClosedStrip 0 1),
      hc_diff.continuousOn.mono (closure_verticalStrip_subset 0 1)⟩,
    fun _ hz ↦ hK _ (hc_ball hz), by simp [c],
    fun ζ hζ ↦ by simpa [Real.dist_eq, Complex.real_smul] using hr_dist ζ hζ, fun z hz ↦ by
      rw [Complex.norm_exp, sub_re, hH0, hH_re (closedBall_subset_ball hr_mem.2 (hc_ball hz))]⟩

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
    exact hpt (norm_nonneg _)
      (hr_dist _ (by simpa using stripToUnitDisc_mul_I_mem_sphere hθ t)) (hψ₀ t)
  · rw [hg'₁, norm_smul, hc_norm _ (by simp [mem_verticalClosedStrip_iff])]
    exact hpt (norm_nonneg _)
      (hr_dist _ (by simpa using stripToUnitDisc_one_add_mul_I_mem_sphere hθ t)) (hψ₁ t)

/-- **Calderón's log-convexity inequality (Bergh–Löfström, Lemma 4.3.2).**
For `0 < θ < 1`, `ε > 0`, and any admissible strip function `F` with boundary traces `g` and
`toSum u = F θ`, the norm in `[X₀, X₁]_θ` is bounded by the exponential of the sum of the two
boundary integrals against `stripPoissonKernel₀ θ` and `stripPoissonKernel₁ θ`. -/
theorem norm_le_exp_integral_stripPoissonKernel {θ ε : ℝ} (hθ : θ ∈ Ioo 0 1) (hε : 0 < ε)
    {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)}
    (hF : C.IsStripFunction F g) (hu : toSum u = F θ) :
    ‖u‖ ≤ Real.exp ((∫ t, stripPoissonKernel₀ θ t * Real.log (max ‖g.1 t‖ ε)) +
      ∫ t, stripPoissonKernel₁ θ t * Real.log (max ‖g.2 t‖ ε)) := by
  have hlog {f : ℝ → ℝ} (hf : Continuous f) (h0 : Tendsto f (cocompact ℝ) (𝓝 0)) :
      Continuous (fun t ↦ Real.log (max (f t) ε)) ∧
        Tendsto (fun t ↦ Real.log (max (f t) ε)) (cocompact ℝ) (𝓝 (Real.log ε)) :=
    ⟨(hf.max continuous_const).log fun _ ↦ (lt_max_of_lt_right hε).ne',
      (Real.continuousAt_log hε.ne').tendsto.comp
        (by simpa [max_eq_right hε.le] using h0.max (tendsto_const_nhds (x := ε)))⟩
  have hl₀ := hlog g.1.continuous.norm (tendsto_norm_zero.comp (zero_at_infty g.1))
  have hl₁ := hlog g.2.continuous.norm (tendsto_norm_zero.comp (zero_at_infty g.2))
  obtain ⟨ψ, hψ, hψ₀, hψ₁⟩ := exists_continuousOn_sphere_comp_stripToUnitDisc hθ
    hl₀.1 hl₁.1 (hl₀.2.mono_left atBot_le_cocompact) (hl₁.2.mono_left atBot_le_cocompact)
    (hl₀.2.mono_left atTop_le_cocompact) (hl₁.2.mono_left atTop_le_cocompact)
  have hca : circleAverage ψ 0 1 =
      (∫ t, stripPoissonKernel₀ θ t * Real.log (max ‖g.1 t‖ ε)) +
        ∫ t, stripPoissonKernel₁ θ t * Real.log (max ‖g.2 t‖ ε) := by
    rw [circleAverage_eq_stripPoissonKernel hθ
      (by simpa using hψ : ContinuousOn ψ (sphere 0 |1|)).circleIntegrable']
    simp_rw [smul_eq_mul, hψ₀, hψ₁]; rfl
  rw [← hca]
  refine ge_of_tendsto (f := fun δ : ℝ ↦ Real.exp (circleAverage ψ 0 1 + δ)) ?_
    (eventually_nhdsWithin_of_forall (a := (0 : ℝ)) (s := Ioi 0) fun δ hδ ↦
      norm_le_exp_circleAverage_add hθ hε hδ hF hu hψ (fun t ↦ (hψ₀ t).ge) (fun t ↦ (hψ₁ t).ge))
  simpa using ((continuous_const.add continuous_id).rexp.tendsto 0).mono_left nhdsWithin_le_nhds

/-- Calderón's log-convexity inequality applied to `mk θ g`. -/
theorem norm_mk_le_exp_integral_stripPoissonKernel {θ ε : ℝ} (hθ : θ ∈ Ioo 0 1) (hε : 0 < ε)
    (g : C.stripTraces) :
    ‖mk θ g‖ ≤ Real.exp ((∫ t, stripPoissonKernel₀ θ t * Real.log (max ‖g.val.1 t‖ ε)) +
      ∫ t, stripPoissonKernel₁ θ t * Real.log (max ‖g.val.2 t‖ ε)) :=
  norm_le_exp_integral_stripPoissonKernel hθ hε (C.isStripFunction_stripFunction g)
    (by simp [stripEval_apply])

/-- **`(L^{p₀}, L^{p₁})` strip Poisson bound for `[X₀, X₁]_θ`.** -/
theorem norm_le_rpow_integral_stripPoissonMeasure {θ p₀ p₁ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace}
    {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g) (hu : toSum u = F θ) :
    ‖u‖ ≤ (∫ t, ‖g.1 t‖ ^ p₀ ∂stripPoissonMeasure₀ θ) ^ ((1 - θ) / p₀) *
      (∫ t, ‖g.2 t‖ ^ p₁ ∂stripPoissonMeasure₁ θ) ^ (θ / p₁) := by
  have := isProbabilityMeasure_stripPoissonMeasure₀ hθ
  have := isProbabilityMeasure_stripPoissonMeasure₁ hθ
  have hside {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ} (hf : Continuous f)
      (h0 : ∀ t, 0 ≤ f t) {M : ℝ} (hM : ∀ t, f t ≤ M) {α p : ℝ} (hα : 0 ≤ α) (hp : 0 < p) :
      Tendsto (fun ε : ℝ ↦ ((∫ t, f t ^ p ∂μ) + ε ^ p) ^ (α / p)) (𝓝[>] 0)
        (𝓝 ((∫ t, f t ^ p ∂μ) ^ (α / p))) ∧
      ∀ ε > 0, Real.exp (α * ∫ t, Real.log (max (f t) ε) ∂μ) ≤
        ((∫ t, f t ^ p ∂μ) + ε ^ p) ^ (α / p) :=
    ⟨by simpa [Real.zero_rpow hp.ne'] using (((continuous_const.add
        (Real.continuous_rpow_const hp.le)).rpow_const fun _ ↦ Or.inr (div_nonneg hα hp.le)).tendsto
        0).mono_left (nhdsWithin_le_nhds (s := Ioi 0)),
      fun ε hε ↦ exp_mul_integral_log_max_le_rpow_integral_rpow_add hα hp hε (.of_forall h0)
        (Integrable.of_bound (hf.rpow_const fun _ ↦ Or.inr hp.le).aestronglyMeasurable (M ^ p)
          (.of_forall fun t ↦ by
            rw [Real.norm_of_nonneg (Real.rpow_nonneg (h0 t) p)]
            exact Real.rpow_le_rpow (h0 t) (hM t) hp.le))⟩
  have ⟨ht₀, h₀⟩ := hside (μ := stripPoissonMeasure₀ θ) g.1.continuous.norm
    (fun _ ↦ norm_nonneg _) g.1.norm_coe_le_norm (sub_nonneg.2 hθ.2.le) hp₀
  have ⟨ht₁, h₁⟩ := hside (μ := stripPoissonMeasure₁ θ) g.2.continuous.norm
    (fun _ ↦ norm_nonneg _) g.2.norm_coe_le_norm hθ.1.le hp₁
  refine ge_of_tendsto (ht₀.mul ht₁) <| eventually_nhdsWithin_of_forall fun ε hε ↦
    ((norm_le_exp_integral_stripPoissonKernel hθ hε hF hu).trans_eq ?_).trans
      (mul_le_mul (h₀ ε hε) (h₁ ε hε) (Real.exp_nonneg _) ((Real.exp_nonneg _).trans (h₀ ε hε)))
  simp [Real.exp_add, integral_stripPoissonMeasure₀ hθ, integral_stripPoissonMeasure₁ hθ,
    mul_inv_cancel_left₀ (sub_pos.2 hθ.2).ne', mul_inv_cancel_left₀ hθ.1.ne']

/-- `(L^{p₀}, L^{p₁})` strip Poisson bound applied to `mk θ g`. -/
theorem norm_mk_le_rpow_integral_stripPoissonMeasure {θ p₀ p₁ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (g : C.stripTraces) :
    ‖mk θ g‖ ≤ (∫ t, ‖g.val.1 t‖ ^ p₀ ∂stripPoissonMeasure₀ θ) ^ ((1 - θ) / p₀) *
      (∫ t, ‖g.val.2 t‖ ^ p₁ ∂stripPoissonMeasure₁ θ) ^ (θ / p₁) :=
  norm_le_rpow_integral_stripPoissonMeasure hθ hp₀ hp₁ (C.isStripFunction_stripFunction g)
    (by simp [stripEval_apply])

/-- **Mixed `(L^∞, L^{p₁})` strip Poisson bound for `[X₀, X₁]_θ`.** -/
theorem norm_le_norm_fst_rpow_mul_rpow_integral_stripPoissonMeasure {θ p₁ : ℝ}
    (hθ : θ ∈ Ioo 0 1) (hp₁ : 0 < p₁) {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace}
    {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g) (hu : toSum u = F θ) :
    ‖u‖ ≤ ‖g.1‖ ^ (1 - θ) * (∫ t, ‖g.2 t‖ ^ p₁ ∂stripPoissonMeasure₁ θ) ^ (θ / p₁) := by
  have := isProbabilityMeasure_stripPoissonMeasure₀ hθ
  have h := norm_le_rpow_integral_stripPoissonMeasure hθ one_pos hp₁ hF hu
  simp only [div_one, Real.rpow_one] at h
  exact h.trans <| mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (integral_nonneg fun _ ↦ norm_nonneg _)
      (TauCeti.MeasureTheory.integral_le_const_of_ae_nonneg (.of_forall fun _ ↦ norm_nonneg _)
        (.of_forall g.1.norm_coe_le_norm))
      (sub_nonneg.2 hθ.2.le))
    (Real.rpow_nonneg (integral_nonneg fun _ ↦ by positivity) _)

/-- **Mixed `(L^{p₀}, L^∞)` strip Poisson bound for `[X₀, X₁]_θ`.** -/
theorem norm_le_rpow_integral_stripPoissonMeasure_mul_norm_snd_rpow {θ p₀ : ℝ}
    (hθ : θ ∈ Ioo 0 1) (hp₀ : 0 < p₀) {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace}
    {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g) (hu : toSum u = F θ) :
    ‖u‖ ≤ (∫ t, ‖g.1 t‖ ^ p₀ ∂stripPoissonMeasure₀ θ) ^ ((1 - θ) / p₀) * ‖g.2‖ ^ θ := by
  have := isProbabilityMeasure_stripPoissonMeasure₁ hθ
  have h := norm_le_rpow_integral_stripPoissonMeasure hθ hp₀ one_pos hF hu
  simp only [div_one, Real.rpow_one] at h
  exact h.trans <| mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (integral_nonneg fun _ ↦ norm_nonneg _)
      (TauCeti.MeasureTheory.integral_le_const_of_ae_nonneg (.of_forall fun _ ↦ norm_nonneg _)
        (.of_forall g.2.norm_coe_le_norm))
      hθ.1.le)
    (Real.rpow_nonneg (integral_nonneg fun _ ↦ by positivity) _)

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

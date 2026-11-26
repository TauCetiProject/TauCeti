/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Poisson.Strip
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Exp.Limits
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.MeasureTheory.Integral.ZeroAtInfty.Log

/-!
# Log-convexity of the complex interpolation norm via strip Poisson kernels

On the open vertical strip `0 < re z < 1`, the holomorphic strip Poisson kernels
`TauCeti.holoPoisson₀` and `TauCeti.holoPoisson₁` realize the real Poisson kernels
`TauCeti.stripPoisson₀` and `TauCeti.stripPoisson₁` as real parts, so convolving real boundary
data against `holoPoisson₀` and `holoPoisson₁` yields holomorphic functions whose real parts are
the corresponding `stripPoisson₀` and `stripPoisson₁` integrals. The real kernels `stripPoisson₀`
and `stripPoisson₁` satisfy uniform one-sided approximate-identity lower bounds for nonnegative
bounded uniformly continuous data along contracted boundary centers
(`TauCeti.exists_forall_sub_le_integral_mul_contracted_stripPoisson₀`,
`TauCeti.exists_forall_sub_le_integral_mul_contracted_stripPoisson₁`). Applying these to the
clipped logarithmic envelopes `ZeroAtInftyContinuousMap.logMaxDiv` yields Bergh–Löfström's
Poisson estimates for Calderón's complex method:

* `CompatibleCouple.ComplexMethodSpace.norm_mk_le_exp_integral_log_max_of_pos`: for `0 < θ < 1`
  and `δ > 0`, `‖mk θ g‖ ≤ exp (∫ log (max ‖g₀ s‖ δ) P₀(θ, s) + ∫ log (max ‖g₁ s‖ δ) P₁(θ, s))`.
* `CompatibleCouple.ComplexMethodSpace.norm_mk_le_integral_stripPoisson_rpow_mul_rpow`: for
  `0 < θ < 1`,
  `‖mk θ g‖ ≤ ((1 - θ)⁻¹ ∫ ‖g₀ t‖ P₀(θ, t) dt) ^ (1 - θ) * (θ⁻¹ ∫ ‖g₁ t‖ P₁(θ, t) dt) ^ θ`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §4.3 (Lemma 4.3.2).
-/

public noncomputable section

open Complex Complex.HadamardThreeLines TauCeti.Complex.HadamardThreeLines
open Filter MeasureTheory Metric Real Set Topology
open scoped ZeroAtInfty

namespace TauCeti.CompatibleCouple.ComplexMethodSpace

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  {C : CompatibleCouple ℂ X₀ X₁ V}

private def holoPotential (g : C.stripTraces) (δ : ℝ) (ζ : ℂ) : ℂ :=
  (Real.log δ : ℂ) +
    ((∫ s, (ZeroAtInftyContinuousMap.logMaxDiv g.val.1 δ s : ℂ) * holoPoisson₀ (ζ - s * I)) +
      ∫ s, (ZeroAtInftyContinuousMap.logMaxDiv g.val.2 δ s : ℂ) * holoPoisson₁ (ζ - s * I))

private theorem differentiableOn_holoPotential (g : C.stripTraces) {δ : ℝ} (hδ : 0 < δ) :
    DifferentiableOn ℂ (holoPotential g δ) (verticalStrip 0 1) :=
  (differentiableOn_const _).add
    ((differentiableOn_integral_holoPoisson₀ (Complex.ofRealCLM.integrable_comp
        (ZeroAtInftyContinuousMap.integrable_logMaxDiv g.val.1 hδ))).add
      (differentiableOn_integral_holoPoisson₁ (Complex.ofRealCLM.integrable_comp
        (ZeroAtInftyContinuousMap.integrable_logMaxDiv g.val.2 hδ))))

private theorem re_holoPotential (g : C.stripTraces) {δ : ℝ} (hδ : 0 < δ) {ζ : ℂ}
    (hζ : ζ ∈ verticalStrip 0 1) :
    (holoPotential g δ ζ).re = Real.log δ +
      ((∫ s, ZeroAtInftyContinuousMap.logMaxDiv g.val.1 δ s * stripPoisson₀ ζ.re (ζ.im - s)) +
        ∫ s, ZeroAtInftyContinuousMap.logMaxDiv g.val.2 δ s * stripPoisson₁ ζ.re (ζ.im - s)) := by
  simp only [holoPotential, add_re, ofReal_re,
    re_integral_holoPoisson₀ (ZeroAtInftyContinuousMap.integrable_logMaxDiv g.val.1 hδ) hζ,
    re_integral_holoPoisson₁ (ZeroAtInftyContinuousMap.integrable_logMaxDiv g.val.2 hδ) hζ]

private theorem integral_logMaxDiv_mul_stripPoisson₀_nonneg {E : Type*} [NormedAddCommGroup E]
    (f : C₀(ℝ, E)) {δ r y : ℝ} (hδ : 0 < δ) (hr : r ∈ Ioo 0 1) :
    0 ≤ ∫ s, ZeroAtInftyContinuousMap.logMaxDiv f δ s * stripPoisson₀ r (y - s) :=
  integral_nonneg fun _ =>
    mul_nonneg (ZeroAtInftyContinuousMap.logMaxDiv_nonneg f hδ _) (stripPoisson₀_pos hr _).le

private theorem integral_logMaxDiv_mul_stripPoisson₁_nonneg {E : Type*} [NormedAddCommGroup E]
    (f : C₀(ℝ, E)) {δ r y : ℝ} (hδ : 0 < δ) (hr : r ∈ Ioo 0 1) :
    0 ≤ ∫ s, ZeroAtInftyContinuousMap.logMaxDiv f δ s * stripPoisson₁ r (y - s) :=
  integral_nonneg fun _ =>
    mul_nonneg (ZeroAtInftyContinuousMap.logMaxDiv_nonneg f hδ _) (stripPoisson₁_pos hr _).le

private theorem norm_exp_neg_holoPotential_le (g : C.stripTraces) {δ : ℝ} (hδ : 0 < δ) {ζ : ℂ}
    (hζ : ζ ∈ verticalStrip 0 1) : ‖Complex.exp (-holoPotential g δ ζ)‖ ≤ δ⁻¹ := by
  rw [Complex.norm_exp, neg_re, ← Real.exp_log (inv_pos.2 hδ), Real.log_inv,
    re_holoPotential g hδ hζ]
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  linarith [integral_logMaxDiv_mul_stripPoisson₀_nonneg g.val.1 hδ (y := ζ.im) hζ,
    integral_logMaxDiv_mul_stripPoisson₁_nonneg g.val.2 hδ (y := ζ.im) hζ]

private noncomputable def contractedExpNegHoloPotential (g : C.stripTraces) (δ ε : ℝ)
    (z : ℂ) : ℂ := Complex.exp (-holoPotential g δ ((1 - 2 * (ε : ℂ)) * z + ε))

private theorem contracted_mul_I (ε t : ℝ) :
    (1 - 2 * (ε : ℂ)) * (t * I) + ε = (ε : ℂ) + ((1 - 2 * ε) * t : ℝ) * I := by push_cast; ring

private theorem contracted_one_add_mul_I (ε t : ℝ) :
    (1 - 2 * (ε : ℂ)) * (1 + t * I) + ε = ((1 - ε : ℝ) : ℂ) + ((1 - 2 * ε) * t : ℝ) * I := by
  push_cast; ring

private theorem diffContOnCl_contractedExpNegHoloPotential (g : C.stripTraces) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : ε ∈ Ioo (0 : ℝ) 2⁻¹) :
    DiffContOnCl ℂ (contractedExpNegHoloPotential g δ ε) (verticalStrip 0 1) := by
  have hdiff : DifferentiableOn ℂ (contractedExpNegHoloPotential g δ ε)
      (verticalStrip (-(ε / 2)) (1 + ε / 2)) :=
    (((differentiableOn_holoPotential g hδ).comp
      (by fun_prop : Differentiable ℂ fun z : ℂ => (1 - 2 * (ε : ℂ)) * z + ε).differentiableOn
      (mapsTo_contracted_verticalStrip hε)).neg).cexp
  have hsub : verticalClosedStrip 0 1 ⊆ verticalStrip (-(ε / 2)) (1 + ε / 2) := fun _ hz =>
    ⟨by linarith [hε.1, hz.1], by linarith [hε.1, hz.2]⟩
  exact ⟨hdiff.mono ((verticalStrip_subset_verticalClosedStrip 0 1).trans hsub),
    hdiff.continuousOn.mono ((closure_verticalStrip_subset 0 1).trans hsub)⟩

private theorem norm_contractedExpNegHoloPotential_le (g : C.stripTraces) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : ε ∈ Ioo (0 : ℝ) 2⁻¹) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    ‖contractedExpNegHoloPotential g δ ε z‖ ≤ δ⁻¹ :=
  norm_exp_neg_holoPotential_le g hδ
    (mapsTo_contracted_verticalStrip hε ⟨by linarith [hε.1, hz.1], by linarith [hε.1, hz.2]⟩)

private theorem norm_contracted_smul_le_of_tail_and_core {δ T κ ε : ℝ} (hδ : 0 < δ)
    (hκ : 0 < κ) (hε : ε ∈ Ioo (0 : ℝ) 2⁻¹) (g : C.stripTraces) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (z : ℂ) (hz : z ∈ verticalClosedStrip 0 1)
    (t : ℝ) (x : E) (htail_le : T ≤ |t| → ‖x‖ ≤ δ)
    (hcore : ¬ T ≤ |t| → Real.log (max ‖x‖ δ) - κ ≤
      (holoPotential g δ ((1 - 2 * (ε : ℂ)) * z + ε)).re) :
    ‖contractedExpNegHoloPotential g δ ε z • x‖ ≤ Real.exp κ := by
  rw [norm_smul]
  by_cases ht : T ≤ |t|
  · exact (mul_le_mul (norm_contractedExpNegHoloPotential_le g hδ hε hz) (htail_le ht)
      (norm_nonneg x) (inv_pos.2 hδ).le).trans
      ((inv_mul_cancel₀ hδ.ne').trans_le (Real.one_le_exp hκ.le))
  · rw [contractedExpNegHoloPotential, Complex.norm_exp, neg_re]
    exact exp_neg_mul_le_exp_of_log_sub_le (norm_nonneg x) (le_max_left _ _)
      (hδ.trans_le (le_max_right _ _)) (hcore ht)

private theorem norm_contracted_smul_fst_le {δ T κ ε : ℝ} (hδ : 0 < δ) (hκ : 0 < κ)
    (hε : ε ∈ Ioo (0 : ℝ) 2⁻¹) (g : C.stripTraces) (hg₀ : ∀ s, T ≤ |s| → ‖g.val.1 s‖ ≤ δ)
    (happrox₀ : ∀ t ∈ Icc (-T) T, ZeroAtInftyContinuousMap.logMaxDiv g.val.1 δ t - κ ≤
      ∫ s, ZeroAtInftyContinuousMap.logMaxDiv g.val.1 δ s *
        stripPoisson₀ ε ((1 - 2 * ε) * t - s))
    (t : ℝ) : ‖contractedExpNegHoloPotential g δ ε (t * I) • g.val.1 t‖ ≤ Real.exp κ := by
  refine norm_contracted_smul_le_of_tail_and_core hδ hκ hε g (t * I)
    (by simp [verticalClosedStrip]) t _ (hg₀ t) fun ht => ?_
  rw [re_holoPotential g hδ (mapsTo_contracted_verticalStrip hε
    (by simp only [mem_verticalStrip_iff, mem_Ioo, mul_I_re, ofReal_im, neg_zero]
        constructor <;> linarith [hε.1]))]
  dsimp only; rw [contracted_mul_I]
  simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero, add_im, mul_I_im, zero_add]
  linarith [happrox₀ t (abs_le.1 (not_le.1 ht).le), ZeroAtInftyContinuousMap.log_add_logMaxDiv
    g.val.1 hδ t, integral_logMaxDiv_mul_stripPoisson₁_nonneg g.val.2 hδ
      (r := ε) (y := (1 - 2 * ε) * t) ⟨hε.1, by linarith [hε.2]⟩]

private theorem norm_contracted_smul_snd_le {δ T κ ε : ℝ} (hδ : 0 < δ) (hκ : 0 < κ)
    (hε : ε ∈ Ioo (0 : ℝ) 2⁻¹) (g : C.stripTraces) (hg₁ : ∀ s, T ≤ |s| → ‖g.val.2 s‖ ≤ δ)
    (happrox₁ : ∀ t ∈ Icc (-T) T, ZeroAtInftyContinuousMap.logMaxDiv g.val.2 δ t - κ ≤
      ∫ s, ZeroAtInftyContinuousMap.logMaxDiv g.val.2 δ s *
        stripPoisson₁ (1 - ε) ((1 - 2 * ε) * t - s))
    (t : ℝ) : ‖contractedExpNegHoloPotential g δ ε (1 + t * I) • g.val.2 t‖ ≤ Real.exp κ := by
  refine norm_contracted_smul_le_of_tail_and_core hδ hκ hε g (1 + t * I)
    (by simp [verticalClosedStrip]) t _ (hg₁ t) fun ht => ?_
  rw [re_holoPotential g hδ (mapsTo_contracted_verticalStrip hε
    (by simp only [mem_verticalStrip_iff, mem_Ioo, add_re, one_re, mul_I_re, ofReal_im, neg_zero,
          add_zero]; constructor <;> linarith [hε.1]))]
  dsimp only; rw [contracted_one_add_mul_I]
  simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero, add_im, mul_I_im, zero_add]
  linarith [happrox₁ t (abs_le.1 (not_le.1 ht).le), ZeroAtInftyContinuousMap.log_add_logMaxDiv
    g.val.2 hδ t, integral_logMaxDiv_mul_stripPoisson₀_nonneg g.val.1 hδ
      (r := 1 - ε) (y := (1 - 2 * ε) * t) ⟨by linarith [hε.2], by linarith [hε.1]⟩]

private theorem norm_mk_le_exp_mul_exp_re_contracted_holoPotential {θ δ T κ ε : ℝ}
    (hδ : 0 < δ) (hκ : 0 < κ) (hε : ε ∈ Ioo (0 : ℝ) 2⁻¹) (g : C.stripTraces)
    (hg₀ : ∀ s, T ≤ |s| → ‖g.val.1 s‖ ≤ δ) (hg₁ : ∀ s, T ≤ |s| → ‖g.val.2 s‖ ≤ δ)
    (happrox₀ : ∀ t ∈ Icc (-T) T, ZeroAtInftyContinuousMap.logMaxDiv g.val.1 δ t - κ ≤
      ∫ s, ZeroAtInftyContinuousMap.logMaxDiv g.val.1 δ s *
        stripPoisson₀ ε ((1 - 2 * ε) * t - s))
    (happrox₁ : ∀ t ∈ Icc (-T) T, ZeroAtInftyContinuousMap.logMaxDiv g.val.2 δ t - κ ≤
      ∫ s, ZeroAtInftyContinuousMap.logMaxDiv g.val.2 δ s *
        stripPoisson₁ (1 - ε) ((1 - 2 * ε) * t - s)) :
    ‖mk θ g‖ ≤ Real.exp κ *
      Real.exp ((holoPotential g δ (((1 - 2 * ε) * θ + ε : ℝ) : ℂ)).re) := by
  by_cases hθ : θ ∈ Icc (0 : ℝ) 1
  · have hb := norm_smul_mk_le_of_diffContOnCl θ g
      (diffContOnCl_contractedExpNegHoloPotential g hδ hε)
      (fun _ hz => norm_contractedExpNegHoloPotential_le g hδ hε hz)
      (norm_contracted_smul_fst_le hδ hκ hε g hg₀ happrox₀)
      (norm_contracted_smul_snd_le hδ hκ hε g hg₁ happrox₁)
    have hnorm : ‖contractedExpNegHoloPotential g δ ε θ‖ =
        (Real.exp ((holoPotential g δ (((1 - 2 * ε) * θ + ε : ℝ) : ℂ)).re))⁻¹ := by
      simp [contractedExpNegHoloPotential, Complex.norm_exp, Real.exp_neg]
    rw [norm_smul, hnorm] at hb
    exact ((inv_mul_le_iff₀ (Real.exp_pos _)).1 hb).trans_eq (mul_comm _ _)
  · rw [eq_zero_of_notMem hθ (mk θ g), norm_zero]; positivity

private theorem norm_mk_le_exp_re_holoPotential {θ δ : ℝ} (hθ : θ ∈ Ioo 0 1) (hδ : 0 < δ)
    (g : C.stripTraces) : ‖mk θ g‖ ≤ Real.exp (holoPotential g δ θ).re := by
  obtain ⟨T₀, _, hg₀⟩ := ZeroAtInftyContinuousMap.exists_forall_norm_le_of_le_abs g.val.1 hδ
  obtain ⟨T₁, _, hg₁⟩ := ZeroAtInftyContinuousMap.exists_forall_norm_le_of_le_abs g.val.2 hδ
  let T := max T₀ T₁; let Φ := holoPotential g δ
  refine Real.le_of_forall_pos_le_exp_mul (c := 1) fun κ hκ => ?_; rw [mul_one]
  have hs₀ := ZeroAtInftyContinuousMap.hasCompactSupport_logMaxDiv g.val.1 hδ
  have hs₁ := ZeroAtInftyContinuousMap.hasCompactSupport_logMaxDiv g.val.2 hδ
  obtain ⟨ε₀, hε₀, happrox₀⟩ := exists_forall_sub_le_integral_mul_contracted_stripPoisson₀
    (hs₀.uniformContinuous_of_continuous (ZeroAtInftyContinuousMap.continuous_logMaxDiv _ hδ))
    (hs₀.exists_bound_of_continuous (ZeroAtInftyContinuousMap.continuous_logMaxDiv _ hδ))
    (ZeroAtInftyContinuousMap.logMaxDiv_nonneg _ hδ) T hκ
  obtain ⟨ε₁, hε₁, happrox₁⟩ := exists_forall_sub_le_integral_mul_contracted_stripPoisson₁
    (hs₁.uniformContinuous_of_continuous (ZeroAtInftyContinuousMap.continuous_logMaxDiv _ hδ))
    (hs₁.exists_bound_of_continuous (ZeroAtInftyContinuousMap.continuous_logMaxDiv _ hδ))
    (ZeroAtInftyContinuousMap.logMaxDiv_nonneg _ hδ) T hκ
  have hΦ_cont : ContinuousAt Φ (θ : ℂ) :=
    (differentiableOn_holoPotential g hδ).continuousOn.continuousAt
      ((isOpen_Ioo.preimage continuous_re).mem_nhds (by simpa [verticalStrip] using hθ))
  have htend : Tendsto (fun ε : ℝ => Real.exp κ *
      Real.exp ((Φ (((1 - 2 * ε) * θ + ε : ℝ) : ℂ)).re)) (𝓝[>] 0)
      (𝓝 (Real.exp κ * Real.exp (Φ θ).re)) := by
    simpa [Function.comp_def] using (((Real.continuous_exp.tendsto _).comp
      ((Complex.continuous_re.tendsto _).comp (hΦ_cont.comp_of_eq
        ((by fun_prop : Continuous fun ε : ℝ => (((1 - 2 * ε) * θ + ε : ℝ) : ℂ)).continuousAt
          (x := 0)) (by simp)).tendsto)).const_mul (Real.exp κ)).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min (lt_min hε₀ hε₁) (by norm_num : (0 : ℝ) < 2⁻¹))]
    with ε hε
  exact norm_mk_le_exp_mul_exp_re_contracted_holoPotential hδ hκ
    ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩ g (fun s hs => hg₀ s ((le_max_left _ _).trans hs))
    (fun s hs => hg₁ s ((le_max_right _ _).trans hs))
    (happrox₀ ε ⟨hε.1, hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))⟩)
    (happrox₁ ε ⟨hε.1, hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))⟩)

/-- **Clipped logarithmic Poisson estimate for the complex method.** For `0 < θ < 1`, `δ > 0`, and
any admissible trace pair `g = (g₀, g₁)`, the quotient norm in `[X₀, X₁]_θ` is bounded by the
exponential of the strip Poisson integrals of `log (max ‖g₀ s‖ δ)` and `log (max ‖g₁ s‖ δ)`. -/
theorem norm_mk_le_exp_integral_log_max_of_pos {θ δ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hδ : 0 < δ) (g : C.stripTraces) :
    ‖mk θ g‖ ≤ Real.exp
      ((∫ s, Real.log (max ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 s‖ δ) * stripPoisson₀ θ s) +
        ∫ s, Real.log (max ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 s‖ δ) * stripPoisson₁ θ s) := by
  have hre := (norm_mk_le_exp_re_holoPotential hθ hδ g).trans_eq
    (congrArg Real.exp (re_holoPotential g hδ (by simpa [verticalStrip] using hθ)))
  simp only [ofReal_re, ofReal_im, zero_sub, stripPoisson₀_neg, stripPoisson₁_neg] at hre
  refine hre.trans_eq (congrArg Real.exp ?_)
  have hlogδ : Real.log δ =
      (∫ s, Real.log δ * stripPoisson₀ θ s) + ∫ s, Real.log δ * stripPoisson₁ θ s := by
    rw [integral_const_mul, integral_const_mul, integral_stripPoisson₀ ⟨hθ.1, hθ.2.le⟩,
      integral_stripPoisson₁ ⟨hθ.1.le, hθ.2⟩]; ring
  linarith [ZeroAtInftyContinuousMap.integral_log_max_mul_eq g.val.1 hδ
      (integrable_stripPoisson₀ θ),
    ZeroAtInftyContinuousMap.integral_log_max_mul_eq g.val.2 hδ (integrable_stripPoisson₁ θ)]

/-- **Bergh–Löfström Lemma 4.3.2 (Poisson log-convexity of the complex method norm).**
For `0 < θ < 1` and any admissible trace pair `g = (g₀, g₁)`, the quotient norm in `[X₀, X₁]_θ` is
bounded by the geometric mean of the Poisson averages of `‖g₀‖` and `‖g₁‖`, normalized by the
kernel masses `1 - θ` and `θ`, with exponents `1 - θ` and `θ`. -/
theorem norm_mk_le_integral_stripPoisson_rpow_mul_rpow {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (g : C.stripTraces) :
    ‖mk θ g‖ ≤
      ((1 - θ)⁻¹ * ∫ t, ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t‖ * stripPoisson₀ θ t) ^ (1 - θ) *
        (θ⁻¹ * ∫ t, ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t‖ * stripPoisson₁ θ t) ^ θ := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ.2
  refine (le_rpow_mul_rpow_mul_of_forall_pos (C := 1) (Ioo_subset_Icc_self hθ)
    fun δ hδ => ?_).trans_eq (mul_one _)
  have hI₀ : 0 ≤ (1 - θ)⁻¹ * (∫ t, ‖g.val.1 t‖ * stripPoisson₀ θ t) + δ := add_nonneg (mul_nonneg
    (inv_pos.2 h1θ).le (integral_nonneg fun s => mul_nonneg (norm_nonneg _)
      (stripPoisson₀_pos hθ s).le)) hδ.le
  exact (norm_mk_le_exp_integral_log_max_of_pos hθ hδ g).trans
    (((Real.exp_add _ _).trans_le (mul_le_mul
      (ZeroAtInftyContinuousMap.exp_integral_log_max_le_rpow g.val.1 h1θ hδ
        (integrable_stripPoisson₀ θ) (ae_of_all _ fun s => (stripPoisson₀_pos hθ s).le)
        (integral_stripPoisson₀ ⟨hθ.1, hθ.2.le⟩))
      (ZeroAtInftyContinuousMap.exp_integral_log_max_le_rpow g.val.2 hθ.1 hδ
        (integrable_stripPoisson₁ θ) (ae_of_all _ fun s => (stripPoisson₁_pos hθ s).le)
        (integral_stripPoisson₁ ⟨hθ.1.le, hθ.2⟩))
      (Real.exp_nonneg _) (Real.rpow_nonneg hI₀ _))).trans_eq (mul_one _).symm)

end TauCeti.CompatibleCouple.ComplexMethodSpace

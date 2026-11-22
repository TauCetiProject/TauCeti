/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Poisson.Strip
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
import TauCeti.MeasureTheory.Integral.MeanInequalities
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Log

/-!
# Log-convexity of the complex interpolation norm via strip Poisson kernels

On the open vertical strip `0 < re z < 1`, bounded harmonic functions are represented from their
boundary values on `re z = 0` and `re z = 1` by the strip Poisson kernels `TauCeti.stripPoisson₀`
and `TauCeti.stripPoisson₁`. Boundary recovery holds as a limit as `re z → 0⁺` or `1⁻`
(`TauCeti.exists_eps_integral_stripPoisson₀_ge`).

Multiplying an admissible strip function `F` by `exp (-Φ ((1 - 2 ε) z + ε))`, where `Φ` is the
holomorphic strip potential of compactly supported logarithmic envelopes of the boundary norms,
yields the clipped logarithmic Poisson estimate
(`CompatibleCouple.ComplexMethodSpace.norm_mk_le_exp_integral_log_max_of_pos`), and applying
weighted logarithmic Jensen (`ZeroAtInftyContinuousMap.exp_integral_log_max_le_rpow`) gives
Bergh–Löfström's Poisson estimate for Calderón's complex method:

* `CompatibleCouple.ComplexMethodSpace.norm_mk_le_exp_integral_log_max_of_pos`: for `0 < θ < 1`
  and `δ > 0`, `‖mk θ g‖ ≤ exp (∫ log (max ‖g₀ s‖ δ) P₀(θ, s) + ∫ log (max ‖g₁ s‖ δ) P₁(θ, s))`.
* `CompatibleCouple.ComplexMethodSpace.norm_mk_le_stripPoisson_geometricMean`: for `0 < θ < 1`,
  `‖mk θ g‖ ≤ ((1 - θ)⁻¹ ∫ ‖g₀ t‖ P₀(θ, t) dt) ^ (1 - θ) * (θ⁻¹ ∫ ‖g₁ t‖ P₁(θ, t) dt) ^ θ`.

Because `stripPoisson₀ θ` and `stripPoisson₁ θ` depend only on `(θ, t)` and the estimates hold
without completeness or duality assumptions, this uniform estimate serves as an ingredient for
vector-valued `Lᵖ` interpolation, applied here to finite-index `PiLp` spaces in
`TauCeti.CompatibleCouple.ComplexMethodSpace.piLpEquiv`.

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

private theorem integrable_logMaxDiv {E : Type*} [NormedAddCommGroup E] (f : C₀(ℝ, E)) {δ : ℝ}
    (hδ : 0 < δ) : Integrable (ZeroAtInftyContinuousMap.logMaxDiv f δ) :=
  (ZeroAtInftyContinuousMap.continuous_logMaxDiv f hδ).integrable_of_hasCompactSupport
    (ZeroAtInftyContinuousMap.hasCompactSupport_logMaxDiv f hδ)

private theorem differentiableOn_holoPotential (g : C.stripTraces) {δ : ℝ} (hδ : 0 < δ) :
    DifferentiableOn ℂ (holoPotential g δ) (verticalStrip 0 1) :=
  (differentiableOn_const _).add
    ((differentiableOn_integral_holoPoisson₀ (integrable_logMaxDiv g.val.1 hδ)).add
      (differentiableOn_integral_holoPoisson₁ (integrable_logMaxDiv g.val.2 hδ)))

private theorem re_holoPotential (g : C.stripTraces) {δ : ℝ} (hδ : 0 < δ) {ζ : ℂ}
    (hζ : ζ ∈ verticalStrip 0 1) :
    (holoPotential g δ ζ).re = Real.log δ +
      ((∫ s, ZeroAtInftyContinuousMap.logMaxDiv g.val.1 δ s * stripPoisson₀ ζ.re (ζ.im - s)) +
        ∫ s, ZeroAtInftyContinuousMap.logMaxDiv g.val.2 δ s * stripPoisson₁ ζ.re (ζ.im - s)) := by
  simp only [holoPotential, add_re, ofReal_re,
    re_integral_holoPoisson₀ (integrable_logMaxDiv g.val.1 hδ) hζ,
    re_integral_holoPoisson₁ (integrable_logMaxDiv g.val.2 hδ) hζ]

private theorem integral_logMaxDiv_mul_stripPoisson₀_nonneg {E : Type*} [NormedAddCommGroup E]
    (f : C₀(ℝ, E)) {δ r y : ℝ} (hδ : 0 < δ) (hr : r ∈ Ioo 0 1) :
    0 ≤ ∫ s, ZeroAtInftyContinuousMap.logMaxDiv f δ s * stripPoisson₀ r (y - s) :=
  integral_nonneg fun s =>
    mul_nonneg (ZeroAtInftyContinuousMap.logMaxDiv_nonneg f hδ s) (stripPoisson₀_pos hr _).le

private theorem integral_logMaxDiv_mul_stripPoisson₁_nonneg {E : Type*} [NormedAddCommGroup E]
    (f : C₀(ℝ, E)) {δ r y : ℝ} (hδ : 0 < δ) (hr : r ∈ Ioo 0 1) :
    0 ≤ ∫ s, ZeroAtInftyContinuousMap.logMaxDiv f δ s * stripPoisson₁ r (y - s) :=
  integral_nonneg fun s =>
    mul_nonneg (ZeroAtInftyContinuousMap.logMaxDiv_nonneg f hδ s) (stripPoisson₁_pos hr _).le

private theorem norm_exp_neg_holoPotential_le (g : C.stripTraces) {δ : ℝ} (hδ : 0 < δ) {ζ : ℂ}
    (hζ : ζ ∈ verticalStrip 0 1) :
    ‖Complex.exp (-holoPotential g δ ζ)‖ ≤ δ⁻¹ := by
  rw [Complex.norm_exp, neg_re, ← Real.exp_log (inv_pos.2 hδ), Real.log_inv,
    re_holoPotential g hδ hζ]
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  have h0 := integral_logMaxDiv_mul_stripPoisson₀_nonneg g.val.1 hδ (y := ζ.im) hζ
  have h1 := integral_logMaxDiv_mul_stripPoisson₁_nonneg g.val.2 hδ (y := ζ.im) hζ
  linarith

private theorem norm_exp_neg_mul_le_of_re_ge {E : Type*} [NormedAddCommGroup E] {δ κ : ℝ}
    (hδ : 0 < δ) {x : E} {w : ℂ} (hre : Real.log (max ‖x‖ δ) - κ ≤ w.re) :
    ‖Complex.exp (-w)‖ * ‖x‖ ≤ Real.exp κ := by
  have hm : 0 < max ‖x‖ δ := hδ.trans_le (le_max_right _ _)
  calc ‖Complex.exp (-w)‖ * ‖x‖
      ≤ Real.exp (κ - Real.log (max ‖x‖ δ)) * max ‖x‖ δ :=
        mul_le_mul (by rw [Complex.norm_exp, neg_re]; exact Real.exp_le_exp.2 (by linarith))
          (le_max_left _ _) (norm_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp κ := by
        rw [Real.exp_sub, div_mul_eq_mul_div, Real.exp_log hm, mul_div_cancel_right₀ _ hm.ne']

private noncomputable def contractedExpNegHoloPotential (g : C.stripTraces) (δ ε : ℝ)
    (z : ℂ) : ℂ :=
  Complex.exp (-holoPotential g δ ((1 - 2 * (ε : ℂ)) * z + ε))

private theorem contracted_mem_verticalStrip {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 4⁻¹) {z : ℂ}
    (hz : z.re ∈ Ioo (-(ε / 2)) (1 + ε / 2)) :
    (1 - 2 * (ε : ℂ)) * z + ε ∈ verticalStrip 0 1 := by
  have hre : ((1 - 2 * (ε : ℂ)) * z + ε).re = (1 - 2 * ε) * z.re + ε := by simp
  rw [mem_verticalStrip_iff, hre, mem_Ioo]
  exact ⟨by nlinarith [hε.1, hε.2, hz.1], by nlinarith [hε.1, hε.2, hz.2]⟩

private theorem diffContOnCl_contractedExpNegHoloPotential (g : C.stripTraces) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : ε ∈ Ioo (0 : ℝ) 4⁻¹) :
    DiffContOnCl ℂ (contractedExpNegHoloPotential g δ ε) (verticalStrip 0 1) := by
  have hdiff : DifferentiableOn ℂ (contractedExpNegHoloPotential g δ ε)
      (verticalStrip (-(ε / 2)) (1 + ε / 2)) :=
    (((differentiableOn_holoPotential g hδ).comp
      (by fun_prop : Differentiable ℂ fun z : ℂ => (1 - 2 * (ε : ℂ)) * z + ε).differentiableOn
      fun _ hz => contracted_mem_verticalStrip hε hz).neg).cexp
  have hsub : verticalClosedStrip 0 1 ⊆ verticalStrip (-(ε / 2)) (1 + ε / 2) := fun _ hz =>
    ⟨by linarith [hε.1, hz.1], by linarith [hε.1, hz.2]⟩
  exact ⟨hdiff.mono ((verticalStrip_subset_verticalClosedStrip 0 1).trans hsub),
    hdiff.continuousOn.mono ((closure_verticalStrip_subset 0 1).trans hsub)⟩

private theorem norm_contractedExpNegHoloPotential_le (g : C.stripTraces) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : ε ∈ Ioo (0 : ℝ) 4⁻¹) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    ‖contractedExpNegHoloPotential g δ ε z‖ ≤ δ⁻¹ :=
  norm_exp_neg_holoPotential_le g hδ
    (contracted_mem_verticalStrip hε ⟨by linarith [hε.1, hz.1], by linarith [hε.1, hz.2]⟩)

private theorem norm_mk_le_exp_mul_exp_re_contracted_holoPotential {θ δ T κ ε : ℝ}
    (hδ : 0 < δ) (hκ : 0 < κ) (hε : ε ∈ Ioo (0 : ℝ) 4⁻¹) (g : C.stripTraces)
    (hg₀ : ∀ s, T ≤ |s| → ‖g.val.1 s‖ ≤ δ) (hg₁ : ∀ s, T ≤ |s| → ‖g.val.2 s‖ ≤ δ)
    (happrox₀ : ∀ t ∈ Icc (-T) T, ZeroAtInftyContinuousMap.logMaxDiv g.val.1 δ t - κ ≤
      ∫ s, ZeroAtInftyContinuousMap.logMaxDiv g.val.1 δ s *
        stripPoisson₀ ε ((1 - 2 * ε) * t - s))
    (happrox₁ : ∀ t ∈ Icc (-T) T,
      (ZeroAtInftyContinuousMap.logMaxDiv g.val.2 δ ∘ Neg.neg) t - κ ≤
      ∫ s, (ZeroAtInftyContinuousMap.logMaxDiv g.val.2 δ ∘ Neg.neg) s *
        stripPoisson₀ ε ((1 - 2 * ε) * t - s)) :
    ‖mk θ g‖ ≤ Real.exp κ *
      Real.exp ((holoPotential g δ (((1 - 2 * ε) * θ + ε : ℝ) : ℂ)).re) := by
  by_cases hθ : θ ∈ Icc (0 : ℝ) 1
  · let w : ℂ → ℂ := fun z => (1 - 2 * (ε : ℂ)) * z + ε
    have hbdry (z : ℂ) (hz : z ∈ verticalClosedStrip 0 1) (t n : ℝ) (hn : 0 ≤ n)
        (htail_le : T ≤ |t| → n ≤ δ)
        (hcore : ¬ T ≤ |t| → Real.log (max n δ) - κ ≤ (holoPotential g δ (w z)).re) :
        ‖contractedExpNegHoloPotential g δ ε z‖ * n ≤ Real.exp κ := by
      by_cases ht : T ≤ |t|
      · exact (mul_le_mul (norm_contractedExpNegHoloPotential_le g hδ hε hz) (htail_le ht) hn
          (inv_pos.2 hδ).le).trans ((inv_mul_cancel₀ hδ.ne').trans_le (Real.one_le_exp hκ.le))
      · have hre := hcore ht
        rw [← Real.norm_of_nonneg hn] at hre ⊢
        exact norm_exp_neg_mul_le_of_re_ge hδ hre
    have hb := norm_smul_mk_le_of_diffContOnCl θ g
      (diffContOnCl_contractedExpNegHoloPotential g hδ hε)
      (fun _ hz => norm_contractedExpNegHoloPotential_le g hδ hε hz) (Real.exp_pos κ).le
      (fun t => by
        rw [norm_smul]
        refine hbdry (t * I) (by simp [verticalClosedStrip]) t ‖g.val.1 t‖ (norm_nonneg _)
          (hg₀ t) fun ht => ?_
        have hws : w (t * I) ∈ verticalStrip 0 1 :=
          contracted_mem_verticalStrip hε ⟨by simp [hε.1], by simp; linarith [hε.1]⟩
        have hw_re : (w (t * I)).re = ε := by simp [w]
        have hw_im : (w (t * I)).im = (1 - 2 * ε) * t := by simp [w]
        rw [re_holoPotential g hδ hws, hw_re, hw_im]
        have hopp := integral_logMaxDiv_mul_stripPoisson₁_nonneg g.val.2 hδ
          (r := ε) (y := (1 - 2 * ε) * t) ⟨hε.1, by linarith [hε.2]⟩
        linarith [happrox₀ t (abs_le.1 (not_le.1 ht).le),
          ZeroAtInftyContinuousMap.log_add_logMaxDiv g.val.1 hδ t])
      (fun t => by
        rw [norm_smul]
        refine hbdry (1 + t * I) (by simp [verticalClosedStrip]) t ‖g.val.2 t‖ (norm_nonneg _)
          (hg₁ t) fun ht => ?_
        obtain ⟨ht1, ht2⟩ := abs_le.1 (not_le.1 ht).le
        have hap := happrox₁ (-t) ⟨by linarith, by linarith⟩
        rw [Function.comp_apply, neg_neg, mul_neg, integral_comp_neg_mul_stripPoisson₀_eq] at hap
        have hws : w (1 + t * I) ∈ verticalStrip 0 1 :=
          contracted_mem_verticalStrip hε ⟨by simp; linarith [hε.1], by simp [hε.1]⟩
        have hw_re : (w (1 + t * I)).re = 1 - ε := by simp [w]; ring
        have hw_im : (w (1 + t * I)).im = (1 - 2 * ε) * t := by simp [w]
        rw [re_holoPotential g hδ hws, hw_re, hw_im]
        have hopp := integral_logMaxDiv_mul_stripPoisson₀_nonneg g.val.1 hδ
          (r := 1 - ε) (y := (1 - 2 * ε) * t) ⟨by linarith [hε.2], by linarith [hε.1]⟩
        linarith [ZeroAtInftyContinuousMap.log_add_logMaxDiv g.val.2 hδ t])
    have hcθ : ‖contractedExpNegHoloPotential g δ ε θ‖ =
        (Real.exp ((holoPotential g δ (((1 - 2 * ε) * θ + ε : ℝ) : ℂ)).re))⁻¹ := by
      simp [contractedExpNegHoloPotential, Complex.norm_exp, Real.exp_neg]
    rw [norm_smul, hcθ] at hb
    exact ((inv_mul_le_iff₀ (Real.exp_pos _)).1 hb).trans_eq (mul_comm _ _)
  · rw [eq_zero_of_notMem hθ (mk θ g), norm_zero]
    positivity

private theorem exists_eps_contracted_integral_stripPoisson₀_ge {u : ℝ → ℝ} (hu : Continuous u)
    (hsupp : HasCompactSupport u) (hunonneg : ∀ s, 0 ≤ u s) (T : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, ∀ t ∈ Icc (-T) T,
      u t - κ ≤ ∫ s, u s * stripPoisson₀ ε ((1 - 2 * ε) * t - s) := by
  obtain ⟨ε₀, hε₀, happrox⟩ :=
    exists_eps_integral_stripPoisson₀_ge hu hsupp hunonneg (half_pos hκ)
  obtain ⟨η, hη, huc⟩ :=
    Metric.uniformContinuous_iff.1 (hsupp.uniformContinuous_of_continuous hu) (κ / 2) (half_pos hκ)
  refine ⟨min ε₀ (η / (2 * (|T| + 1))), lt_min hε₀ (by positivity), fun ε hε t ht => ?_⟩
  have hdist : dist ((1 - 2 * ε) * t) t < η := by
    rw [Real.dist_eq]
    have htabs : |t| ≤ |T| + 1 :=
      (abs_le.2 ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩).trans
        ((le_abs_self T).trans (by linarith))
    have hεη : ε * (2 * (|T| + 1)) < η :=
      (lt_div_iff₀ (mul_pos two_pos (add_pos_of_nonneg_of_pos (abs_nonneg T) one_pos))).1
        (hε.2.trans_le (min_le_right _ _))
    calc |(1 - 2 * ε) * t - t| = 2 * ε * |t| := by
          rw [show (1 - 2 * ε) * t - t = -(2 * ε * t) by ring, abs_neg, abs_mul,
            abs_of_pos (mul_pos two_pos hε.1)]
      _ ≤ 2 * ε * (|T| + 1) := mul_le_mul_of_nonneg_left htabs (mul_pos two_pos hε.1).le
      _ < η := by linarith
  have hdu := huc hdist
  rw [Real.dist_eq] at hdu
  have h1 : u t - κ / 2 ≤ u ((1 - 2 * ε) * t) := by linarith [(abs_sub_le_iff.1 hdu.le).2]
  have h2 := happrox ε ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩ ((1 - 2 * ε) * t)
  linarith

private theorem norm_mk_le_exp_re_holoPotential {θ δ : ℝ} (hθ : θ ∈ Ioo 0 1) (hδ : 0 < δ)
    (g : C.stripTraces) :
    ‖mk θ g‖ ≤ Real.exp (holoPotential g δ θ).re := by
  obtain ⟨T₀, _, hg₀⟩ := ZeroAtInftyContinuousMap.exists_abs_ge_norm_le g.val.1 hδ
  obtain ⟨T₁, _, hg₁⟩ := ZeroAtInftyContinuousMap.exists_abs_ge_norm_le g.val.2 hδ
  let T := max T₀ T₁
  let Φ := holoPotential g δ
  have hθstrip : (θ : ℂ) ∈ verticalStrip 0 1 := by simpa [verticalStrip] using hθ
  suffices hκ_le : ∀ κ > 0, ‖mk θ g‖ ≤ Real.exp κ * Real.exp (Φ θ).re by
    have htendκ : Tendsto (fun κ : ℝ => Real.exp κ * Real.exp (Φ θ).re) (𝓝[>] 0)
        (𝓝 (Real.exp (Φ θ).re)) := by
      simpa using ((by fun_prop : Continuous fun κ : ℝ => Real.exp κ * Real.exp (Φ θ).re).tendsto 0)
        |>.mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto htendκ (eventually_nhdsWithin_of_forall hκ_le)
  intro κ hκ
  obtain ⟨ε₀, hε₀, happrox₀⟩ := exists_eps_contracted_integral_stripPoisson₀_ge
    (ZeroAtInftyContinuousMap.continuous_logMaxDiv g.val.1 hδ)
    (ZeroAtInftyContinuousMap.hasCompactSupport_logMaxDiv g.val.1 hδ)
    (ZeroAtInftyContinuousMap.logMaxDiv_nonneg g.val.1 hδ) T hκ
  obtain ⟨ε₁, hε₁, happrox₁⟩ := exists_eps_contracted_integral_stripPoisson₀_ge
    ((ZeroAtInftyContinuousMap.continuous_logMaxDiv g.val.2 hδ).comp continuous_neg)
    ((ZeroAtInftyContinuousMap.hasCompactSupport_logMaxDiv g.val.2 hδ).comp_homeomorph
      (Homeomorph.neg ℝ))
    (fun s => ZeroAtInftyContinuousMap.logMaxDiv_nonneg g.val.2 hδ (-s)) T hκ
  have hΦ_cont : ContinuousAt Φ (((1 - 2 * (0 : ℝ)) * θ + (0 : ℝ) : ℝ) : ℂ) := by
    simpa using (differentiableOn_holoPotential g hδ).continuousOn.continuousAt
      ((isOpen_Ioo.preimage continuous_re).mem_nhds hθstrip)
  have hcomp : ContinuousAt (fun ε : ℝ => Φ (((1 - 2 * ε) * θ + ε : ℝ) : ℂ)) 0 :=
    ContinuousAt.comp (g := Φ) (f := fun ε : ℝ => (((1 - 2 * ε) * θ + ε : ℝ) : ℂ))
      hΦ_cont
      ((by fun_prop : Continuous fun ε : ℝ => (((1 - 2 * ε) * θ + ε : ℝ) : ℂ)).continuousAt)
  have htend_ε : Tendsto
      (fun ε : ℝ => Real.exp κ * Real.exp ((Φ (((1 - 2 * ε) * θ + ε : ℝ) : ℂ)).re))
      (𝓝[>] 0) (𝓝 (Real.exp κ * Real.exp (Φ θ).re)) := by
    simpa [Function.comp_def] using
      (((Real.continuous_exp.tendsto _).comp ((Complex.continuous_re.tendsto _).comp hcomp.tendsto))
        |>.const_mul (Real.exp κ)).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto htend_ε ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min (lt_min hε₀ hε₁) (by norm_num : (0 : ℝ) < 4⁻¹))]
    with ε hε
  exact norm_mk_le_exp_mul_exp_re_contracted_holoPotential hδ hκ
    ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩ g
    (fun s hs => hg₀ s ((le_max_left _ _).trans hs))
    (fun s hs => hg₁ s ((le_max_right _ _).trans hs))
    (happrox₀ ε ⟨hε.1, hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))⟩)
    (happrox₁ ε ⟨hε.1, hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))⟩)

/-- **Clipped logarithmic Poisson estimate for the complex method.** For `0 < θ < 1`, `δ > 0`, and
any admissible trace pair `g = (g₀, g₁)`, the quotient norm in `[X₀, X₁]_θ` is bounded by the
exponential of the strip Poisson integrals of `log (max ‖g₀‖ δ)` and `log (max ‖g₁‖ δ)`. -/
theorem norm_mk_le_exp_integral_log_max_of_pos {θ δ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hδ : 0 < δ) (g : C.stripTraces) :
    ‖mk θ g‖ ≤ Real.exp
      ((∫ s, Real.log (max ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 s‖ δ) * stripPoisson₀ θ s) +
        ∫ s, Real.log (max ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 s‖ δ) * stripPoisson₁ θ s) := by
  have hθstrip : (θ : ℂ) ∈ verticalStrip 0 1 := by simpa [verticalStrip] using hθ
  have hre := (norm_mk_le_exp_re_holoPotential hθ hδ g).trans_eq
    (congrArg Real.exp (re_holoPotential g hδ hθstrip))
  simp only [ofReal_re, ofReal_im, zero_sub, stripPoisson₀_neg, stripPoisson₁_neg] at hre
  refine hre.trans_eq (congrArg Real.exp ?_)
  have hlogδ : Real.log δ =
      (∫ s, Real.log δ * stripPoisson₀ θ s) + ∫ s, Real.log δ * stripPoisson₁ θ s := by
    rw [integral_const_mul, integral_const_mul, integral_stripPoisson₀ ⟨hθ.1, hθ.2.le⟩,
      integral_stripPoisson₁ ⟨hθ.1.le, hθ.2⟩]
    ring
  linarith [ZeroAtInftyContinuousMap.integral_log_max_eq g.val.1 hδ (integrable_stripPoisson₀ θ),
    ZeroAtInftyContinuousMap.integral_log_max_eq g.val.2 hδ (integrable_stripPoisson₁ θ)]

/-- **Bergh–Löfström Lemma 4.3.2 (Stieltjes/Poisson log-convexity of the complex method norm).**
For `0 < θ < 1` and any admissible trace pair `g = (g₀, g₁)`, the quotient norm in `[X₀, X₁]_θ` is
bounded by the weighted geometric mean of the strip Poisson integrals of `‖g₀‖` and `‖g₁‖`. -/
theorem norm_mk_le_stripPoisson_geometricMean {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (g : C.stripTraces) :
    ‖mk θ g‖ ≤
      ((1 - θ)⁻¹ * ∫ t, ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t‖ * stripPoisson₀ θ t) ^ (1 - θ) *
        (θ⁻¹ * ∫ t, ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t‖ * stripPoisson₁ θ t) ^ θ := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ.2
  let I₀ := (1 - θ)⁻¹ * ∫ t, ‖g.val.1 t‖ * stripPoisson₀ θ t
  let I₁ := θ⁻¹ * ∫ t, ‖g.val.2 t‖ * stripPoisson₁ θ t
  have hadd (a : ℝ) : Tendsto (fun δ : ℝ => a + δ) (𝓝[>] 0) (𝓝 a) := by
    simpa using ((by fun_prop : Continuous fun δ : ℝ => a + δ).tendsto 0)
      |>.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto
    (((hadd I₀).rpow_const (Or.inr h1θ.le)).mul ((hadd I₁).rpow_const (Or.inr hθ.1.le))) ?_
  filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
  have hI₀ : 0 ≤ I₀ + δ := add_nonneg (mul_nonneg (inv_pos.2 h1θ).le
    (integral_nonneg fun s => mul_nonneg (norm_nonneg _) (stripPoisson₀_pos hθ s).le)) hδ.le
  refine (norm_mk_le_exp_integral_log_max_of_pos hθ hδ g).trans
    ((Real.exp_add _ _).trans_le (mul_le_mul
      (ZeroAtInftyContinuousMap.exp_integral_log_max_le_rpow g.val.1 h1θ hδ
        (integrable_stripPoisson₀ θ) (fun s => (stripPoisson₀_pos hθ s).le)
        (integral_stripPoisson₀ ⟨hθ.1, hθ.2.le⟩))
      (ZeroAtInftyContinuousMap.exp_integral_log_max_le_rpow g.val.2 hθ.1 hδ
        (integrable_stripPoisson₁ θ) (fun s => (stripPoisson₁_pos hθ s).le)
        (integral_stripPoisson₁ ⟨hθ.1.le, hθ.2⟩))
      (Real.exp_nonneg _) (Real.rpow_nonneg hI₀ _)))

end TauCeti.CompatibleCouple.ComplexMethodSpace

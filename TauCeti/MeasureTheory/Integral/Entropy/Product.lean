/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import TauCeti.MeasureTheory.Integral.Entropy.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.SpecialFunctions.Log.MulLog
import TauCeti.MeasureTheory.Integral.Pi

/-!
# Tensorization and subadditivity of functional entropy on product measures

For probability measures `μ` and `ν` and an a.e. nonnegative integrable function `g : α × β → ℝ`
with `g log g` integrable, the functional entropy satisfies:
* the **chain rule** `entropy_prod_eq`:
  `Ent_{μ ⊗ ν}(g) = ∫ x, Ent_ν(g(x, ·)) ∂μ + Ent_μ(x ↦ ∫ y, g(x, y) ∂ν)`;
* **convexity under averaging** `entropy_integral_prod_le`:
  `Ent_μ(x ↦ ∫ y, g(x, y) ∂ν) ≤ ∫ y, Ent_μ(g(·, y)) ∂ν`;
* **two-factor subadditivity** `entropy_prod_le`:
  `Ent_{μ ⊗ ν}(g) ≤ ∫ x, Ent_ν(g(x, ·)) ∂μ + ∫ y, Ent_μ(g(·, y)) ∂ν`;
* **finite-product subadditivity** `entropy_pi_le_sum`: for independent coordinates under
  `Measure.pi μ`,
  `Ent_{⨂ i, μ i}(g) ≤ ∑ i, ∫ x, Ent_{μ i}(y ↦ g (Function.update x i y)) ∂Measure.pi μ`.

## Main results

* `MeasureTheory.Measure.entropy_prod_eq`: exact chain-rule decomposition on `μ.prod ν`.
* `MeasureTheory.Measure.entropy_integral_prod_le`: convexity of `entropy μ` under `ν`-averaging.
* `MeasureTheory.Measure.entropy_prod_le`: subadditivity of entropy on `μ.prod ν`.
* `MeasureTheory.Measure.integrable_entropy_update_pi`: integrability of each coordinate slice
  entropy on `Measure.pi μ`.
* `MeasureTheory.Measure.entropy_pi_le_sum`: subadditivity of entropy on `Measure.pi μ` over any
  finite index type.

## References

* S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities*, Oxford University Press
  (2013), Theorem 4.10.
* D. Bakry, I. Gentil and M. Ledoux, *Analysis and Geometry of Markov Diffusion Operators*,
  Springer (2014), Proposition 5.2.1.
* G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), Lemma 2.3.3.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Measure

section BinaryProduct

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- If `g ≥ 0` a.e. on `μ.prod ν` with `g` and `g log g` integrable, then `G x * log (G x)` is
`μ`-integrable for the marginal average `G x = ∫ y, g (x, y) ∂ν`. -/
theorem integrable_mul_log_integral_prod_left {g : α × β → ℝ}
    (hg0 : 0 ≤ᵐ[μ.prod ν] g) (hg : Integrable g (μ.prod ν))
    (hglog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    Integrable (fun x ↦ (∫ y, g (x, y) ∂ν) * Real.log (∫ y, g (x, y) ∂ν)) μ := by
  let G : α → ℝ := fun x ↦ ∫ y, g (x, y) ∂ν
  have hGm : AEStronglyMeasurable G μ := hg.aestronglyMeasurable.integral_prod_right'
  have hmeas : AEStronglyMeasurable (fun x ↦ G x * Real.log (G x)) μ :=
    Real.continuous_mul_log.comp_aestronglyMeasurable hGm
  have hdom : Integrable (fun x ↦ 1 + ‖∫ y, g (x, y) * Real.log (g (x, y)) ∂ν‖) μ :=
    (integrable_const 1).add hglog.integral_prod_left.norm
  refine hdom.mono' hmeas ?_
  filter_upwards [ae_ae_of_ae_prod hg0, hg.prod_right_ae, hglog.prod_right_ae]
    with x hx0 hxg hxglog
  have hGx0 : 0 ≤ G x := integral_nonneg_of_ae hx0
  have hlow : -1 ≤ G x * Real.log (G x) := TauCeti.neg_one_le_mul_log hGx0
  have hhigh : G x * Real.log (G x) ≤ ∫ y, g (x, y) * Real.log (g (x, y)) ∂ν :=
    Real.convexOn_mul_log.map_integral_le Real.continuous_mul_log.continuousOn
      isClosed_Ici hx0 hxg hxglog
  dsimp only [G] at hlow hhigh ⊢
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact abs_le.2 ⟨by linarith [abs_nonneg (∫ y, g (x, y) * Real.log (g (x, y)) ∂ν)],
    by linarith [le_abs_self (∫ y, g (x, y) * Real.log (g (x, y)) ∂ν)]⟩

/-- Symmetric version of `integrable_mul_log_integral_prod_left` for the second-coordinate
marginal `m y = ∫ x, g (x, y) ∂μ`. -/
theorem integrable_mul_log_integral_prod_right {g : α × β → ℝ}
    (hg0 : 0 ≤ᵐ[μ.prod ν] g) (hg : Integrable g (μ.prod ν))
    (hglog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    Integrable (fun y ↦ (∫ x, g (x, y) ∂μ) * Real.log (∫ x, g (x, y) ∂μ)) ν := by
  have hswap : MeasurePreserving Prod.swap (ν.prod μ) (μ.prod ν) := measurePreserving_swap
  have hg0' : 0 ≤ᵐ[ν.prod μ] g ∘ Prod.swap := hswap.quasiMeasurePreserving.ae hg0
  have hg' : Integrable (g ∘ Prod.swap) (ν.prod μ) := hswap.integrable_comp_of_integrable hg
  have hglog' : Integrable (fun p : β × α ↦ g (Prod.swap p) * Real.log (g (Prod.swap p)))
      (ν.prod μ) := hswap.integrable_comp_of_integrable hglog
  exact integrable_mul_log_integral_prod_left hg0' hg' hglog'

/-- Under `μ.prod ν`, the slice entropy `x ↦ entropy ν (fun y ↦ g (x, y))` is `μ`-integrable. -/
theorem integrable_entropy_prod_right {g : α × β → ℝ}
    (hg0 : 0 ≤ᵐ[μ.prod ν] g) (hg : Integrable g (μ.prod ν))
    (hglog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    Integrable (fun x ↦ entropy ν (fun y ↦ g (x, y))) μ := by
  simp_rw [entropy_def]
  exact hglog.integral_prod_left.sub (integrable_mul_log_integral_prod_left hg0 hg hglog)

/-- Under `μ.prod ν`, the slice entropy `y ↦ entropy μ (fun x ↦ g (x, y))` is `ν`-integrable. -/
theorem integrable_entropy_prod_left {g : α × β → ℝ}
    (hg0 : 0 ≤ᵐ[μ.prod ν] g) (hg : Integrable g (μ.prod ν))
    (hglog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    Integrable (fun y ↦ entropy μ (fun x ↦ g (x, y))) ν := by
  simp_rw [entropy_def]
  exact hglog.integral_prod_right.sub (integrable_mul_log_integral_prod_right hg0 hg hglog)

/-- **Chain rule for functional entropy on a product measure.** The entropy of `g` under `μ.prod ν`
equals the `μ`-average of the `ν`-slice entropies plus the `μ`-entropy of the `ν`-averages. -/
theorem entropy_prod_eq {g : α × β → ℝ}
    (hg0 : 0 ≤ᵐ[μ.prod ν] g) (hg : Integrable g (μ.prod ν))
    (hglog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    entropy (μ.prod ν) g =
      (∫ x, entropy ν (fun y ↦ g (x, y)) ∂μ) + entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) := by
  have hGlog := integrable_mul_log_integral_prod_left hg0 hg hglog
  simp only [entropy_def]
  rw [integral_sub hglog.integral_prod_left hGlog, integral_prod _ hglog, integral_prod _ hg]
  ring

private theorem integrable_and_integral_mul_log_marginal_fst {g : α × β → ℝ}
    (hgm : Measurable g) (hg0 : ∀ p, 0 ≤ g p) (hg : Integrable g (μ.prod ν))
    (hglog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    Integrable (fun p : α × β ↦ g p * Real.log (∫ y, g (p.1, y) ∂ν)) (μ.prod ν) ∧
      (∫ p, g p * Real.log (∫ y, g (p.1, y) ∂ν) ∂(μ.prod ν)) =
        ∫ x, (∫ y, g (x, y) ∂ν) * Real.log (∫ y, g (x, y) ∂ν) ∂μ := by
  let G : α → ℝ := fun x ↦ ∫ y, g (x, y) ∂ν
  have hGm : Measurable G := hgm.stronglyMeasurable.integral_prod_right'.measurable
  have hGlog : Integrable (fun x ↦ G x * Real.log (G x)) μ :=
    integrable_mul_log_integral_prod_left (.of_forall hg0) hg hglog
  have hint : Integrable (fun p : α × β ↦ g p * Real.log (G p.1)) (μ.prod ν) := by
    refine integrable_prod_iff (hgm.mul (Real.measurable_log.comp
      (hGm.comp measurable_fst))).aestronglyMeasurable |>.2 ⟨?_, ?_⟩
    · filter_upwards [hg.prod_right_ae] with x hx using hx.mul_const (Real.log (G x))
    · refine hGlog.norm.congr ?_
      filter_upwards [hg.prod_right_ae] with x _
      dsimp
      have hcongr : (fun y ↦ |g (x, y) * Real.log (G x)|) =
          fun y ↦ g (x, y) * |Real.log (G x)| := by
        funext y
        rw [abs_mul, abs_of_nonneg (hg0 (x, y))]
      rw [abs_mul, abs_of_nonneg (integral_nonneg fun y ↦ hg0 (x, y)), hcongr, integral_mul_const]
  refine ⟨hint, ?_⟩
  rw [integral_prod _ hint]
  exact integral_congr_ae (.of_forall fun x ↦ integral_mul_const (Real.log (G x)) _)

private theorem ae_eq_zero_of_integral_fst_eq_zero {g : α × β → ℝ}
    (hgm : Measurable g) (hg0 : ∀ p, 0 ≤ g p) (hg : Integrable g (μ.prod ν)) :
    ∀ᵐ p ∂(μ.prod ν), (∫ y, g (p.1, y) ∂ν) = 0 → g p = 0 := by
  let G : α → ℝ := fun x ↦ ∫ y, g (x, y) ∂ν
  have hGm : Measurable G := hgm.stronglyMeasurable.integral_prod_right'.measurable
  have hmset : MeasurableSet {p : α × β | G p.1 = 0 → g p = 0} := by
    have heq : {p : α × β | G p.1 = 0 → g p = 0} =
        {p : α × β | (G ∘ Prod.fst) p = 0}ᶜ ∪ {p : α × β | g p = 0} :=
      Set.ext fun _ ↦ imp_iff_not_or
    rw [heq]
    exact (measurableSet_eq_fun (hGm.comp measurable_fst) measurable_const).compl.union
      (measurableSet_eq_fun hgm measurable_const)
  rw [ae_prod_iff_ae_ae hmset]
  filter_upwards [hg.prod_right_ae] with x hx
  by_cases hGx : G x = 0
  · filter_upwards [(integral_eq_zero_iff_of_nonneg (fun y ↦ hg0 (x, y)) hx).1 hGx]
      with y hy _ using hy
  · exact .of_forall fun _ h ↦ absurd h hGx

/-- Measurable, everywhere-nonnegative core of `entropy_integral_prod_le`. -/
private theorem entropy_integral_prod_le_of_measurable {g : α × β → ℝ}
    (hgm : Measurable g) (hg0 : ∀ p, 0 ≤ g p) (hg : Integrable g (μ.prod ν))
    (hglog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) ≤ ∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν := by
  let G : α → ℝ := fun x ↦ ∫ y, g (x, y) ∂ν
  let m : β → ℝ := fun y ↦ ∫ x, g (x, y) ∂μ
  let M : ℝ := ∫ p, g p ∂(μ.prod ν)
  have hG0 (x : α) : 0 ≤ G x := integral_nonneg fun y ↦ hg0 (x, y)
  have hm0 (y : β) : 0 ≤ m y := integral_nonneg fun x ↦ hg0 (x, y)
  have hM0 : 0 ≤ M := integral_nonneg hg0
  rcases hM0.eq_or_lt with hM_zero | hM_pos
  · have hgae : g =ᵐ[μ.prod ν] 0 :=
      (integral_eq_zero_iff_of_nonneg hg0 hg).1 hM_zero.symm
    have hGae : G =ᵐ[μ] 0 := by
      filter_upwards [ae_ae_of_ae_prod hgae] with x hx
      simpa [G] using integral_congr_ae hx
    have hslice_ae : (fun y ↦ entropy μ (fun x ↦ g (x, y))) =ᵐ[ν] 0 := by
      have hswap_ae : (g ∘ Prod.swap) =ᵐ[ν.prod μ] 0 :=
        measurePreserving_swap.quasiMeasurePreserving.ae hgae
      filter_upwards [ae_ae_of_ae_prod hswap_ae] with y hy
      simpa using entropy_congr_ae (μ := μ) hy
    rw [entropy_congr_ae hGae, Pi.zero_def, entropy_zero, integral_congr_ae hslice_ae,
      Pi.zero_def, integral_zero]
  · have hswap : MeasurePreserving Prod.swap (ν.prod μ) (μ.prod ν) := measurePreserving_swap
    have hgs_int : Integrable (g ∘ Prod.swap) (ν.prod μ) := hswap.integrable_comp_of_integrable hg
    have hgslog_int : Integrable (fun q : β × α ↦ g (Prod.swap q) * Real.log (g (Prod.swap q)))
        (ν.prod μ) := hswap.integrable_comp_of_integrable hglog
    obtain ⟨h_glogG_int, h_glogG_eq⟩ :=
      integrable_and_integral_mul_log_marginal_fst hgm hg0 hg hglog
    obtain ⟨h_gslogm_int, h_gslogm_eq⟩ :=
      integrable_and_integral_mul_log_marginal_fst (hgm.comp measurable_swap)
        (fun q ↦ hg0 (Prod.swap q)) hgs_int hgslog_int
    have h_glogm_int : Integrable (fun p : α × β ↦ g p * Real.log (m p.2)) (μ.prod ν) :=
      (measurePreserving_swap (μ := μ) (ν := ν)).integrable_comp_of_integrable h_gslogm_int
    have h_glogm_eq : ∫ p, g p * Real.log (m p.2) ∂(μ.prod ν) = ∫ y, m y * Real.log (m y) ∂ν := by
      rw [← integral_prod_swap (fun p : α × β ↦ g p * Real.log (m p.2))]
      exact h_gslogm_eq
    have hae_G : ∀ᵐ p ∂(μ.prod ν), G p.1 = 0 → g p = 0 :=
      ae_eq_zero_of_integral_fst_eq_zero hgm hg0 hg
    have hae_m : ∀ᵐ p ∂(μ.prod ν), m p.2 = 0 → g p = 0 :=
      (measurePreserving_swap (μ := μ) (ν := ν)).quasiMeasurePreserving.ae <|
        ae_eq_zero_of_integral_fst_eq_zero (hgm.comp measurable_swap)
          (fun q ↦ hg0 (Prod.swap q)) hgs_int
    have hG_int : Integrable G μ := hg.integral_prod_left
    have hm_int : Integrable m ν := hg.integral_prod_right
    have hmlog : Integrable (fun y ↦ m y * Real.log (m y)) ν :=
      integrable_mul_log_integral_prod_right (.of_forall hg0) hg hglog
    -- Pointwise Klein inequality `g * (log G + log m - log M - log g) ≤ G * m / M - g`.
    have hpt : ∀ᵐ p ∂(μ.prod ν),
        g p * Real.log (G p.1) + g p * Real.log (m p.2) -
          g p * Real.log M - g p * Real.log (g p) ≤ G p.1 * m p.2 / M - g p := by
      filter_upwards [hae_G, hae_m] with p hpG hpm
      rcases (hg0 p).eq_or_lt with hgp0 | hgp_pos
      · simp only [← hgp0, zero_mul, add_zero, sub_zero]
        exact div_nonneg (mul_nonneg (hG0 p.1) (hm0 p.2)) hM_pos.le
      · have hGp_pos : 0 < G p.1 :=
          lt_of_le_of_ne (hG0 p.1) fun h0 ↦ hgp_pos.ne' (hpG h0.symm)
        have hmp_pos : 0 < m p.2 :=
          lt_of_le_of_ne (hm0 p.2) fun h0 ↦ hgp_pos.ne' (hpm h0.symm)
        have hklein := Real.sub_le_mul_log_sub_mul_log (hg0 p)
          (div_pos (mul_pos hGp_pos hmp_pos) hM_pos).le
          (fun h0 ↦ absurd h0 (div_pos (mul_pos hGp_pos hmp_pos) hM_pos).ne')
        rw [Real.log_div (mul_pos hGp_pos hmp_pos).ne' hM_pos.ne',
          Real.log_mul hGp_pos.ne' hmp_pos.ne'] at hklein
        linarith
    have h_sum1_int :
        Integrable (fun p : α × β ↦ g p * Real.log (G p.1) + g p * Real.log (m p.2))
          (μ.prod ν) := h_glogG_int.add h_glogm_int
    have h_sum2_int :
        Integrable (fun p : α × β ↦
          g p * Real.log (G p.1) + g p * Real.log (m p.2) - g p * Real.log M) (μ.prod ν) :=
      h_sum1_int.sub (hg.mul_const (Real.log M))
    have h_lhs_int : Integrable (fun p : α × β ↦
        g p * Real.log (G p.1) + g p * Real.log (m p.2) -
          g p * Real.log M - g p * Real.log (g p)) (μ.prod ν) :=
      h_sum2_int.sub hglog
    have h_rhs_int : Integrable (fun p : α × β ↦ G p.1 * m p.2 / M - g p) (μ.prod ν) :=
      ((hG_int.mul_prod hm_int).div_const M).sub hg
    have hint_le := integral_mono_ae h_lhs_int h_rhs_int hpt
    have h_lhs_val : ∫ p, (g p * Real.log (G p.1) + g p * Real.log (m p.2) -
        g p * Real.log M - g p * Real.log (g p)) ∂(μ.prod ν) =
        (∫ x, G x * Real.log (G x) ∂μ) + (∫ y, m y * Real.log (m y) ∂ν) -
          M * Real.log M - ∫ p, g p * Real.log (g p) ∂(μ.prod ν) := by
      rw [integral_sub h_sum2_int hglog, integral_sub h_sum1_int (hg.mul_const (Real.log M)),
        integral_add h_glogG_int h_glogm_int, integral_mul_const, h_glogG_eq, h_glogm_eq]
    have h_GM : ∫ x, G x ∂μ = M := (integral_prod g hg).symm
    have h_mM : ∫ y, m y ∂ν = M := (integral_prod_symm g hg).symm
    have h_rhs_val : ∫ p, (G p.1 * m p.2 / M - g p) ∂(μ.prod ν) = 0 := by
      rw [integral_sub ((hG_int.mul_prod hm_int).div_const M) hg, integral_div,
        integral_prod_mul G m, h_GM, h_mM, mul_div_cancel_right₀ M hM_pos.ne']
      exact sub_self M
    rw [h_lhs_val, h_rhs_val] at hint_le
    simp only [entropy_def]
    rw [integral_sub hglog.integral_prod_right hmlog, ← integral_prod_symm _ hglog]
    dsimp only [G, m, M] at h_GM hint_le
    rw [h_GM]
    linarith

/-- **Convexity of functional entropy under marginal averaging.** Under probability measures `μ`
and `ν`, for any a.e. nonnegative integrable `g` on `μ.prod ν` with `g log g` integrable,
`Ent_μ(x ↦ ∫ y, g (x, y) ∂ν) ≤ ∫ y, Ent_μ(x ↦ g (x, y)) ∂ν`. -/
theorem entropy_integral_prod_le {g : α × β → ℝ}
    (hg0 : 0 ≤ᵐ[μ.prod ν] g) (hg : Integrable g (μ.prod ν))
    (hglog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) ≤ ∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν := by
  let g' : α × β → ℝ := fun p ↦ max 0 (hg.aestronglyMeasurable.mk g p)
  have hg'_meas : Measurable g' :=
    measurable_const.max hg.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hg'_nonneg (p : α × β) : 0 ≤ g' p := le_max_left 0 _
  have h_ae : g' =ᵐ[μ.prod ν] g := by
    filter_upwards [hg0, hg.aestronglyMeasurable.ae_eq_mk] with p hp0 hmk
    simpa [g', hmk] using max_eq_right hp0
  have hg'_int : Integrable g' (μ.prod ν) := hg.congr h_ae.symm
  have hg'log_int : Integrable (fun p ↦ g' p * Real.log (g' p)) (μ.prod ν) :=
    hglog.congr (h_ae.symm.mono fun _ hp ↦ by dsimp; rw [hp])
  have hG_ae : (fun x ↦ ∫ y, g' (x, y) ∂ν) =ᵐ[μ] fun x ↦ ∫ y, g (x, y) ∂ν := by
    filter_upwards [ae_ae_of_ae_prod h_ae] with x hx
    exact integral_congr_ae hx
  have hslice_ae : (fun y ↦ entropy μ (fun x ↦ g' (x, y))) =ᵐ[ν]
      fun y ↦ entropy μ (fun x ↦ g (x, y)) := by
    have hswap_ae : (g' ∘ Prod.swap) =ᵐ[ν.prod μ] (g ∘ Prod.swap) :=
      measurePreserving_swap.quasiMeasurePreserving.ae h_ae
    filter_upwards [ae_ae_of_ae_prod hswap_ae] with y hy
    exact entropy_congr_ae hy
  rw [← entropy_congr_ae hG_ae, ← integral_congr_ae hslice_ae]
  exact entropy_integral_prod_le_of_measurable hg'_meas hg'_nonneg hg'_int hg'log_int

/-- **Subadditivity of functional entropy on a binary product measure.** -/
theorem entropy_prod_le {g : α × β → ℝ}
    (hg0 : 0 ≤ᵐ[μ.prod ν] g) (hg : Integrable g (μ.prod ν))
    (hglog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    entropy (μ.prod ν) g ≤
      (∫ x, entropy ν (fun y ↦ g (x, y)) ∂μ) + ∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν := by
  rw [entropy_prod_eq hg0 hg hglog]
  linarith [entropy_integral_prod_le hg0 hg hglog]

end BinaryProduct

section FiniteProduct

universe u

/-- For an a.e. nonnegative integrable function `g` on `Measure.pi μ` with `g log g` integrable,
almost every one-coordinate slice `y ↦ g (Function.update x i y)` is nonnegative and has `g` and
`g log g` integrable under `μ i`. -/
theorem ae_integrable_mul_log_pi_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type u} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (i : ι) {g : (∀ j, α j) → ℝ}
    (hg0 : 0 ≤ᵐ[Measure.pi μ] g) (hg : Integrable g (Measure.pi μ))
    (hglog : Integrable (fun x ↦ g x * Real.log (g x)) (Measure.pi μ)) :
    ∀ᵐ x ∂Measure.pi μ,
      (0 ≤ᵐ[μ i] fun y ↦ g (Function.update x i y)) ∧
      Integrable (fun y ↦ g (Function.update x i y)) (μ i) ∧
      Integrable (fun y ↦ g (Function.update x i y) * Real.log (g (Function.update x i y)))
        (μ i) := by
  have hmp := TauCeti.measurePreserving_update_prod_pi μ i
  have h0' : 0 ≤ᵐ[(Measure.pi μ).prod (μ i)] fun p ↦ g (Function.update p.1 i p.2) :=
    hmp.quasiMeasurePreserving.ae hg0
  have hg' : Integrable (fun p : (∀ j, α j) × α i ↦ g (Function.update p.1 i p.2))
      ((Measure.pi μ).prod (μ i)) := hmp.integrable_comp_of_integrable hg
  have hglog' : Integrable (fun p : (∀ j, α j) × α i ↦
      g (Function.update p.1 i p.2) * Real.log (g (Function.update p.1 i p.2)))
      ((Measure.pi μ).prod (μ i)) := hmp.integrable_comp_of_integrable hglog
  filter_upwards [ae_ae_of_ae_prod h0', hg'.prod_right_ae, hglog'.prod_right_ae]
    with x hx0 hxg hxglog
  exact ⟨hx0, hxg, hxglog⟩

/-- On a finite product of probability measures, each coordinate slice entropy
`x ↦ entropy (μ i) (fun y ↦ g (Function.update x i y))` is `Measure.pi μ`-integrable. -/
theorem integrable_entropy_update_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type u} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (i : ι) {g : (∀ j, α j) → ℝ}
    (hg0 : 0 ≤ᵐ[Measure.pi μ] g) (hg : Integrable g (Measure.pi μ))
    (hglog : Integrable (fun x ↦ g x * Real.log (g x)) (Measure.pi μ)) :
    Integrable (fun x ↦ entropy (μ i) (fun y ↦ g (Function.update x i y))) (Measure.pi μ) := by
  have hmp := TauCeti.measurePreserving_update_prod_pi μ i
  exact integrable_entropy_prod_right (hmp.quasiMeasurePreserving.ae hg0)
    (hmp.integrable_comp_of_integrable hg) (hmp.integrable_comp_of_integrable hglog)

/-- Entropy subadditivity on `Measure.pi` over `Fin 0`. -/
private theorem entropy_pi_fin_zero {α : Fin 0 → Type u} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)] {g : (∀ i, α i) → ℝ} :
    entropy (Measure.pi μ) g ≤
      ∑ i, ∫ x, entropy (μ i) (fun y ↦ g (Function.update x i y)) ∂Measure.pi μ := by
  have hconst : g = fun _ ↦ g default := funext fun x ↦ congrArg g (Subsingleton.elim x default)
  rw [hconst, entropy_const]
  simp

/-- The expectation of the `0`-th coordinate slice entropy after `piFinSuccAbove` equals the `0`-th
summand on `Measure.pi μ`. -/
private theorem integral_entropy_piFinSuccAbove_symm_zero {n : ℕ} {α : Fin (n + 1) → Type u}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (g : (∀ i, α i) → ℝ) :
    ∫ w, entropy (μ 0) (fun a ↦ g ((MeasurableEquiv.piFinSuccAbove α 0).symm (a, w)))
        ∂(Measure.pi fun j ↦ μ (Fin.succAbove 0 j)) =
      ∫ x, entropy (μ 0) (fun y ↦ g (Function.update x 0 y)) ∂Measure.pi μ := by
  let e := MeasurableEquiv.piFinSuccAbove α 0
  have mps := (measurePreserving_piFinSuccAbove μ 0).symm e
  let H : (∀ i, α i) → ℝ := fun x ↦ entropy (μ 0) (fun y ↦ g (Function.update x 0 y))
  by_cases hHi : Integrable H (Measure.pi μ)
  · have hHp : Integrable (fun p ↦ H (e.symm p))
        ((μ 0).prod (Measure.pi fun j ↦ μ (Fin.succAbove 0 j))) :=
      mps.integrable_comp_of_integrable hHi
    have hcomp_eq := mps.integral_comp e.symm.measurableEmbedding H
    have hprod_eq := integral_prod_symm (fun p ↦ H (e.symm p)) hHp
    rw [← hcomp_eq, hprod_eq]
    refine integral_congr_ae (.of_forall fun w ↦ ?_)
    have hconst (a : α 0) :
        H (e.symm (a, w)) = entropy (μ 0) (fun y ↦ g (e.symm (y, w))) := by
      simp only [H, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
        Fin.update_insertNth]
    simp_rw [hconst, integral_const, probReal_univ, one_smul]
    rfl
  · -- If `H` is not integrable, both Bochner integrals vanish.
    have h_not_int_w : ¬ Integrable (fun w ↦ entropy (μ 0) (fun a ↦ g (e.symm (a, w))))
        (Measure.pi fun j ↦ μ (Fin.succAbove 0 j)) := by
      intro hw
      apply hHi
      have hHp : Integrable (fun p : α 0 × (∀ j, α (Fin.succAbove 0 j)) ↦ H (e.symm p))
          ((μ 0).prod (Measure.pi fun j ↦ μ (Fin.succAbove 0 j))) := by
        have heq : (fun p : α 0 × (∀ j, α (Fin.succAbove 0 j)) ↦ H (e.symm p)) =
            fun p ↦ (1 : ℝ) * entropy (μ 0) (fun y ↦ g (e.symm (y, p.2))) := by
          funext p
          simp only [one_mul, H, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv_apply, Fin.update_insertNth]
        rw [heq]
        exact (integrable_const (1 : ℝ)).mul_prod hw
      exact (mps.integrable_comp_emb e.symm.measurableEmbedding).1 hHp
    -- Unfold the let-bindings `e` and `H` so both sides match `integral_undef`.
    dsimp only [e, H] at h_not_int_w hHi
    rw [integral_undef h_not_int_w, integral_undef hHi]

/-- Entropy subadditivity on `Measure.pi` over `Fin n` for measurable nonnegative functions. -/
private theorem entropy_pi_fin : ∀ {n : ℕ} {α : Fin n → Type u} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)] {g : (∀ i, α i) → ℝ},
    Measurable g → (∀ x, 0 ≤ g x) → Integrable g (Measure.pi μ) →
    Integrable (fun x ↦ g x * Real.log (g x)) (Measure.pi μ) →
    entropy (Measure.pi μ) g ≤
      ∑ i, ∫ x, entropy (μ i) (fun y ↦ g (Function.update x i y)) ∂Measure.pi μ
  | 0, _, _, μ, _, _, _, _, _, _ => entropy_pi_fin_zero μ
  | n + 1, α, _, μ, _, g, hgm, hg0, hg, hglog => by
    let e := MeasurableEquiv.piFinSuccAbove α 0
    have mps := (measurePreserving_piFinSuccAbove μ 0).symm e
    let ν := Measure.pi fun j ↦ μ (Fin.succAbove 0 j)
    let F : α 0 × (∀ j, α (Fin.succAbove 0 j)) → ℝ := fun p ↦ g (e.symm p)
    have hFm : Measurable F := hgm.comp e.symm.measurable
    have hF0 (p : α 0 × (∀ j, α (Fin.succAbove 0 j))) : 0 ≤ F p := hg0 (e.symm p)
    have hF_int : Integrable F ((μ 0).prod ν) := mps.integrable_comp_of_integrable hg
    have hFlog_int : Integrable (fun p ↦ F p * Real.log (F p)) ((μ 0).prod ν) :=
      mps.integrable_comp_of_integrable hglog
    let H : Fin (n + 1) → (∀ i, α i) → ℝ :=
      fun i x ↦ entropy (μ i) (fun y ↦ g (Function.update x i y))
    have hHi (i : Fin (n + 1)) : Integrable (H i) (Measure.pi μ) :=
      integrable_entropy_update_pi μ i (.of_forall hg0) hg hglog
    have hEnt : entropy (Measure.pi μ) g = entropy ((μ 0).prod ν) F :=
      (mps.entropy_comp hgm.aestronglyMeasurable).symm
    have hH_eq (j : Fin n) (a : α 0) (w : ∀ j, α (Fin.succAbove 0 j)) :
        entropy (μ (Fin.succAbove 0 j)) (fun y ↦ F (a, Function.update w j y)) =
          H (Fin.succAbove 0 j) (e.symm (a, w)) := by
      simp only [F, H, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv_apply, Fin.insertNth_update]
    have hHp_int (j : Fin n) :
        Integrable (fun p ↦ H (Fin.succAbove 0 j) (e.symm p)) ((μ 0).prod ν) :=
      mps.integrable_comp_of_integrable (hHi (Fin.succAbove 0 j))
    have h1 : (∫ a, entropy ν (fun w ↦ F (a, w)) ∂μ 0) ≤
        ∑ j : Fin n, ∫ x, H (Fin.succAbove 0 j) x ∂Measure.pi μ := by
      have h_rhs_int : Integrable
          (fun a ↦ ∑ j : Fin n, ∫ w, H (Fin.succAbove 0 j) (e.symm (a, w)) ∂ν) (μ 0) :=
        integrable_finsetSum _ fun j _ ↦ (hHp_int j).integral_prod_left
      calc (∫ a, entropy ν (fun w ↦ F (a, w)) ∂μ 0)
          ≤ ∫ a, (∑ j : Fin n, ∫ w, H (Fin.succAbove 0 j) (e.symm (a, w)) ∂ν) ∂μ 0 := by
            refine integral_mono_ae
              (integrable_entropy_prod_right (.of_forall hF0) hF_int hFlog_int) h_rhs_int ?_
            filter_upwards [hF_int.prod_right_ae, hFlog_int.prod_right_ae] with a ha ha_log
            have hih := entropy_pi_fin (α := fun j ↦ α (Fin.succAbove 0 j))
              (fun j ↦ μ (Fin.succAbove 0 j)) (g := fun w ↦ F (a, w))
              (hFm.comp measurable_prodMk_left) (fun w ↦ hF0 (a, w)) ha ha_log
            simpa only [hH_eq] using hih
        _ = ∑ j : Fin n, ∫ a, ∫ w, H (Fin.succAbove 0 j) (e.symm (a, w)) ∂ν ∂μ 0 :=
            integral_finsetSum _ fun j _ ↦ (hHp_int j).integral_prod_left
        _ = ∑ j : Fin n, ∫ x, H (Fin.succAbove 0 j) x ∂Measure.pi μ :=
            Finset.sum_congr rfl fun j _ ↦ by
              rw [← integral_prod (fun p ↦ H (Fin.succAbove 0 j) (e.symm p)) (hHp_int j),
                mps.integral_comp e.symm.measurableEmbedding (H (Fin.succAbove 0 j))]
    have h2 : (∫ w, entropy (μ 0) (fun a ↦ F (a, w)) ∂ν) = ∫ x, H 0 x ∂Measure.pi μ :=
      integral_entropy_piFinSuccAbove_symm_zero μ g
    calc entropy (Measure.pi μ) g
        = entropy ((μ 0).prod ν) F := hEnt
      _ ≤ (∫ a, entropy ν (fun w ↦ F (a, w)) ∂μ 0) +
            ∫ w, entropy (μ 0) (fun a ↦ F (a, w)) ∂ν :=
          entropy_prod_le (.of_forall hF0) hF_int hFlog_int
      _ ≤ (∑ j : Fin n, ∫ x, H (Fin.succAbove 0 j) x ∂Measure.pi μ) +
            ∫ x, H 0 x ∂Measure.pi μ := add_le_add h1 h2.le
      _ = ∑ i, ∫ x, H i x ∂Measure.pi μ := by rw [Fin.sum_univ_succAbove _ 0, add_comm]

/-- **Subadditivity (tensorization) of functional entropy** on `Measure.pi` over an arbitrary
finite index type: for an a.e. nonnegative integrable function `g` of independent coordinates with
`g log g` integrable, `Ent(g) ≤ ∑ i, E[Ent_{μ i}(y ↦ g (Function.update x i y))]`. -/
theorem entropy_pi_le_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type u}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    {g : (∀ i, α i) → ℝ} (hg0 : 0 ≤ᵐ[Measure.pi μ] g) (hg : Integrable g (Measure.pi μ))
    (hglog : Integrable (fun x ↦ g x * Real.log (g x)) (Measure.pi μ)) :
    entropy (Measure.pi μ) g ≤
      ∑ i, ∫ x, entropy (μ i) (fun y ↦ g (Function.update x i y)) ∂Measure.pi μ := by
  let g' : (∀ i, α i) → ℝ := fun x ↦ max 0 (hg.aestronglyMeasurable.mk g x)
  have hg'_meas : Measurable g' :=
    measurable_const.max hg.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hg'_nonneg (x : ∀ i, α i) : 0 ≤ g' x := le_max_left 0 _
  have h_ae : g' =ᵐ[Measure.pi μ] g := by
    filter_upwards [hg0, hg.aestronglyMeasurable.ae_eq_mk] with x hx0 hmk
    simpa [g', hmk] using max_eq_right hx0
  have hg'_int : Integrable g' (Measure.pi μ) := hg.congr h_ae.symm
  have hg'log_int : Integrable (fun x ↦ g' x * Real.log (g' x)) (Measure.pi μ) :=
    hglog.congr (h_ae.symm.mono fun _ hx ↦ by dsimp; rw [hx])
  have hslice_eq (i : ι) :
      (∫ x, entropy (μ i) (fun y ↦ g' (Function.update x i y)) ∂Measure.pi μ) =
        ∫ x, entropy (μ i) (fun y ↦ g (Function.update x i y)) ∂Measure.pi μ := by
    apply integral_congr_ae
    have hmp := TauCeti.measurePreserving_update_prod_pi μ i
    filter_upwards [ae_ae_of_ae_prod (hmp.quasiMeasurePreserving.ae h_ae)] with x hx
    exact entropy_congr_ae hx
  rw [← entropy_congr_ae h_ae]
  simp_rw [← hslice_eq]
  -- Transport from `Fin (Fintype.card ι)` to `ι` along `MeasurableEquiv.piCongrLeft`.
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let Φ := MeasurableEquiv.piCongrLeft α e
  have mp : MeasurePreserving Φ (Measure.pi fun k ↦ μ (e k)) (Measure.pi μ) :=
    measurePreserving_piCongrLeft μ e
  have hupd (k : Fin (Fintype.card ι)) (y : ∀ k, α (e k)) (v : α (e k)) :
      Φ (Function.update y k v) = Function.update (Φ y) (e k) v := by
    simpa [Φ, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft] using
      Function.piCongrLeft'_symm_update α e.symm y k v
  have hterm (k : Fin (Fintype.card ι)) :
      (∫ y, entropy (μ (e k)) (fun v ↦ g' (Φ (Function.update y k v)))
          ∂Measure.pi (fun k ↦ μ (e k))) =
        ∫ x, entropy (μ (e k)) (fun v ↦ g' (Function.update x (e k) v)) ∂Measure.pi μ := by
    simp_rw [hupd]
    exact mp.integral_comp Φ.measurableEmbedding
      (fun x ↦ entropy (μ (e k)) (fun v ↦ g' (Function.update x (e k) v)))
  calc entropy (Measure.pi μ) g'
      = entropy (Measure.pi fun k ↦ μ (e k)) (g' ∘ Φ) :=
        (mp.entropy_comp hg'_meas.aestronglyMeasurable).symm
    _ ≤ ∑ k, ∫ y, entropy (μ (e k)) (fun v ↦ g' (Φ (Function.update y k v)))
          ∂Measure.pi (fun k ↦ μ (e k)) :=
        entropy_pi_fin (α := fun k ↦ α (e k)) (fun k ↦ μ (e k)) (g := g' ∘ Φ)
          (hg'_meas.comp Φ.measurable) (fun y ↦ hg'_nonneg (Φ y))
          (mp.integrable_comp_of_integrable hg'_int)
          (mp.integrable_comp_of_integrable hg'log_int)
    _ = ∑ k, ∫ x, entropy (μ (e k)) (fun v ↦ g' (Function.update x (e k) v)) ∂Measure.pi μ :=
        Finset.sum_congr rfl fun k _ ↦ hterm k
    _ = ∑ i, ∫ x, entropy (μ i) (fun y ↦ g' (Function.update x i y)) ∂Measure.pi μ :=
        Equiv.sum_comp e fun i ↦
          ∫ x, entropy (μ i) (fun y ↦ g' (Function.update x i y)) ∂Measure.pi μ

end FiniteProduct

end MeasureTheory.Measure

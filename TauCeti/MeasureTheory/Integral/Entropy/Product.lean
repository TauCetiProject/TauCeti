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

/-- Replace an a.e. nonnegative integrable function by an everywhere-nonnegative measurable
representative that is a.e. equal to it and preserves integrability of `g` and `g log g`. -/
private theorem exists_measurable_nonneg_ae_eq {α : Type*} {mα : MeasurableSpace α}
    {μ : Measure α} {g : α → ℝ} (hg0 : 0 ≤ᵐ[μ] g) (hg : Integrable g μ)
    (hglog : Integrable (fun x ↦ g x * Real.log (g x)) μ) :
    ∃ g' : α → ℝ, Measurable g' ∧ (∀ x, 0 ≤ g' x) ∧ g' =ᵐ[μ] g ∧ Integrable g' μ ∧
      Integrable (fun x ↦ g' x * Real.log (g' x)) μ := by
  let g' : α → ℝ := fun x ↦ max 0 (hg.aestronglyMeasurable.mk g x)
  have h_ae : g' =ᵐ[μ] g := by
    filter_upwards [hg0, hg.aestronglyMeasurable.ae_eq_mk] with x hx0 hmk
    simpa [g', hmk] using max_eq_right hx0
  exact ⟨g', measurable_const.max hg.aestronglyMeasurable.stronglyMeasurable_mk.measurable,
    fun _ ↦ le_max_left 0 _, h_ae, hg.congr h_ae.symm,
    hglog.congr (h_ae.symm.mono fun _ hx ↦ by simp only [hx])⟩

section BinaryProduct

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- If `g ≥ 0` a.e. on `μ.prod ν` with `g` and `g log g` integrable, then `G x * log (G x)` is
`μ`-integrable for the marginal average `G x = ∫ y, g (x, y) ∂ν`. -/
theorem integrable_mul_log_integral_prod_left {g : α × β → ℝ}
    (hg0 : 0 ≤ᵐ[μ.prod ν] g) (hg : Integrable g (μ.prod ν))
    (hglog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    Integrable (fun x ↦ (∫ y, g (x, y) ∂ν) * Real.log (∫ y, g (x, y) ∂ν)) μ := by
  refine ((integrable_const 1).add hglog.integral_prod_left.norm).mono'
    (Real.continuous_mul_log.comp_aestronglyMeasurable
      hg.aestronglyMeasurable.integral_prod_right') ?_
  filter_upwards [ae_ae_of_ae_prod hg0, hg.prod_right_ae, hglog.prod_right_ae]
    with x hx0 hxg hxglog
  have hlow := TauCeti.neg_one_le_mul_log (integral_nonneg_of_ae hx0)
  have hhigh := Real.convexOn_mul_log.map_integral_le Real.continuous_mul_log.continuousOn
    isClosed_Ici hx0 hxg hxglog
  simp only [Pi.add_apply, Real.norm_eq_abs]
  exact abs_le.2 ⟨by linarith [abs_nonneg (∫ y, g (x, y) * Real.log (g (x, y)) ∂ν)],
    by linarith [le_abs_self (∫ y, g (x, y) * Real.log (g (x, y)) ∂ν)]⟩

/-- Symmetric version of `integrable_mul_log_integral_prod_left` for the second-coordinate
marginal `m y = ∫ x, g (x, y) ∂μ`. -/
theorem integrable_mul_log_integral_prod_right {g : α × β → ℝ}
    (hg0 : 0 ≤ᵐ[μ.prod ν] g) (hg : Integrable g (μ.prod ν))
    (hglog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    Integrable (fun y ↦ (∫ x, g (x, y) ∂μ) * Real.log (∫ x, g (x, y) ∂μ)) ν :=
  integrable_mul_log_integral_prod_left
    (measurePreserving_swap.quasiMeasurePreserving.ae hg0)
    (measurePreserving_swap.integrable_comp_of_integrable hg)
    (measurePreserving_swap.integrable_comp_of_integrable hglog)

/-- Under `μ.prod ν`, the slice entropy `x ↦ entropy ν (fun y ↦ g (x, y))` is `μ`-integrable. -/
theorem integrable_entropy_prod_left {g : α × β → ℝ}
    (hg0 : 0 ≤ᵐ[μ.prod ν] g) (hg : Integrable g (μ.prod ν))
    (hglog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    Integrable (fun x ↦ entropy ν (fun y ↦ g (x, y))) μ := by
  simp_rw [entropy_def]
  exact hglog.integral_prod_left.sub (integrable_mul_log_integral_prod_left hg0 hg hglog)

/-- Under `μ.prod ν`, the slice entropy `y ↦ entropy μ (fun x ↦ g (x, y))` is `ν`-integrable. -/
theorem integrable_entropy_prod_right {g : α × β → ℝ}
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
  simp only [entropy_def]
  rw [integral_sub hglog.integral_prod_left (integrable_mul_log_integral_prod_left hg0 hg hglog),
    integral_prod _ hglog, integral_prod _ hg]
  ring

private theorem integrable_and_integral_mul_log_marginal_fst {g : α × β → ℝ}
    (hgm : Measurable g) (hg0 : ∀ p, 0 ≤ g p) (hg : Integrable g (μ.prod ν))
    (hglog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    Integrable (fun p : α × β ↦ g p * Real.log (∫ y, g (p.1, y) ∂ν)) (μ.prod ν) ∧
      (∫ p, g p * Real.log (∫ y, g (p.1, y) ∂ν) ∂(μ.prod ν)) =
        ∫ x, (∫ y, g (x, y) ∂ν) * Real.log (∫ y, g (x, y) ∂ν) ∂μ := by
  let G : α → ℝ := fun x ↦ ∫ y, g (x, y) ∂ν
  have hGm : Measurable G := hgm.stronglyMeasurable.integral_prod_right'.measurable
  have hint : Integrable (fun p : α × β ↦ g p * Real.log (G p.1)) (μ.prod ν) := by
    refine (integrable_prod_iff (hgm.mul (Real.measurable_log.comp
      (hGm.comp measurable_fst))).aestronglyMeasurable).2 ⟨?_, ?_⟩
    · filter_upwards [hg.prod_right_ae] with x hx using hx.mul_const (Real.log (G x))
    · refine (integrable_mul_log_integral_prod_left (.of_forall hg0) hg hglog).norm.congr ?_
      filter_upwards [hg.prod_right_ae] with x _
      simp only [Real.norm_eq_abs, Pi.mul_apply, Function.comp_apply, G]
      have hcongr : (fun y ↦ |g (x, y) * Real.log (∫ z, g (x, z) ∂ν)|) =
          fun y ↦ g (x, y) * |Real.log (∫ z, g (x, z) ∂ν)| :=
        funext fun y ↦ by rw [abs_mul, abs_of_nonneg (hg0 (x, y))]
      rw [abs_mul, abs_of_nonneg (integral_nonneg fun y ↦ hg0 (x, y)), hcongr, integral_mul_const]
  exact ⟨hint, by
    rw [integral_prod _ hint]
    exact integral_congr_ae (.of_forall fun x ↦ integral_mul_const (Real.log (G x)) _)⟩

private theorem integrable_and_integral_mul_log_marginal_snd {g : α × β → ℝ}
    (hgm : Measurable g) (hg0 : ∀ p, 0 ≤ g p) (hg : Integrable g (μ.prod ν))
    (hglog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    Integrable (fun p : α × β ↦ g p * Real.log (∫ x, g (x, p.2) ∂μ)) (μ.prod ν) ∧
      (∫ p, g p * Real.log (∫ x, g (x, p.2) ∂μ) ∂(μ.prod ν)) =
        ∫ y, (∫ x, g (x, y) ∂μ) * Real.log (∫ x, g (x, y) ∂μ) ∂ν := by
  obtain ⟨hint, heq⟩ :=
    integrable_and_integral_mul_log_marginal_fst (hgm.comp measurable_swap)
      (fun q ↦ hg0 (Prod.swap q)) (measurePreserving_swap.integrable_comp_of_integrable hg)
      (measurePreserving_swap.integrable_comp_of_integrable hglog)
  exact ⟨measurePreserving_swap.integrable_comp_of_integrable hint, by
    rw [← integral_prod_swap (fun p : α × β ↦ g p * Real.log (∫ x, g (x, p.2) ∂μ))]; exact heq⟩

private theorem ae_eq_zero_of_integral_fst_eq_zero {g : α × β → ℝ}
    (hgm : Measurable g) (hg0 : ∀ p, 0 ≤ g p) (hg : Integrable g (μ.prod ν)) :
    ∀ᵐ p ∂(μ.prod ν), (∫ y, g (p.1, y) ∂ν) = 0 → g p = 0 := by
  let G : α → ℝ := fun x ↦ ∫ y, g (x, y) ∂ν
  have hGm : Measurable G := hgm.stronglyMeasurable.integral_prod_right'.measurable
  have hmset : MeasurableSet {p : α × β | G p.1 = 0 → g p = 0} := by
    rw [show {p : α × β | G p.1 = 0 → g p = 0} =
        {p : α × β | (G ∘ Prod.fst) p = 0}ᶜ ∪ {p : α × β | g p = 0} from
      Set.ext fun _ ↦ imp_iff_not_or]
    exact (measurableSet_eq_fun (hGm.comp measurable_fst) measurable_const).compl.union
      (measurableSet_eq_fun hgm measurable_const)
  rw [ae_prod_iff_ae_ae hmset]
  filter_upwards [hg.prod_right_ae] with x hx
  by_cases hGx : G x = 0
  · filter_upwards [(integral_eq_zero_iff_of_nonneg (fun y ↦ hg0 (x, y)) hx).1 hGx]
      with y hy _ using hy
  · exact .of_forall fun _ h ↦ absurd h hGx

/-- Zero-mass case of `entropy_integral_prod_le_of_measurable`: when the total integral vanishes,
`g` vanishes `μ.prod ν`-a.e., so both sides vanish. -/
private theorem entropy_integral_prod_le_of_integral_eq_zero {g : α × β → ℝ}
    (hg0 : ∀ p, 0 ≤ g p) (hg : Integrable g (μ.prod ν))
    (hM : ∫ p, g p ∂(μ.prod ν) = 0) :
    entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) ≤ ∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν := by
  have hgae : g =ᵐ[μ.prod ν] 0 := (integral_eq_zero_iff_of_nonneg hg0 hg).1 hM
  have hGae : (fun x ↦ ∫ y, g (x, y) ∂ν) =ᵐ[μ] 0 :=
    (ae_ae_of_ae_prod hgae).mono fun _ hx ↦ by simpa using integral_congr_ae hx
  have hslice_ae : (fun y ↦ entropy μ (fun x ↦ g (x, y))) =ᵐ[ν] 0 :=
    (ae_ae_of_ae_prod (measurePreserving_swap.quasiMeasurePreserving.ae hgae)).mono fun _ hy ↦ by
      simpa using entropy_congr_ae (μ := μ) hy
  rw [entropy_congr_ae hGae, Pi.zero_def, entropy_zero, integral_congr_ae hslice_ae,
    Pi.zero_def, integral_zero]

/-- Pointwise Klein bound comparing `g` against the rank-one product `G p.1 * m p.2 / M` of its
marginals when the total mass `M` is positive. -/
private theorem ae_mul_log_marginal_sub_le {g : α × β → ℝ}
    (hgm : Measurable g) (hg0 : ∀ p, 0 ≤ g p) (hg : Integrable g (μ.prod ν))
    (hM_pos : 0 < ∫ p, g p ∂(μ.prod ν)) :
    ∀ᵐ p ∂(μ.prod ν),
      g p * Real.log (∫ y, g (p.1, y) ∂ν) + g p * Real.log (∫ x, g (x, p.2) ∂μ) -
        g p * Real.log (∫ q, g q ∂(μ.prod ν)) - g p * Real.log (g p) ≤
      (∫ y, g (p.1, y) ∂ν) * (∫ x, g (x, p.2) ∂μ) / (∫ q, g q ∂(μ.prod ν)) - g p := by
  have hae_m : ∀ᵐ p ∂(μ.prod ν), (∫ x, g (x, p.2) ∂μ) = 0 → g p = 0 :=
    measurePreserving_swap.quasiMeasurePreserving.ae <|
      ae_eq_zero_of_integral_fst_eq_zero (hgm.comp measurable_swap)
        (fun q ↦ hg0 (Prod.swap q)) (measurePreserving_swap.integrable_comp_of_integrable hg)
  filter_upwards [ae_eq_zero_of_integral_fst_eq_zero hgm hg0 hg, hae_m] with p hpG hpm
  have hG0 : 0 ≤ ∫ y, g (p.1, y) ∂ν := integral_nonneg fun y ↦ hg0 (p.1, y)
  have hm0 : 0 ≤ ∫ x, g (x, p.2) ∂μ := integral_nonneg fun x ↦ hg0 (x, p.2)
  rcases (hg0 p).eq_or_lt with hgp0 | hgp_pos
  · simp only [← hgp0, zero_mul, add_zero, sub_zero]
    exact div_nonneg (mul_nonneg hG0 hm0) hM_pos.le
  · have hGp : 0 < ∫ y, g (p.1, y) ∂ν := lt_of_le_of_ne hG0 fun h0 ↦ hgp_pos.ne' (hpG h0.symm)
    have hmp : 0 < ∫ x, g (x, p.2) ∂μ := lt_of_le_of_ne hm0 fun h0 ↦ hgp_pos.ne' (hpm h0.symm)
    have hq := div_pos (mul_pos hGp hmp) hM_pos
    have hklein := Real.sub_le_mul_log_sub_mul_log (hg0 p) hq.le (fun h0 ↦ absurd h0 hq.ne')
    rw [Real.log_div (mul_pos hGp hmp).ne' hM_pos.ne', Real.log_mul hGp.ne' hmp.ne'] at hklein
    linarith

/-- Measurable, everywhere-nonnegative core of `entropy_integral_prod_le`. -/
private theorem entropy_integral_prod_le_of_measurable {g : α × β → ℝ}
    (hgm : Measurable g) (hg0 : ∀ p, 0 ≤ g p) (hg : Integrable g (μ.prod ν))
    (hglog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) ≤ ∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν := by
  let G : α → ℝ := fun x ↦ ∫ y, g (x, y) ∂ν
  let m : β → ℝ := fun y ↦ ∫ x, g (x, y) ∂μ
  let M : ℝ := ∫ p, g p ∂(μ.prod ν)
  -- Degenerate case `M = 0`: `g` vanishes a.e.
  rcases (integral_nonneg hg0 : 0 ≤ M).eq_or_lt with hM_zero | hM_pos
  · exact entropy_integral_prod_le_of_integral_eq_zero hg0 hg hM_zero.symm
  -- Positive-mass case: integrate the pointwise Klein bound against `G p.1 * m p.2 / M` and
  -- evaluate the left-hand and right-hand product integrals separately.
  obtain ⟨h_glogG_int, h_glogG_eq⟩ :=
    integrable_and_integral_mul_log_marginal_fst hgm hg0 hg hglog
  obtain ⟨h_glogm_int, h_glogm_eq⟩ :=
    integrable_and_integral_mul_log_marginal_snd hgm hg0 hg hglog
  have h_sum1 : Integrable (fun p ↦ g p * Real.log (G p.1) + g p * Real.log (m p.2)) (μ.prod ν) :=
    h_glogG_int.add h_glogm_int
  have h_sum2 : Integrable (fun p ↦
      g p * Real.log (G p.1) + g p * Real.log (m p.2) - g p * Real.log M) (μ.prod ν) :=
    h_sum1.sub (hg.mul_const (Real.log M))
  have h_rhs : Integrable (fun p : α × β ↦ G p.1 * m p.2 / M) (μ.prod ν) :=
    (hg.integral_prod_left.mul_prod hg.integral_prod_right).div_const M
  have hint_le : ∫ p, (g p * Real.log (G p.1) + g p * Real.log (m p.2) -
      g p * Real.log M - g p * Real.log (g p)) ∂(μ.prod ν) ≤
      ∫ p, (G p.1 * m p.2 / M - g p) ∂(μ.prod ν) :=
    integral_mono_ae (h_sum2.sub hglog) (h_rhs.sub hg)
      (ae_mul_log_marginal_sub_le hgm hg0 hg hM_pos)
  have hlhs : ∫ p, (g p * Real.log (G p.1) + g p * Real.log (m p.2) -
      g p * Real.log M - g p * Real.log (g p)) ∂(μ.prod ν) =
      (∫ x, G x * Real.log (G x) ∂μ) + (∫ y, m y * Real.log (m y) ∂ν) -
        M * Real.log M - ∫ p, g p * Real.log (g p) ∂(μ.prod ν) := by
    rw [integral_sub h_sum2 hglog, integral_sub h_sum1 (hg.mul_const _),
      integral_add h_glogG_int h_glogm_int, integral_mul_const]
    rw [h_glogG_eq, h_glogm_eq]
  have h_GM : ∫ x, G x ∂μ = M := (integral_prod g hg).symm
  have h_mM : ∫ y, m y ∂ν = M := (integral_prod_symm g hg).symm
  have hrhs : ∫ p, (G p.1 * m p.2 / M - g p) ∂(μ.prod ν) = 0 := by
    rw [integral_sub h_rhs hg, integral_div, integral_prod_mul G m, h_GM, h_mM]
    exact sub_eq_zero.2 (mul_div_cancel_right₀ M hM_pos.ne')
  rw [hlhs, hrhs] at hint_le
  simp only [entropy_def]
  rw [integral_sub hglog.integral_prod_right
    (integrable_mul_log_integral_prod_right (.of_forall hg0) hg hglog),
    ← integral_prod_symm _ hglog, h_GM]
  linarith

/-- **Convexity of functional entropy under marginal averaging.** Under probability measures `μ`
and `ν`, for any a.e. nonnegative integrable `g` on `μ.prod ν` with `g log g` integrable,
`Ent_μ(x ↦ ∫ y, g (x, y) ∂ν) ≤ ∫ y, Ent_μ(x ↦ g (x, y)) ∂ν`. -/
theorem entropy_integral_prod_le {g : α × β → ℝ}
    (hg0 : 0 ≤ᵐ[μ.prod ν] g) (hg : Integrable g (μ.prod ν))
    (hglog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) ≤ ∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν := by
  obtain ⟨g', hg'm, hg'0, h_ae, hg'i, hg'li⟩ := exists_measurable_nonneg_ae_eq hg0 hg hglog
  have hG_ae : (fun x ↦ ∫ y, g' (x, y) ∂ν) =ᵐ[μ] fun x ↦ ∫ y, g (x, y) ∂ν :=
    (ae_ae_of_ae_prod h_ae).mono fun _ hx ↦ integral_congr_ae hx
  have hslice_ae : (fun y ↦ entropy μ (fun x ↦ g' (x, y))) =ᵐ[ν]
      fun y ↦ entropy μ (fun x ↦ g (x, y)) :=
    (ae_ae_of_ae_prod (measurePreserving_swap.quasiMeasurePreserving.ae h_ae)).mono
      fun _ hy ↦ entropy_congr_ae hy
  rw [← entropy_congr_ae hG_ae, ← integral_congr_ae hslice_ae]
  exact entropy_integral_prod_le_of_measurable hg'm hg'0 hg'i hg'li

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

section SliceIntegrability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type u} [∀ i, MeasurableSpace (α i)]
  (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- For an a.e. nonnegative integrable function `g` on `Measure.pi μ` with `g log g` integrable,
almost every one-coordinate slice `y ↦ g (Function.update x i y)` is nonnegative and has `g` and
`g log g` integrable under `μ i`. -/
theorem ae_integrable_mul_log_pi_update (i : ι) {g : (∀ j, α j) → ℝ}
    (hg0 : 0 ≤ᵐ[Measure.pi μ] g) (hg : Integrable g (Measure.pi μ))
    (hglog : Integrable (fun x ↦ g x * Real.log (g x)) (Measure.pi μ)) :
    ∀ᵐ x ∂Measure.pi μ,
      (0 ≤ᵐ[μ i] fun y ↦ g (Function.update x i y)) ∧
      Integrable (fun y ↦ g (Function.update x i y)) (μ i) ∧
      Integrable (fun y ↦ g (Function.update x i y) * Real.log (g (Function.update x i y)))
        (μ i) := by
  have hmp := TauCeti.measurePreserving_update_prod_pi μ i
  filter_upwards [ae_ae_of_ae_prod (hmp.quasiMeasurePreserving.ae hg0),
    (hmp.integrable_comp_of_integrable hg).prod_right_ae,
    (hmp.integrable_comp_of_integrable hglog).prod_right_ae] with x hx0 hxg hxglog
  exact ⟨hx0, hxg, hxglog⟩

/-- On a finite product of probability measures, each coordinate slice entropy
`x ↦ entropy (μ i) (fun y ↦ g (Function.update x i y))` is `Measure.pi μ`-integrable. -/
theorem integrable_entropy_update_pi (i : ι) {g : (∀ j, α j) → ℝ}
    (hg0 : 0 ≤ᵐ[Measure.pi μ] g) (hg : Integrable g (Measure.pi μ))
    (hglog : Integrable (fun x ↦ g x * Real.log (g x)) (Measure.pi μ)) :
    Integrable (fun x ↦ entropy (μ i) (fun y ↦ g (Function.update x i y))) (Measure.pi μ) :=
  have hmp := TauCeti.measurePreserving_update_prod_pi μ i
  integrable_entropy_prod_left (hmp.quasiMeasurePreserving.ae hg0)
    (hmp.integrable_comp_of_integrable hg) (hmp.integrable_comp_of_integrable hglog)

end SliceIntegrability

/-- Under `Measure.pi μ` on `Fin (n + 1)`, the `μ 0`-entropy averaged over the remaining
coordinates equals the `i = 0` coordinate-refresh entropy integral. -/
private theorem integral_entropy_piFinSuccAbove_symm_zero {n : ℕ} {α : Fin (n + 1) → Type u}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    {g : (∀ i, α i) → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hg : Integrable g (Measure.pi μ))
    (hglog : Integrable (fun x ↦ g x * Real.log (g x)) (Measure.pi μ)) :
    (∫ w, entropy (μ 0) (fun a ↦ g ((MeasurableEquiv.piFinSuccAbove α 0).symm (a, w)))
        ∂Measure.pi (fun j ↦ μ (Fin.succAbove 0 j))) =
      ∫ x, entropy (μ 0) (fun y ↦ g (Function.update x 0 y)) ∂Measure.pi μ := by
  let e := MeasurableEquiv.piFinSuccAbove α 0
  have mps := (measurePreserving_piFinSuccAbove μ 0).symm e
  let H0 : (∀ i, α i) → ℝ := fun x ↦ entropy (μ 0) (fun y ↦ g (Function.update x 0 y))
  have hH0 : Integrable H0 (Measure.pi μ) :=
    integrable_entropy_update_pi μ 0 (.of_forall hg0) hg hglog
  rw [← mps.integral_comp e.symm.measurableEmbedding H0,
    integral_prod_symm (fun p ↦ H0 (e.symm p)) (mps.integrable_comp_of_integrable hH0)]
  refine integral_congr_ae (.of_forall fun w ↦ ?_)
  have hc (a : α 0) :
      H0 (e.symm (a, w)) =
        entropy (μ 0) (fun y ↦ g ((MeasurableEquiv.piFinSuccAbove α 0).symm (y, w))) := by
    simp only [H0, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
      Fin.update_insertNth]
  simp_rw [hc, integral_const, probReal_univ, one_smul]

/-- Entropy subadditivity on `Measure.pi` over `Fin n` for measurable nonnegative functions. -/
private theorem entropy_pi_fin : ∀ {n : ℕ} {α : Fin n → Type u} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)] {g : (∀ i, α i) → ℝ},
    Measurable g → (∀ x, 0 ≤ g x) → Integrable g (Measure.pi μ) →
    Integrable (fun x ↦ g x * Real.log (g x)) (Measure.pi μ) →
    entropy (Measure.pi μ) g ≤
      ∑ i, ∫ x, entropy (μ i) (fun y ↦ g (Function.update x i y)) ∂Measure.pi μ
  | 0, _, _, _, _, g, _, _, _, _ => by
    rw [show g = fun _ ↦ g default from funext fun x ↦ congrArg g (Subsingleton.elim x default),
      entropy_const]; simp
  | n + 1, α, _, μ, _, g, hgm, hg0, hg, hglog => by
    -- Split off coordinate `0` via `piFinSuccAbove`, reducing `Measure.pi μ` to `(μ 0).prod ν`.
    let e := MeasurableEquiv.piFinSuccAbove α 0
    have mps := (measurePreserving_piFinSuccAbove μ 0).symm e
    let ν := Measure.pi fun j ↦ μ (Fin.succAbove 0 j)
    let F : α 0 × (∀ j, α (Fin.succAbove 0 j)) → ℝ := fun p ↦ g (e.symm p)
    have hF0 (p : α 0 × (∀ j, α (Fin.succAbove 0 j))) : 0 ≤ F p := hg0 (e.symm p)
    have hF_int := mps.integrable_comp_of_integrable hg
    have hFlog_int := mps.integrable_comp_of_integrable hglog
    let H (i : Fin (n + 1)) (x : ∀ i, α i) := entropy (μ i) (fun y ↦ g (Function.update x i y))
    have hH_eq (j : Fin n) (a : α 0) (w : ∀ j, α (Fin.succAbove 0 j)) :
        entropy (μ (Fin.succAbove 0 j)) (fun y ↦ F (a, Function.update w j y)) =
          H (Fin.succAbove 0 j) (e.symm (a, w)) := by
      simp only [F, H, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv_apply, Fin.insertNth_update]
    have hHp_int (j : Fin n) := mps.integrable_comp_of_integrable
      (integrable_entropy_update_pi μ (Fin.succAbove 0 j) (.of_forall hg0) hg hglog)
    -- Bound the `ν`-slice entropies by the induction hypothesis on the remaining `n` coordinates.
    have h1 : (∫ a, entropy ν (fun w ↦ F (a, w)) ∂μ 0) ≤
        ∑ j : Fin n, ∫ x, H (Fin.succAbove 0 j) x ∂Measure.pi μ := calc
      _ ≤ ∫ a, (∑ j : Fin n, ∫ w, H (Fin.succAbove 0 j) (e.symm (a, w)) ∂ν) ∂μ 0 := by
          refine integral_mono_ae
            (integrable_entropy_prod_left (.of_forall hF0) hF_int hFlog_int)
            (integrable_finsetSum _ fun j _ ↦ (hHp_int j).integral_prod_left) ?_
          filter_upwards [hF_int.prod_right_ae, hFlog_int.prod_right_ae] with a ha ha_log
          simpa only [hH_eq] using entropy_pi_fin (α := fun j ↦ α (Fin.succAbove 0 j))
            (fun j ↦ μ (Fin.succAbove 0 j)) (g := fun w ↦ F (a, w))
            ((hgm.comp e.symm.measurable).comp measurable_prodMk_left)
            (fun w ↦ hF0 (a, w)) ha ha_log
      _ = ∑ j : Fin n, ∫ a, ∫ w, H (Fin.succAbove 0 j) (e.symm (a, w)) ∂ν ∂μ 0 :=
          integral_finsetSum _ fun j _ ↦ (hHp_int j).integral_prod_left
      _ = ∑ j : Fin n, ∫ x, H (Fin.succAbove 0 j) x ∂Measure.pi μ :=
          Finset.sum_congr rfl fun j _ ↦ by
            rw [← integral_prod (fun p ↦ H (Fin.succAbove 0 j) (e.symm p)) (hHp_int j),
              mps.integral_comp e.symm.measurableEmbedding (H (Fin.succAbove 0 j))]
    -- Combine `h1` with the `i = 0` term via binary subadditivity `entropy_prod_le`.
    have h0 := integral_entropy_piFinSuccAbove_symm_zero μ hg0 hg hglog
    calc entropy (Measure.pi μ) g
        = entropy ((μ 0).prod ν) F := (mps.entropy_comp hgm.aestronglyMeasurable).symm
      _ ≤ (∫ a, entropy ν (fun w ↦ F (a, w)) ∂μ 0) +
            ∫ w, entropy (μ 0) (fun a ↦ F (a, w)) ∂ν :=
          entropy_prod_le (.of_forall hF0) hF_int hFlog_int
      _ ≤ (∑ j : Fin n, ∫ x, H (Fin.succAbove 0 j) x ∂Measure.pi μ) + ∫ x, H 0 x ∂Measure.pi μ :=
          add_le_add h1 h0.le
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
  obtain ⟨g', hg'm, hg'0, h_ae, hg'i, hg'li⟩ := exists_measurable_nonneg_ae_eq hg0 hg hglog
  have hslice_eq (i : ι) :
      (∫ x, entropy (μ i) (fun y ↦ g' (Function.update x i y)) ∂Measure.pi μ) =
        ∫ x, entropy (μ i) (fun y ↦ g (Function.update x i y)) ∂Measure.pi μ :=
    integral_congr_ae <| (ae_ae_of_ae_prod
      ((TauCeti.measurePreserving_update_prod_pi μ i).quasiMeasurePreserving.ae h_ae)).mono
        fun _ hx ↦ entropy_congr_ae hx
  rw [← entropy_congr_ae h_ae]; simp_rw [← hslice_eq]
  -- Transport from `Fin (Fintype.card ι)` to `ι` along `MeasurableEquiv.piCongrLeft`.
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let Φ := MeasurableEquiv.piCongrLeft α e
  have mp := measurePreserving_piCongrLeft μ e
  calc entropy (Measure.pi μ) g'
      = entropy (Measure.pi fun k ↦ μ (e k)) (g' ∘ Φ) :=
        (mp.entropy_comp hg'm.aestronglyMeasurable).symm
    _ ≤ ∑ k, ∫ y, entropy (μ (e k)) (fun v ↦ g' (Φ (Function.update y k v)))
          ∂Measure.pi (fun k ↦ μ (e k)) :=
        entropy_pi_fin (α := fun k ↦ α (e k)) (fun k ↦ μ (e k)) (g := g' ∘ Φ)
          (hg'm.comp Φ.measurable) (fun y ↦ hg'0 (Φ y))
          (mp.integrable_comp_of_integrable hg'i) (mp.integrable_comp_of_integrable hg'li)
    _ = ∑ i, ∫ x, entropy (μ i) (fun y ↦ g' (Function.update x i y)) ∂Measure.pi μ :=
        TauCeti.sum_integral_piCongrLeft_update μ e (fun i h ↦ entropy (μ i) h) g'

end FiniteProduct

end MeasureTheory.Measure

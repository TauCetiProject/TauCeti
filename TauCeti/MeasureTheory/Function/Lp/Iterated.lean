/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.WithDensityFinite
public import TauCeti.MeasureTheory.Function.Lp.TendstoExponentTop
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.MeasureTheory.Integral.Lebesgue.Norm

/-!
# Iterated `Lᵖ` seminorms on a product measure

For a function `f` on `α × β` and an exponent `p : ℝ≥0∞`, taking the `Lᵖ(ν)` seminorm of each
section `y ↦ f (x, y)` gives a function of `x`. This file shows that this function is
almost-everywhere strongly measurable as soon as `f` is, and that its `Lᵖ(μ)` seminorm is the
`Lᵖ(μ ⊗ ν)` seminorm of `f`. For `0 < p < ∞` this is Tonelli's theorem applied to `‖f‖ₑ ^ p`; at
`p = ∞` it says that the essential supremum over the product is the iterated essential supremum.
Only the second measure needs to be s-finite.

## Main statements

* `Measurable.eLpNorm_prod_right` and `MeasureTheory.AEStronglyMeasurable.eLpNorm_prod_right` —
  the section seminorms `x ↦ ‖f (x, ·)‖_{Lᵖ(ν)}` form a measurable, respectively
  almost-everywhere strongly measurable, function;
* `TauCeti.eLpNorm_prod_eq_eLpNorm_eLpNorm` — the `Lᵖ(μ ⊗ ν)` seminorm of `f` is the `Lᵖ(μ)`
  seminorm of its section seminorms.
* `TauCeti.lintegral_lintegral_enorm_sq_eq_eLpNorm_prod_sq` — the squared `L²(μ ⊗ ν)` seminorm
  is the iterated integral of the squared extended norm, integrating over `μ` first.
* `TauCeti.tendsto_measure_le_lintegral_enorm_sq_of_tendsto_eLpNorm` — convergence to zero in
  `L²(μ ⊗ ν)` makes the section square energies over `μ` converge to zero in `ν`-measure.
* `TauCeti.tendsto_measure_le_lintegral_enorm_sq_of_add` — convergence to zero in `ν`-measure
  of section square energies over `μ` is closed under addition.
* `TauCeti.eLpNorm_integral_le_eLpNorm_prod` and
  `TauCeti.eLpNorm_integral_sub_integral_le_eLpNorm_prod` — Fubini `L¹` bounds comparing
  pathwise integrals with the `L¹(μ ⊗ ν)` seminorm.
* `TauCeti.eLpNorm_prod_smul` — the `Lᵖ(μ ⊗ ν)` seminorm of `(x, y) ↦ f x • g y` is the product
  of the `Lᵖ(μ)` seminorm of `f` and the `Lᵖ(ν)` seminorm of `g`.
* `MeasureTheory.MemLp.ae_memLp_prod_right` — for `f ∈ Lᵖ(μ ⊗ ν)`, almost every section is in
  `Lᵖ(ν)`.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

variable {α β ε : Type*} [MeasurableSpace α] [MeasurableSpace β] [TopologicalSpace ε]
  {μ : Measure α} {ν : Measure β} {p : ℝ≥0∞}

namespace TauCeti

/-
The unconditional formulation below is adapted from Harald Husum and Claude Opus 5.5's
generalization audit, commit f0e7fac60832894e7feb09497ff5c956dcc7f7f4.
-/

/-- The `L^∞` seminorm only sees the null sets of the measure, so it does not change when an
s-finite measure is replaced by the equivalent finite measure `Measure.toFinite`. -/
@[simp]
theorem eLpNorm_exponent_top_toFinite [ENorm ε] [SFinite ν] (g : β → ε) :
    eLpNorm g ∞ ν.toFinite = eLpNorm g ∞ ν := by
  by_cases hg : AEStronglyMeasurable g ν
  · rw [eLpNorm_exponent_top hg, eLpNorm_exponent_top
      (hg.mono_ac (toFinite_absolutelyContinuous ν))]
    simp only [eLpNormEssSup, essSup, ae_toFinite]
  · rw [eLpNorm_of_not_aestronglyMeasurable hg, eLpNorm_of_not_aestronglyMeasurable
      fun h ↦ hg (h.mono_ac (absolutelyContinuous_toFinite ν))]

end TauCeti

variable [ContinuousENorm ε]

/-- For a measurable `g : α × β → ℝ≥0∞` and an s-finite `ν`, the section seminorms
`x ↦ ‖g (x, ·)‖_{Lᵖ(ν)}` form a measurable function, for every exponent including `p = ∞`. -/
theorem Measurable.eLpNorm_prod_right [SFinite ν] {g : α × β → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun x ↦ eLpNorm (fun y ↦ g (x, y)) p ν := by
  have hsec (x : α) : Measurable fun y ↦ g (x, y) := hg.comp measurable_prodMk_left
  -- The finite-exponent case, for an arbitrary s-finite measure.
  have hfin (q : ℝ≥0∞) (ρ : Measure β) [SFinite ρ] (hq0 : q ≠ 0) (hq : q ≠ ∞) :
      Measurable fun x ↦ eLpNorm (fun y ↦ g (x, y)) q ρ := by
    simp only [eLpNorm_eq_lintegral_rpow_eNorm_toReal hq0 hq (hsec _).aestronglyMeasurable,
      eNorm_eq_self]
    exact ((hg.pow_const _).lintegral_prod_right').pow_const _
  rcases eq_or_ne p 0 with rfl | hp0
  · simp only [eLpNorm_exponent_zero (hsec _).aestronglyMeasurable]
    exact measurable_const
  rcases ne_or_eq p ∞ with hp | rfl
  · exact hfin p ν hp0 hp
  -- At `p = ∞`, pass to the equivalent finite measure and take the limit of the finite exponents.
  have heq : (fun x ↦ eLpNorm (fun y ↦ g (x, y)) ∞ ν) =
      fun x ↦ eLpNorm (fun y ↦ g (x, y)) ∞ ν.toFinite :=
    funext fun x ↦ (TauCeti.eLpNorm_exponent_top_toFinite _).symm
  rw [heq]
  have hseq : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ≥0)) atTop atTop :=
    tendsto_atTop_mono (fun _ ↦ le_self_add) tendsto_natCast_atTop_atTop
  have htend (x : α) : Tendsto (fun n : ℕ ↦ eLpNorm (fun y ↦ g (x, y)) ((n + 1 : ℝ≥0) : ℝ≥0∞)
      ν.toFinite) atTop (𝓝 (eLpNorm (fun y ↦ g (x, y)) ∞ ν.toFinite)) :=
    TauCeti.tendsto_eLpNorm_atTop.comp hseq
  have hm (n : ℕ) : Measurable fun x ↦
      eLpNorm (fun y ↦ g (x, y)) ((n + 1 : ℝ≥0) : ℝ≥0∞) ν.toFinite :=
    hfin _ _ (ENNReal.coe_ne_zero.2 n.cast_add_one_ne_zero) ENNReal.coe_ne_top
  exact measurable_of_tendsto_metrizable hm (tendsto_pi_nhds.2 htend)

namespace MeasureTheory

/-- For an almost-everywhere strongly measurable `f` on `μ ⊗ ν`, the section seminorms
`x ↦ ‖f (x, ·)‖_{Lᵖ(ν)}` form an almost-everywhere strongly measurable function, for every
exponent including `p = ∞`. -/
theorem AEStronglyMeasurable.eLpNorm_prod_right [SFinite ν] {f : α × β → ε}
    (hf : AEStronglyMeasurable f (μ.prod ν)) :
    AEStronglyMeasurable (fun x ↦ eLpNorm (fun y ↦ f (x, y)) p ν) μ := by
  have hg := hf.eNorm
  refine (hg.measurable_mk.eLpNorm_prod_right (p := p) (ν := ν)).aestronglyMeasurable.congr ?_
  filter_upwards [hf.prodMk_left, Measure.ae_ae_of_ae_prod hg.ae_eq_mk] with x hx hxg
  rw [← eLpNorm_eNorm _ hx]
  exact (eLpNorm_congr_ae hxg).symm

end MeasureTheory

namespace TauCeti

/-- The `L^∞` case of `TauCeti.eLpNorm_prod_eq_eLpNorm_eLpNorm`, for a measurable
`ℝ≥0∞`-valued function: the essential supremum over the product is the iterated essential
supremum. -/
private theorem eLpNorm_top_prod_eq_of_measurable [SFinite ν] {g : α × β → ℝ≥0∞}
    (hg : Measurable g) :
    eLpNorm g ∞ (μ.prod ν) = eLpNorm (fun x ↦ eLpNorm (fun y ↦ g (x, y)) ∞ ν) ∞ μ := by
  have hsec (x : α) : AEStronglyMeasurable (fun y ↦ g (x, y)) ν :=
    (hg.comp measurable_prodMk_left).aestronglyMeasurable
  rw [eLpNorm_exponent_top hg.aestronglyMeasurable,
    eLpNorm_exponent_top (hg.eLpNorm_prod_right (p := ∞) (ν := ν)).aestronglyMeasurable]
  refine le_antisymm (eLpNormEssSup_le_of_ae_eNorm_bound ?_)
    (eLpNormEssSup_le_of_ae_eNorm_bound ?_)
  · -- A bound valid for almost every section is valid almost everywhere on the product.
    refine (Measure.ae_prod_iff_ae_ae (measurableSet_le hg.eNorm measurable_const)).2 ?_
    filter_upwards [ae_le_eLpNormEssSup (f := fun x ↦ eLpNorm (fun y ↦ g (x, y)) ∞ ν) (μ := μ)]
      with x hx
    filter_upwards [ae_le_eLpNormEssSup (f := fun y ↦ g (x, y)) (μ := ν)] with y hy
    rw [eNorm_eq_self, eLpNorm_exponent_top (hsec x)] at hx
    exact hy.trans hx
  · -- Conversely, a bound valid almost everywhere bounds almost every section seminorm.
    filter_upwards [Measure.ae_ae_of_ae_prod (ae_le_eLpNormEssSup (f := g) (μ := μ.prod ν))]
      with x hx
    rw [eNorm_eq_self, eLpNorm_exponent_top (hsec x)]
    exact eLpNormEssSup_le_of_ae_eNorm_bound hx

/-- **Iterated `Lᵖ` seminorms.** The `Lᵖ(μ ⊗ ν)` seminorm of an almost-everywhere strongly
measurable function is the `Lᵖ(μ)` seminorm of its section seminorms `x ↦ ‖f (x, ·)‖_{Lᵖ(ν)}`.
This holds for every exponent, including `p = ∞`, where it identifies the essential supremum
over the product with the iterated essential supremum. -/
theorem eLpNorm_prod_eq_eLpNorm_eLpNorm [SFinite ν] {f : α × β → ε}
    (hf : AEStronglyMeasurable f (μ.prod ν)) :
    eLpNorm f p (μ.prod ν) = eLpNorm (fun x ↦ eLpNorm (fun y ↦ f (x, y)) p ν) p μ := by
  -- Reduce to a measurable representative `g` of `‖f‖ₑ`.
  set g := hf.eNorm.mk
  have hg : Measurable g := hf.eNorm.measurable_mk
  have hfg : (fun z ↦ ‖f z‖ₑ) =ᵐ[μ.prod ν] g := hf.eNorm.ae_eq_mk
  have hsec (x : α) : AEStronglyMeasurable (fun y ↦ g (x, y)) ν :=
    (hg.comp measurable_prodMk_left).aestronglyMeasurable
  have hout : AEStronglyMeasurable (fun x ↦ eLpNorm (fun y ↦ g (x, y)) p ν) μ :=
    hg.eLpNorm_prod_right.aestronglyMeasurable
  rw [← eLpNorm_eNorm f hf, eLpNorm_congr_ae hfg]
  rw [eLpNorm_congr_ae (g := fun x ↦ eLpNorm (fun y ↦ g (x, y)) p ν) ?_]
  swap
  · filter_upwards [hf.prodMk_left, Measure.ae_ae_of_ae_prod hfg] with x hx hxg
    rw [← eLpNorm_eNorm _ hx]
    exact eLpNorm_congr_ae hxg
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [eLpNorm_exponent_zero hg.aestronglyMeasurable, eLpNorm_exponent_zero hout]
  rcases ne_or_eq p ∞ with hp | rfl
  swap
  · exact eLpNorm_top_prod_eq_of_measurable hg
  -- For `0 < p < ∞` this is Tonelli's theorem for `g ^ p`.
  have hr : p.toReal ≠ 0 := (ENNReal.toReal_pos hp0 hp).ne'
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hg.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hout]
  simp only [eNorm_eq_self]
  rw [lintegral_prod _ (hg.pow_const _).aemeasurable]
  congr 1
  refine lintegral_congr fun x ↦ ?_
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp (hsec x)]
  simp only [eNorm_eq_self, one_div, ENNReal.rpow_inv_rpow hr]

/-- The squared `L²(μ ⊗ ν)` seminorm of an a.e. strongly measurable function is its iterated
square energy, integrating over the first factor `μ` first. -/
theorem lintegral_lintegral_enorm_sq_eq_eLpNorm_prod_sq [SFinite μ] [SFinite ν]
    {f : α × β → ε} (hf : AEStronglyMeasurable f (μ.prod ν)) :
    ∫⁻ y, ∫⁻ x, ‖f (x, y)‖ₑ ^ 2 ∂μ ∂ν = eLpNorm f 2 (μ.prod ν) ^ 2 := by
  rw [eLpNorm_two_sq_eq_lintegral hf, lintegral_prod_symm _ (hf.eNorm.pow_const 2)]

/-- **Markov's inequality for section energies.** If `f k → 0` in `L²(μ ⊗ ν)`, then the section
square energies `y ↦ ∫⁻ x, ‖f k (x, y)‖ₑ ^ 2 ∂μ` converge to zero in `ν`-measure: for each
`δ > 0`, the `ν`-measure of the set where the energy is at least `δ` tends to zero. -/
theorem tendsto_measure_le_lintegral_enorm_sq_of_tendsto_eLpNorm [SFinite μ] [SFinite ν]
    {ι : Type*} {l : Filter ι} {f : ι → α × β → ε}
    (hf : ∀ k, AEStronglyMeasurable (f k) (μ.prod ν))
    (h : Tendsto (fun k ↦ eLpNorm (f k) 2 (μ.prod ν)) l (𝓝 0)) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    Tendsto (fun k ↦ ν {y | δ ≤ ∫⁻ x, ‖f k (x, y)‖ₑ ^ 2 ∂μ}) l (𝓝 0) := by
  -- Markov's inequality at the finite level `min δ 1`.
  set c := min δ 1
  have hc : c ≠ 0 := (lt_min hδ one_pos).ne'
  have hc' : c ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hbound (k : ι) : ν {y | δ ≤ ∫⁻ x, ‖f k (x, y)‖ₑ ^ 2 ∂μ} ≤
      eLpNorm (f k) 2 (μ.prod ν) ^ 2 / c := by
    rw [← lintegral_lintegral_enorm_sq_eq_eLpNorm_prod_sq (hf k)]
    exact (measure_mono fun y hy ↦ (min_le_left δ 1).trans hy).trans
      (meas_ge_le_lintegral_div ((hf k).eNorm.pow_const 2).lintegral_prod_left' hc hc')
  have hlim : Tendsto (fun k ↦ eLpNorm (f k) 2 (μ.prod ν) ^ 2 / c) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.div_const (((ENNReal.continuous_pow 2).tendsto 0).comp h)
      (Or.inr hc)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ bot_le)
    hbound

/-- **Addition rule for convergence in measure of section square energies.** If section square
energies over `μ` of `f k` and `g k` both converge to zero in `ν`-measure, then so do those of
any process `h k` satisfying `h k x y = f k x y + g k x y`. -/
theorem tendsto_measure_le_lintegral_enorm_sq_of_add {ι E : Type*} [SeminormedAddCommGroup E]
    {l : Filter ι} {f g h : ι → α → β → E}
    (hf : ∀ k y, AEMeasurable (fun x ↦ ‖f k x y‖ₑ ^ 2) μ)
    (hpt : ∀ k x y, h k x y = f k x y + g k x y)
    (hf0 : ∀ δ : ℝ≥0∞, 0 < δ →
      Tendsto (fun k ↦ ν {y | δ ≤ ∫⁻ x, ‖f k x y‖ₑ ^ 2 ∂μ}) l (𝓝 0))
    (hg0 : ∀ δ : ℝ≥0∞, 0 < δ →
      Tendsto (fun k ↦ ν {y | δ ≤ ∫⁻ x, ‖g k x y‖ₑ ^ 2 ∂μ}) l (𝓝 0))
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    Tendsto (fun k ↦ ν {y | δ ≤ ∫⁻ x, ‖h k x y‖ₑ ^ 2 ∂μ}) l (𝓝 0) := by
  wlog htop : δ ≠ ∞ generalizing δ
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (this zero_lt_one ENNReal.one_ne_top) (fun _ ↦ bot_le) fun k ↦
      measure_mono fun _ hy ↦ (le_top : (1 : ℝ≥0∞) ≤ ∞).trans (by rwa [not_not.mp htop] at hy)
  set η := δ / 4
  have hη : 0 < η := ENNReal.div_pos hδ.ne' (by norm_num)
  have hbound : 2 * (η + η) ≤ δ := by
    calc 2 * (η + η) = 4 * (δ / 4) := by ring
      _ ≤ δ := ENNReal.mul_div_le
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using (hf0 η hη).add (hg0 η hη)) (fun _ ↦ bot_le) fun k ↦ ?_
  refine (measure_mono fun y hy ↦ ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hy ⊢
  by_contra hnot
  simp only [not_or, not_le] at hnot
  have hlt := (lintegral_enorm_add_sq_le_two_mul (hf k y)).trans_lt
    ((ENNReal.mul_lt_mul_right (by norm_num) (by norm_num)
      (ENNReal.add_lt_add hnot.1 hnot.2)).trans_le hbound)
  exact hlt.not_ge (hy.trans_eq (lintegral_congr fun x ↦ by rw [hpt k x y]))

/-- **Fubini's inequality in `L¹`.** The `L¹(ν)` seminorm of the `μ`-integral `y ↦ ∫ x, f x y ∂μ`
is at most the `L¹(μ ⊗ ν)` seminorm of `Function.uncurry f`. -/
theorem eLpNorm_integral_le_eLpNorm_prod [SFinite μ] [SFinite ν] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α → β → E}
    (hsec : AEStronglyMeasurable (fun y ↦ ∫ x, f x y ∂μ) ν)
    (hprod : AEStronglyMeasurable (Function.uncurry f) (μ.prod ν)) :
    eLpNorm (fun y ↦ ∫ x, f x y ∂μ) 1 ν ≤
      eLpNorm (Function.uncurry f) 1 (μ.prod ν) := by
  rw [eLpNorm_one_eq_lintegral_eNorm hsec, eLpNorm_one_eq_lintegral_eNorm hprod,
    lintegral_prod_symm _ hprod.eNorm]
  exact lintegral_mono fun y ↦ eNorm_integral_le_lintegral_eNorm _

/-- **Fubini's `L¹` estimate for a difference of section integrals.** When almost every
`μ`-section of `f` and `g` is integrable, the `L¹(ν)` seminorm of
`y ↦ (∫ x, f x y ∂μ) - ∫ x, g x y ∂μ` is at most the `L¹(μ ⊗ ν)` seminorm of
`(x, y) ↦ f x y - g x y`. -/
theorem eLpNorm_integral_sub_integral_le_eLpNorm_prod [SFinite μ] [SFinite ν] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : α → β → E}
    (hf : ∀ᵐ y ∂ν, Integrable (fun x ↦ f x y) μ)
    (hg : ∀ᵐ y ∂ν, Integrable (fun x ↦ g x y) μ)
    (hsec : AEStronglyMeasurable (fun y ↦ (∫ x, f x y ∂μ) - ∫ x, g x y ∂μ) ν)
    (hprod : AEStronglyMeasurable (fun p : α × β ↦ f p.1 p.2 - g p.1 p.2) (μ.prod ν)) :
    eLpNorm (fun y ↦ (∫ x, f x y ∂μ) - ∫ x, g x y ∂μ) 1 ν ≤
      eLpNorm (fun p : α × β ↦ f p.1 p.2 - g p.1 p.2) 1 (μ.prod ν) := by
  have hae : (fun y ↦ (∫ x, f x y ∂μ) - ∫ x, g x y ∂μ) =ᵐ[ν]
      fun y ↦ ∫ x, (f x y - g x y) ∂μ :=
    hf.mp (hg.mono fun y hgy hfy ↦ (integral_sub hfy hgy).symm)
  rw [eLpNorm_congr_ae hae]
  exact eLpNorm_integral_le_eLpNorm_prod (hsec.congr hae) hprod

/-- **The `Lᵖ` seminorm of a tensor product.** The `Lᵖ(μ ⊗ ν)` seminorm of `(x, y) ↦ f x • g y`
is the product of the `Lᵖ(μ)` seminorm of `f` and the `Lᵖ(ν)` seminorm of `g`, for every
exponent, including `p = ∞`. The scalar action need only be continuous and satisfy
`‖c • v‖ₑ = ‖c‖ₑ * ‖v‖ₑ`. -/
theorem eLpNorm_prod_smul [SFinite ν] {𝕜 : Type*} [TopologicalSpace 𝕜] [ContinuousENorm 𝕜]
    [SMul 𝕜 ε] [ContinuousSMul 𝕜 ε] [ENormSMulClass 𝕜 ε]
    {f : α → 𝕜} {g : β → ε} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g ν) :
    eLpNorm (fun z : α × β ↦ f z.1 • g z.2) p (μ.prod ν) = eLpNorm f p μ * eLpNorm g p ν := by
  rw [eLpNorm_prod_eq_eLpNorm_eLpNorm (f := fun z : α × β ↦ f z.1 • g z.2)
    (hf.comp_fst.smul hg.comp_snd)]
  -- Each section is a constant multiple of `g`.
  have hsec (x : α) : eLpNorm (fun y ↦ f x • g y) p ν = ‖f x‖ₑ * eLpNorm g p ν := by
    rw [← eLpNorm_eNorm _ (hg.fun_const_smul (f x))]
    simp_rw [eNorm_smul]
    rw [eLpNorm_const_mul_ennreal hg.eNorm.aestronglyMeasurable, eLpNorm_eNorm _ hg]
  simp_rw [hsec, mul_comm _ (eLpNorm g p ν)]
  rw [eLpNorm_const_mul_ennreal hf.eNorm.aestronglyMeasurable, eLpNorm_eNorm _ hf, mul_comm]

end TauCeti

/-- If `f ∈ Lᵖ(μ ⊗ ν)` then almost every section `y ↦ f (x, y)` is in `Lᵖ(ν)`. -/
theorem MeasureTheory.MemLp.ae_memLp_prod_right [SFinite ν] {f : α × β → ε}
    (hf : MemLp f p (μ.prod ν)) : ∀ᵐ x ∂μ, MemLp (fun y ↦ f (x, y)) p ν := by
  have h : eLpNorm (fun x ↦ eLpNorm (fun y ↦ f (x, y)) p ν) p μ < ∞ := by
    rw [← TauCeti.eLpNorm_prod_eq_eLpNorm_eLpNorm hf.aestronglyMeasurable]
    exact hf
  set g : α → ℝ≥0∞ := fun x ↦ eLpNorm (fun y ↦ f (x, y)) p ν with hg
  suffices ∀ᵐ x ∂μ, g x < ∞ from this.mono fun x hx ↦ hx
  rcases eq_or_ne p 0 with rfl | hp0
  · filter_upwards [hf.aestronglyMeasurable.prodMk_left] with x hx
    simp [hg, eLpNorm_exponent_zero hx]
  · exact TauCeti.ae_lt_top_of_eLpNorm_ne_top hp0 h.ne

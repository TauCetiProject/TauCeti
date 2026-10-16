/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.WithDensityFinite
public import TauCeti.MeasureTheory.Function.Lp.TendstoExponentTop

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
* `TauCeti.eLpNorm_prod_smul` — the `Lᵖ(μ ⊗ ν)` seminorm of `(x, y) ↦ f x • g y` is the product
  of the `Lᵖ(μ)` seminorm of `f` and the `Lᵖ(ν)` seminorm of `g`.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

variable {α β ε : Type*} [MeasurableSpace α] [MeasurableSpace β] [TopologicalSpace ε]
  [ContinuousENorm ε] {μ : Measure α} {ν : Measure β} {p : ℝ≥0∞}

namespace TauCeti

/-- The `L^∞` seminorm only sees the null sets of the measure, so it does not change when an
s-finite measure is replaced by the equivalent finite measure `Measure.toFinite`. -/
theorem eLpNorm_exponent_top_toFinite [SFinite ν] {g : β → ε} (hg : AEStronglyMeasurable g ν) :
    eLpNorm g ∞ ν.toFinite = eLpNorm g ∞ ν := by
  rw [eLpNorm_exponent_top hg, eLpNorm_exponent_top
    (hg.mono_ac (toFinite_absolutelyContinuous ν))]
  simp only [eLpNormEssSup, essSup, ae_toFinite]

end TauCeti

/-- For a measurable `g : α × β → ℝ≥0∞` and an s-finite `ν`, the section seminorms
`x ↦ ‖g (x, ·)‖_{Lᵖ(ν)}` form a measurable function, for every exponent including `p = ∞`. -/
theorem Measurable.eLpNorm_prod_right [SFinite ν] {g : α × β → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun x ↦ eLpNorm (fun y ↦ g (x, y)) p ν := by
  have hsec (x : α) : Measurable fun y ↦ g (x, y) := hg.comp measurable_prodMk_left
  -- The finite-exponent case, for an arbitrary s-finite measure.
  have hfin (q : ℝ≥0∞) (ρ : Measure β) [SFinite ρ] (hq0 : q ≠ 0) (hq : q ≠ ∞) :
      Measurable fun x ↦ eLpNorm (fun y ↦ g (x, y)) q ρ := by
    simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq (hsec _).aestronglyMeasurable,
      enorm_eq_self]
    exact ((hg.pow_const _).lintegral_prod_right').pow_const _
  rcases eq_or_ne p 0 with rfl | hp0
  · simp only [eLpNorm_exponent_zero (hsec _).aestronglyMeasurable]
    exact measurable_const
  rcases ne_or_eq p ∞ with hp | rfl
  · exact hfin p ν hp0 hp
  -- At `p = ∞`, pass to the equivalent finite measure and take the limit of the finite exponents.
  have heq : (fun x ↦ eLpNorm (fun y ↦ g (x, y)) ∞ ν) =
      fun x ↦ eLpNorm (fun y ↦ g (x, y)) ∞ ν.toFinite :=
    funext fun x ↦ (TauCeti.eLpNorm_exponent_top_toFinite (hsec x).aestronglyMeasurable).symm
  rw [heq]
  have hseq : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ≥0)) atTop atTop :=
    tendsto_atTop_mono (fun _ ↦ le_self_add) tendsto_natCast_atTop_atTop
  have htend (x : α) : Tendsto (fun n : ℕ ↦ eLpNorm (fun y ↦ g (x, y)) ((n + 1 : ℝ≥0) : ℝ≥0∞)
      ν.toFinite) atTop (𝓝 (eLpNorm (fun y ↦ g (x, y)) ∞ ν.toFinite)) :=
    (TauCeti.tendsto_eLpNorm_atTop (hsec x).aestronglyMeasurable).comp hseq
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
  have hg := hf.enorm
  refine (hg.measurable_mk.eLpNorm_prod_right (p := p) (ν := ν)).aestronglyMeasurable.congr ?_
  filter_upwards [hf.prodMk_left, Measure.ae_ae_of_ae_prod hg.ae_eq_mk] with x hx hxg
  rw [← eLpNorm_enorm _ hx]
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
  refine le_antisymm (eLpNormEssSup_le_of_ae_enorm_bound ?_)
    (eLpNormEssSup_le_of_ae_enorm_bound ?_)
  · -- A bound valid for almost every section is valid almost everywhere on the product.
    refine (Measure.ae_prod_iff_ae_ae (measurableSet_le hg.enorm measurable_const)).2 ?_
    filter_upwards [ae_le_eLpNormEssSup (f := fun x ↦ eLpNorm (fun y ↦ g (x, y)) ∞ ν) (μ := μ)]
      with x hx
    filter_upwards [ae_le_eLpNormEssSup (f := fun y ↦ g (x, y)) (μ := ν)] with y hy
    rw [enorm_eq_self, eLpNorm_exponent_top (hsec x)] at hx
    exact hy.trans hx
  · -- Conversely, a bound valid almost everywhere bounds almost every section seminorm.
    filter_upwards [Measure.ae_ae_of_ae_prod (ae_le_eLpNormEssSup (f := g) (μ := μ.prod ν))]
      with x hx
    rw [enorm_eq_self, eLpNorm_exponent_top (hsec x)]
    exact eLpNormEssSup_le_of_ae_enorm_bound hx

/-- **Iterated `Lᵖ` seminorms.** The `Lᵖ(μ ⊗ ν)` seminorm of an almost-everywhere strongly
measurable function is the `Lᵖ(μ)` seminorm of its section seminorms `x ↦ ‖f (x, ·)‖_{Lᵖ(ν)}`.
This holds for every exponent, including `p = ∞`, where it identifies the essential supremum
over the product with the iterated essential supremum. -/
theorem eLpNorm_prod_eq_eLpNorm_eLpNorm [SFinite ν] {f : α × β → ε}
    (hf : AEStronglyMeasurable f (μ.prod ν)) :
    eLpNorm f p (μ.prod ν) = eLpNorm (fun x ↦ eLpNorm (fun y ↦ f (x, y)) p ν) p μ := by
  -- Reduce to a measurable representative `g` of `‖f‖ₑ`.
  set g := hf.enorm.mk
  have hg : Measurable g := hf.enorm.measurable_mk
  have hfg : (fun z ↦ ‖f z‖ₑ) =ᵐ[μ.prod ν] g := hf.enorm.ae_eq_mk
  have hsec (x : α) : AEStronglyMeasurable (fun y ↦ g (x, y)) ν :=
    (hg.comp measurable_prodMk_left).aestronglyMeasurable
  have hout : AEStronglyMeasurable (fun x ↦ eLpNorm (fun y ↦ g (x, y)) p ν) μ :=
    hg.eLpNorm_prod_right.aestronglyMeasurable
  rw [← eLpNorm_enorm f hf, eLpNorm_congr_ae hfg]
  rw [eLpNorm_congr_ae (g := fun x ↦ eLpNorm (fun y ↦ g (x, y)) p ν) ?_]
  swap
  · filter_upwards [hf.prodMk_left, Measure.ae_ae_of_ae_prod hfg] with x hx hxg
    rw [← eLpNorm_enorm _ hx]
    exact eLpNorm_congr_ae hxg
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [eLpNorm_exponent_zero hg.aestronglyMeasurable, eLpNorm_exponent_zero hout]
  rcases ne_or_eq p ∞ with hp | rfl
  swap
  · exact eLpNorm_top_prod_eq_of_measurable hg
  -- For `0 < p < ∞` this is Tonelli's theorem for `g ^ p`.
  have hr : p.toReal ≠ 0 := (ENNReal.toReal_pos hp0 hp).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hg.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hout]
  simp only [enorm_eq_self]
  rw [lintegral_prod _ (hg.pow_const _).aemeasurable]
  congr 1
  refine lintegral_congr fun x ↦ ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (hsec x)]
  simp only [enorm_eq_self, one_div, ENNReal.rpow_inv_rpow hr]

/-- **The `Lᵖ` seminorm of a tensor product.** The `Lᵖ(μ ⊗ ν)` seminorm of `(x, y) ↦ f x • g y`
is the product of the `Lᵖ(μ)` seminorm of `f` and the `Lᵖ(ν)` seminorm of `g`, for every
exponent, including `p = ∞`. -/
theorem eLpNorm_prod_smul [SFinite ν] {𝕜 E : Type*} [NormedDivisionRing 𝕜] [NormedAddCommGroup E]
    [Module 𝕜 E] [NormSMulClass 𝕜 E] {f : α → 𝕜} {g : β → E} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g ν) :
    eLpNorm (fun z : α × β ↦ f z.1 • g z.2) p (μ.prod ν) = eLpNorm f p μ * eLpNorm g p ν := by
  rw [eLpNorm_prod_eq_eLpNorm_eLpNorm (f := fun z : α × β ↦ f z.1 • g z.2)
    (hf.comp_fst.smul hg.comp_snd)]
  -- Each section is a constant multiple of `g`.
  have hsec (x : α) : eLpNorm (fun y ↦ f x • g y) p ν = ‖f x‖ₑ * eLpNorm g p ν :=
    eLpNorm_const_smul (f x) g p ν
  simp only [hsec]
  set c := eLpNorm g p ν
  have hfc : AEStronglyMeasurable (fun x ↦ ‖f x‖ₑ * c) μ :=
    (hf.enorm.mul_const c).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [eLpNorm_exponent_zero hfc, eLpNorm_exponent_zero hf, zero_mul]
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [eLpNorm_exponent_top hfc, eLpNorm_exponent_top hf, eLpNormEssSup_eq_essSup_enorm,
      eLpNormEssSup_eq_essSup_enorm]
    simp only [enorm_eq_self]
    simp_rw [mul_comm _ c]
    exact ENNReal.essSup_const_mul
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hfc,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hf]
  simp only [enorm_eq_self, ENNReal.mul_rpow_of_nonneg _ _ hr.le]
  rw [lintegral_mul_const'' _ (hf.enorm.pow_const _),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), one_div, ENNReal.rpow_rpow_inv hr.ne']

end TauCeti

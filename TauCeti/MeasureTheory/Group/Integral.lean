/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.MeasureTheory.Group.Measure
import TauCeti.MeasureTheory.Integral.OddSymmetric

/-!
# Integration on groups

Integrating against an inverse measure is equivalent to precomposing the integrand with
inversion. This transports integrals between left and right Haar measures.

For a measure invariant under addition, an integral over a ball can be translated to a ball
about the origin. Only measurability of translations is needed; the measure need not be an
additive Haar measure, and the function need not be integrable. If the measure is also invariant
under negation, the centre of a ball is its barycentre.

For a right-invariant `s`-finite measure `μ`, integrating `z ↦ f (x * g z)` or `z ↦ f (x / g z)`
against an `s`-finite measure `ν` (or over a set `s`) and then `x` against `μ` factors out
`ν univ` (or `ν s`) times `∫⁻ x, f x ∂μ` by Tonelli's theorem and right-translation invariance.

For a measure invariant under a group action, an integrand invariant under `g` has the same
integral, and the same integrability, on `g • V` as on `V`.

The integral of the difference `w (· + a) - w` of an integrable function against a bounded
measurable test function equals the integral of `w` against `φ (· - a) - φ`, by translation
invariance.

## Main declarations

* `TauCeti.integral_comp_add_sub_mul_eq`: moving a translation of an integrable function
  onto a bounded measurable test function inside an integral.
* `TauCeti.setIntegral_ball_eq_setIntegral_ball_zero_add`: translating a ball integral to the
  origin.
* `TauCeti.setIntegral_ball_sub_eq_zero`, `TauCeti.setAverage_ball_id`: for a measure invariant
  under translation and negation, the centre of a ball is its barycentre.
* `TauCeti.lintegral_lintegral_mul_right`, `TauCeti.lintegral_lintegral_add_right`,
  `TauCeti.lintegral_lintegral_div_right`, `TauCeti.lintegral_lintegral_sub_right`,
  `TauCeti.lintegral_setLIntegral_mul_right`, `TauCeti.lintegral_setLIntegral_add_right`,
  `TauCeti.lintegral_setLIntegral_div_right`, `TauCeti.lintegral_setLIntegral_sub_right`:
  factoring out the parameter measure when integrating right-translated lower Lebesgue integrals.
* `TauCeti.setIntegral_smul_set`, `TauCeti.integrableOn_smul_set_iff`: integrals and
  integrability of an invariant integrand over a translated set.
-/

public section

open MeasureTheory Metric Set

open scoped ENNReal Pointwise

namespace TauCeti

/-- An integral against `μ.inv` is an integral against `μ` with the argument inverted.
This orientation removes the inverse measure and needs no integrability assumption. -/
theorem integral_inv_measure {G E : Type*} [MeasurableSpace G] [InvolutiveInv G]
    [MeasurableInv G] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : G → E) (μ : Measure G) :
    ∫ x, f x ∂μ.inv = ∫ x, f x⁻¹ ∂μ := by
  rw [Measure.inv_def]
  exact integral_map_equiv (MeasurableEquiv.inv G) f

/-- For a measure invariant under right addition, the integral over `ball x₀ R` is the integral
over `ball 0 R` of the translate `y ↦ f (y + x₀)`. No integrability hypothesis is needed. -/
theorem setIntegral_ball_eq_setIntegral_ball_zero_add
    {E F : Type*} [SeminormedAddCommGroup E] [MeasurableSpace E] [MeasurableAdd E]
    {μ : Measure E} [μ.IsAddRightInvariant] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x₀ : E) (R : ℝ) :
    ∫ x in ball x₀ R, f x ∂μ = ∫ y in ball (0 : E) R, f (y + x₀) ∂μ := by
  simpa using ((measurePreserving_add_right μ x₀).setIntegral_preimage_emb
    (MeasurableEquiv.addRight x₀).measurableEmbedding f (ball x₀ R)).symm

/-- For a measure invariant under right addition and under negation, such as an additive Haar
measure on a finite-dimensional real normed space, the integral of `x - x₀` over `ball x₀ R`
vanishes: the centre is the barycentre of the ball. -/
@[simp]
theorem setIntegral_ball_sub_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [MeasurableAdd E] [MeasurableNeg E] {μ : Measure E}
    [μ.IsAddRightInvariant] [μ.IsNegInvariant] (x₀ : E) (R : ℝ) :
    ∫ x in ball x₀ R, (x - x₀) ∂μ = 0 := by
  rw [setIntegral_ball_eq_setIntegral_ball_zero_add]
  simp only [add_sub_cancel_right]
  -- Restricted to the symmetric set `ball 0 R`, `μ` is still invariant under negation.
  have := Measure.isNegInvariant_restrict (μ := μ) (s := ball (0 : E) R) (by simp [neg_ball])
  exact integral_eq_zero_of_odd (g := fun y : E ↦ y) fun _ ↦ rfl

/-- For a measure invariant under right addition and under negation, such as an additive Haar
measure on a finite-dimensional real normed space, the average of the identity over a ball of
positive finite measure is its centre. -/
theorem setAverage_ball_id {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure E}
    [μ.IsAddRightInvariant] [μ.IsNegInvariant] {x₀ : E} {R : ℝ} (h0 : μ (ball x₀ R) ≠ 0)
    (hR : μ (ball x₀ R) ≠ ⊤) : ⨍ x in ball x₀ R, x ∂μ = x₀ := by
  have hint : IntegrableOn (fun x : E ↦ x - x₀) (ball x₀ R) μ :=
    .of_bound hR.lt_top (continuous_id.sub continuous_const).aestronglyMeasurable R
      (ae_restrict_of_forall_mem measurableSet_ball fun x hx ↦ (mem_ball_iff_norm.1 hx).le)
  have h := integral_add hint (integrableOn_const (C := x₀) hR)
  simp only [sub_add_cancel] at h
  rw [setAverage_eq, h, setIntegral_ball_sub_eq_zero, setIntegral_const, zero_add,
    inv_smul_smul₀ ((measureReal_ne_zero_iff hR).2 h0)]

section LIntegral

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
  {μ : Measure G} [SFinite μ] [μ.IsMulRightInvariant] {f : G → ℝ≥0∞}

/-- Integrating `z ↦ f (x * g z)` against an `s`-finite measure `ν` and then `x` against a
right-invariant `s`-finite measure `μ` factors out `ν univ` by Tonelli's theorem and
right-translation invariance of `μ`. -/
@[to_additive
/-- Integrating `z ↦ f (x + g z)` against an `s`-finite measure `ν` and then `x` against a
right-invariant `s`-finite measure `μ` factors out `ν univ` by Tonelli's theorem and
right-translation invariance of `μ`. -/]
theorem lintegral_lintegral_mul_right (hf : AEMeasurable f μ) {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [SFinite ν] {g : α → G} (hg : AEMeasurable g ν) :
    ∫⁻ x, ∫⁻ z, f (x * g z) ∂ν ∂μ = ν univ * ∫⁻ x, f x ∂μ := by
  have hcongr (x : G) : ∫⁻ z, f (x * g z) ∂ν = ∫⁻ z, f (x * hg.mk g z) ∂ν :=
    lintegral_congr_ae (hg.ae_eq_mk.mono fun z hz ↦ congrArg (fun w ↦ f (x * w)) hz)
  simp_rw [hcongr]
  have hqmp : QuasiMeasurePreserving (fun q : G × α ↦ q.1 * hg.mk g q.2) (μ.prod ν) μ :=
    QuasiMeasurePreserving.prod_of_left
      (measurable_fst.mul (hg.measurable_mk.comp measurable_snd)).aemeasurable
      (Filter.Eventually.of_forall fun z ↦
        (measurePreserving_mul_right μ (hg.mk g z)).quasiMeasurePreserving)
  have hm : AEMeasurable (Function.uncurry fun x z ↦ f (x * hg.mk g z)) (μ.prod ν) :=
    hf.comp_quasiMeasurePreserving hqmp
  rw [lintegral_lintegral_swap hm]
  simp_rw [lintegral_mul_right_eq_self f]
  rw [lintegral_const, mul_comm]

/-- Integrating `z ↦ f (x / g z)` against an `s`-finite measure `ν` and then `x` against a
right-invariant `s`-finite measure `μ` factors out `ν univ`. -/
@[to_additive
/-- Integrating `z ↦ f (x - g z)` against an `s`-finite measure `ν` and then `x` against a
right-invariant `s`-finite measure `μ` factors out `ν univ`. -/]
theorem lintegral_lintegral_div_right [MeasurableInv G] (hf : AEMeasurable f μ) {α : Type*}
    [MeasurableSpace α] {ν : Measure α} [SFinite ν] {g : α → G} (hg : AEMeasurable g ν) :
    ∫⁻ x, ∫⁻ z, f (x / g z) ∂ν ∂μ = ν univ * ∫⁻ x, f x ∂μ := by
  simp_rw [div_eq_mul_inv]
  exact lintegral_lintegral_mul_right hf hg.inv

/-- Integrating `z ↦ f (x * g z)` over `s` against an `s`-finite measure `ν` and then `x` against
a right-invariant `s`-finite measure `μ` factors out `ν s`. -/
@[to_additive
/-- Integrating `z ↦ f (x + g z)` over `s` against an `s`-finite measure `μ` and then `x` against
a right-invariant `s`-finite measure `μ` factors out `ν s`. -/]
theorem lintegral_setLIntegral_mul_right (hf : AEMeasurable f μ) {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [SFinite ν] {g : α → G} {s : Set α} (hg : AEMeasurable g (ν.restrict s)) :
    ∫⁻ x, ∫⁻ z in s, f (x * g z) ∂ν ∂μ = ν s * ∫⁻ x, f x ∂μ := by
  rw [lintegral_lintegral_mul_right hf hg, Measure.restrict_apply_univ]

/-- Integrating `z ↦ f (x / g z)` over `s` against an `s`-finite measure `ν` and then `x` against
a right-invariant `s`-finite measure `μ` factors out `ν s`. -/
@[to_additive
/-- Integrating `z ↦ f (x - g z)` over `s` against an `s`-finite measure `ν` and then `x` against
a right-invariant `s`-finite measure `μ` factors out `ν s`. -/]
theorem lintegral_setLIntegral_div_right [MeasurableInv G] (hf : AEMeasurable f μ) {α : Type*}
    [MeasurableSpace α] {ν : Measure α} [SFinite ν] {g : α → G} {s : Set α}
    (hg : AEMeasurable g (ν.restrict s)) :
    ∫⁻ x, ∫⁻ z in s, f (x / g z) ∂ν ∂μ = ν s * ∫⁻ x, f x ∂μ := by
  rw [lintegral_lintegral_div_right hf hg, Measure.restrict_apply_univ]

end LIntegral

section SMulSet

variable {G α E : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [MeasurableConstSMul G α]
  {μ : Measure α} [SMulInvariantMeasure G α μ] [NormedAddCommGroup E]

/-- For an invariant measure, an integrand invariant under `g` is integrable on `g • V` exactly
when it is integrable on `V`. -/
theorem integrableOn_smul_set_iff {g : G} {f : α → E} (hf : ∀ x, f (g • x) = f x)
    (V : Set α) : IntegrableOn f (g • V) μ ↔ IntegrableOn f V μ := by
  rw [← image_smul, (measurePreserving_smul g μ).integrableOn_image
    (measurableEmbedding_const_smul g)]
  exact iff_of_eq (congrArg (IntegrableOn · V μ) (funext hf))

variable [NormedSpace ℝ E]

/-- For an invariant measure, an integrand invariant under `g` has the same integral over
`g • V` as over `V`. No integrability or measurability hypothesis is needed. -/
theorem setIntegral_smul_set {g : G} {f : α → E} (hf : ∀ x, f (g • x) = f x)
    (V : Set α) : ∫ x in g • V, f x ∂μ = ∫ x in V, f x ∂μ := by
  rw [← image_smul, (measurePreserving_smul g μ).setIntegral_image_emb
    (measurableEmbedding_const_smul g) f V]
  simp_rw [hf]

end SMulSet

section Translation

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddRightInvariant]

/-- Moving a translation from the integrable function `w` onto the bounded measurable test
function `φ` inside an integral:
`∫ (w (· + a) - w) * φ = ∫ (φ (· - a) - φ) * w`. -/
theorem integral_comp_add_sub_mul_eq {w φ : E → ℝ} (hw : Integrable w μ)
    (hφ : Measurable φ) {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) (a : E) :
    ∫ x, (w (x + a) - w x) * φ x ∂μ = ∫ y, (φ (y - a) - φ y) * w y ∂μ := by
  have h1 : Integrable (fun x => w (x + a) * φ x) μ :=
    (hw.comp_add_right a).mul_bdd hφ.aestronglyMeasurable (ae_of_all _ hM)
  have h2 : Integrable (fun x => w x * φ x) μ :=
    hw.mul_bdd hφ.aestronglyMeasurable (ae_of_all _ hM)
  have h3 : Integrable (fun x => w x * φ (x - a)) μ :=
    hw.mul_bdd (hφ.comp (continuous_sub_right a).measurable).aestronglyMeasurable
      (ae_of_all _ fun x => hM _)
  calc ∫ x, (w (x + a) - w x) * φ x ∂μ
      = ∫ x, w (x + a) * φ x ∂μ - ∫ y, w y * φ y ∂μ := by
        rw [← integral_sub h1 h2]
        congr 1 with x
        ring
    _ = ∫ y, w y * φ (y - a) ∂μ - ∫ y, w y * φ y ∂μ := by
        rw [← integral_add_right_eq_self (fun y => w y * φ (y - a)) a]
        simp
    _ = ∫ y, (φ (y - a) - φ y) * w y ∂μ := by
        rw [← integral_sub h3 h2]
        congr 1 with y
        ring

end Translation

end TauCeti

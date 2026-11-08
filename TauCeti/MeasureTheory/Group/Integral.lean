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

For a measure invariant under a group action, an integrand invariant under `g` has the same
integral, and the same integrability, on `g • V` as on `V`.

The integral of a difference quotient of an integrable function against a compactly supported
continuous test function can be moved onto the test function, by translation invariance.

## Main declarations

* `TauCeti.integral_comp_add_sub_mul_eq`: moving a translation of an integrable function
  onto a compactly supported continuous test function inside an integral.
* `TauCeti.setIntegral_ball_eq_setIntegral_ball_zero_add`: translating a ball integral to the
  origin.
* `TauCeti.setIntegral_ball_sub_eq_zero`, `TauCeti.setAverage_ball_id`: for a measure invariant
  under translation and negation, the centre of a ball is its barycentre.
* `TauCeti.setIntegral_smul_set`, `TauCeti.integrableOn_smul_set_iff`: integrals and
  integrability of an invariant integrand over a translated set.
-/

public section

open MeasureTheory Metric Set

open scoped Pointwise

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

/-- Moving a translation from the integrable function `w` onto the compactly supported continuous
test function `φ` inside an integral:
`∫ (w (· + a) - w) * φ = ∫ (φ (· - a) - φ) * w`. -/
theorem integral_comp_add_sub_mul_eq {w φ : E → ℝ} (hw : Integrable w μ)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (a : E) :
    ∫ x, (w (x + a) - w x) * φ x ∂μ = ∫ y, (φ (y - a) - φ y) * w y ∂μ := by
  obtain ⟨M, hM⟩ := hφ.bounded_above_of_compact_support hφc
  have h1 : Integrable (fun x => w (x + a) * φ x) μ :=
    (hw.comp_add_right a).mul_bdd hφ.aestronglyMeasurable (ae_of_all _ hM)
  have h2 : Integrable (fun x => w x * φ x) μ :=
    hw.mul_bdd hφ.aestronglyMeasurable (ae_of_all _ hM)
  have h3 : Integrable (fun x => w x * φ (x - a)) μ :=
    hw.mul_bdd (hφ.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
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

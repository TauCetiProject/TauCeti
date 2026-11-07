/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Integration on groups

Integrating against an inverse measure is equivalent to precomposing the integrand with
inversion. This transports integrals between left and right Haar measures.

For a measure invariant under addition, an integral over a ball can be translated to a ball
about the origin. Only measurability of translations is needed; the measure need not be an
additive Haar measure, and the function need not be integrable.

For a measure invariant under a group action, an integrand invariant under `g` has the same
integral, and the same integrability, on `g • V` as on `V`.

For a topological group with Borel σ-algebra, integrating a compactly supported continuous
vector-valued function against any left-invariant measure finite on compacts scales its integral
against a Haar measure by `Measure.haarScalarFactor`.

## Main declarations

* `TauCeti.setIntegral_ball_eq_setIntegral_ball_zero_add`: translating a ball integral to the
  origin.
* `TauCeti.setIntegral_smul_set`, `TauCeti.integrableOn_smul_set_iff`: integrals and
  integrability of an invariant integrand over a translated set.
* `TauCeti.integral_isMulLeftInvariant_eq_haarScalarFactor_smul`: comparing Bochner integrals of
  compactly supported continuous functions against a left-invariant locally finite measure and a
  Haar measure via `Measure.haarScalarFactor`.
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

/-- **Uniqueness of left-invariant Bochner integrals**: integrating a compactly supported
continuous vector-valued function against any left-invariant measure `μ'` finite on compacts
scales the integral against a Haar measure `μ` by `Measure.haarScalarFactor μ' μ`. -/
theorem integral_isMulLeftInvariant_eq_haarScalarFactor_smul {G E : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ' μ : Measure G) [μ.IsHaarMeasure] [IsFiniteMeasureOnCompacts μ'] [μ'.IsMulLeftInvariant]
    {f : G → E} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∫ x, f x ∂μ' = (Measure.haarScalarFactor μ' μ : ℝ) • ∫ x, f x ∂μ := by
  -- Pass from real-valued integrands to `E`-valued ones by testing against the dual of `E`.
  by_cases hE : CompleteSpace E
  · refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun φ => ?_
    have hfi' : Integrable f μ' := hf.integrable_of_hasCompactSupport hfc
    have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport hfc
    rw [map_smul, ← φ.integral_comp_comm hfi', ← φ.integral_comp_comm hfi,
      Measure.integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport μ' μ
        (f := fun x => φ (f x)) (φ.continuous.comp hf) (hfc.comp_left φ.map_zero),
      integral_smul_nnreal_measure, NNReal.smul_def]
  · simp [integral_of_not_completeSpace hE]

end TauCeti

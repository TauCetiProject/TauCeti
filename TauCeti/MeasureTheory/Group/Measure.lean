/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.WithDensity
-- Proof-only: change of variables in set integrals along a measurable embedding.
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Measures and the group operations

This file records measure formulas for finite families of disjoint additive translates.  In
lattice-point counting, the formula turns disjoint translates of a fundamental-domain cell into
measure bounds that can be compared with the number of cells. It also records that inverting or
negating a probability measure gives a probability measure, so that the law of `X⁻¹` or `-X` can
be used wherever a probability law is expected, and that restricting an inversion-invariant
measure to a symmetric set, or weighting it by an even density, keeps it inversion-invariant.

## Main results

* `Measure.measure_biUnion_sub_mem`: a finite disjoint union of translates has measure
  equal to the number of translates times the measure of the original set.
* `Measure.isProbabilityMeasure_inv`, `Measure.isProbabilityMeasure_neg`: the inverse and the
  negation of a probability measure are probability measures.
* `Measure.map_inv_comp`, `Measure.map_neg_comp`: composing a pushforward from the inverted or
  negated measure with inversion or negation recovers the original pushforward.
* `Measure.ae_inv_mem_preimage`, `Measure.ae_neg_mem_preimage`: a full-mass set reflects to a
  full-mass set for the inverted or negated measure.
* `Measure.isInvInvariant_restrict`, `Measure.isNegInvariant_restrict`,
  `Measure.isInvInvariant_withDensity`, `Measure.isNegInvariant_withDensity`: restriction to a
  symmetric set and an even density preserve inversion or negation invariance.
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace TauCeti

variable {E : Type*} [AddGroup E] [MeasurableSpace E] [MeasurableAdd E]

/-- The union of finitely many pairwise disjoint translates of a measurable set has measure equal
to the number of translates times the measure of the set. -/
theorem _root_.MeasureTheory.Measure.measure_biUnion_sub_mem
    (mu : Measure E) [mu.IsAddRightInvariant]
    {G F : Set E} (hFm : MeasurableSet F)
    (hdisj : ∀ w₁ ∈ G, ∀ w₂ ∈ G, w₁ ≠ w₂ →
      Disjoint {y : E | y - w₁ ∈ F} {y : E | y - w₂ ∈ F})
    {T : Finset E} (hT : ↑T ⊆ G) :
    mu (⋃ w ∈ T, {y : E | y - w ∈ F}) = T.card * mu F := by
  rw [measure_biUnion_finset (fun w₁ h₁ w₂ h₂ h ↦ hdisj w₁ (hT h₁) w₂ (hT h₂) h)
    fun w _ ↦ by
      have h : {y : E | y - w ∈ F} = (fun y : E ↦ y + -w) ⁻¹' F := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, sub_eq_add_neg]
      rw [h]
      exact measurableSet_preimage (measurable_id.add_const (-w)) hFm]
  have htranslate (w : E) : mu {y : E | y - w ∈ F} = mu F := by
    have h : {y : E | y - w ∈ F} = (fun y : E ↦ y + -w) ⁻¹' F := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, sub_eq_add_neg]
    rw [h, measure_preimage_add_right]
  simp_rw [htranslate]
  simp

end TauCeti

namespace MeasureTheory.Measure

/-- The inverse of a probability measure is a probability measure. -/
@[to_additive /-- The negation of a probability measure is a probability measure. -/]
instance isProbabilityMeasure_inv {G : Type*} [MeasurableSpace G] [Inv G] (μ : Measure G)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure μ.inv := by
  rw [inv_def]
  infer_instance

/-- Pushing an inverted measure forward along `f` after inversion gives the pushforward of the
original measure along `f`. -/
@[to_additive /-- Pushing a negated measure forward along `f` after negation gives the pushforward
of the original measure along `f`. -/]
theorem map_inv_comp {G H : Type*} [MeasurableSpace G] [MeasurableSpace H] [InvolutiveInv G]
    [MeasurableInv G] (μ : Measure G) {f : G → H} (hf : AEMeasurable (f ∘ Inv.inv) μ.inv) :
    μ.inv.map (f ∘ Inv.inv) = μ.map f := by
  rw [inv_def] at hf ⊢
  rw [AEMeasurable.map_map_of_aemeasurable hf measurable_inv.aemeasurable]
  congr 1
  ext x
  simp

/-- A set of full measure reflects to a set of full measure for the inverted measure. -/
@[to_additive /-- A set of full measure reflects to a set of full measure for the negated
measure. -/]
theorem ae_inv_mem_preimage {G : Type*} [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G]
    (μ : Measure G) {s : Set G} (hs : MeasurableSet s) (hμs : ∀ᵐ x ∂μ, x ∈ s) :
    ∀ᵐ x ∂μ.inv, x ∈ Inv.inv ⁻¹' s := by
  simp only [Set.mem_preimage]
  rw [inv_def, ae_map_iff measurable_inv.aemeasurable (measurable_inv hs)]
  simpa only [inv_inv] using hμs

section InvolutiveInv

variable {G : Type*} [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G] {μ : Measure G}

/-- The restriction of an inversion-invariant measure to a set closed under inversion is
inversion-invariant. -/
@[to_additive /-- The restriction of a negation-invariant measure to a set closed under negation
is negation-invariant. -/]
theorem isInvInvariant_restrict [μ.IsInvInvariant] {s : Set G} (hs : s⁻¹ = s) :
    (μ.restrict s).IsInvInvariant := by
  refine ⟨Measure.ext fun t ht ↦ ?_⟩
  rw [inv_apply, restrict_apply ht.inv, restrict_apply ht, ← measure_inv μ, Set.inter_inv,
    inv_inv, hs]

/-- An inversion-invariant measure weighted by a density invariant under inversion is
inversion-invariant. -/
@[to_additive /-- A negation-invariant measure weighted by an even density is
negation-invariant. -/]
theorem isInvInvariant_withDensity [μ.IsInvInvariant] {f : G → ℝ≥0∞} (hf : ∀ x, f x⁻¹ = f x) :
    (μ.withDensity f).IsInvInvariant := by
  refine ⟨Measure.ext fun t ht ↦ ?_⟩
  rw [inv_apply, withDensity_apply _ ht.inv, withDensity_apply _ ht, ← Set.inv_preimage]
  simpa only [hf] using (measurePreserving_inv μ).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.inv G).measurableEmbedding f t

end InvolutiveInv

end MeasureTheory.Measure

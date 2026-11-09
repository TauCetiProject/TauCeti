/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
# Uniform Lᵖ integrability of conditional expectations

For a fixed Lᵖ random variable, its conditional expectations over an arbitrary family of
sub-σ-algebras are uniformly Lᵖ integrable, for every finite exponent p ≥ 1. In particular,
Vitali's theorem applies to almost surely convergent sequences from such a family.

The proof uses Mathlib's `Integrable.uniformIntegrable_condExp` for the real random variable
`‖f‖ ^ p` and conditional Jensen's inequality. No ordering of the σ-algebras is required.
-/

public section

open Filter
open scoped ENNReal

namespace MeasureTheory

variable {Ω E ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsFiniteMeasure μ] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {p : ℝ≥0∞} {f : Ω → E}

/-- Conditional expectations of one Lᵖ variable form a uniformly Lᵖ integrable family,
for finite p ≥ 1, even when the conditioning σ-algebras are not ordered. -/
theorem MemLp.uniformIntegrable_condExp (hf : MemLp f p μ) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {ℱ : ι → MeasurableSpace Ω} (hℱ : ∀ i, ℱ i ≤ mΩ) :
    UniformIntegrable (fun i => μ[f | ℱ i]) p μ := by
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le hp)) hp_top
  have hp_real : 1 ≤ p.toReal := by
    rwa [← ENNReal.toReal_one, ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top]
  have hint : Integrable (fun ω => ‖f ω‖ ^ p.toReal) μ :=
    (integrable_norm_rpow_iff hf.aestronglyMeasurable
      (ne_of_gt (zero_lt_one.trans_le hp)) hp_top).2 hf
  have hui := hint.uniformIntegrable_condExp hℱ
  refine ⟨unifIntegrable_iff.2 ?_, (eLpNorm f p μ).toNNReal, fun i => ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := unifIntegrable_iff.1 hui.1 (ε ^ p.toReal)
      (ENNReal.rpow_pos_of_nonneg hε hp_pos.le)
    refine ⟨δ, hδ, fun i s hs => ?_⟩
    apply (ENNReal.rpow_le_rpow_iff hp_pos).mp
    calc
      eLpNorm (μ[f | ℱ i]) p (μ.restrict s) ^ p.toReal =
          eLpNorm (fun ω => ‖μ[f | ℱ i] ω‖ ^ p.toReal) 1 (μ.restrict s) := by
        rw [eLpNorm_norm_rpow _ integrable_condExp.aestronglyMeasurable.restrict hp_pos]
        simp [ENNReal.ofReal_toReal hp_top]
      _ ≤ eLpNorm (μ[(fun ω => ‖f ω‖ ^ p.toReal) | ℱ i]) 1 (μ.restrict s) := by
        have hm : AEStronglyMeasurable (μ[f | ℱ i]) μ :=
          integrable_condExp.aestronglyMeasurable
        apply eLpNorm_mono_ae
          ((hm.norm.aemeasurable.pow_const p.toReal).aestronglyMeasurable.restrict)
        filter_upwards [ae_restrict_of_ae (Integrable.norm_condExp_rpow_le hp_real hint),
          ae_restrict_of_ae (condExp_nonneg (μ := μ) (m := ℱ i)
            (f := fun ω => ‖f ω‖ ^ p.toReal)
            (Eventually.of_forall fun ω => Real.rpow_nonneg (norm_nonneg _) _))] with ω hω hnonneg
        simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
          abs_of_nonneg hnonneg] using hω
      _ ≤ ε ^ p.toReal := hbound i s hs
  · exact (eLpNorm_condExp_le_eLpNorm f hp).trans_eq
      (ENNReal.coe_toNNReal hf.eLpNorm_ne_top).symm

end MeasureTheory

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan Braams, Claude
-/
module

public import Mathlib.MeasureTheory.Group.Pointwise
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Averaging a kernel over a finite group

Let a finite group `G` act measurably on measurable spaces `X` and `A`. A kernel `κ : Kernel X A`
is *equivariant* if `κ (g • x) = (κ x).map (g • ·)` for all `g` and `x`. The group average

  `groupAverage G κ x = |G|⁻¹ • ∑ g, (κ (g⁻¹ • x)).map (g • ·)`

of any kernel is equivariant, it is Markov if `κ` is, and it fixes exactly the equivariant
kernels. Composed with a measure `μ` on `X`, it is the average over `g` of the images under
`g • ·` of `κ ∘ₘ μ.map (g⁻¹ • ·)`.

## Main definitions

* `ProbabilityTheory.Kernel.groupAverage G κ`: the average of the translates of `κ`.

## Main results

* `ProbabilityTheory.Kernel.groupAverage_smul_apply`: the group average is equivariant.
* `ProbabilityTheory.Kernel.groupAverage_eq_self_iff`: a kernel is its own group average
  exactly when it is equivariant; in particular averaging is idempotent
  (`ProbabilityTheory.Kernel.groupAverage_groupAverage`).
* `ProbabilityTheory.Kernel.groupAverage_comp`: the composition of the group average with a
  measure.

The construction is adapted from the proof of `CKSD.exists_equivariant_rule_risk_eq_average` in
lean-CKSD, `CKSD/Inference/Decision.lean`.

## References

* T. S. Ferguson, *Mathematical Statistics: A Decision Theoretic Approach*, Academic Press
  (1967), §4.3.
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace ProbabilityTheory.Kernel

variable (G : Type*) {X A : Type*} [Group G] [Fintype G] [MeasurableSpace X] [MeasurableSpace A]
  [MulAction G X] [MulAction G A] [MeasurableConstSMul G X] [MeasurableConstSMul G A]

/-- The average over a finite group `G` of the translates `x ↦ (κ (g⁻¹ • x)).map (g • ·)` of a
kernel `κ`. It is an equivariant kernel (`groupAverage_smul_apply`). -/
noncomputable def groupAverage (κ : Kernel X A) : Kernel X A where
  toFun x := (Fintype.card G : ℝ≥0∞)⁻¹ • ∑ g : G, (κ (g⁻¹ • x)).map (g • ·)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
    simp only [smul_apply, FunLike.coe_sum, Finset.sum_apply,
      Measure.map_apply (measurable_const_smul _) hs, smul_eq_mul]
    exact (Finset.measurable_sum _ fun g _ ↦ (κ.measurable_coe
      (measurable_const_smul g hs)).comp (measurable_const_smul g⁻¹)).const_mul _

/-- The value of the group average of a kernel at a point. -/
theorem groupAverage_apply (κ : Kernel X A) (x : X) :
    groupAverage G κ x = (Fintype.card G : ℝ≥0∞)⁻¹ • ∑ g : G, (κ (g⁻¹ • x)).map (g • ·) :=
  (rfl)

/-- The measure of a set under the group average of a kernel. -/
theorem groupAverage_apply' (κ : Kernel X A) (x : X) (s : Set A) :
    groupAverage G κ x s = (Fintype.card G : ℝ≥0∞)⁻¹ * ∑ g : G, κ (g⁻¹ • x) (g⁻¹ • s) := by
  simp only [groupAverage_apply, smul_apply, FunLike.coe_sum, Finset.sum_apply,
    (measurableEmbedding_const_smul _).map_apply, preimage_smul, smul_eq_mul]

/-- The group average of a Markov kernel is a Markov kernel. -/
instance (κ : Kernel X A) [IsMarkovKernel κ] : IsMarkovKernel (groupAverage G κ) where
  isProbabilityMeasure x := ⟨by
    simp only [groupAverage_apply' G κ x univ, smul_set_univ, measure_univ,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _)⟩

/-- The group average of a kernel is equivariant. -/
theorem groupAverage_smul_apply (κ : Kernel X A) (h : G) (x : X) :
    groupAverage G κ (h • x) = (groupAverage G κ x).map (h • ·) := by
  ext s hs
  rw [Measure.map_apply (measurable_const_smul h) hs, groupAverage_apply',
    groupAverage_apply', preimage_smul]
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulLeft h)]
  simp [mul_smul]

/-- A kernel is its own group average exactly when it is equivariant. -/
theorem groupAverage_eq_self_iff {κ : Kernel X A} :
    groupAverage G κ = κ ↔ ∀ (g : G) x, κ (g • x) = (κ x).map (g • ·) := by
  refine ⟨fun h ↦ h ▸ groupAverage_smul_apply G κ, fun hκ ↦ ?_⟩
  ext x s hs
  have hg (g : G) : κ (g⁻¹ • x) (g⁻¹ • s) = κ x s := by
    rw [hκ, Measure.map_apply (measurable_const_smul _) (hs.const_smul _), preimage_smul,
      inv_inv, smul_inv_smul]
  simp only [groupAverage_apply', hg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← mul_assoc]
  rw [ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _), one_mul]

/-- Averaging is idempotent: the group average of a group average is itself. -/
@[simp]
theorem groupAverage_groupAverage (κ : Kernel X A) :
    groupAverage G (groupAverage G κ) = groupAverage G κ :=
  (groupAverage_eq_self_iff G).2 (groupAverage_smul_apply G κ)

/-- Composing the group average of `κ` with a measure `μ` averages the images under `g • ·` of
`κ ∘ₘ μ.map (g⁻¹ • ·)`. -/
theorem groupAverage_comp (κ : Kernel X A) (μ : Measure X) :
    groupAverage G κ ∘ₘ μ =
      (Fintype.card G : ℝ≥0∞)⁻¹ • ∑ g : G, (κ ∘ₘ μ.map (g⁻¹ • ·)).map (g • ·) := by
  ext s hs
  have hm (g : G) : Measurable fun x ↦ κ (g⁻¹ • x) (g⁻¹ • s) :=
    (κ.measurable_coe (hs.const_smul _)).comp (measurable_const_smul _)
  simp only [Measure.bind_apply hs (Kernel.aemeasurable _), groupAverage_apply',
    smul_apply, FunLike.coe_sum, Finset.sum_apply, smul_eq_mul,
    Measure.map_apply (measurable_const_smul _) hs, preimage_smul,
    Measure.bind_apply (hs.const_smul _) (Kernel.aemeasurable _),
    MeasureTheory.lintegral_map (κ.measurable_coe (hs.const_smul _)) (measurable_const_smul _)]
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun g _ ↦ hm g),
    lintegral_finsetSum _ fun g _ ↦ hm g]

end ProbabilityTheory.Kernel

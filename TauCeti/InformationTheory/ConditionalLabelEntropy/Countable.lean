/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.ConditionalLabelEntropy
public import TauCeti.InformationTheory.PartitionEntropy
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Conditional entropy of standard-Borel labels on countable labels

For measurable labels `a : X → ι` and `b : X → κ` into countable types, the conditional entropy
`TauCeti.conditionalLabelEntropy μ a b`, defined by integrating the information of the atom of
`a` under the conditional distribution given `b`, agrees with the countable formula
`TauCeti.conditionalPartitionEntropy μ a b = ∑ p_ij log (p_j / p_ij)`.

## Main results

* `TauCeti.condDistrib_apply_singleton_ae_eq`: for a countable label `b`, almost everywhere the
  conditional probability of the atom of `a` given `b = b x` is the ratio of the masses of the
  cell and of the atom of `b`.
* `TauCeti.conditionalLabelEntropy_eq_conditionalPartitionEntropy`: the two conditional entropies
  agree on countable measurable labels, under a finite measure.

## References

* G. A. Margulis and G. M. Tomanov, Invariant measures for actions of unipotent groups over local
  fields on homogeneous spaces, Invent. Math. 116 (1994), 347–392, §9.3, pp. 381–383,
  doi:10.1007/BF01231565.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace TauCeti

variable {X ι κ : Type*} {mX : MeasurableSpace X} {μ : Measure X}

/-- Almost every point lies in an atom of positive mass of a countable measurable label. -/
theorem ae_measure_preimage_singleton_ne_zero [Countable κ] {b : X → κ} :
    ∀ᵐ x ∂μ, μ (b ⁻¹' {b x}) ≠ 0 := by
  rw [ae_iff]
  refine measure_mono_null (t := ⋃ j ∈ {j | μ (b ⁻¹' {j}) = 0}, b ⁻¹' {j}) ?_
    ((measure_biUnion_null_iff (Set.to_countable _)).2 fun j hj ↦ hj)
  intro x hx
  simp only [ne_eq, not_not, Set.mem_ofPred_eq] at hx
  exact Set.mem_biUnion (x := b x) hx rfl

variable [IsFiniteMeasure μ] [MeasurableSpace ι] [StandardBorelSpace ι] [Nonempty ι] [Countable κ]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- **Conditional probabilities of atoms.** For a measurable standard-Borel label `a` and a
countable measurable label `b`, almost everywhere the
conditional probability of the atom `{a x}` given `b = b x` is
`μ (a ⁻¹' {a x} ∩ b ⁻¹' {b x}) / μ (b ⁻¹' {b x})`. -/
theorem condDistrib_apply_singleton_ae_eq {a : X → ι} {b : X → κ} (ha : Measurable a)
    (hb : Measurable b) :
    ∀ᵐ x ∂μ, condDistrib a b μ (b x) {a x} =
      (μ (b ⁻¹' {b x}))⁻¹ * μ (a ⁻¹' {a x} ∩ b ⁻¹' {b x}) := by
  filter_upwards [ae_measure_preimage_singleton_ne_zero (μ := μ) (b := b)] with x hx
  have hmap : μ.map b {b x} = μ (b ⁻¹' {b x}) := Measure.map_apply hb (measurableSet_singleton _)
  rw [condDistrib_apply_of_ne_zero hb ha (b x) (hmap ▸ hx), hmap,
    Measure.map_apply (hb.prodMk ha) ((measurableSet_singleton _).prod (measurableSet_singleton _)),
    Set.mk_preimage_prod, Set.inter_comm]

/-- The per-cell identity: the information of a cell of mass `m` inside an atom of mass `q`,
weighted by `m`, is `m * log (q / m)`. -/
private theorem atomInformation_mul_eq {m q : ℝ≥0∞} (hmq : m ≤ q) (hq : q ≠ ∞) :
    atomInformation (q⁻¹ * m) * m = ENNReal.ofReal (m.toReal * log (q.toReal / m.toReal)) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  have hq0 : q ≠ 0 := (pos_of_ne_zero hm |>.trans_le hmq).ne'
  have hmt : m ≠ ∞ := ne_top_of_le_ne_top hq hmq
  rw [atomInformation_of_ne_zero (mul_ne_zero (ENNReal.inv_ne_zero.2 hq) hm),
    ENNReal.toReal_mul, ENNReal.toReal_inv, ← div_eq_inv_mul, log_div (ENNReal.toReal_ne_zero.2
      ⟨hm, hmt⟩) (ENNReal.toReal_ne_zero.2 ⟨hq0, hq⟩), log_div (ENNReal.toReal_ne_zero.2
      ⟨hq0, hq⟩) (ENNReal.toReal_ne_zero.2 ⟨hm, hmt⟩), mul_comm m.toReal,
    ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hmt, neg_sub]

/-- **Agreement with the countable formula.** On countable measurable labels, the conditional
entropy defined through the conditional distribution is the countable conditional entropy
`∑ p_ij log (p_j / p_ij)`. -/
theorem conditionalLabelEntropy_eq_conditionalPartitionEntropy [Countable ι] {a : X → ι}
    {b : X → κ} (ha : Measurable a) (hb : Measurable b) :
    conditionalLabelEntropy μ a b = conditionalPartitionEntropy μ a b := by
  set g : ι × κ → ℝ≥0∞ := fun p ↦
    atomInformation ((μ (b ⁻¹' {p.2}))⁻¹ * μ (a ⁻¹' {p.1} ∩ b ⁻¹' {p.2})) with hg
  have hc : Measurable fun x ↦ (a x, b x) := ha.prodMk hb
  have hcell (p : ι × κ) : (fun x ↦ (a x, b x)) ⁻¹' {p} = a ⁻¹' {p.1} ∩ b ⁻¹' {p.2} := by
    ext x
    simp [Prod.ext_iff]
  calc conditionalLabelEntropy μ a b = ∫⁻ x, g (a x, b x) ∂μ := by
        rw [conditionalLabelEntropy_def]
        refine lintegral_congr_ae ?_
        filter_upwards [condDistrib_apply_singleton_ae_eq (μ := μ) ha hb] with x hx
        rw [hx]
    _ = ∑' p, g p * μ (a ⁻¹' {p.1} ∩ b ⁻¹' {p.2}) := by
        rw [← lintegral_map (f := g) (measurable_of_countable g) hc, lintegral_countable']
        refine tsum_congr fun p ↦ ?_
        rw [Measure.map_apply hc (measurableSet_singleton _), hcell]
    _ = conditionalPartitionEntropy μ a b := by
        rw [conditionalPartitionEntropy_def]
        refine tsum_congr fun p ↦ ?_
        rw [hg, atomInformation_mul_eq (measure_mono Set.inter_subset_right) (measure_ne_top _ _)]
        rfl

end TauCeti

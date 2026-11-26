/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.PartitionEntropy
import TauCeti.InformationTheory.PartitionEntropy.Finite
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import TauCeti.MeasureTheory.Measure.Real

/-!
# Equality in subadditivity of partition entropy

Under a probability measure the entropy of the join of two measurable countable labels is at most
the sum of their entropies, `H(a ∨ b) ≤ H(a) + H(b)`
(`TauCeti.countablePartitionEntropy_pair_le_add`), with equality for independent labels
(`TauCeti.countablePartitionEntropy_pair_of_indepFun`). This file proves the converse for labels
with finitely many values: equality forces independence.

Write `p_ij`, `P_i`, `Q_j` for the masses of the cells `a ⁻¹' {i} ∩ b ⁻¹' {j}` and of the atoms
`a ⁻¹' {i}`, `b ⁻¹' {j}`. Then `H(a) + H(b) - H(a ∨ b)` is the sum over the cells of
`p_ij log p_ij - p_ij log P_i - p_ij log Q_j - p_ij + P_i Q_j`, each of which is nonnegative by
`log y ≤ y - 1` and vanishes only when `p_ij = P_i Q_j`.

## Main results

* `TauCeti.indepFun_of_countablePartitionEntropy_pair_eq_add`: if `H(a ∨ b) = H(a) + H(b)` for
  measurable labels with finitely many values, they are independent.
* `TauCeti.countablePartitionEntropy_pair_eq_add_iff_indepFun`: for such labels,
  `H(a ∨ b) = H(a) + H(b)` exactly when `a` and `b` are independent.

This is the equality case of subadditivity used by item 5 of §4.1 of the ClassicalErgodicTheory
roadmap.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, 2023, Proposition 4.3, p. 106 (the locator given
  by the ClassicalErgodicTheory roadmap).
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace TauCeti

variable {X ι κ : Type*} {mX : MeasurableSpace X} {μ : Measure X}

/-- The per-cell gap in subadditivity: for `0 ≤ p ≤ P` and `p ≤ Q`,
`0 ≤ p log p - p log P - p log Q - p + P Q`. -/
private theorem cellGap_nonneg {p P Q : ℝ} (hp : 0 ≤ p) (hpP : p ≤ P) (hpQ : p ≤ Q) :
    0 ≤ p * log p - p * log P - p * log Q - p + P * Q := by
  rcases hp.eq_or_lt with rfl | hp
  · simpa using mul_nonneg (hp.trans hpP) (hp.trans hpQ)
  have hP := hp.trans_le hpP
  have hQ := hp.trans_le hpQ
  have hy := log_le_sub_one_of_pos (show 0 < P * Q / p by positivity)
  rw [log_div (by positivity) hp.ne', log_mul hP.ne' hQ.ne'] at hy
  have h := mul_le_mul_of_nonneg_left hy hp.le
  rw [show p * (P * Q / p - 1) = P * Q - p by field_simp, mul_sub, mul_add] at h
  linarith

/-- The per-cell gap vanishes only at `p = P Q`. -/
private theorem eq_mul_of_cellGap_eq_zero {p P Q : ℝ} (hp : 0 ≤ p) (hpP : p ≤ P) (hpQ : p ≤ Q)
    (h : p * log p - p * log P - p * log Q - p + P * Q = 0) : p = P * Q := by
  rcases hp.eq_or_lt with rfl | hp
  · simpa using h.symm
  have hP := hp.trans_le hpP
  have hQ := hp.trans_le hpQ
  by_contra hne
  have hy := log_lt_sub_one_of_pos (show 0 < P * Q / p by positivity)
    (by rw [Ne, div_eq_one_iff_eq hp.ne']; exact fun h' ↦ hne h'.symm)
  rw [log_div (by positivity) hp.ne', log_mul hP.ne' hQ.ne'] at hy
  have h' := mul_lt_mul_of_pos_left hy hp
  rw [show p * (P * Q / p - 1) = P * Q - p by field_simp, mul_sub, mul_add] at h'
  linarith

/-- Measurable labels into countable types whose cells have the product masses are
independent. -/
private theorem indepFun_of_forall_measureReal_inter_eq_mul [IsFiniteMeasure μ] [Countable ι]
    [Countable κ] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] {a : X → ι} {b : X → κ} (ha : Measurable a) (hb : Measurable b)
    (h : ∀ i j, μ.real (a ⁻¹' {i} ∩ b ⁻¹' {j}) = μ.real (a ⁻¹' {i}) * μ.real (b ⁻¹' {j})) :
    IndepFun a b μ := by
  rw [indepFun_iff_map_prod_eq_prod_map_map ha.aemeasurable hb.aemeasurable,
    Measure.ext_iff_singleton]
  rintro ⟨i, j⟩
  rw [Measure.map_apply (ha.prodMk hb) (measurableSet_singleton _), ← Set.singleton_prod_singleton,
    Measure.prod_prod, Measure.map_apply ha (measurableSet_singleton _),
    Measure.map_apply hb (measurableSet_singleton _), Set.mk_preimage_prod,
    ← ofReal_measureReal, ← ofReal_measureReal, ← ofReal_measureReal,
    ← ENNReal.ofReal_mul measureReal_nonneg]
  exact congrArg ENNReal.ofReal (h i j)

variable [Finite ι] [Finite κ] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- **Equality in subadditivity.** Under a probability measure (or the zero measure), if two
measurable labels with finitely many values satisfy `H(a ∨ b) = H(a) + H(b)`, they are
independent. -/
theorem indepFun_of_countablePartitionEntropy_pair_eq_add [IsZeroOrProbabilityMeasure μ]
    {a : X → ι} {b : X → κ} (ha : Measurable a) (hb : Measurable b)
    (h : countablePartitionEntropy μ (fun x ↦ (a x, b x)) =
      countablePartitionEntropy μ a + countablePartitionEntropy μ b) :
    IndepFun a b μ := by
  obtain rfl | _ := eq_zero_or_isProbabilityMeasure (μ := μ)
  · exact indepFun_of_forall_measureReal_inter_eq_mul ha hb fun _ _ ↦ by simp
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  set p : ι → κ → ℝ := fun i j ↦ μ.real (a ⁻¹' {i} ∩ b ⁻¹' {j})
  set P : ι → ℝ := fun i ↦ μ.real (a ⁻¹' {i})
  set Q : κ → ℝ := fun j ↦ μ.real (b ⁻¹' {j})
  have hA : ∀ i, MeasurableSet (a ⁻¹' {i}) := fun i ↦ ha (measurableSet_singleton i)
  have hB : ∀ j, MeasurableSet (b ⁻¹' {j}) := fun j ↦ hb (measurableSet_singleton j)
  have hrow : ∀ i, ∑ j, p i j = P i := fun i ↦ by
    simp only [p, P, Set.inter_comm (a ⁻¹' _)]
    exact sum_measureReal_preimage_singleton_inter hB _
  have hcol : ∀ j, ∑ i, p i j = Q j := fun j ↦ sum_measureReal_preimage_singleton_inter hA _
  have hPsum : ∑ i, P i = 1 := sum_measureReal_preimage_singleton_eq_one hA
  have hQsum : ∑ j, Q j = 1 := sum_measureReal_preimage_singleton_eq_one hB
  have hreal : ∑ i, ∑ j, negMulLog (p i j) = ∑ i, negMulLog (P i) + ∑ j, negMulLog (Q j) := by
    rw [countablePartitionEntropy_eq_ofReal_labelEntropy,
      countablePartitionEntropy_eq_ofReal_labelEntropy,
      countablePartitionEntropy_eq_ofReal_labelEntropy,
      ← ENNReal.ofReal_add (labelEntropy_nonneg a) (labelEntropy_nonneg b),
      ENNReal.ofReal_eq_ofReal_iff (labelEntropy_nonneg _)
        (add_nonneg (labelEntropy_nonneg a) (labelEntropy_nonneg b)), labelEntropy_pair,
      labelEntropy_def, labelEntropy_def] at h
    exact h
  -- The per-cell gaps are nonnegative and sum to zero, so each vanishes.
  have hnn : ∀ i j, 0 ≤ p i j * log (p i j) - p i j * log (P i) - p i j * log (Q j) - p i j +
      P i * Q j := fun i j ↦ cellGap_nonneg measureReal_nonneg
    (measureReal_mono Set.inter_subset_left) (measureReal_mono Set.inter_subset_right)
  have hgap : ∑ i, ∑ j, (p i j * log (p i j) - p i j * log (P i) - p i j * log (Q j) - p i j +
      P i * Q j) = 0 := by
    have e1 : ∑ i, ∑ j, p i j * log (P i) = ∑ i, P i * log (P i) := by
      simp_rw [← Finset.sum_mul, hrow]
    have e2 : ∑ i, ∑ j, p i j * log (Q j) = ∑ j, Q j * log (Q j) := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hcol]
    have e3 : ∑ i, ∑ j, P i * Q j = 1 := by
      simp_rw [← Finset.mul_sum, hQsum, mul_one, hPsum]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, e1, e2, e3, hrow, hPsum]
    simp only [negMulLog, neg_mul, Finset.sum_neg_distrib] at hreal
    linarith
  refine indepFun_of_forall_measureReal_inter_eq_mul ha hb fun i j ↦ ?_
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    hnn i j).mp hgap i (Finset.mem_univ i)
  exact eq_mul_of_cellGap_eq_zero measureReal_nonneg (measureReal_mono Set.inter_subset_left)
    (measureReal_mono Set.inter_subset_right)
    ((Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ hnn i j).mp hi j (Finset.mem_univ j))

/-- **Equality in subadditivity.** Under a probability measure (or the zero measure), measurable
labels with finitely many values satisfy `H(a ∨ b) = H(a) + H(b)` exactly when they are
independent. -/
theorem countablePartitionEntropy_pair_eq_add_iff_indepFun [IsZeroOrProbabilityMeasure μ]
    {a : X → ι} {b : X → κ} (ha : Measurable a) (hb : Measurable b) :
    countablePartitionEntropy μ (fun x ↦ (a x, b x)) =
        countablePartitionEntropy μ a + countablePartitionEntropy μ b ↔ IndepFun a b μ :=
  ⟨indepFun_of_countablePartitionEntropy_pair_eq_add ha hb,
    countablePartitionEntropy_pair_of_indepFun ha hb⟩

end TauCeti

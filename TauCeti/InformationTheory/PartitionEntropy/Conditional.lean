/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ConditionalProbability
public import TauCeti.InformationTheory.PartitionEntropy
import Mathlib.MeasureTheory.Measure.Real
import TauCeti.Analysis.SpecialFunctions.Log.MulLog
import TauCeti.MeasureTheory.Measure.Restrict
import TauCeti.Probability.ConditionalProbability
import TauCeti.Probability.Independence.Basic

/-!
# Conditional partition entropy as an average over atoms

For a measurable label `b`, the conditional partition entropy
`H(a | b)` is the average over the atoms `B_j = b ⁻¹' {j}` of the entropy of `a` under the
conditional probability `μ[|B_j]`, weighted by `μ B_j`. This formula gives the refinement,
subadditivity and independence properties of conditional entropy.

## Main results

* `TauCeti.conditionalPartitionEntropy_eq_tsum_cond`:
  `H(a | b) = ∑' j, μ (b ⁻¹' {j}) * H_{μ[|b ⁻¹' {j}]}(a)`.
* `TauCeti.conditionalPartitionEntropy_eq_of_indepFun`: `H(a | b) = H(a)` when `a` is
  independent of a measurable countable label `b`.
* `TauCeti.conditionalPartitionEntropy_comp_le`: coarsening the conditioned label does not
  increase conditional entropy, `H(f ∘ a | b) ≤ H(a | b)`.
* `TauCeti.conditionalPartitionEntropy_pair_le`, `TauCeti.conditionalPartitionEntropy_le_comp`:
  refining the conditioning label does not increase conditional entropy,
  `H(a | b ∨ c) ≤ H(a | b)` and `H(a | c) ≤ H(a | f ∘ c)`.
* `TauCeti.conditionalPartitionEntropy_pair_left_le_add`,
  `TauCeti.conditionalPartitionEntropy_pair_pair_le_add`: conditional subadditivity,
  `H(a ∨ a' | b) ≤ H(a | b) + H(a' | b)` and `H(a ∨ a' | b ∨ b') ≤ H(a | b) + H(a' | b')`.

Together with `TauCeti.conditionalPartitionEntropy_le` these give `H(ξ | η) ≤ H(ξ)` with equality
for independent labels, and monotonicity of `H(ξ | η)` in both arguments.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, 2023, Propositions 4.2–4.3, p. 106.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace TauCeti

variable {X ι κ κ' : Type*} {mX : MeasurableSpace X} {μ : Measure X}

/-- The per-cell identity behind `conditionalPartitionEntropy_eq_tsum_cond`: the mass of an atom
`B` times the `negMulLog` of the conditional mass of `A` given `B` is the cell term
`p log (q / p)` of `A ∩ B`. -/
private theorem measure_mul_ofReal_negMulLog_cond (μ : Measure X) {B : Set X}
    (hB : MeasurableSet B) (A : Set X) :
    μ B * ENNReal.ofReal (negMulLog (μ[|B].real A)) =
      ENNReal.ofReal (μ.real (A ∩ B) * log (μ.real B / μ.real (A ∩ B))) := by
  rw [cond_real_apply hB]
  rcases eq_or_ne (μ B) ∞ with htop | htop
  · simp [measureReal_def, htop]
  rw [Set.inter_comm, ← ofReal_measureReal htop, ← ENNReal.ofReal_mul measureReal_nonneg,
    mul_negMulLog_div]

/-- **Conditional entropy as an average.** For a measurable label `b`, the conditional entropy
`H(a | b)` is the sum over the atoms `b ⁻¹' {j}` of their mass times the entropy of `a` under the
conditional probability given the atom. Atoms of infinite mass contribute zero on both sides. -/
theorem conditionalPartitionEntropy_eq_tsum_cond [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (a : X → ι) {b : X → κ} (hb : Measurable b) :
    conditionalPartitionEntropy μ a b =
      ∑' j, μ (b ⁻¹' {j}) * countablePartitionEntropy μ[|b ⁻¹' {j}] a := by
  rw [conditionalPartitionEntropy_def, tsum_prod', tsum_comm]
  refine tsum_congr fun j ↦ ?_
  rw [countablePartitionEntropy_def, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun i ↦
    (measure_mul_ofReal_negMulLog_cond μ (hb (measurableSet_singleton j)) _).symm

section Measurable

variable [MeasurableSpace κ] [MeasurableSingletonClass κ]

private theorem conditionalPartitionEntropy_eq_of_indepFun_of_isZeroOrProbabilityMeasure
    [IsZeroOrProbabilityMeasure μ] [Countable κ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] {a : X → ι} {b : X → κ} (hb : Measurable b)
    (hab : IndepFun a b μ) :
    conditionalPartitionEntropy μ a b = countablePartitionEntropy μ a := by
  have hatom : ∀ j, μ (b ⁻¹' {j}) * countablePartitionEntropy μ[|b ⁻¹' {j}] a =
      μ (b ⁻¹' {j}) * countablePartitionEntropy μ a := fun j ↦ by
    rcases eq_or_ne (μ (b ⁻¹' {j})) 0 with h0 | h0
    · simp [h0]
    congr 1
    simp only [countablePartitionEntropy_def, measureReal_def]
    refine tsum_congr fun i ↦ ?_
    rw [cond_apply (hb (measurableSet_singleton j)), Set.inter_comm,
      hab.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton i)
        (measurableSet_singleton j)]
    simp [mul_comm, mul_assoc, ENNReal.mul_inv_cancel h0 (measure_ne_top μ _)]
  rw [conditionalPartitionEntropy_eq_tsum_cond a hb]
  simp only [hatom, ENNReal.tsum_mul_right, tsum_measure_preimage_singleton_eq_measure_univ hb]
  obtain rfl | _ := eq_zero_or_isProbabilityMeasure (μ := μ) <;> simp

/-- **Independence.** Conditioning on an independent measurable countable label does not change
the entropy: `H(a | b) = H(a)`. This holds for every measure, not only for probability
measures. -/
theorem conditionalPartitionEntropy_eq_of_indepFun [Countable κ] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {a : X → ι} {b : X → κ} (hb : Measurable b)
    (hab : IndepFun a b μ) :
    conditionalPartitionEntropy μ a b = countablePartitionEntropy μ a := by
  rcases eq_or_ne (μ Set.univ) ∞ with htop | htop
  · -- Every atom of `a` and every cell has real mass zero.
    have hC : ∀ i j, μ.real (a ⁻¹' {i} ∩ b ⁻¹' {j}) = 0 := fun i j ↦
      hab.measureReal_inter_preimage_eq_zero_of_measure_univ_eq_top htop
        (measurableSet_singleton i) (measurableSet_singleton j)
    have hA : ∀ i, μ.real (a ⁻¹' {i}) = 0 := fun i ↦
      hab.measureReal_preimage_eq_zero_of_measure_univ_eq_top htop (measurableSet_singleton i)
    simp [conditionalPartitionEntropy_def, countablePartitionEntropy_def, hA, hC]
  -- Otherwise independence forces `μ` to be zero or a probability measure.
  have : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.mpr htop⟩
  have := hab.isZeroOrProbabilityMeasure
  exact conditionalPartitionEntropy_eq_of_indepFun_of_isZeroOrProbabilityMeasure hb hab

/-- **Coarsening the conditioned label.** For a measurable label `b`, `H(f ∘ a | b) ≤ H(a | b)`
for every countable label `a`. -/
theorem conditionalPartitionEntropy_comp_le [Countable ι] (a : X → ι)
    (f : ι → κ') {b : X → κ} (hb : Measurable b) :
    conditionalPartitionEntropy μ (f ∘ a) b ≤ conditionalPartitionEntropy μ a b := by
  rw [conditionalPartitionEntropy_eq_tsum_cond _ hb, conditionalPartitionEntropy_eq_tsum_cond _ hb]
  gcongr
  exact countablePartitionEntropy_comp_le a f

/-- The conditional entropy given a join, as an average over the atoms of the first label: for a
finite measure and measurable labels `b`, `c`,
`H(a | b ∨ c) = ∑' j, μ (b ⁻¹' {j}) * H_{μ[|b ⁻¹' {j}]}(a | c)`. -/
theorem conditionalPartitionEntropy_pair_eq_tsum_cond [IsFiniteMeasure μ] [MeasurableSpace κ']
    [MeasurableSingletonClass κ'] (a : X → ι) {b : X → κ} {c : X → κ'} (hb : Measurable b)
    (hc : Measurable c) :
    conditionalPartitionEntropy μ a (fun x ↦ (b x, c x)) =
      ∑' j, μ (b ⁻¹' {j}) * conditionalPartitionEntropy μ[|b ⁻¹' {j}] a c := by
  rw [conditionalPartitionEntropy_eq_tsum_cond a (hb.prodMk hc), tsum_prod']
  refine tsum_congr fun j ↦ ?_
  have hB := hb (measurableSet_singleton j)
  rw [conditionalPartitionEntropy_eq_tsum_cond a hc, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun k ↦ ?_
  have hC := hc (measurableSet_singleton k)
  have hcell : (fun x ↦ (b x, c x)) ⁻¹' {(j, k)} = b ⁻¹' {j} ∩ c ⁻¹' {k} := by
    rw [← Set.singleton_prod_singleton, Set.mk_preimage_prod]
  rw [hcell, cond_cond_eq_cond_inter hB hC, ← mul_assoc, mul_comm (μ (b ⁻¹' {j})),
    cond_mul_eq_inter' hB (measure_ne_top μ _)]

/-- **Refining the conditioning label.** For a finite measure and measurable labels `b`, `c`, the
second into a countable type, `H(a | b ∨ c) ≤ H(a | b)`. -/
theorem conditionalPartitionEntropy_pair_le [IsFiniteMeasure μ] [MeasurableSpace κ']
    [MeasurableSingletonClass κ'] [Countable κ'] (a : X → ι) {b : X → κ} {c : X → κ'}
    (hb : Measurable b) (hc : Measurable c) :
    conditionalPartitionEntropy μ a (fun x ↦ (b x, c x)) ≤ conditionalPartitionEntropy μ a b := by
  rw [conditionalPartitionEntropy_pair_eq_tsum_cond a hb hc,
    conditionalPartitionEntropy_eq_tsum_cond a hb]
  gcongr
  exact conditionalPartitionEntropy_le a hc

/-- **Coarsening the conditioning label.** For a finite measure and a measurable label `c` into a
countable type, `H(a | c) ≤ H(a | f ∘ c)` for every map `f`. -/
theorem conditionalPartitionEntropy_le_comp [IsFiniteMeasure μ] [Countable κ]
    [MeasurableSpace κ'] [MeasurableSingletonClass κ'] (a : X → ι) {c : X → κ} (hc : Measurable c)
    (f : κ → κ') :
    conditionalPartitionEntropy μ a c ≤ conditionalPartitionEntropy μ a (f ∘ c) := by
  calc conditionalPartitionEntropy μ a c
      = conditionalPartitionEntropy μ a (fun x ↦ ((f ∘ c) x, c x)) :=
        (conditionalPartitionEntropy_comp_right_of_injective (e := fun j ↦ (f j, j)) a c
          fun _ _ h ↦ congrArg Prod.snd h).symm
    _ ≤ _ := conditionalPartitionEntropy_pair_le a ((measurable_of_countable f).comp hc) hc

/-- **Conditional subadditivity.** For a measurable label `b`, conditional entropy is subadditive
in the conditioned label: `H(a ∨ a' | b) ≤ H(a | b) + H(a' | b)` for measurable countable labels
`a`, `a'`. -/
theorem conditionalPartitionEntropy_pair_left_le_add {ι' : Type*} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι'] [MeasurableSpace ι']
    [MeasurableSingletonClass ι'] {a : X → ι} {a' : X → ι'} (ha : Measurable a)
    (ha' : Measurable a') {b : X → κ} (hb : Measurable b) :
    conditionalPartitionEntropy μ (fun x ↦ (a x, a' x)) b ≤
      conditionalPartitionEntropy μ a b + conditionalPartitionEntropy μ a' b := by
  rw [conditionalPartitionEntropy_eq_tsum_cond _ hb, conditionalPartitionEntropy_eq_tsum_cond _ hb,
    conditionalPartitionEntropy_eq_tsum_cond _ hb, ← tsum_add]
  refine tsum_le_tsum fun j ↦ ?_
  rw [← mul_add]
  gcongr
  exact countablePartitionEntropy_pair_le_add ha ha'

/-- **Subadditivity of conditional entropy over joins.** For a finite measure and measurable
countable labels, `H(a ∨ a' | b ∨ b') ≤ H(a | b) + H(a' | b')`. -/
theorem conditionalPartitionEntropy_pair_pair_le_add {ι' : Type*} [IsFiniteMeasure μ]
    [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι']
    [MeasurableSpace ι'] [MeasurableSingletonClass ι'] [Countable κ] [Countable κ']
    [MeasurableSpace κ'] [MeasurableSingletonClass κ'] {a : X → ι} {a' : X → ι'} {b : X → κ}
    {b' : X → κ'} (ha : Measurable a) (ha' : Measurable a') (hb : Measurable b)
    (hb' : Measurable b') :
    conditionalPartitionEntropy μ (fun x ↦ (a x, a' x)) (fun x ↦ (b x, b' x)) ≤
      conditionalPartitionEntropy μ a b + conditionalPartitionEntropy μ a' b' := by
  refine (conditionalPartitionEntropy_pair_left_le_add ha ha' (hb.prodMk hb')).trans ?_
  gcongr
  · exact conditionalPartitionEntropy_le_comp a (hb.prodMk hb') Prod.fst
  · exact conditionalPartitionEntropy_le_comp a' (hb.prodMk hb') Prod.snd

end Measurable

end TauCeti

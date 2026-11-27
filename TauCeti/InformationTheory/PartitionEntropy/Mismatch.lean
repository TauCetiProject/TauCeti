/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.PartitionEntropy.Conditional
public import TauCeti.MeasureTheory.MeasurableSpace.Sum
import Mathlib.MeasureTheory.Measure.Real

/-!
# The disagreement label of two labels

For labels `a b : X → ι`, `mismatchLabel a b` records where `a` and `b` disagree, together with the
value of `a` there. Knowing `b` and `mismatchLabel a b` determines `a`, so the conditional entropy
`H(a | b)` is at most the entropy of `mismatchLabel a b`; on a finite alphabet, this entropy is
small when `a` and `b` disagree only on a set of small probability.

## Main results

* `TauCeti.conditionalPartitionEntropy_le_countablePartitionEntropy_mismatchLabel`: `H(a | b)` is
  at most the entropy of the disagreement label.
* `TauCeti.tendsto_countablePartitionEntropy_mismatchLabel`: the entropy of the disagreement label
  tends to zero when the probability of disagreement does.
-/

public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace TauCeti

variable {X ι : Type*} {mX : MeasurableSpace X} {μ : Measure X}

/-- The label recording where the labels `a` and `b` disagree, and the value of `a` there: it is
`Sum.inr ()` where `a x = b x` and `Sum.inl (a x)` elsewhere. -/
def mismatchLabel [DecidableEq ι] (a b : X → ι) : X → ι ⊕ Unit :=
  fun x ↦ if a x = b x then Sum.inr () else Sum.inl (a x)

/-- Unfolding `mismatchLabel`. -/
theorem mismatchLabel_apply [DecidableEq ι] (a b : X → ι) (x : X) :
    mismatchLabel a b x = if a x = b x then Sum.inr () else Sum.inl (a x) :=
  (rfl)

/-- The disagreement label takes the value `Sum.inr ()` exactly where the labels agree. -/
@[simp]
theorem mismatchLabel_eq_inr_iff [DecidableEq ι] {a b : X → ι} {x : X} {u : Unit} :
    mismatchLabel a b x = Sum.inr u ↔ a x = b x := by
  by_cases h : a x = b x <;> simp [mismatchLabel_apply, h]

/-- The disagreement label takes the value `Sum.inl i` exactly where the labels disagree and `a`
takes the value `i`. -/
@[simp]
theorem mismatchLabel_eq_inl_iff [DecidableEq ι] {a b : X → ι} {x : X} {i : ι} :
    mismatchLabel a b x = Sum.inl i ↔ a x ≠ b x ∧ a x = i := by
  by_cases h : a x = b x <;> simp [mismatchLabel_apply, h]

/-- The disagreement label of measurable countable labels is measurable. -/
theorem measurable_mismatchLabel [DecidableEq ι] [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {a b : X → ι} (ha : Measurable a) (hb : Measurable b) :
    Measurable (mismatchLabel a b) :=
  (measurable_of_countable fun p : ι × ι ↦
    if p.1 = p.2 then (Sum.inr () : ι ⊕ Unit) else Sum.inl p.1).comp (ha.prodMk hb)

/-- **Conditional entropy and disagreement.** Under a probability measure (or the zero measure),
for measurable countable labels `a`, `b` into the same type, `H(a | b)` is at most the entropy of
`mismatchLabel a b`: knowing `b` and where `a` differs from `b`, with the value of `a` there,
determines `a`. -/
theorem conditionalPartitionEntropy_le_countablePartitionEntropy_mismatchLabel
    [IsZeroOrProbabilityMeasure μ] [DecidableEq ι] [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {a b : X → ι} (ha : Measurable a) (hb : Measurable b) :
    conditionalPartitionEntropy μ a b ≤ countablePartitionEntropy μ (mismatchLabel a b) := by
  have hd := measurable_mismatchLabel ha hb
  have hab : a = (fun p : (ι ⊕ Unit) × ι ↦ p.1.elim id fun _ ↦ p.2) ∘
      fun x ↦ (mismatchLabel a b x, b x) := by
    funext x
    by_cases h : a x = b x <;> simp [mismatchLabel_apply, h]
  calc conditionalPartitionEntropy μ a b
      ≤ conditionalPartitionEntropy μ (fun x ↦ (mismatchLabel a b x, b x)) b := by
        conv_lhs => rw [hab]
        exact conditionalPartitionEntropy_comp_le _ _ hb
    _ ≤ conditionalPartitionEntropy μ (mismatchLabel a b) b +
          conditionalPartitionEntropy μ b b :=
        conditionalPartitionEntropy_pair_left_le_add hd hb hb
    _ ≤ countablePartitionEntropy μ (mismatchLabel a b) := by
        rw [conditionalPartitionEntropy_self, add_zero]
        exact conditionalPartitionEntropy_le _ hb

/-- If measurable labels `b n` into a finite type agree with the measurable label `a` outside
sets of probabilities tending to zero, the entropies of the disagreement labels
`mismatchLabel a (b n)` tend to zero. -/
theorem tendsto_countablePartitionEntropy_mismatchLabel [IsProbabilityMeasure μ] [DecidableEq ι]
    [Finite ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] {a : X → ι} {b : ℕ → X → ι}
    (ha : Measurable a) (hb : ∀ n, Measurable (b n))
    (h : Tendsto (fun n ↦ μ.real {x | a x ≠ b n x}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ countablePartitionEntropy μ (mismatchLabel a (b n))) atTop (𝓝 0) := by
  have := Fintype.ofFinite ι
  simp only [countablePartitionEntropy_def, tsum_fintype]
  rw [show (0 : ℝ≥0∞) = ∑ _ : ι ⊕ Unit, ENNReal.ofReal (negMulLog 0) by simp]
  refine tendsto_finsetSum _ fun o _ ↦ ?_
  rcases o with i | u
  · -- The atom `Sum.inl i` lies in the disagreement set.
    refine ENNReal.tendsto_ofReal ((continuous_negMulLog.tendsto 0).comp ?_)
    refine squeeze_zero (fun _ ↦ measureReal_nonneg) (fun n ↦ measureReal_mono ?_) h
    intro x hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff, mismatchLabel_eq_inl_iff] at hx
    exact hx.1
  · -- The atom `Sum.inr ()` is the agreement set, of probability tending to one.
    rw [show negMulLog 0 = negMulLog 1 by simp]
    refine ENNReal.tendsto_ofReal ((continuous_negMulLog.tendsto 1).comp ?_)
    have hreal (n : ℕ) : μ.real (mismatchLabel a (b n) ⁻¹' {Sum.inr u}) =
        1 - μ.real {x | a x ≠ b n x} := by
      have hset : mismatchLabel a (b n) ⁻¹' {Sum.inr u} = {x | a x ≠ b n x}ᶜ := by
        ext x
        simp
      have hmeas : MeasurableSet {x | a x ≠ b n x} :=
        (ha.prodMk (hb n)) (Set.to_countable {p : ι × ι | p.1 ≠ p.2}).measurableSet
      rw [hset, measureReal_compl hmeas, probReal_univ]
    simp only [hreal]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h

end TauCeti

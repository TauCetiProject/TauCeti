/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.MeasureEntropy.Congr
public import TauCeti.InformationTheory.PartitionEntropy.Conditional
import TauCeti.InformationTheory.PartitionEntropy.Finite

/-!
# Entropy rates under conditional entropy, and the finite-partition formula

For a measure-preserving map `T` of a probability space and measurable countable labels `a`, `b`,
the entropy rate of `a` exceeds that of `b` by at most the conditional entropy of `a` given `b`:
`h(T, a) ≤ h(T, b) + H(a | b)`. Consequently the entropy rate is continuous on finite labels for
the Rokhlin distance `H(a | b) + H(b | a)`, and truncating a label of finite entropy shows that
the Kolmogorov–Sinai entropy `TauCeti.measureEntropy μ T` is the supremum of the entropy rates of
the measurable finite labels.

## Main results

* `TauCeti.conditionalPartitionEntropy_iteratedPartitionLabel_le_mul`: for measure-preserving `T`,
  `H(join_n a | join_n b) ≤ n * H(a | b)`.
* `TauCeti.partitionEntropyRate_le_add_conditionalPartitionEntropy`:
  `h(T, a) ≤ h(T, b) + H(a | b)`.
* `TauCeti.abs_toReal_partitionEntropyRate_sub_le`: on finite labels,
  `|h(T, a) - h(T, b)| ≤ H(a | b) + H(b | a)`.
* `TauCeti.measureEntropy_eq_iSup_fin`: `h(T)` is the supremum of the entropy rates of measurable
  labels into `Fin n`, `n : ℕ`; the value `∞` is retained.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, 2023, §§4.1–4.3, pp. 103–108; Problems 4.8–4.9,
  p. 130. Entropies there are in base 2; here they use natural logarithms.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace TauCeti

variable {X ι κ : Type*} {mX : MeasurableSpace X} {μ : Measure X} {T : X → X}

section Countable

variable [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable κ]
  [MeasurableSpace κ] [MeasurableSingletonClass κ] {a : X → ι} {b : X → κ}

/-- For a measure-preserving map under a probability measure (or the zero measure), the
conditional entropy of the length-`n` itinerary of `a` given that of `b` is at most
`n * H(a | b)`. -/
theorem conditionalPartitionEntropy_iteratedPartitionLabel_le_mul [IsZeroOrProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (ha : Measurable a) (hb : Measurable b) (n : ℕ) :
    conditionalPartitionEntropy μ (iteratedPartitionLabel T a n) (iteratedPartitionLabel T b n) ≤
      n * conditionalPartitionEntropy μ a b := by
  have ha' := measurable_iteratedPartitionLabel hT.measurable ha
  have hb' := measurable_iteratedPartitionLabel hT.measurable hb
  induction n with
  | zero =>
    refine le_of_le_of_eq (conditionalPartitionEntropy_le _ (hb' 0)) ?_
    rw [iteratedPartitionLabel_zero, countablePartitionEntropy_const, Nat.cast_zero, zero_mul]
  | succ n ih =>
    have hTn := hT.iterate n
    have hpb : Measurable fun x ↦
        (iteratedPartitionLabel T b n x, iteratedPartitionLabel T b 1 (T^[n] x)) :=
      (hb' n).prodMk ((hb' 1).comp hTn.measurable)
    have happ : Function.Injective fun p : (Fin n → κ) × (Fin 1 → κ) ↦ Fin.append p.1 p.2 :=
      (Fin.appendEquiv n 1).injective
    rw [iteratedPartitionLabel_add T a n 1, iteratedPartitionLabel_add T b n 1,
      conditionalPartitionEntropy_comp_right_of_injective _ _ happ]
    refine (conditionalPartitionEntropy_comp_le _ _ hpb).trans <|
      (conditionalPartitionEntropy_pair_pair_le_add (ha' n) ((ha' 1).comp hTn.measurable) (hb' n)
        ((hb' 1).comp hTn.measurable)).trans ?_
    have hone : conditionalPartitionEntropy μ (iteratedPartitionLabel T a 1)
        (iteratedPartitionLabel T b 1) ≤ conditionalPartitionEntropy μ a b := by
      rw [iteratedPartitionLabel_one, iteratedPartitionLabel_one,
        conditionalPartitionEntropy_comp_right_of_injective _ _ Function.const_injective]
      exact conditionalPartitionEntropy_comp_le _ _ hb
    rw [conditionalPartitionEntropy_comp_of_measurePreserving hTn (ha' 1) (hb' 1), Nat.cast_succ,
      add_mul, one_mul]
    exact add_le_add ih hone

/-- **Entropy rate and conditional entropy.** For a measure-preserving map of a probability space
(or the zero measure) and measurable countable labels `a`, `b`,
`h(T, a) ≤ h(T, b) + H(a | b)`. -/
theorem partitionEntropyRate_le_add_conditionalPartitionEntropy [IsZeroOrProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (ha : Measurable a) (hb : Measurable b) :
    partitionEntropyRate μ T a ≤
      partitionEntropyRate μ T b + conditionalPartitionEntropy μ a b := by
  rw [partitionEntropyRate_def μ T b, ENNReal.iInf_add]
  refine le_iInf fun n ↦ (partitionEntropyRate_le_div n.succ_pos μ T a).trans ?_
  have ha' := measurable_iteratedPartitionLabel hT.measurable ha (n + 1)
  have key : countablePartitionEntropy μ (iteratedPartitionLabel T a (n + 1)) ≤
      countablePartitionEntropy μ (iteratedPartitionLabel T b (n + 1)) +
        (n + 1 : ℕ) * conditionalPartitionEntropy μ a b :=
    calc countablePartitionEntropy μ (iteratedPartitionLabel T a (n + 1))
        ≤ countablePartitionEntropy μ fun x ↦
            (iteratedPartitionLabel T a (n + 1) x, iteratedPartitionLabel T b (n + 1) x) :=
          countablePartitionEntropy_comp_le (μ := μ) (fun x ↦
            (iteratedPartitionLabel T a (n + 1) x, iteratedPartitionLabel T b (n + 1) x)) Prod.fst
      _ = countablePartitionEntropy μ (iteratedPartitionLabel T b (n + 1)) +
            conditionalPartitionEntropy μ (iteratedPartitionLabel T a (n + 1))
              (iteratedPartitionLabel T b (n + 1)) :=
          countablePartitionEntropy_pair_eq_add ha' _
      _ ≤ _ := by
          gcongr
          exact conditionalPartitionEntropy_iteratedPartitionLabel_le_mul hT ha hb (n + 1)
  refine (ENNReal.div_le_div_right key _).trans_eq ?_
  rw [ENNReal.add_div, Nat.cast_succ, mul_comm _ (conditionalPartitionEntropy μ a b),
    ENNReal.mul_div_cancel_right (by positivity) (by simp)]

end Countable

/-- **Continuity in the Rokhlin distance.** For a measure-preserving map of a probability space
(or the zero measure) and measurable finite labels `a`, `b`, the entropy rates differ by at most
the Rokhlin distance: `|h(T, a) - h(T, b)| ≤ H(a | b) + H(b | a)`. -/
theorem abs_toReal_partitionEntropyRate_sub_le [IsZeroOrProbabilityMeasure μ] [Finite ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Finite κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] {a : X → ι} {b : X → κ} (hT : MeasurePreserving T μ μ)
    (ha : Measurable a) (hb : Measurable b) :
    |(partitionEntropyRate μ T a).toReal - (partitionEntropyRate μ T b).toReal| ≤
      (conditionalPartitionEntropy μ a b).toReal + (conditionalPartitionEntropy μ b a).toReal := by
  have hfa : partitionEntropyRate μ T a ≠ ∞ :=
    ne_top_of_le_ne_top (countablePartitionEntropy_ne_top μ a) (partitionEntropyRate_le μ T a)
  have hfb : partitionEntropyRate μ T b ≠ ∞ :=
    ne_top_of_le_ne_top (countablePartitionEntropy_ne_top μ b) (partitionEntropyRate_le μ T b)
  have hab := conditionalPartitionEntropy_ne_top μ a b
  have hba := conditionalPartitionEntropy_ne_top μ b a
  have h₁ := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfb, hab⟩)
    (partitionEntropyRate_le_add_conditionalPartitionEntropy hT ha hb)
  have h₂ := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfa, hba⟩)
    (partitionEntropyRate_le_add_conditionalPartitionEntropy hT hb ha)
  rw [ENNReal.toReal_add hfb hab] at h₁
  rw [ENNReal.toReal_add hfa hba] at h₂
  have := ENNReal.toReal_nonneg (a := conditionalPartitionEntropy μ a b)
  have := ENNReal.toReal_nonneg (a := conditionalPartitionEntropy μ b a)
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- **The finite-partition formula.** For a measure-preserving map of a probability space (or the
zero measure), the Kolmogorov–Sinai entropy is the supremum of the entropy rates of the
measurable finite labels `a : X → Fin n`, the value `∞` included (Sarig 2023, Problem 4.9). -/
theorem measureEntropy_eq_iSup_fin [IsZeroOrProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) :
    measureEntropy μ T =
      ⨆ (n : ℕ) (a : X → Fin n) (_ : Measurable a), partitionEntropyRate μ T a := by
  refine le_antisymm (measureEntropy_le_iff.mpr fun a ha hfin ↦ ?_)
    (iSup₂_le fun n a ↦ iSup_le fun ha ↦ partitionEntropyRate_le_measureEntropy_of_finite T ha)
  -- Truncate `a : X → ℕ` to `min a N`: `h(T, a) ≤ h(T, min a N) + H(a | min a N)`, and the
  -- conditional entropy tends to zero.
  set S := ⨆ (n : ℕ) (a : X → Fin n) (_ : Measurable a), partitionEntropyRate μ T a
  have hq (N : ℕ) : partitionEntropyRate μ T a ≤
      S + conditionalPartitionEntropy μ a fun x ↦ min (a x) N := by
    set q : X → Fin (N + 1) :=
      (fun i : ℕ ↦ (⟨min i N, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (N + 1))) ∘ a
    have hq : Measurable q := (measurable_of_countable _).comp ha
    have hqN : (fun i : ℕ ↦ min i N) ∘ a = Fin.val ∘ q := rfl
    refine (partitionEntropyRate_le_add_conditionalPartitionEntropy hT ha
      ((measurable_of_countable fun i : ℕ ↦ min i N).comp ha)).trans (add_le_add ?_ le_rfl)
    rw [hqN, partitionEntropyRate_comp_of_injective T q Fin.val_injective]
    exact le_iSup₂_of_le (N + 1) q (le_iSup_of_le hq le_rfl)
  calc partitionEntropyRate μ T a
      ≤ ⨅ N : ℕ, (S + conditionalPartitionEntropy μ a fun x ↦ min (a x) N) := le_iInf hq
    _ = S + ⨅ N : ℕ, conditionalPartitionEntropy μ a fun x ↦ min (a x) N :=
        ENNReal.add_iInf.symm
    _ ≤ S + 0 := add_le_add le_rfl
        (ge_of_tendsto' (tendsto_conditionalPartitionEntropy_min hfin) fun N ↦ iInf_le _ N)
    _ = S := add_zero S

end TauCeti

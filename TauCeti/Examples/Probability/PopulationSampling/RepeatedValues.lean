/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PopulationSampling.Distinct
public import TauCeti.Probability.PopulationSampling.RepeatedValues
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
# Examples: sampling discrepancy of the one-pair population and of repeated values

Worked values of the exact sampling discrepancy for small populations, computed from the general
theorems of `TauCeti.Probability.PopulationSampling.OnePair`,
`TauCeti.Probability.PopulationSampling.Distinct` and
`TauCeti.Probability.PopulationSampling.RepeatedValues`. Draw `m` values from a population of
size `n`, once without replacement (`sampleWithoutReplacement`) and once with replacement
(`sampleWithReplacement`), and write `p = n.descFactorial m / n ^ m`,
`t = m.descFactorial 2 / n.descFactorial 2`. The *excess* is the largest event excess
`⨆ A, P A - Q A` of the first law over the second.

The running example is `n = 3`, `m = 2`, with population indices `Fin 3 = {0, 1, 2}`:

* The one-pair population `update id 1 0 : Fin 3 → Fin 3` takes the value `0` twice. The word
  `(0, 0)` is produced by two embeddings and four index maps, the word `(0, 2)` by two of each.
  Sampling without replacement gives `(0, 0)` and `(0, 2)` mass `1/3` each; sampling with
  replacement gives them `4/9` and `2/9`, and gives `(2, 2)` mass `1/9`. A uniform injective
  sample contains both `0` and `1` with probability `t = 1/3`.
* The one-pair excess is `2/9`, which is `1 - p - t * min p (1 - p)` for `p = 2/3`, `t = 1/3`.
  Distinct values (`id : Fin 3 → Fin 3`) have excess `1 - p = 1/3`, and a constant population
  has excess `0`; Mathlib's total variation distances are `4/9`, `2/3` and `0`. Every population
  of three values with a repeated value has excess at most `2/9`, strictly below `1/3`.

For `n = m = 4` the one-pair excess is `13/16` (total variation `13/8`), strictly below the excess
`1 - p = 29/32` of distinct values. For `n = m = 2` the one-pair population is constant, both
sampling laws are the Dirac measure at `(0, 0)`, and the one-pair formula gives `0`.

Two hypotheses of the general theorems are needed. For `n = 2`, `m = 3` the
one-pair excess is `0` while the formula evaluates to `1`, so the one-pair formula needs `m ≤ n`.
For `m = 1` the two-hit mass `t` vanishes, and every population has excess `1 - p = 0`, so the
characterization of the populations attaining `1 - p` as the injective ones needs `2 ≤ m`.

## References

* P. Diaconis and D. Freedman, “Finite exchangeable sequences”, *Annals of Probability* 8
  (1980), 745–764.
-/

public section

noncomputable section

open Function MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Probability

/-! ### Fibres and singleton masses of the one-pair population -/

/-- For `n = 3` and `m = 2`, the word `(0, 0)` of the one-pair population `update id 1 0` is
produced by two embeddings `Fin 2 ↪ Fin 3`, namely `(0, 1)` and `(1, 0)`. -/
theorem natCard_embedding_update_id_fin_three_comp_eq_zero_zero :
    Nat.card {g : Fin 2 ↪ Fin 3 // update id (1 : Fin 3) 0 ∘ g = ![0, 0]} = 2 := by
  have hw : (![0, 0] : Fin 2 → Fin 3) = update id 1 0 ∘ (⟨![0, 1], by decide⟩ : Fin 2 ↪ Fin 3) :=
    by decide
  rw [hw, natCard_embedding_update_id_comp_eq_update_id_comp (by decide)]
  decide

/-- For `n = 3` and `m = 2`, the word `(0, 0)` of the one-pair population `update id 1 0` is
produced by four index maps `Fin 2 → Fin 3`: each position independently takes `0` or `1`. -/
theorem natCard_update_id_fin_three_comp_eq_zero_zero :
    Nat.card {g : Fin 2 → Fin 3 // update id (1 : Fin 3) 0 ∘ g = ![0, 0]} = 4 := by
  have hw : (![0, 0] : Fin 2 → Fin 3) = update id 1 0 ∘ ![0, 1] := by decide
  rw [hw, natCard_update_id_comp_eq_update_id_comp (by decide)]
  decide

/-- For `n = 3` and `m = 2`, a uniform injective sample contains both `0` and `1` with
probability `t = 2/6 = 1/3`. -/
theorem uniformOn_injective_fin_three_mem_range_zero_and_mem_range_one :
    uniformOn {k : Fin 2 → Fin 3 | Injective k} {k | 0 ∈ Set.range k ∧ 1 ∈ Set.range k} =
      1 / 3 := by
  rw [uniformOn_injective_mem_range_and_mem_range (by decide) (by simp), ENNReal.div_eq_div_iff]
    <;> norm_num [Nat.descFactorial]

/-- A sample of size `m = 1` never contains two given indices: the two-hit mass `t` vanishes. -/
theorem uniformOn_injective_fin_one_mem_range_zero_and_mem_range_one :
    uniformOn {k : Fin 1 → Fin 3 | Injective k} {k | 0 ∈ Set.range k ∧ 1 ∈ Set.range k} = 0 := by
  rw [uniformOn_injective_mem_range_and_mem_range (by decide) (by simp)]
  simp [Nat.descFactorial]

/-- Sampling the one-pair population `update id 1 0` of size `3` twice without replacement gives
the word `(0, 0)` mass `2/6 = 1/3`. -/
theorem sampleWithoutReplacement_dirac_update_id_fin_three_singleton_zero_zero :
    sampleWithoutReplacement (ι := Fin 2) (Measure.dirac (update id (1 : Fin 3) 0)) {![0, 0]} =
      1 / 3 := by
  rw [sampleWithoutReplacement_dirac_apply_singleton,
    natCard_embedding_update_id_fin_three_comp_eq_zero_zero, ENNReal.div_eq_div_iff]
    <;> norm_num [Nat.descFactorial]

/-- Sampling the one-pair population `update id 1 0` of size `3` twice with replacement gives the
word `(0, 0)` mass `4/9`. -/
theorem sampleWithReplacement_dirac_update_id_fin_three_singleton_zero_zero :
    sampleWithReplacement (ι := Fin 2) (Measure.dirac (update id (1 : Fin 3) 0)) {![0, 0]} =
      4 / 9 := by
  rw [sampleWithReplacement_dirac_apply_singleton, natCard_update_id_fin_three_comp_eq_zero_zero]
  norm_num

/-- For `n = 3` and `m = 2`, the word `(0, 2)` of the one-pair population `update id 1 0` is
produced by two embeddings `Fin 2 ↪ Fin 3`, namely `(0, 2)` and `(1, 2)`. -/
theorem natCard_embedding_update_id_fin_three_comp_eq_zero_two :
    Nat.card {g : Fin 2 ↪ Fin 3 // update id (1 : Fin 3) 0 ∘ g = ![0, 2]} = 2 := by
  have hw : (![0, 2] : Fin 2 → Fin 3) = update id 1 0 ∘ (⟨![0, 2], by decide⟩ : Fin 2 ↪ Fin 3) :=
    by decide
  rw [hw, natCard_embedding_update_id_comp_eq_update_id_comp (by decide)]
  decide

/-- Sampling the one-pair population `update id 1 0` of size `3` twice without replacement gives
the word `(0, 2)` mass `2/6 = 1/3`. -/
theorem sampleWithoutReplacement_dirac_update_id_fin_three_singleton_zero_two :
    sampleWithoutReplacement (ι := Fin 2) (Measure.dirac (update id (1 : Fin 3) 0)) {![0, 2]} =
      1 / 3 := by
  rw [sampleWithoutReplacement_dirac_apply_singleton,
    natCard_embedding_update_id_fin_three_comp_eq_zero_two, ENNReal.div_eq_div_iff]
    <;> norm_num [Nat.descFactorial]

/-- Sampling the one-pair population `update id 1 0` of size `3` twice with replacement gives the
word `(0, 2)` mass `2/9`: it is produced by the index maps `(0, 2)` and `(1, 2)`. -/
theorem sampleWithReplacement_dirac_update_id_fin_three_singleton_zero_two :
    sampleWithReplacement (ι := Fin 2) (Measure.dirac (update id (1 : Fin 3) 0)) {![0, 2]} =
      2 / 9 := by
  have hw : (![0, 2] : Fin 2 → Fin 3) = update id 1 0 ∘ ![0, 2] := by decide
  have hcard : Nat.card {g : Fin 2 → Fin 3 // update id 1 0 ∘ g = ![0, 2]} = 2 := by
    rw [hw, natCard_update_id_comp_eq_update_id_comp (by decide)]
    decide
  rw [sampleWithReplacement_dirac_apply_singleton, hcard, ENNReal.div_eq_div_iff] <;> norm_num

/-- Sampling the one-pair population `update id 1 0` of size `3` twice with replacement gives the
word `(2, 2)` mass `1/9`: it is produced by the single index map `(2, 2)`. -/
theorem sampleWithReplacement_dirac_update_id_fin_three_singleton_two_two :
    sampleWithReplacement (ι := Fin 2) (Measure.dirac (update id (1 : Fin 3) 0)) {![2, 2]} =
      1 / 9 := by
  have hw : (![2, 2] : Fin 2 → Fin 3) = update id 1 0 ∘ ![2, 2] := by decide
  have hcard : Nat.card {g : Fin 2 → Fin 3 // update id 1 0 ∘ g = ![2, 2]} = 1 := by
    rw [hw, natCard_update_id_comp_eq_update_id_comp (by decide)]
    decide
  rw [sampleWithReplacement_dirac_apply_singleton, hcard, ENNReal.div_eq_div_iff] <;> norm_num

/-! ### The one-pair formula -/

/-- **The one-pair excess for `n = 3`, `m = 2`.** The largest event excess of sampling the
one-pair population `update id 1 0` without replacement over sampling it with replacement is
`2/9`: here `p = 2/3`, `t = 1/3` and `1 - p - t * min p (1 - p) = 2/9`. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_fin_three :
    (⨆ (A : Set (Fin 2 → Fin 3)) (_ : MeasurableSet A),
      sampleWithoutReplacement (Measure.dirac (update id (1 : Fin 3) 0)) A -
        sampleWithReplacement (Measure.dirac (update id (1 : Fin 3) 0)) A) = 2 / 9 := by
  rw [iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq (by decide)
    (by simp)]
  norm_num [Nat.descFactorial, ENNReal.ofReal_div_of_pos]

/-- The total variation distance between sampling the one-pair population `update id 1 0` of
size `3` twice without and with replacement is `4/9`, twice the excess. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_update_id_fin_three :
    etvDist (sampleWithoutReplacement (ι := Fin 2) (Measure.dirac (update id (1 : Fin 3) 0)))
      (sampleWithReplacement (ι := Fin 2) (Measure.dirac (update id (1 : Fin 3) 0))) = 4 / 9 := by
  rw [etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_update_id_eq (by decide)
    (by simp)]
  norm_num [Nat.descFactorial, ENNReal.ofReal_div_of_pos]
  rw [← mul_div_assoc, ENNReal.div_eq_div_iff] <;> norm_num

/-- **The one-pair excess for `n = m = 4`.** Here `p = 24/256 = 3/32`, `t = 1`, and the largest
event excess of sampling the one-pair population `update id 1 0` without replacement over sampling
it with replacement is `1 - 3/32 - 3/32 = 13/16`. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_fin_four :
    (⨆ (A : Set (Fin 4 → Fin 4)) (_ : MeasurableSet A),
      sampleWithoutReplacement (Measure.dirac (update id (1 : Fin 4) 0)) A -
        sampleWithReplacement (Measure.dirac (update id (1 : Fin 4) 0)) A) = 13 / 16 := by
  rw [iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq (by decide)
    (by simp)]
  norm_num [Nat.descFactorial, ENNReal.ofReal_div_of_pos]

/-- The total variation distance between sampling the one-pair population `update id 1 0` of
size `4` four times without and with replacement is `13/8`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_update_id_fin_four :
    etvDist (sampleWithoutReplacement (ι := Fin 4) (Measure.dirac (update id (1 : Fin 4) 0)))
      (sampleWithReplacement (ι := Fin 4) (Measure.dirac (update id (1 : Fin 4) 0))) =
      13 / 8 := by
  rw [etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_update_id_eq (by decide)
    (by simp)]
  norm_num [Nat.descFactorial, ENNReal.ofReal_div_of_pos]
  rw [← mul_div_assoc, ENNReal.div_eq_div_iff] <;> norm_num

/-- For `n = m = 2` the one-pair population `update id 1 0 : Fin 2 → Fin 2` is constant, so
sampling it without replacement gives the word `(0, 0)` almost surely. -/
theorem sampleWithoutReplacement_dirac_update_id_fin_two :
    sampleWithoutReplacement (ι := Fin 2) (Measure.dirac (update id (1 : Fin 2) 0)) =
      Measure.dirac ![0, 0] := by
  have hq : update id (1 : Fin 2) 0 = fun _ => 0 := by decide
  have hw : (![0, 0] : Fin 2 → Fin 2) = fun _ => 0 := by decide
  rw [hq, hw, sampleWithoutReplacement_dirac_const (Embedding.refl _)]

/-- For `n = m = 2`, sampling the constant one-pair population `update id 1 0 : Fin 2 → Fin 2`
with replacement also gives the word `(0, 0)` almost surely. -/
theorem sampleWithReplacement_dirac_update_id_fin_two :
    sampleWithReplacement (ι := Fin 2) (Measure.dirac (update id (1 : Fin 2) 0)) =
      Measure.dirac ![0, 0] := by
  have hq : update id (1 : Fin 2) 0 = fun _ => 0 := by decide
  have hw : (![0, 0] : Fin 2 → Fin 2) = fun _ => 0 := by decide
  rw [hq, hw, sampleWithReplacement_dirac_const]

/-- For `n = m = 2`, the one-pair formula gives excess `0`: here `p = 1/2`, `t = 1` and
`1 - p - t * min p (1 - p) = 0`, in agreement with the two sampling laws being equal. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_fin_two :
    (⨆ (A : Set (Fin 2 → Fin 2)) (_ : MeasurableSet A),
      sampleWithoutReplacement (Measure.dirac (update id (1 : Fin 2) 0)) A -
        sampleWithReplacement (Measure.dirac (update id (1 : Fin 2) 0)) A) = 0 := by
  rw [iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq (by decide)
    (by simp)]
  norm_num [Nat.descFactorial]

/-- **The one-pair formula needs `m ≤ n`.** For `n = 2` and `m = 3` no injective selection
exists, so sampling without replacement is the zero measure and the largest event excess is `0`,
while the one-pair formula `1 - p - t * min p (1 - p)` evaluates to `1` (`p = 0`). -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_fin_two_ne :
    (⨆ (A : Set (Fin 3 → Fin 2)) (_ : MeasurableSet A),
      sampleWithoutReplacement (Measure.dirac (update id (1 : Fin 2) 0)) A -
        sampleWithReplacement (Measure.dirac (update id (1 : Fin 2) 0)) A) ≠
      ENNReal.ofReal
        (let p : ℝ := (2 : ℕ).descFactorial 3 / (2 : ℝ) ^ 3
         let t : ℝ := (3 : ℕ).descFactorial 2 / (2 : ℕ).descFactorial 2
         1 - p - t * min p (1 - p)) := by
  rw [sampleWithoutReplacement_eq_zero_of_card_lt (by simp)]
  norm_num [Nat.descFactorial]

/-! ### Distinct values, constant populations and the repeated-value bound -/

/-- The collision probability `1 - p` for `n = 3`, `m = 2` is `1 - 6/9 = 1/3`. -/
private theorem one_sub_descFactorial_div_pow_fin_three_fin_two :
    1 - (Fintype.card (Fin 3)).descFactorial (Fintype.card (Fin 2)) /
      (Fintype.card (Fin 3) : ℝ≥0∞) ^ Fintype.card (Fin 2) = 1 / 3 := by
  rw [← uniformOn_not_injective_apply_eq, ← ofReal_measureReal,
    uniformOn_real_not_injective_apply_eq]
  norm_num [Nat.descFactorial, ENNReal.ofReal_div_of_pos]

/-- The collision probability `1 - p` for `n = m = 4` is `1 - 24/256 = 29/32`. -/
private theorem one_sub_descFactorial_div_pow_fin_four_fin_four :
    1 - (Fintype.card (Fin 4)).descFactorial (Fintype.card (Fin 4)) /
      (Fintype.card (Fin 4) : ℝ≥0∞) ^ Fintype.card (Fin 4) = 29 / 32 := by
  rw [← uniformOn_not_injective_apply_eq, ← ofReal_measureReal,
    uniformOn_real_not_injective_apply_eq]
  norm_num [Nat.descFactorial, ENNReal.ofReal_div_of_pos]

/-- **Distinct values for `n = 3`, `m = 2`.** The largest event excess of sampling the population
`id : Fin 3 → Fin 3` of distinct values without replacement over sampling it with replacement is
the collision probability `1 - 6/9 = 1/3`. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_id_fin_three :
    (⨆ (A : Set (Fin 2 → Fin 3)) (_ : MeasurableSet A),
      sampleWithoutReplacement (Measure.dirac (id : Fin 3 → Fin 3)) A -
        sampleWithReplacement (Measure.dirac (id : Fin 3 → Fin 3)) A) = 1 / 3 := by
  rw [iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq injective_id
    ⟨![0, 1], by decide⟩ .of_discrete, one_sub_descFactorial_div_pow_fin_three_fin_two]

/-- The total variation distance between sampling the distinct-valued population
`id : Fin 3 → Fin 3` twice without and with replacement is `2/3`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_id_fin_three :
    etvDist (sampleWithoutReplacement (ι := Fin 2) (Measure.dirac (id : Fin 3 → Fin 3)))
      (sampleWithReplacement (ι := Fin 2) (Measure.dirac (id : Fin 3 → Fin 3))) = 2 / 3 := by
  rw [etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq injective_id
    ⟨![0, 1], by decide⟩ .of_discrete, one_sub_descFactorial_div_pow_fin_three_fin_two,
    ← mul_div_assoc, mul_one]

/-- **Constant populations.** Sampling a constant population of size `3` twice gives the
constant word almost surely, with and without replacement, so the largest event excess is `0`.
-/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_const_fin_three
    {α : Type*} [MeasurableSpace α] (c : α) :
    (⨆ (A : Set (Fin 2 → α)) (_ : MeasurableSet A),
      sampleWithoutReplacement (Measure.dirac fun _ : Fin 3 => c) A -
        sampleWithReplacement (Measure.dirac fun _ : Fin 3 => c) A) = 0 := by
  rw [sampleWithoutReplacement_dirac_const ⟨![0, 1], by decide⟩, sampleWithReplacement_dirac_const]
  simp

/-- The total variation distance between sampling a constant population of size `3` twice
without and with replacement is `0`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_const_fin_three
    {α : Type*} [MeasurableSpace α] (c : α) :
    etvDist (sampleWithoutReplacement (ι := Fin 2) (Measure.dirac fun _ : Fin 3 => c))
      (sampleWithReplacement (ι := Fin 2) (Measure.dirac fun _ : Fin 3 => c)) = 0 := by
  rw [sampleWithoutReplacement_dirac_const ⟨![0, 1], by decide⟩, sampleWithReplacement_dirac_const,
    etvDist_self]

/-- **The repeated-value bound for `n = 3`, `m = 2`.** Every population of three values with a
repeated value, in any measurable space, has largest event excess at most `2/9`, the excess of
the one-pair population. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_fin_three_le_of_not_injective
    {α : Type*} [MeasurableSpace α] {x : Fin 3 → α} (hx : ¬ Injective x) :
    (⨆ (A : Set (Fin 2 → α)) (_ : MeasurableSet A),
      sampleWithoutReplacement (Measure.dirac x) A -
        sampleWithReplacement (Measure.dirac x) A) ≤ 2 / 9 := by
  refine (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_of_not_injective
    hx).trans_eq ?_
  norm_num [Nat.descFactorial, ENNReal.ofReal_div_of_pos]

/-- **Strictness for `n = 3`, `m = 2`.** Every population of three values with a repeated value
has largest event excess strictly below `1/3`, the excess of a population of distinct values. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_fin_three_lt_of_not_injective
    {α : Type*} [MeasurableSpace α] {x : Fin 3 → α} (hx : ¬ Injective x) :
    (⨆ (A : Set (Fin 2 → α)) (_ : MeasurableSet A),
      sampleWithoutReplacement (Measure.dirac x) A -
        sampleWithReplacement (Measure.dirac x) A) < 1 / 3 := by
  rw [← one_sub_descFactorial_div_pow_fin_three_fin_two]
  exact iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_lt_of_not_injective hx
    (by simp)

/-- **Distinct values for `n = m = 4`.** The largest event excess of sampling the population
`id : Fin 4 → Fin 4` of distinct values four times without replacement over sampling it with
replacement is the collision probability `1 - 24/256 = 29/32`. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_id_fin_four :
    (⨆ (A : Set (Fin 4 → Fin 4)) (_ : MeasurableSet A),
      sampleWithoutReplacement (Measure.dirac (id : Fin 4 → Fin 4)) A -
        sampleWithReplacement (Measure.dirac (id : Fin 4 → Fin 4)) A) = 29 / 32 := by
  rw [iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq injective_id
    (Embedding.refl _) .of_discrete, one_sub_descFactorial_div_pow_fin_four_fin_four]

/-- **Strictness for `n = m = 4`.** The one-pair excess `13/16` is strictly below the collision
probability `29/32` attained by distinct values. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_fin_four_lt :
    (⨆ (A : Set (Fin 4 → Fin 4)) (_ : MeasurableSet A),
      sampleWithoutReplacement (Measure.dirac (update id (1 : Fin 4) 0)) A -
        sampleWithReplacement (Measure.dirac (update id (1 : Fin 4) 0)) A) < 29 / 32 := by
  rw [← one_sub_descFactorial_div_pow_fin_four_fin_four]
  exact iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_lt_of_not_injective
    (not_injective_iff.2 ⟨1, 0, by decide, by decide⟩) (by simp)

/-! ### Samples of size one -/

/-- **The characterization needs `2 ≤ m`.** For a sample of size `m = 1`, every population of
three values, injective or not, has largest event excess equal to the collision probability
`1 - p = 1 - 3/3 = 0`: both sampling laws agree. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_fin_three_fin_one_eq
    {α : Type*} [MeasurableSpace α] (x : Fin 3 → α) :
    (⨆ (A : Set (Fin 1 → α)) (_ : MeasurableSet A),
      sampleWithoutReplacement (Measure.dirac x) A -
        sampleWithReplacement (Measure.dirac x) A) =
      1 - (Fintype.card (Fin 3)).descFactorial (Fintype.card (Fin 1)) /
        (Fintype.card (Fin 3) : ℝ≥0∞) ^ Fintype.card (Fin 1) := by
  rw [sampleWithoutReplacement_eq_sampleWithReplacement_of_subsingleton]
  norm_num [Nat.descFactorial, ENNReal.div_self]

end TauCeti.Probability

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PopulationSampling.Map
public import TauCeti.Probability.PopulationSampling.OnePair

/-!
# Sampling discrepancy for populations with a repeated value

Draw a sample of size `m = |ι|` from a deterministic population `x : κ → α` of size `n = |κ|`,
once without and once with replacement. Write `p = n.descFactorial m / n ^ m` for the probability
that a uniform index map `ι → κ` is injective and `t = m.descFactorial 2 / n.descFactorial 2`.
For a population of distinct values, `m ≤ n` and a measurable all-distinct event, the largest
event excess between the two laws is the collision probability `1 - p`
(`iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq`).

This file shows that a population with a repeated value does strictly better once `2 ≤ m`.
If `x a = x b` for distinct `a b : κ`, both sampling laws of `x` are pushforwards of those of the
one-pair population `Function.update id b a`, whose exact excess is `1 - p - t * min p (1 - p)`.
Hence the excess of a non-injective population is at most `1 - p - t * min p (1 - p)` in either
direction, for every value space `α` and every sample size (when `m > n`, sampling without
replacement is the zero measure and the bound reads `1`). For `2 ≤ m` this is strictly below
`1 - p`, so for `2 ≤ m ≤ n` and a measurable all-distinct event exactly the injective populations
attain the collision probability. For `m ≤ 1` the two sampling laws coincide for every population
(`sampleWithoutReplacement_eq_sampleWithReplacement_of_subsingleton`).

## Main statements

* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_of_not_injective`,
  `iSup_sampleWithReplacement_sub_sampleWithoutReplacement_dirac_le_of_not_injective`: the
  repeated-value bound on the largest event excess, in both directions;
* `sampleWithoutReplacement_le_sampleWithReplacement_dirac_add_of_not_injective`,
  `sampleWithReplacement_le_sampleWithoutReplacement_dirac_add_of_not_injective`: its eventwise
  form;
* `etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_le_of_not_injective`,
  `tvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_le_of_not_injective`: its total
  variation form;
* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_lt_of_not_injective`,
  `etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_lt_of_not_injective`,
  `tvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_lt_of_not_injective`: for
  `2 ≤ m`, the excess and total variation distances of a non-injective population are strictly
  below the collision values;
* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq_iff_injective`,
  `etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_iff_injective`,
  `tvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_iff_injective`: for
  `2 ≤ m ≤ n` and a measurable all-distinct event, the collision values are attained exactly by
  injective populations;
* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq_iff`,
  `etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_iff`,
  `tvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_iff`: the same characterization
  under `[MeasurableSingletonClass α]` without an explicit measurability hypothesis.

## References

* P. Diaconis and D. Freedman, “Finite exchangeable sequences”, *Annals of Probability* 8
  (1980), 745–764.
-/

public section

noncomputable section

open Function MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Probability

variable {ι κ α : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
  [MeasurableSpace α] {x : κ → α}

section Bound

/-- **The repeated-value bound, excess form.** If the deterministic population `x : κ → α` repeats
a value, the largest event excess of sampling `x` without replacement over sampling it with
replacement is at most `1 - p - t * min p (1 - p)`, where
`p = |κ|.descFactorial |ι| / |κ| ^ |ι|` and `t = |ι|.descFactorial 2 / |κ|.descFactorial 2`.
No assumption on the value space `α` or on the sample size is needed. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_of_not_injective
    (hx : ¬ Injective x) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
      sampleWithoutReplacement (Measure.dirac x) A -
        sampleWithReplacement (Measure.dirac x) A) ≤
      ENNReal.ofReal
        (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ) ^ Fintype.card ι
         let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
         1 - p - t * min p (1 - p)) := by
  classical
  obtain ⟨a, b, hxab, hab⟩ := not_injective_iff.1 hx
  rcases le_or_gt (Fintype.card ι) (Fintype.card κ) with hmn | hnm
  · exact (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_update_id hxab).trans
      (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq hab hmn).le
  · simp [sampleWithoutReplacement_eq_zero_of_card_lt hnm]

/-- **The repeated-value bound, reversed excess form.** If the deterministic population
`x : κ → α` repeats a value, the largest event excess of sampling `x` with replacement over
sampling it without replacement is at most `1 - p - t * min p (1 - p)`, where
`p = |κ|.descFactorial |ι| / |κ| ^ |ι|` and `t = |ι|.descFactorial 2 / |κ|.descFactorial 2`.
When `|ι| > |κ|`, sampling without replacement is the zero measure and the bound is `1`. -/
theorem iSup_sampleWithReplacement_sub_sampleWithoutReplacement_dirac_le_of_not_injective
    (hx : ¬ Injective x) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
      sampleWithReplacement (Measure.dirac x) A -
        sampleWithoutReplacement (Measure.dirac x) A) ≤
      ENNReal.ofReal
        (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ) ^ Fintype.card ι
         let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
         1 - p - t * min p (1 - p)) := by
  classical
  obtain ⟨a, b, hxab, hab⟩ := not_injective_iff.1 hx
  rcases le_or_gt (Fintype.card ι) (Fintype.card κ) with hmn | hnm
  · obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
    exact (iSup_sampleWithReplacement_sub_sampleWithoutReplacement_dirac_le_update_id e hxab).trans
      (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq hab hmn).le
  · have : Nonempty (ι → κ) := ⟨fun _ => a⟩
    have := isProbabilityMeasure_sampleWithReplacement (ι := ι) (Measure.dirac x)
    simpa [sampleWithoutReplacement_eq_zero_of_card_lt hnm,
      Nat.descFactorial_eq_zero_iff_lt.2 hnm] using fun A (_ : MeasurableSet A) => prob_le_one

/-- **The repeated-value bound, eventwise form.** If the deterministic population `x : κ → α`
repeats a value, every event has mass under sampling without replacement at most its mass under
sampling with replacement plus `1 - p - t * min p (1 - p)`. -/
theorem sampleWithoutReplacement_le_sampleWithReplacement_dirac_add_of_not_injective
    (hx : ¬ Injective x) (A : Set (ι → α)) :
    sampleWithoutReplacement (Measure.dirac x) A ≤
      sampleWithReplacement (Measure.dirac x) A +
        ENNReal.ofReal
          (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
              (Fintype.card κ : ℝ) ^ Fintype.card ι
           let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
           1 - p - t * min p (1 - p)) :=
  measure_le_add_of_iSup_sub_le
    (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_of_not_injective hx) A

/-- **The repeated-value bound, reversed eventwise form.** If the deterministic population
`x : κ → α` repeats a value, every event has mass under sampling with replacement at most its mass
under sampling without replacement plus `1 - p - t * min p (1 - p)`. -/
theorem sampleWithReplacement_le_sampleWithoutReplacement_dirac_add_of_not_injective
    (hx : ¬ Injective x) (A : Set (ι → α)) :
    sampleWithReplacement (Measure.dirac x) A ≤
      sampleWithoutReplacement (Measure.dirac x) A +
        ENNReal.ofReal
          (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
              (Fintype.card κ : ℝ) ^ Fintype.card ι
           let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
           1 - p - t * min p (1 - p)) :=
  measure_le_add_of_iSup_sub_le
    (iSup_sampleWithReplacement_sub_sampleWithoutReplacement_dirac_le_of_not_injective hx) A

/-- **The repeated-value bound, total-variation form.** If the deterministic population
`x : κ → α` repeats a value, Mathlib's extended total variation distance between sampling `x`
without and with replacement is at most `2 * ENNReal.ofReal (1 - p - t * min p (1 - p))`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_le_of_not_injective
    (hx : ¬ Injective x) :
    etvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
        (sampleWithReplacement (ι := ι) (Measure.dirac x)) ≤
      2 * ENNReal.ofReal
        (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ) ^ Fintype.card ι
         let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
         1 - p - t * min p (1 - p)) := by
  rw [two_mul, etvDist_eq_iSup_sub_add_iSup_sub]
  exact add_le_add
    (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_of_not_injective hx)
    (iSup_sampleWithReplacement_sub_sampleWithoutReplacement_dirac_le_of_not_injective hx)

/-- **The repeated-value bound, real total-variation form.** If the deterministic population
`x : κ → α` repeats a value, the real total variation distance between sampling `x` without and
with replacement is at most `2 * (1 - p - t * min p (1 - p))`. -/
theorem tvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_le_of_not_injective
    (hx : ¬ Injective x) :
    tvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
        (sampleWithReplacement (ι := ι) (Measure.dirac x)) ≤
      let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ) ^ Fintype.card ι
      let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
      2 * (1 - p - t * min p (1 - p)) := by
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top)
    (etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_le_of_not_injective (ι := ι) hx)
  dsimp only at h ⊢
  rwa [← tvDist, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (one_sub_descFactorial_div_pow_sub_mul_min_nonneg _ _)] at h

end Bound

section Characterization

/-- **Strictness of the repeated-value bound.** For a sample of size `|ι| ≥ 2`, the largest event
excess of sampling a population with a repeated value without replacement over sampling it with
replacement is strictly below the collision probability `1 - |κ|.descFactorial |ι| / |κ| ^ |ι|`,
which, for `|ι| ≤ |κ|` and a measurable all-distinct event, populations of distinct values
attain. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_lt_of_not_injective
    (hx : ¬ Injective x) (hm : 2 ≤ Fintype.card ι) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
      sampleWithoutReplacement (Measure.dirac x) A -
        sampleWithReplacement (Measure.dirac x) A) <
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι := by
  obtain ⟨a, -⟩ := not_injective_iff.1 hx
  have : Nonempty (ι → κ) := ⟨fun _ => a⟩
  -- Write the collision probability as `ENNReal.ofReal (1 - p)` through the uniform law.
  rw [← uniformOn_not_injective_apply_eq, ← ofReal_measureReal,
    uniformOn_real_not_injective_apply_eq]
  rcases le_or_gt (Fintype.card ι) (Fintype.card κ) with hmn | hnm
  · refine (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_of_not_injective
      hx).trans_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ?_).2 ?_)
    · exact one_sub_descFactorial_div_pow_sub_mul_min_nonneg _ _
    · linarith [descFactorial_div_mul_min_pos hm hmn]
  · simp [sampleWithoutReplacement_eq_zero_of_card_lt hnm,
      Nat.descFactorial_eq_zero_iff_lt.2 hnm]

/-- **Strictness of the repeated-value bound, extended total-variation form.** For a sample of
size `|ι| ≥ 2`, Mathlib's extended total variation distance between sampling a population with a
repeated value without and with replacement is strictly below twice the collision probability
`1 - |κ|.descFactorial |ι| / |κ| ^ |ι|`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_lt_of_not_injective
    (hx : ¬ Injective x) (hm : 2 ≤ Fintype.card ι) :
    etvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
        (sampleWithReplacement (ι := ι) (Measure.dirac x)) <
      2 * (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) := by
  obtain ⟨a, -⟩ := not_injective_iff.1 hx
  have : Nonempty (ι → κ) := ⟨fun _ => a⟩
  have := isProbabilityMeasure_sampleWithReplacement (ι := ι) (Measure.dirac x)
  rcases le_or_gt (Fintype.card ι) (Fintype.card κ) with hmn | hnm
  · obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
    have := isProbabilityMeasure_sampleWithoutReplacement (Measure.dirac x) e
    rw [etvDist_eq_two_mul_iSup_sub (by rw [measure_univ, measure_univ])]
    exact ENNReal.mul_lt_mul_right two_ne_zero ENNReal.ofNat_ne_top
      (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_lt_of_not_injective hx hm)
  · rw [etvDist_eq_iSup_sub_add_iSup_sub, sampleWithoutReplacement_eq_zero_of_card_lt hnm,
      Nat.descFactorial_eq_zero_iff_lt.2 hnm]
    simp only [Nat.cast_zero, ENNReal.zero_div, tsub_zero, mul_one, FunLike.coe_zero,
      Pi.zero_apply, zero_tsub]
    have h0 : (⨆ (A : Set (ι → α)) (_ : MeasurableSet A), (0 : ℝ≥0∞)) = 0 := by simp
    have h1 : (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        sampleWithReplacement (Measure.dirac x) A) ≤ 1 := iSup₂_le fun _ _ => prob_le_one
    rw [h0, zero_add]
    exact h1.trans_lt (by norm_num : (1 : ℝ≥0∞) < 2)

/-- **Strictness of the repeated-value bound, real total-variation form.** For a sample of size
`|ι| ≥ 2`, the real total variation distance between sampling a population with a repeated value
without and with replacement is strictly below twice the collision probability
`1 - |κ|.descFactorial |ι| / |κ| ^ |ι|`. -/
theorem tvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_lt_of_not_injective
    (hx : ¬ Injective x) (hm : 2 ≤ Fintype.card ι) :
    tvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
        (sampleWithReplacement (ι := ι) (Measure.dirac x)) <
      2 * (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ) ^ Fintype.card ι) := by
  obtain ⟨a, -⟩ := not_injective_iff.1 hx
  have : Nonempty (ι → κ) := ⟨fun _ => a⟩
  have h := ENNReal.toReal_strict_mono (by finiteness)
    (etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_lt_of_not_injective
      (ι := ι) hx hm)
  rwa [← tvDist, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ← uniformOn_not_injective_apply_eq,
    ← measureReal_def, uniformOn_real_not_injective_apply_eq] at h

/-- **Distinct values are the only populations attaining the collision probability.** For
`2 ≤ |ι| ≤ |κ|` and a measurable all-distinct event, the largest event excess of sampling
`x : κ → α` without replacement over sampling it with replacement equals the collision
probability `1 - |κ|.descFactorial |ι| / |κ| ^ |ι|` if and only if `x` is injective. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq_iff_injective
    (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ Fintype.card κ)
    (hI : MeasurableSet {f : ι → α | Injective f}) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
      sampleWithoutReplacement (Measure.dirac x) A -
        sampleWithReplacement (Measure.dirac x) A) =
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι ↔ Injective x := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  refine ⟨fun h => ?_, fun hx => iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq
    hx e hI⟩
  by_contra hx
  exact (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_lt_of_not_injective
    hx hm).ne h

/-- **Total-variation form of the characterization.** For `2 ≤ |ι| ≤ |κ|` and a measurable
all-distinct event, Mathlib's extended total variation distance between sampling `x : κ → α`
without and with replacement equals twice the collision probability
`1 - |κ|.descFactorial |ι| / |κ| ^ |ι|` if and only if `x` is injective. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_iff_injective
    (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ Fintype.card κ)
    (hI : MeasurableSet {f : ι → α | Injective f}) :
    etvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
        (sampleWithReplacement (ι := ι) (Measure.dirac x)) =
      2 * (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) ↔ Injective x := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  have : Nonempty (ι → κ) := ⟨e⟩
  have := isProbabilityMeasure_sampleWithoutReplacement (Measure.dirac x) e
  have := isProbabilityMeasure_sampleWithReplacement (ι := ι) (Measure.dirac x)
  rw [etvDist_eq_two_mul_iSup_sub (by rw [measure_univ, measure_univ]),
    ENNReal.mul_right_inj two_ne_zero ENNReal.ofNat_ne_top]
  exact iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq_iff_injective hm hmn hI

/-- **Real total-variation form of the characterization.** For `2 ≤ |ι| ≤ |κ|` and a measurable
all-distinct event, the real total variation distance between sampling `x : κ → α` without and with
replacement equals twice the collision probability `1 - |κ|.descFactorial |ι| / |κ| ^ |ι|` if and
only if `x` is injective. -/
theorem tvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_iff_injective
    (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ Fintype.card κ)
    (hI : MeasurableSet {f : ι → α | Injective f}) :
    tvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
        (sampleWithReplacement (ι := ι) (Measure.dirac x)) =
      2 * (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ) ^ Fintype.card ι) ↔ Injective x := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  refine ⟨fun h => ?_, fun hx => tvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq
    hx e hI⟩
  by_contra hx
  exact (tvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_lt_of_not_injective
    hx hm).ne h

/-- **Attainment characterization under measurable singletons (excess form).** When `α` has
measurable singletons and `2 ≤ |ι| ≤ |κ|`, a deterministic population attains the collision excess
`1 - |κ|.descFactorial |ι| / |κ| ^ |ι|` if and only if its values are distinct, without requiring
measurability of the all-distinct event in `ι → α`. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq_iff
    [MeasurableSingletonClass α] (hm : 2 ≤ Fintype.card ι)
    (hmn : Fintype.card ι ≤ Fintype.card κ) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
      sampleWithoutReplacement (Measure.dirac x) A -
        sampleWithReplacement (Measure.dirac x) A) =
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι ↔ Injective x := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  refine ⟨fun h => ?_, fun hx =>
    iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq_of_injective hx e⟩
  by_contra hx
  exact (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_lt_of_not_injective
    hx hm).ne h

/-- **Attainment characterization under measurable singletons (`etvDist` form).** When `α` has
measurable singletons and `2 ≤ |ι| ≤ |κ|`, Mathlib's extended total variation distance between
sampling `x : κ → α` without and with replacement equals twice the collision probability
`1 - |κ|.descFactorial |ι| / |κ| ^ |ι|` if and only if `x` is injective, without requiring
measurability of the all-distinct event in `ι → α`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_iff
    [MeasurableSingletonClass α] (hm : 2 ≤ Fintype.card ι)
    (hmn : Fintype.card ι ≤ Fintype.card κ) :
    etvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
        (sampleWithReplacement (ι := ι) (Measure.dirac x)) =
      2 * (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) ↔ Injective x := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  refine ⟨fun h => ?_, fun hx =>
    etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_of_injective hx e⟩
  by_contra hx
  exact (etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_lt_of_not_injective
    hx hm).ne h

/-- **Attainment characterization under measurable singletons (`tvDist` form).** When `α` has
measurable singletons and `2 ≤ |ι| ≤ |κ|`, the real total variation distance between sampling
`x : κ → α` without and with replacement equals twice the collision probability
`1 - |κ|.descFactorial |ι| / |κ| ^ |ι|` if and only if `x` is injective, without requiring
measurability of the all-distinct event in `ι → α`. -/
theorem tvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_iff
    [MeasurableSingletonClass α] (hm : 2 ≤ Fintype.card ι)
    (hmn : Fintype.card ι ≤ Fintype.card κ) :
    tvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
        (sampleWithReplacement (ι := ι) (Measure.dirac x)) =
      2 * (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ) ^ Fintype.card ι) ↔ Injective x := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  refine ⟨fun h => ?_, fun hx =>
    tvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_of_injective hx e⟩
  by_contra hx
  exact (tvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_lt_of_not_injective
    hx hm).ne h

end Characterization

end TauCeti.Probability

end

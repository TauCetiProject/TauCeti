/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PopulationSampling.Map
public import TauCeti.Probability.PopulationSampling.OnePair

/-!
# Sampling discrepancy for repeated-value populations and attainment characterization

If a deterministic finite population `x : κ → α` fails to be injective, then `x a = x b` for some
distinct indices `a b : κ`, so `x` factors through the one-pair population
`Function.update id b a : κ → κ`. Pushing forward the exact one-pair discrepancy formula
(`iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq`) shows that every
non-injective population satisfies the sharp discrepancy bound
`onePairSamplingExcess m n = 1 - p - t * min p (1 - p)` on every set in both directions, and
`2 * onePairSamplingExcess m n` in `etvDist`, where `p = n_(m) / n^m` and `t = m_(2) / n_(2)`. No
separation or singleton hypothesis on the value space `α`, and no relation between `m = |ι|` and
`n = |κ|`, is required: when `m > n` the without-replacement law is zero and the bound evaluates
to `1`.

Whenever `2 ≤ m ≤ n`, the reduction `t * min p (1 - p)` is strictly positive, so every
non-injective population has discrepancy strictly below the collision probability `1 - p` (and
`etvDist` strictly below `2 * (1 - p)`). Combining this strict inequality with the distinct-value
attainment theorems (`TauCeti.Probability.PopulationSampling.Distinct` and
`TauCeti.Probability.PopulationSampling.Map`) characterizes attainment: for `2 ≤ m ≤ n`, a
deterministic population attains the collision discrepancy if and only if its values are distinct.
For `m ≤ 1` (i.e. `Subsingleton ι`), the two sampling laws agree for every population law
(`sampleWithoutReplacement_eq_sampleWithReplacement_of_subsingleton`), so `2 ≤ m` is sharp.

## Main declarations

* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_of_not_injective`,
  `iSup_sampleWithReplacement_sub_sampleWithoutReplacement_dirac_le_of_not_injective`: both
  one-sided excesses of a non-injective population are bounded by `onePairSamplingExcess |ι| |κ|`;
* `sampleWithoutReplacement_dirac_le_sampleWithReplacement_add_of_not_injective`,
  `sampleWithReplacement_dirac_le_sampleWithoutReplacement_add_of_not_injective`: the
  corresponding eventwise bounds for arbitrary sets;
* `etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_le_of_not_injective`: twice that
  bound for `etvDist`;
* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_lt_of_not_injective`,
  `etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_lt_of_not_injective`: strict
  inequality below the collision bound for non-injective populations when `2 ≤ m ≤ n`;
* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq_iff_of_measurableSet`,
  `etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_iff_of_measurableSet`:
  attainment of the collision discrepancy characterizes injectivity for `2 ≤ m ≤ n` when the
  all-distinct event is measurable;
* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq_iff`,
  `etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_iff`: the same characterization
  under `[MeasurableSingletonClass α]` without a diagonal-measurability hypothesis.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Probability

section RepeatedBound

variable {ι κ α : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
  [MeasurableSpace α]

/-- If a deterministic finite population repeats a value, the largest eventwise excess of sampling
without replacement over sampling with replacement is at most `onePairSamplingExcess |ι| |κ|`. No
separation assumption on `α` and no inequality between `|ι|` and `|κ|` is required. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_of_not_injective
    {x : κ → α} (hx : ¬ Function.Injective x) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        sampleWithoutReplacement (Measure.dirac x) A -
          sampleWithReplacement (Measure.dirac x) A) ≤
      ENNReal.ofReal (onePairSamplingExcess (Fintype.card ι) (Fintype.card κ)) := by
  classical
  rcases le_or_gt (Fintype.card ι) (Fintype.card κ) with hmn | hlt
  · obtain ⟨a, b, hxab, hab⟩ := Function.not_injective_iff.1 hx
    calc
      (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
          sampleWithoutReplacement (Measure.dirac x) A -
            sampleWithReplacement (Measure.dirac x) A)
          ≤ ⨆ (B : Set (ι → κ)) (_ : MeasurableSet B),
              sampleWithoutReplacement (Measure.dirac (Function.update id b a)) B -
                sampleWithReplacement (Measure.dirac (Function.update id b a)) B :=
        iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_update_id hxab
      _ = ENNReal.ofReal (onePairSamplingExcess (Fintype.card ι) (Fintype.card κ)) := by
        simpa only [onePairSamplingExcess_def] using
          iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq hab hmn
  · have : IsEmpty (ι ↪ κ) := Function.Embedding.isEmpty_of_card_lt hlt
    simp [sampleWithoutReplacement_eq_zero_of_isEmpty]

/-- If a deterministic finite population repeats a value, the largest eventwise excess of sampling
with replacement over sampling without replacement is at most `onePairSamplingExcess |ι| |κ|`. No
separation assumption on `α` and no inequality between `|ι|` and `|κ|` is required. -/
theorem iSup_sampleWithReplacement_sub_sampleWithoutReplacement_dirac_le_of_not_injective
    {x : κ → α} (hx : ¬ Function.Injective x) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        sampleWithReplacement (Measure.dirac x) A -
          sampleWithoutReplacement (Measure.dirac x) A) ≤
      ENNReal.ofReal (onePairSamplingExcess (Fintype.card ι) (Fintype.card κ)) := by
  classical
  obtain ⟨a, b, hxab, hab⟩ := Function.not_injective_iff.1 hx
  rcases le_or_gt (Fintype.card ι) (Fintype.card κ) with hmn | hlt
  · obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
    calc
      (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
          sampleWithReplacement (Measure.dirac x) A -
            sampleWithoutReplacement (Measure.dirac x) A)
          ≤ ⨆ (B : Set (ι → κ)) (_ : MeasurableSet B),
              sampleWithoutReplacement (Measure.dirac (Function.update id b a)) B -
                sampleWithReplacement (Measure.dirac (Function.update id b a)) B :=
        iSup_sampleWithReplacement_sub_sampleWithoutReplacement_dirac_le_update_id e hxab
      _ = ENNReal.ofReal (onePairSamplingExcess (Fintype.card ι) (Fintype.card κ)) := by
        simpa only [onePairSamplingExcess_def] using
          iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq hab hmn
  · have : IsEmpty (ι ↪ κ) := Function.Embedding.isEmpty_of_card_lt hlt
    let _ : Nonempty (ι → κ) := ⟨fun _ => a⟩
    let _ := isProbabilityMeasure_sampleWithReplacement (ι := ι) (Measure.dirac x)
    rw [onePairSamplingExcess_eq_one_of_lt hlt, ENNReal.ofReal_one]
    simp only [sampleWithoutReplacement_eq_zero_of_isEmpty, FunLike.coe_zero,
      Pi.zero_apply, tsub_zero]
    exact iSup₂_le fun _ _ => prob_le_one

/-- **Repeated-value sampling bound, without replacement to with replacement.** For a
non-injective deterministic population and any set `A` (measurable or not), the
without-replacement mass of `A` exceeds its with-replacement mass by at most
`onePairSamplingExcess |ι| |κ|`. -/
theorem sampleWithoutReplacement_dirac_le_sampleWithReplacement_add_of_not_injective
    {x : κ → α} (hx : ¬ Function.Injective x) (A : Set (ι → α)) :
    sampleWithoutReplacement (Measure.dirac x) A ≤
      sampleWithReplacement (Measure.dirac x) A +
        ENNReal.ofReal (onePairSamplingExcess (Fintype.card ι) (Fintype.card κ)) :=
  measure_le_add_of_iSup_sub_le
    (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_of_not_injective hx) A

/-- **Repeated-value sampling bound, with replacement to without replacement.** For a
non-injective deterministic population and any set `A` (measurable or not), the
with-replacement mass of `A` exceeds its without-replacement mass by at most
`onePairSamplingExcess |ι| |κ|`. -/
theorem sampleWithReplacement_dirac_le_sampleWithoutReplacement_add_of_not_injective
    {x : κ → α} (hx : ¬ Function.Injective x) (A : Set (ι → α)) :
    sampleWithReplacement (Measure.dirac x) A ≤
      sampleWithoutReplacement (Measure.dirac x) A +
        ENNReal.ofReal (onePairSamplingExcess (Fintype.card ι) (Fintype.card κ)) :=
  measure_le_add_of_iSup_sub_le
    (iSup_sampleWithReplacement_sub_sampleWithoutReplacement_dirac_le_of_not_injective hx) A

/-- **Repeated-value sampling bound (`etvDist` form).** For a non-injective deterministic
population, Mathlib's total variation distance between sampling without and with replacement is
at most `2 * onePairSamplingExcess |ι| |κ|`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_le_of_not_injective
    {x : κ → α} (hx : ¬ Function.Injective x) :
    etvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
        (sampleWithReplacement (ι := ι) (Measure.dirac x)) ≤
      2 * ENNReal.ofReal (onePairSamplingExcess (Fintype.card ι) (Fintype.card κ)) := by
  rw [two_mul]
  exact etvDist_le_of_forall_le_add
    (fun A _ =>
      sampleWithoutReplacement_dirac_le_sampleWithReplacement_add_of_not_injective hx A)
    (fun A _ =>
      sampleWithReplacement_dirac_le_sampleWithoutReplacement_add_of_not_injective hx A)

end RepeatedBound

section Strictness

variable {ι κ α : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
  [MeasurableSpace α]

/-- For `2 ≤ |ι| ≤ |κ|`, every non-injective deterministic population has largest sampling excess
strictly below the collision probability `1 - n_(m) / n^m`, with no assumption on `α`. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_lt_of_not_injective
    {x : κ → α} (hx : ¬ Function.Injective x)
    (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        sampleWithoutReplacement (Measure.dirac x) A -
          sampleWithReplacement (Measure.dirac x) A) <
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι :=
  (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_of_not_injective hx).trans_lt
    (ofReal_onePairSamplingExcess_lt_one_sub_descFactorial_div_pow hm hmn)

/-- For `2 ≤ |ι| ≤ |κ|`, every non-injective deterministic population has `etvDist` strictly below
twice the collision probability `2 * (1 - n_(m) / n^m)`, with no assumption on `α`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_lt_of_not_injective
    {x : κ → α} (hx : ¬ Function.Injective x)
    (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    etvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
        (sampleWithReplacement (ι := ι) (Measure.dirac x)) <
      2 * (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) :=
  (etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_le_of_not_injective hx).trans_lt
    (ENNReal.mul_lt_mul_right two_ne_zero ENNReal.ofNat_ne_top
      (ofReal_onePairSamplingExcess_lt_one_sub_descFactorial_div_pow hm hmn))

end Strictness

section Characterization

variable {ι κ α : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
  [MeasurableSpace α]

/-- **Attainment characterization (excess form).** For `2 ≤ |ι| ≤ |κ|` and an arbitrary value space
with measurable all-distinct event, a deterministic population attains the collision excess
`1 - n_(m) / n^m` if and only if its values are distinct. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq_iff_of_measurableSet
    (x : κ → α) (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ Fintype.card κ)
    (hI : MeasurableSet {f : ι → α | Function.Injective f}) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        sampleWithoutReplacement (Measure.dirac x) A -
          sampleWithReplacement (Measure.dirac x) A) =
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι ↔ Function.Injective x := by
  refine ⟨fun h => ?_, fun hx => ?_⟩
  · by_contra hx
    exact (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_lt_of_not_injective
      hx hm hmn).ne h
  · obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
    exact iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq hx e hI

/-- **Attainment characterization (`etvDist` form).** For `2 ≤ |ι| ≤ |κ|` and an arbitrary value
space with measurable all-distinct event, a deterministic population attains `etvDist` equal to
`2 * (1 - n_(m) / n^m)` if and only if its values are distinct. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_iff_of_measurableSet
    (x : κ → α) (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ Fintype.card κ)
    (hI : MeasurableSet {f : ι → α | Function.Injective f}) :
    etvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
        (sampleWithReplacement (ι := ι) (Measure.dirac x)) =
      2 * (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) ↔ Function.Injective x := by
  refine ⟨fun h => ?_, fun hx => ?_⟩
  · by_contra hx
    exact (etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_lt_of_not_injective
      hx hm hmn).ne h
  · obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
    exact etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq hx e hI

/-- **Attainment characterization under measurable singletons (excess form).** When `α` has
measurable singletons and `2 ≤ |ι| ≤ |κ|`, a deterministic population attains the collision excess
`1 - n_(m) / n^m` if and only if its values are distinct, without requiring measurability of the
all-distinct event in `ι → α`. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq_iff
    [MeasurableSingletonClass α] (x : κ → α)
    (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        sampleWithoutReplacement (Measure.dirac x) A -
          sampleWithReplacement (Measure.dirac x) A) =
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι ↔ Function.Injective x := by
  refine ⟨fun h => ?_, fun hx => ?_⟩
  · by_contra hx
    exact (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_lt_of_not_injective
      hx hm hmn).ne h
  · obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
    exact iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq_of_injective hx e

/-- **Attainment characterization under measurable singletons (`etvDist` form).** When `α` has
measurable singletons and `2 ≤ |ι| ≤ |κ|`, a deterministic population attains `etvDist` equal to
`2 * (1 - n_(m) / n^m)` if and only if its values are distinct, without requiring measurability of
the all-distinct event in `ι → α`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_iff
    [MeasurableSingletonClass α] (x : κ → α)
    (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    etvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
        (sampleWithReplacement (ι := ι) (Measure.dirac x)) =
      2 * (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) ↔ Function.Injective x := by
  refine ⟨fun h => ?_, fun hx => ?_⟩
  · by_contra hx
    exact (etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_lt_of_not_injective
      hx hm hmn).ne h
  · obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
    exact etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq_of_injective hx e

end Characterization

end TauCeti.Probability

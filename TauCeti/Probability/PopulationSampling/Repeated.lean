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
non-injective population satisfies the sharp discrepancy bound `1 - p - t * min p (1 - p)` on
every set in both directions, and `2 * (1 - p - t * min p (1 - p))` in `etvDist`, where
`p = n_(m) / n^m` and `t = m_(2) / n_(2)`. No separation or singleton hypothesis on the value space
`α`, and no relation between `m = |ι|` and `n = |κ|`, is required: when `m > n` the
without-replacement law is zero and the bound evaluates to `1`.

Whenever `2 ≤ m ≤ n`, the reduction `t * min p (1 - p)` is strictly positive, so every
non-injective population has discrepancy strictly below the collision probability `1 - p` (and
`etvDist` strictly below `2 * (1 - p)`). Combining this strict inequality with the distinct-value
attainment theorems (`TauCeti.Probability.PopulationSampling.Distinct` and
`TauCeti.Probability.PopulationSampling.Map`) characterizes attainment: for `2 ≤ m ≤ n`, a
deterministic population attains the collision discrepancy if and only if its values are distinct.
For `m ≤ 1`, the two sampling laws agree for every population law
(`sampleWithoutReplacement_eq_sampleWithReplacement_of_card_le_one`), so `2 ≤ m` is sharp.

## Main declarations

* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_of_not_injective`,
  `iSup_sampleWithReplacement_sub_sampleWithoutReplacement_dirac_le_of_not_injective`: both
  one-sided excesses of a non-injective population are bounded by `1 - p - t * min p (1 - p)`;
* `sampleWithoutReplacement_dirac_le_sampleWithReplacement_add_of_not_injective`,
  `sampleWithReplacement_dirac_le_sampleWithoutReplacement_add_of_not_injective`: the
  corresponding eventwise bounds for arbitrary sets;
* `etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_le_of_not_injective`: twice that
  bound for `etvDist`;
* `descFactorial_two_div_mul_min_pos`, `ofReal_sub_mul_min_lt_one_sub_descFactorial_div_pow`:
  positivity of `t * min p (1 - p)` and strictness below `1 - p` for `2 ≤ m ≤ n`;
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
without replacement over sampling with replacement is at most `1 - p - t * min p (1 - p)`. No
separation assumption on `α` and no inequality between `|ι|` and `|κ|` is required. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_of_not_injective
    {x : κ → α} (hx : ¬ Function.Injective x) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        sampleWithoutReplacement (Measure.dirac x) A -
          sampleWithReplacement (Measure.dirac x) A) ≤
      ENNReal.ofReal
        (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ) ^ Fintype.card ι
         let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
         1 - p - t * min p (1 - p)) := by
  classical
  rcases le_or_gt (Fintype.card ι) (Fintype.card κ) with hmn | hlt
  · have hne : ∃ a b, x a = x b ∧ a ≠ b := by
      simpa only [Function.Injective, not_forall, not_imp, exists_prop] using hx
    obtain ⟨a, b, hxab, hab⟩ := hne
    calc
      (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
          sampleWithoutReplacement (Measure.dirac x) A -
            sampleWithReplacement (Measure.dirac x) A)
          ≤ ⨆ (B : Set (ι → κ)) (_ : MeasurableSet B),
              sampleWithoutReplacement (Measure.dirac (Function.update id b a)) B -
                sampleWithReplacement (Measure.dirac (Function.update id b a)) B :=
        iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_update_id hxab
      _ = _ :=
        iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq hab hmn
  · have : IsEmpty (ι ↪ κ) :=
      ⟨fun e => hlt.not_ge (Fintype.card_le_of_injective e e.injective)⟩
    simp [sampleWithoutReplacement_eq_zero_of_isEmpty_embedding]

/-- If a deterministic finite population repeats a value, the largest eventwise excess of sampling
with replacement over sampling without replacement is at most `1 - p - t * min p (1 - p)`. No
separation assumption on `α` and no inequality between `|ι|` and `|κ|` is required. -/
theorem iSup_sampleWithReplacement_sub_sampleWithoutReplacement_dirac_le_of_not_injective
    {x : κ → α} (hx : ¬ Function.Injective x) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
        sampleWithReplacement (Measure.dirac x) A -
          sampleWithoutReplacement (Measure.dirac x) A) ≤
      ENNReal.ofReal
        (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ) ^ Fintype.card ι
         let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
         1 - p - t * min p (1 - p)) := by
  classical
  have hne : ∃ a b, x a = x b ∧ a ≠ b := by
    simpa only [Function.Injective, not_forall, not_imp, exists_prop] using hx
  obtain ⟨a, b, hxab, hab⟩ := hne
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
      _ = _ :=
        iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq hab hmn
  · have : IsEmpty (ι ↪ κ) :=
      ⟨fun e => hlt.not_ge (Fintype.card_le_of_injective e e.injective)⟩
    let _ : Nonempty (ι → κ) := ⟨fun _ => a⟩
    let _ := isProbabilityMeasure_sampleWithReplacement (ι := ι) (Measure.dirac x)
    have h0 : (Fintype.card κ).descFactorial (Fintype.card ι) = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.2 hlt
    simp only [sampleWithoutReplacement_eq_zero_of_isEmpty_embedding, FunLike.coe_zero,
      Pi.zero_apply, tsub_zero, h0, Nat.cast_zero, zero_div, min_eq_left zero_le_one,
      mul_zero, ENNReal.ofReal_one]
    exact iSup₂_le fun _ _ => prob_le_one

/-- **Repeated-value sampling bound, without replacement to with replacement.** For a
non-injective deterministic population and any set `A` (measurable or not), the
without-replacement mass of `A` exceeds its with-replacement mass by at most
`1 - p - t * min p (1 - p)`. -/
theorem sampleWithoutReplacement_dirac_le_sampleWithReplacement_add_of_not_injective
    {x : κ → α} (hx : ¬ Function.Injective x) (A : Set (ι → α)) :
    sampleWithoutReplacement (Measure.dirac x) A ≤
      sampleWithReplacement (Measure.dirac x) A +
        ENNReal.ofReal
          (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
              (Fintype.card κ : ℝ) ^ Fintype.card ι
           let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
           1 - p - t * min p (1 - p)) :=
  measure_le_add_of_iSup_sub_le
    (iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_le_of_not_injective hx) A

/-- **Repeated-value sampling bound, with replacement to without replacement.** For a
non-injective deterministic population and any set `A` (measurable or not), the
with-replacement mass of `A` exceeds its without-replacement mass by at most
`1 - p - t * min p (1 - p)`. -/
theorem sampleWithReplacement_dirac_le_sampleWithoutReplacement_add_of_not_injective
    {x : κ → α} (hx : ¬ Function.Injective x) (A : Set (ι → α)) :
    sampleWithReplacement (Measure.dirac x) A ≤
      sampleWithoutReplacement (Measure.dirac x) A +
        ENNReal.ofReal
          (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
              (Fintype.card κ : ℝ) ^ Fintype.card ι
           let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
           1 - p - t * min p (1 - p)) :=
  measure_le_add_of_iSup_sub_le
    (iSup_sampleWithReplacement_sub_sampleWithoutReplacement_dirac_le_of_not_injective hx) A

/-- **Repeated-value sampling bound (`etvDist` form).** For a non-injective deterministic
population, Mathlib's total variation distance between sampling without and with replacement is
at most `2 * (1 - p - t * min p (1 - p))`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_le_of_not_injective
    {x : κ → α} (hx : ¬ Function.Injective x) :
    etvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
        (sampleWithReplacement (ι := ι) (Measure.dirac x)) ≤
      2 * ENNReal.ofReal
        (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ) ^ Fintype.card ι
         let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
         1 - p - t * min p (1 - p)) := by
  rw [two_mul]
  exact etvDist_le_of_forall_le_add
    (fun A _ =>
      sampleWithoutReplacement_dirac_le_sampleWithReplacement_add_of_not_injective hx A)
    (fun A _ =>
      sampleWithReplacement_dirac_le_sampleWithoutReplacement_add_of_not_injective hx A)

end RepeatedBound

section Strictness

/-- For `2 ≤ m ≤ n`, the repeated-value discrepancy reduction `t * min p (1 - p)` is strictly
positive, where `p = n_(m) / n^m` and `t = m_(2) / n_(2)`. -/
theorem descFactorial_two_div_mul_min_pos {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    0 < (m.descFactorial 2 / (n.descFactorial 2 : ℝ)) *
      min (n.descFactorial m / (n : ℝ) ^ m) (1 - n.descFactorial m / (n : ℝ) ^ m) := by
  have hn2 : 2 ≤ n := hm.trans hmn
  have hn0 : n ≠ 0 := by omega
  have hm2_pos : (0 : ℝ) < m.descFactorial 2 := by exact_mod_cast Nat.descFactorial_pos.2 hm
  have hn2_pos : (0 : ℝ) < n.descFactorial 2 := by exact_mod_cast Nat.descFactorial_pos.2 hn2
  have hnm_pos : (0 : ℝ) < n.descFactorial m := by exact_mod_cast Nat.descFactorial_pos.2 hmn
  have hpow_pos : (0 : ℝ) < (n : ℝ) ^ m := by positivity
  have hp_pos : (0 : ℝ) < n.descFactorial m / (n : ℝ) ^ m := div_pos hnm_pos hpow_pos
  have hp_lt : (n.descFactorial m : ℝ) / (n : ℝ) ^ m < 1 :=
    (div_lt_one hpow_pos).2 (by exact_mod_cast Nat.descFactorial_lt_pow hn0 hm)
  exact mul_pos (div_pos hm2_pos hn2_pos) (lt_min hp_pos (sub_pos.2 hp_lt))

/-- For `2 ≤ m ≤ n`, the repeated-value sampling bound `1 - p - t * min p (1 - p)` is strictly
smaller than the collision probability `1 - p` in `ℝ≥0∞`. -/
theorem ofReal_sub_mul_min_lt_one_sub_descFactorial_div_pow {m n : ℕ}
    (hm : 2 ≤ m) (hmn : m ≤ n) :
    ENNReal.ofReal
        (let p : ℝ := n.descFactorial m / (n : ℝ) ^ m
         let t : ℝ := m.descFactorial 2 / n.descFactorial 2
         1 - p - t * min p (1 - p)) <
      1 - (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m := by
  let p : ℝ := n.descFactorial m / (n : ℝ) ^ m
  have hn0 : n ≠ 0 := by omega
  have hn_pos : (0 : ℝ) < n := by positivity
  have hpow_pos : (0 : ℝ) < (n : ℝ) ^ m := by positivity
  have hp_lt : p < 1 :=
    (div_lt_one hpow_pos).2 (by exact_mod_cast Nat.descFactorial_lt_pow hn0 hm)
  have hp_eq : (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m = ENNReal.ofReal p := by
    simp only [p, ENNReal.ofReal_div_of_pos hpow_pos, ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow hn_pos.le]
  have h1p : 1 - (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m = ENNReal.ofReal (1 - p) := by
    rw [hp_eq, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by positivity : (0 : ℝ) ≤ p)]
  rw [h1p, ENNReal.ofReal_lt_ofReal_iff (sub_pos.2 hp_lt)]
  exact sub_lt_self _ (descFactorial_two_div_mul_min_pos hm hmn)

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
    (ofReal_sub_mul_min_lt_one_sub_descFactorial_div_pow hm hmn)

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
      (ofReal_sub_mul_min_lt_one_sub_descFactorial_div_pow hm hmn))

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

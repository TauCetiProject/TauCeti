/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.TotalVariation.Finite
public import TauCeti.Probability.PopulationSampling.Finite
import Mathlib.Data.Finset.Preimage
import Mathlib.Tactic.IntervalCases
import TauCeti.Logic.Function.Update

/-!
# The one-pair population: fibres and exact sampling discrepancy

For distinct indices `a b : κ`, the *one-pair population* `Function.update id b a : κ → κ` sends
`b` to `a` and fixes every other index; it is the canonical population with a single repeated
value. Sampling it along an index map `f : ι → κ` gives the word `Function.update id b a ∘ f`.
This file counts the index maps and embeddings producing a given word, and combines those fibre
counts with singleton-mass and finite-space excess formulas to compute the exact discrepancy
between sampling the one-pair population without and with replacement.

Write `r` for the number of coordinates `i : ι` with `Function.update id b a (f i) = a`, that is
with `f i ∈ {a, b}`. For an injective `f`, `r ≤ 2`, and `r = 2` exactly when `a` and `b` both lie
in the range of `f`. The word of `f` is produced by `2 ^ r` index maps, and, when `f` is an
embedding, by one embedding if `r = 0` and by two (namely `f` and `Equiv.swap a b ∘ f`) otherwise.

Consequently, when `|ι| ≤ |κ|`, let `p = (|κ|)_|ι| / |κ| ^ |ι|` be the injectivity probability of
a uniform index map and `t = (|ι|)_2 / (|κ|)_2` the probability that a uniform injective selection
hits both `a` and `b`. On the support of the without-replacement law `P`, the likelihood ratio
`Q {y} / P {y}` is `p` when `r ≤ 1` (total `P`-mass `1 - t`) and `2 * p` when `r = 2` (total
`P`-mass `t`). Summing the positive singleton differences gives the exact largest eventwise excess
`1 - p - t * min p (1 - p)`, and twice that value for `etvDist`.

## Main declarations

* `card_filter_update_id_apply_eq_le_two`, `card_filter_update_id_apply_eq_eq_two_iff`: an
  injective index map meets `{a, b}` at most twice, and twice exactly when it hits both;
* `natCard_update_id_comp_eq_update_id_comp`: the number of index maps with the same word is
  `2 ^ r`;
* `natCard_embedding_update_id_comp_eq_update_id_comp`: the number of embeddings with the same
  word is `1` if `r = 0` and `2` otherwise;
* `sampleWithoutReplacement_dirac_update_id_card_filter_eq_two`: under sampling without
  replacement, the sampled word takes the repeated value `a` twice with probability
  `(|ι|)_2 / (|κ|)_2`;
* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq`: the exact largest
  eventwise excess `1 - p - t * min p (1 - p)` for the one-pair population;
* `etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_update_id_eq`: Mathlib's total
  variation distance `etvDist` is twice that excess.

The embeddings with the same word as an embedding `f`, namely `f` and `Equiv.swap a b ∘ f`, are
described by `Function.Embedding.update_id_comp_eq_update_id_comp_iff` in
`TauCeti.Logic.Function.Update`.
-/

public section

noncomputable section

open Finset Function MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {ι κ : Type*} {a b : κ}

section Fibres

variable [DecidableEq κ]

/-- The values of an injective index map at the indices it sends to `a` or `b` are distinct
elements of `{a, b}`, so they number the elements of `{a, b}` in its range. -/
private theorem card_filter_update_id_apply_eq_eq_card_filter_mem_range [Fintype ι] {f : ι → κ}
    (hf : Injective f) :
    #{i | update id b a (f i) = a} = #(({a, b} : Finset κ).filter (· ∈ Set.range f)) := by
  rw [← card_preimage _ f hf.injOn]
  congr 1
  ext i
  simp

/-- An injective index map sends at most two indices into `{a, b}`. -/
theorem card_filter_update_id_apply_eq_le_two [Fintype ι] {f : ι → κ} (hf : Injective f) :
    #{i | update id b a (f i) = a} ≤ 2 := by
  classical
  rw [card_filter_update_id_apply_eq_eq_card_filter_mem_range hf]
  exact (card_filter_le _ _).trans card_le_two

/-- An injective index map sends exactly two indices into `{a, b}` if and only if both `a` and
`b` lie in its range. -/
theorem card_filter_update_id_apply_eq_eq_two_iff [Fintype ι] {f : ι → κ} (hf : Injective f)
    (hab : a ≠ b) :
    #{i | update id b a (f i) = a} = 2 ↔ a ∈ Set.range f ∧ b ∈ Set.range f := by
  classical
  rw [card_filter_update_id_apply_eq_eq_card_filter_mem_range hf, ← card_pair hab,
    card_filter_eq_iff]
  simp

/-- The index maps with the same one-pair word as `f` choose freely between `a` and `b` at each
index that `f` sends into `{a, b}`, and agree with `f` elsewhere: there are `2 ^ r` of them, where
`r` is the number of such indices. The index type `κ` need not be finite. -/
theorem natCard_update_id_comp_eq_update_id_comp [Fintype ι] (hab : a ≠ b) (f : ι → κ) :
    Nat.card {g : ι → κ // update id b a ∘ g = update id b a ∘ f} =
      2 ^ #{i | update id b a (f i) = a} := by
  classical
  -- The fibre is a product, over `ι`, of the fibres of the one-pair population.
  have hfib (i : ι) : Nat.card {y : κ // update id b a y = update id b a (f i)} =
      if update id b a (f i) = a then 2 else 1 := by
    have hset : {y : κ | update id b a y = update id b a (f i)} =
        ({f i, Equiv.swap a b (f i)} : Set κ) := by
      ext y
      simp [update_id_apply_eq_update_id_apply_iff]
    rw [← Set.coe_ofPred, Nat.card_coe_set_eq, hset]
    split_ifs with h
    · exact Set.ncard_pair (Equiv.swap_apply_ne_self_iff.2 ⟨hab, update_id_apply_eq_iff.1 h⟩).symm
    · have he : Equiv.swap a b (f i) = f i := not_not.1 fun hne =>
        h (update_id_apply_eq_iff.2 (Equiv.swap_apply_ne_self_iff.1 hne).2)
      rw [he, Set.pair_eq_singleton, Set.ncard_singleton]
  have e : {g : ι → κ // update id b a ∘ g = update id b a ∘ f} ≃
      ∀ i, {y : κ // update id b a y = update id b a (f i)} :=
    (Equiv.subtypeEquivRight fun g => funext_iff).trans
      (Equiv.subtypePiEquivPi (p := fun i y => update id b a y = update id b a (f i)))
  rw [Nat.card_congr e, Nat.card_pi]
  simp_rw [hfib]
  rw [prod_ite, prod_const_one, mul_one, prod_const]

/-- The embeddings with the same one-pair word as an embedding `f` number one when `f` avoids
`{a, b}` and two otherwise: `f` itself and `Equiv.swap a b ∘ f`. The index type `κ` need not be
finite. -/
theorem natCard_embedding_update_id_comp_eq_update_id_comp [Fintype ι] (hab : a ≠ b)
    (f : ι ↪ κ) :
    Nat.card {g : ι ↪ κ // update id b a ∘ g = update id b a ∘ f} =
      if #{i | update id b a (f i) = a} = 0 then 1 else 2 := by
  classical
  have hset : {g : ι ↪ κ | update id b a ∘ g = update id b a ∘ f} =
      ({f, f.trans (Equiv.swap a b).toEmbedding} : Set (ι ↪ κ)) := by
    ext g
    simp [Embedding.update_id_comp_eq_update_id_comp_iff]
  have hfix : f.trans (Equiv.swap a b).toEmbedding = f ↔ #{i | update id b a (f i) = a} = 0 := by
    simp only [DFunLike.ext_iff, Embedding.trans_apply, Equiv.coe_toEmbedding, card_eq_zero,
      filter_eq_empty_iff, mem_univ, true_implies, update_id_apply_eq_iff, not_or]
    refine forall_congr' fun i => ?_
    rw [← not_iff_not, ← ne_eq, Equiv.swap_apply_ne_self_iff]
    simp [hab, or_iff_not_imp_left]
  rw [← Set.coe_ofPred, Nat.card_coe_set_eq, hset]
  split_ifs with h
  · rw [hfix.2 h, Set.pair_eq_singleton, Set.ncard_singleton]
  · exact Set.ncard_pair fun he => h (hfix.1 he.symm)

end Fibres

section Discrepancy

variable [Fintype ι] [Fintype κ] [DecidableEq κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- Under sampling without replacement from the one-pair population `Function.update id b a`, the
probability that the sampled word takes the repeated value `a` twice is `(|ι|)_2 / (|κ|)_2`. -/
theorem sampleWithoutReplacement_dirac_update_id_card_filter_eq_two
    (hab : a ≠ b) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))
        {y | #{i | y i = a} = 2} =
      (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2 := by
  classical
  have heq : {k : ι → κ | Injective k} ∩
      ((fun k i => update id b a (k i)) ⁻¹' {y | #{i | y i = a} = 2}) =
      {k : ι → κ | Injective k} ∩ {k | a ∈ Set.range k ∧ b ∈ Set.range k} := by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    exact and_congr_right fun hk => card_filter_update_id_apply_eq_eq_two_iff hk hab
  rw [sampleWithoutReplacement_dirac,
    Measure.map_apply (measurable_readPopulation _) (Set.toFinite _).measurableSet,
    ← uniformOn_inter_self (Set.toFinite _), heq, uniformOn_inter_self (Set.toFinite _),
    uniformOn_injective_mem_range_and_mem_range hab hmn]

/-- On the support of sampling without replacement from `update id b a`, the real singleton mass
under sampling with replacement is `p` times the without-replacement mass when `r ≤ 1`, and
`2 * p` times it when `r = 2`. -/
private theorem sampleWithReplacement_dirac_update_id_real_singleton_comp
    (hab : a ≠ b) (hmn : Fintype.card ι ≤ Fintype.card κ) (f : ι ↪ κ) :
    (sampleWithReplacement (ι := ι) (Measure.dirac (update id b a))).real
        {update id b a ∘ f} =
      (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
          (Fintype.card κ : ℝ) ^ Fintype.card ι
       if #{i | update id b a (f i) = a} = 2 then 2 * p else p) *
      (sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))).real
        {update id b a ∘ f} := by
  classical
  have hdesc : ((Fintype.card κ).descFactorial (Fintype.card ι) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.descFactorial_eq_zero_iff_lt.not.2 (not_lt.2 hmn)
  have hr : #{i | update id b a (f i) = a} ≤ 2 :=
    card_filter_update_id_apply_eq_le_two f.injective
  simp only [Measure.real, sampleWithReplacement_dirac_apply_singleton,
    sampleWithoutReplacement_dirac_apply_singleton,
    natCard_update_id_comp_eq_update_id_comp hab f,
    natCard_embedding_update_id_comp_eq_update_id_comp hab f,
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow]
  interval_cases #{i | update id b a (f i) = a} <;> simp <;> field_simp [hdesc]; ring

/-- For every word `y : ι → κ`, the positive singleton difference `(P {y} - Q {y}).toReal` is
`max (1 - 2 * p) 0 * P.real {y}` when `y` hits `a` twice and `(1 - p) * P.real {y}` otherwise;
words outside the support of `P` satisfy `P.real {y} = 0`, so both sides vanish there. -/
private theorem toReal_sampleWithoutReplacement_sub_sampleWithReplacement_singleton
    (hab : a ≠ b) (hmn : Fintype.card ι ≤ Fintype.card κ) (y : ι → κ) :
    (sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {y} -
        sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) {y}).toReal =
      (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
          (Fintype.card κ : ℝ) ^ Fintype.card ι
       if #{i | y i = a} = 2 then max (1 - 2 * p) 0 else 1 - p) *
      (sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))).real {y} := by
  classical
  set P := sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))
  set Q := sampleWithReplacement (ι := ι) (Measure.dirac (update id b a))
  set p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
      (Fintype.card κ : ℝ) ^ Fintype.card ι
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  have := isProbabilityMeasure_sampleWithoutReplacement (Measure.dirac (update id b a)) e
  by_cases hy : ∃ f : ι ↪ κ, update id b a ∘ f = y
  · obtain ⟨f, rfl⟩ := hy
    have hp_le : p ≤ 1 := div_le_one_of_le₀
      (by exact_mod_cast Nat.descFactorial_le_pow _ _) (by positivity)
    rw [← ofReal_measureReal (μ := P), ← ofReal_measureReal (μ := Q),
      ← ENNReal.ofReal_sub _ measureReal_nonneg, ENNReal.toReal_ofReal',
      sampleWithReplacement_dirac_update_id_real_singleton_comp hab hmn f]
    have hsub : P.real {update id b a ∘ f} -
        (if #{i | update id b a (f i) = a} = 2 then 2 * p else p) *
          P.real {update id b a ∘ f} =
        (1 - if #{i | update id b a (f i) = a} = 2 then 2 * p else p) *
          P.real {update id b a ∘ f} := by ring
    have hmax : max ((1 - if #{i | update id b a (f i) = a} = 2 then 2 * p else p) *
          P.real {update id b a ∘ f}) 0 =
        max (1 - if #{i | update id b a (f i) = a} = 2 then 2 * p else p) 0 *
          P.real {update id b a ∘ f} := by
      simpa using (max_mul_of_nonneg
        (1 - if #{i | update id b a (f i) = a} = 2 then 2 * p else p) 0 measureReal_nonneg).symm
    rw [hsub, hmax]
    simp only [Function.comp_apply]
    split_ifs
    · rfl
    · rw [max_eq_left (sub_nonneg.2 hp_le)]
  · have hempty : IsEmpty {f : ι ↪ κ // update id b a ∘ f = y} :=
      ⟨fun f => hy ⟨f.1, f.2⟩⟩
    have hP0 : P {y} = 0 := by
      rw [sampleWithoutReplacement_dirac_apply_singleton]
      simp
    simp [Measure.real, hP0]

/-- The real sum of the positive singleton differences between sampling `update id b a` without
and with replacement is `1 - p - t * min p (1 - p)`. -/
private theorem sum_toReal_sampleWithoutReplacement_sub_sampleWithReplacement_singleton
    [DecidableEq ι] (hab : a ≠ b) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    ∑ y : ι → κ,
        (sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {y} -
          sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) {y}).toReal =
      let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
          (Fintype.card κ : ℝ) ^ Fintype.card ι
      let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
      1 - p - t * min p (1 - p) := by
  simp_rw [toReal_sampleWithoutReplacement_sub_sampleWithReplacement_singleton hab hmn]
  set P := sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))
  set p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
      (Fintype.card κ : ℝ) ^ Fintype.card ι
  set t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  have := isProbabilityMeasure_sampleWithoutReplacement (Measure.dirac (update id b a)) e
  have hT₂ : P.real ((univ.filter fun y : ι → κ => #{i | y i = a} = 2 : Finset (ι → κ)) :
      Set (ι → κ)) = t := by
    have hset : ((univ.filter fun y : ι → κ => #{i | y i = a} = 2 : Finset (ι → κ)) :
        Set (ι → κ)) = {y | #{i | y i = a} = 2} := by
      ext y
      simp
    rw [Measure.real, hset, sampleWithoutReplacement_dirac_update_id_card_filter_eq_two hab hmn,
      ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  have hT₂c : P.real ((univ.filter fun y : ι → κ => ¬ #{i | y i = a} = 2 : Finset (ι → κ)) :
      Set (ι → κ)) = 1 - t := by
    have hcompl : ((univ.filter fun y : ι → κ => ¬ #{i | y i = a} = 2 : Finset (ι → κ)) :
        Set (ι → κ)) = ((univ.filter fun y : ι → κ => #{i | y i = a} = 2 : Finset (ι → κ)) :
        Set (ι → κ))ᶜ := by
      ext y
      simp
    rw [hcompl, probReal_compl_eq_one_sub (Finset.measurableSet _), hT₂]
  rw [← sum_filter_add_sum_filter_not univ (fun y : ι → κ => #{i | y i = a} = 2)]
  have h1 : ∑ y ∈ univ.filter (fun y : ι → κ => #{i | y i = a} = 2),
      (if #{i | y i = a} = 2 then max (1 - 2 * p) 0 else 1 - p) * P.real {y} =
      max (1 - 2 * p) 0 * t := calc
    _ = ∑ y ∈ univ.filter (fun y : ι → κ => #{i | y i = a} = 2), max (1 - 2 * p) 0 * P.real {y} :=
      sum_congr rfl fun y hy => by simp [(mem_filter.1 hy).2]
    _ = max (1 - 2 * p) 0 * t := by rw [← mul_sum, sum_measureReal_singleton, hT₂]
  have h2 : ∑ y ∈ univ.filter (fun y : ι → κ => ¬ #{i | y i = a} = 2),
      (if #{i | y i = a} = 2 then max (1 - 2 * p) 0 else 1 - p) * P.real {y} =
      (1 - p) * (1 - t) := calc
    _ = ∑ y ∈ univ.filter (fun y : ι → κ => ¬ #{i | y i = a} = 2), (1 - p) * P.real {y} :=
      sum_congr rfl fun y hy => by simp [(mem_filter.1 hy).2]
    _ = (1 - p) * (1 - t) := by rw [← mul_sum, sum_measureReal_singleton, hT₂c]
  rw [h1, h2]
  rcases le_total p (1 - p) with hp | hp
  · rw [min_eq_left hp, max_eq_left (by linarith)]
    ring
  · rw [min_eq_right hp, max_eq_right (by linarith)]
    ring

/-- For the population `Function.update id b a` identifying a single pair `a ≠ b`, and
`|ι| ≤ |κ|`, the largest excess of sampling without replacement over sampling with replacement is
`1 - p - t * min p (1 - p)`, where `p = (|κ|)_|ι| / |κ| ^ |ι|` and `t = (|ι|)_2 / (|κ|)_2`. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq
    (hab : a ≠ b) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    (⨆ (A : Set (ι → κ)) (_ : MeasurableSet A),
        sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) A -
          sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) A) =
      ENNReal.ofReal
        (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ) ^ Fintype.card ι
         let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
         1 - p - t * min p (1 - p)) := by
  classical
  rw [iSup_measure_sub_eq_sum]
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  have := isProbabilityMeasure_sampleWithoutReplacement (Measure.dirac (update id b a)) e
  have hfin (y : ι → κ) :
      sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {y} -
        sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) {y} ≠ ⊤ :=
    ENNReal.sub_ne_top (measure_ne_top _ _)
  rw [← ENNReal.ofReal_toReal (ENNReal.sum_ne_top.2 fun y _ => hfin y),
    ENNReal.toReal_sum fun y _ => hfin y,
    sum_toReal_sampleWithoutReplacement_sub_sampleWithReplacement_singleton hab hmn]

/-- For the population `Function.update id b a` identifying a single pair `a ≠ b`, and
`|ι| ≤ |κ|`, Mathlib's extended total variation distance between sampling without and with
replacement is `2 * ENNReal.ofReal (1 - p - t * min p (1 - p))`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_update_id_eq
    (hab : a ≠ b) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    etvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)))
        (sampleWithReplacement (ι := ι) (Measure.dirac (update id b a))) =
      2 * ENNReal.ofReal
        (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ) ^ Fintype.card ι
         let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
         1 - p - t * min p (1 - p)) := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  have : Nonempty (ι → κ) := ⟨e⟩
  have := isProbabilityMeasure_sampleWithoutReplacement (Measure.dirac (update id b a)) e
  have := isProbabilityMeasure_sampleWithReplacement (ι := ι) (Measure.dirac (update id b a))
  rw [etvDist_eq_two_mul_iSup_sub (by rw [measure_univ, measure_univ]),
    iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq hab hmn]

end Discrepancy

end Probability

end TauCeti

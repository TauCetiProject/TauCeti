/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Set.Card
public import TauCeti.MeasureTheory.Measure.TotalVariation.Basic
public import TauCeti.Probability.PopulationSampling.Finite
import Mathlib.Data.Finset.Preimage
import TauCeti.Logic.Function.Update
import TauCeti.MeasureTheory.Measure.TotalVariation.Countable

/-!
# The one-pair population: fibres and exact sampling discrepancy

For distinct indices `a b : κ`, the *one-pair population* `Function.update id b a : κ → κ` sends
`b` to `a` and fixes every other index; it is the population with exactly one repeated value.
Sampling it along an index map `f : ι → κ` gives the word `Function.update id b a ∘ f`. This file
counts the index maps and embeddings producing a given word, and uses those fibre counts together
with the two-hit probability `uniformOn_injective_mem_range_and_mem_range` to compute the exact
discrepancy between sampling `Function.update id b a` without and with replacement.

Write `r` for the number of `i` with `Function.update id b a (f i) = a`, that is with
`f i ∈ {a, b}`. For an injective `f`, `r ≤ 2`, and `r = 2` exactly when `a` and `b` both lie in the
range of `f`. The word of `f` is produced by `2 ^ r` index maps, and, when `f` is an embedding, by
one embedding if `r = 0` and by two (namely `f` and `Equiv.swap a b ∘ f`) otherwise.

Write `m = |ι|`, `n = |κ|`, and write `P` and `Q` for
`sampleWithoutReplacement (Measure.dirac (Function.update id b a))` and
`sampleWithReplacement (Measure.dirac (Function.update id b a))`. On the support of `P`, the
likelihood ratio `Q {y} / P {y}` is `p = n_(m) / n^m` when `r ≤ 1` and `2 * p` when `r = 2`, while
the two regimes have `P`-masses `1 - t` and `t = m_(2) / n_(2)`. Summing singleton excesses over
`ι → κ` gives the exact excess `onePairSamplingExcess m n = 1 - p - t * min p (1 - p)` whenever
`m ≤ n`, and `etvDist` is twice that value.

## Main declarations

* `card_filter_update_id_apply_eq_le_two`, `card_filter_update_id_apply_eq_eq_two_iff`: an
  injective index map meets `{a, b}` at most twice, and twice exactly when it hits both;
* `natCard_update_id_comp_eq_update_id_comp`: the number of index maps with the same word is
  `2 ^ r`;
* `natCard_embedding_update_id_comp_eq_update_id_comp`: the number of embeddings with the same
  word is `1` if `r = 0` and `2` otherwise;
* `onePairSamplingExcess`: the closed-form one-pair excess `1 - p - t * min p (1 - p)`, together
  with its definitional formula, bounds, and degenerate-regime values;
* `ofReal_descFactorial_div_pow`: `ENNReal.ofReal` conversion of the injective-selection ratio
  `n_(m) / n^m`;
* `sampleWithoutReplacement_dirac_update_id_card_filter_eq_two`: the without-replacement mass of
  words containing `a` twice is `m_(2) / n_(2)`;
* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq`: the exact largest
  eventwise excess between sampling `Function.update id b a` without and with replacement;
* `etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_update_id_eq`: twice that excess
  in Mathlib's total variation normalization.

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

section OnePairExcess

/-- The exact largest eventwise excess between sampling the one-pair population of size `n`
without and with replacement in a sample of size `m`:
`1 - p - t * min p (1 - p)`, where `p = n_(m) / n^m` and `t = m_(2) / n_(2)`. -/
def onePairSamplingExcess (m n : ℕ) : ℝ :=
  1 - (n.descFactorial m : ℝ) / (n : ℝ) ^ m -
    (m.descFactorial 2 / (n.descFactorial 2 : ℝ)) *
      min ((n.descFactorial m : ℝ) / (n : ℝ) ^ m)
        (1 - (n.descFactorial m : ℝ) / (n : ℝ) ^ m)

/-- Definitional formula for `onePairSamplingExcess`. -/
theorem onePairSamplingExcess_def (m n : ℕ) :
    onePairSamplingExcess m n =
      1 - (n.descFactorial m : ℝ) / (n : ℝ) ^ m -
        (m.descFactorial 2 / (n.descFactorial 2 : ℝ)) *
          min ((n.descFactorial m : ℝ) / (n : ℝ) ^ m)
            (1 - (n.descFactorial m : ℝ) / (n : ℝ) ^ m) :=
  (rfl)

/-- When the sample size exceeds the population size, `onePairSamplingExcess m n = 1`. -/
theorem onePairSamplingExcess_eq_one_of_lt {m n : ℕ} (h : n < m) :
    onePairSamplingExcess m n = 1 := by
  rw [onePairSamplingExcess_def, Nat.descFactorial_eq_zero_iff_lt.2 h]
  simp

/-- When the sample has size at most one and fits inside the population,
`onePairSamplingExcess m n = 0`. -/
theorem onePairSamplingExcess_eq_zero_of_le_one {m n : ℕ} (hm : m ≤ 1) (hmn : m ≤ n) :
    onePairSamplingExcess m n = 0 := by
  rw [onePairSamplingExcess_def]
  interval_cases m
  · simp
  · have hn0 : (n : ℝ) ≠ 0 := by positivity
    simp [hn0]

/-- The real injective-selection ratio `n_(m) / n^m` never exceeds `1`. -/
private theorem descFactorial_div_pow_le_one (n m : ℕ) :
    (n.descFactorial m : ℝ) / (n : ℝ) ^ m ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · cases m <;> simp
  · exact (div_le_one (by positivity)).2 (by exact_mod_cast Nat.descFactorial_le_pow n m)

/-- `onePairSamplingExcess m n` is always nonnegative. -/
theorem onePairSamplingExcess_nonneg (m n : ℕ) : 0 ≤ onePairSamplingExcess m n := by
  rcases le_or_gt m n with hmn | hlt
  · rcases le_or_gt n 1 with hn1 | hn2
    · rw [onePairSamplingExcess_eq_zero_of_le_one (hmn.trans hn1) hmn]
    · rw [onePairSamplingExcess_def]
      have hp0 : (0 : ℝ) ≤ n.descFactorial m / (n : ℝ) ^ m := by positivity
      have hp1 : (n.descFactorial m : ℝ) / (n : ℝ) ^ m ≤ 1 := descFactorial_div_pow_le_one n m
      have hn2_pos : (0 : ℝ) < n.descFactorial 2 := by
        exact_mod_cast Nat.descFactorial_pos.2 hn2
      have ht1 : (m.descFactorial 2 : ℝ) / n.descFactorial 2 ≤ 1 :=
        (div_le_one hn2_pos).2 (by exact_mod_cast Nat.descFactorial_le 2 hmn)
      nlinarith [min_le_right ((n.descFactorial m : ℝ) / (n : ℝ) ^ m)
        (1 - (n.descFactorial m : ℝ) / (n : ℝ) ^ m),
        le_min hp0 (sub_nonneg.2 hp1)]
  · rw [onePairSamplingExcess_eq_one_of_lt hlt]
    norm_num

/-- `onePairSamplingExcess m n` never exceeds the real collision probability `1 - n_(m) / n^m`. -/
theorem onePairSamplingExcess_le_one_sub_descFactorial_div_pow (m n : ℕ) :
    onePairSamplingExcess m n ≤ 1 - (n.descFactorial m : ℝ) / (n : ℝ) ^ m := by
  rw [onePairSamplingExcess_def]
  have hp0 : (0 : ℝ) ≤ n.descFactorial m / (n : ℝ) ^ m := by positivity
  have hp1 : (n.descFactorial m : ℝ) / (n : ℝ) ^ m ≤ 1 := descFactorial_div_pow_le_one n m
  have hmin : 0 ≤ min ((n.descFactorial m : ℝ) / (n : ℝ) ^ m)
      (1 - (n.descFactorial m : ℝ) / (n : ℝ) ^ m) := le_min hp0 (sub_nonneg.2 hp1)
  have ht0 : (0 : ℝ) ≤ m.descFactorial 2 / n.descFactorial 2 := by positivity
  linarith [mul_nonneg ht0 hmin]

/-- In `ℝ≥0∞`, the injective-selection ratio `n_(m) / n^m` is the `ENNReal.ofReal` image of its
real counterpart. -/
theorem ofReal_descFactorial_div_pow (n m : ℕ) :
    ENNReal.ofReal ((n.descFactorial m : ℝ) / (n : ℝ) ^ m) =
      (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m := by
  rcases eq_or_ne n 0 with rfl | hn
  · cases m <;> simp
  · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    simp [ENNReal.ofReal_div_of_pos (pow_pos hn_pos m), ENNReal.ofReal_pow hn_pos.le]

/-- For `2 ≤ n` and `m ≤ n`, the two-regime `ℝ≥0∞` excess sum
`(1 - 2 * p) * t + (1 - p) * (1 - t)` equals `ENNReal.ofReal (onePairSamplingExcess m n)`. -/
private theorem ofReal_onePairSamplingExcess_eq {m n : ℕ} (hn : 2 ≤ n) (hmn : m ≤ n) :
    (1 - 2 * ((n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m)) *
        ((m.descFactorial 2 : ℝ≥0∞) / (n.descFactorial 2 : ℝ≥0∞)) +
      (1 - (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m) *
        (1 - (m.descFactorial 2 : ℝ≥0∞) / (n.descFactorial 2 : ℝ≥0∞)) =
      ENNReal.ofReal (onePairSamplingExcess m n) := by
  rw [onePairSamplingExcess_def, ← ofReal_descFactorial_div_pow]
  have hn2_pos : (0 : ℝ) < n.descFactorial 2 := by exact_mod_cast Nat.descFactorial_pos.2 hn
  have ht_eq : (m.descFactorial 2 : ℝ≥0∞) / (n.descFactorial 2 : ℝ≥0∞) =
      ENNReal.ofReal (m.descFactorial 2 / (n.descFactorial 2 : ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos hn2_pos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [ht_eq]
  set p : ℝ := (n.descFactorial m : ℝ) / (n : ℝ) ^ m
  set t : ℝ := (m.descFactorial 2 : ℝ) / (n.descFactorial 2 : ℝ)
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := descFactorial_div_pow_le_one n m
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := (div_le_one hn2_pos).2 (by exact_mod_cast Nat.descFactorial_le 2 hmn)
  have hp_sub : 1 - ENNReal.ofReal p = ENNReal.ofReal (1 - p) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hp0]
  have ht_sub : 1 - ENNReal.ofReal t = ENNReal.ofReal (1 - t) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 ht0]
  have h2p : 1 - 2 * ENNReal.ofReal p = ENNReal.ofReal (1 - 2 * p) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by positivity)]
  rw [hp_sub, ht_sub, h2p]
  rcases le_total p (1 - p) with h | h
  · rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by linarith),
      ← ENNReal.ofReal_add (by nlinarith) (by nlinarith)]
    congr 1
    rw [min_eq_left h]
    ring
  · rw [ENNReal.ofReal_of_nonpos (by linarith), zero_mul, zero_add,
      ← ENNReal.ofReal_mul (by linarith)]
    congr 1
    rw [min_eq_right h]
    ring

end OnePairExcess

section Discrepancy

variable [Fintype ι] [Fintype κ] [DecidableEq κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- Sampling the one-pair population `Function.update id b a` without replacement produces a word
containing `a` twice with probability `|ι| (|ι| - 1) / (|κ| (|κ| - 1))` whenever `a ≠ b` and
`|ι| ≤ |κ|`. -/
theorem sampleWithoutReplacement_dirac_update_id_card_filter_eq_two (hab : a ≠ b)
    (hmn : Fintype.card ι ≤ Fintype.card κ) :
    sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))
        {y | #{i | y i = a} = 2} =
      (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2 := by
  rw [sampleWithoutReplacement_dirac,
    Measure.map_apply (measurable_readPopulation _) (Set.toFinite _).measurableSet,
    ← uniformOn_inter_self (Set.toFinite _)]
  have hinter :
      {k : ι → κ | Injective k} ∩
          (fun k i => update id b a (k i)) ⁻¹' {y | #{i | y i = a} = 2} =
        {k : ι → κ | Injective k} ∩ {k : ι → κ | a ∈ Set.range k ∧ b ∈ Set.range k} := by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    exact and_congr_right fun hk => card_filter_update_id_apply_eq_eq_two_iff hk hab
  rw [hinter, uniformOn_inter_self (Set.toFinite _),
    uniformOn_injective_mem_range_and_mem_range hab hmn]

/-- Cancelling `n_(m)` converts a without-replacement singleton mass into the corresponding
with-replacement denominator when `m ≤ n`. -/
private theorem descFactorial_div_pow_mul_div_descFactorial {m n : ℕ} (hmn : m ≤ n) (c : ℝ≥0∞) :
    ((n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m) * (c / (n.descFactorial m : ℝ≥0∞)) =
      c / (n : ℝ≥0∞) ^ m := by
  have hd0 : (n.descFactorial m : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.2 hmn).ne'
  calc
    ((n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m) * (c / (n.descFactorial m : ℝ≥0∞))
        = (n.descFactorial m : ℝ≥0∞) * (n.descFactorial m : ℝ≥0∞)⁻¹ *
            (c * ((n : ℝ≥0∞) ^ m)⁻¹) := by
          simp only [div_eq_mul_inv]; ac_rfl
    _ = c / (n : ℝ≥0∞) ^ m := by
          rw [ENNReal.mul_inv_cancel hd0 (ENNReal.natCast_ne_top _), one_mul, div_eq_mul_inv]

/-- On a word of the one-pair population where `a` appears twice, the with-replacement singleton
mass is `2 * |κ|_(|ι|) / |κ| ^ |ι|` times the without-replacement singleton mass. -/
private theorem sampleWithReplacement_dirac_update_id_singleton_eq_two_mul (hab : a ≠ b)
    (hmn : Fintype.card ι ≤ Fintype.card κ) (f : ι ↪ κ)
    (hr : #{i | update id b a (f i) = a} = 2) :
    sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) {update id b a ∘ f} =
      (2 * ((Fintype.card κ).descFactorial (Fintype.card ι) /
          (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι)) *
        sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))
          {update id b a ∘ f} := by
  rw [sampleWithoutReplacement_dirac_singleton, sampleWithReplacement_dirac_singleton,
    natCard_embedding_update_id_comp_eq_update_id_comp hab f,
    natCard_update_id_comp_eq_update_id_comp hab f, hr, mul_assoc,
    descFactorial_div_pow_mul_div_descFactorial hmn, ← mul_div_assoc]
  norm_num

/-- On a word of the one-pair population where `a` appears at most once, the with-replacement
singleton mass is `|κ|_(|ι|) / |κ| ^ |ι|` times the without-replacement singleton mass. -/
private theorem sampleWithReplacement_dirac_update_id_singleton_eq_mul_of_ne_two (hab : a ≠ b)
    (hmn : Fintype.card ι ≤ Fintype.card κ) (f : ι ↪ κ)
    (hr : #{i | update id b a (f i) = a} ≠ 2) :
    sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) {update id b a ∘ f} =
      ((Fintype.card κ).descFactorial (Fintype.card ι) /
          (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) *
        sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))
          {update id b a ∘ f} := by
  have hle : #{i | update id b a (f i) = a} ≤ 1 := by
    have := card_filter_update_id_apply_eq_le_two (a := a) (b := b) f.injective
    omega
  have hcard : 2 ^ #{i | update id b a (f i) = a} =
      if #{i | update id b a (f i) = a} = 0 then 1 else 2 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h | h <;> rw [h] <;> norm_num
  rw [sampleWithoutReplacement_dirac_singleton, sampleWithReplacement_dirac_singleton,
    natCard_embedding_update_id_comp_eq_update_id_comp hab f,
    natCard_update_id_comp_eq_update_id_comp hab f, hcard,
    descFactorial_div_pow_mul_div_descFactorial hmn]

omit [Fintype κ] in
/-- If the with-replacement mass of a word `y` equals `c` times its without-replacement mass
whenever `y` lies in the support of `sampleWithoutReplacement (Measure.dirac (update id b a))`,
then the truncated singleton excess equals `(1 - c)` times the without-replacement mass. -/
private theorem sampleWithoutReplacement_dirac_update_id_singleton_sub_of_eq_mul
    [Finite κ] {y : ι → κ} {c : ℝ≥0∞}
    (hc : ∀ f : ι ↪ κ, update id b a ∘ f = y →
      sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) {y} =
        c * sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {y}) :
    sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {y} -
        sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) {y} =
      (1 - c) * sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {y} := by
  by_cases hy : ∃ f : ι ↪ κ, update id b a ∘ f = y
  · obtain ⟨f, hf⟩ := hy
    rw [hc f hf, ENNReal.sub_mul fun _ _ => measure_ne_top _ _, one_mul]
  · cases nonempty_fintype κ
    have : IsEmpty {f : ι ↪ κ // update id b a ∘ f = y} := ⟨fun f => hy ⟨f.1, f.2⟩⟩
    have hP0 : sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {y} = 0 := by
      rw [sampleWithoutReplacement_dirac_singleton, Nat.card_eq_fintype_card, Fintype.card_eq_zero]
      simp
    rw [hP0, zero_tsub, mul_zero]

/-- Splitting the singleton-excess sum of `Function.update id b a` by whether `a` occurs twice
expresses the largest excess in `ℝ≥0∞` as `(1 - 2 * p) * t + (1 - p) * (1 - t)`, where
`p = |κ|_(|ι|) / |κ| ^ |ι|` and `t = |ι|_(2) / |κ|_(2)`. -/
private theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq_ennreal
    (hab : a ≠ b) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    (⨆ (A : Set (ι → κ)) (_ : MeasurableSet A),
        sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) A -
          sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) A) =
      (1 - 2 * ((Fintype.card κ).descFactorial (Fintype.card ι) /
          (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι)) *
        ((Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2) +
      (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
          (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) *
        (1 - (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2) := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  let _ := isProbabilityMeasure_sampleWithoutReplacement (Measure.dirac (update id b a)) e
  have hE2 : sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))
        {y | #{i | y i = a} = 2} =
      (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2 :=
    sampleWithoutReplacement_dirac_update_id_card_filter_eq_two hab hmn
  have hE2c : sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))
        {y | #{i | y i = a} = 2}ᶜ =
      1 - (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2 := by
    rw [prob_compl_eq_one_sub (Set.toFinite _).measurableSet, hE2]
  have hS2 : ((univ.filter fun y : ι → κ => #{i | y i = a} = 2) : Set (ι → κ)) =
      {y | #{i | y i = a} = 2} := by
    rw [coe_filter]
    ext y
    simp
  have hS2c : ((univ.filter fun y : ι → κ => ¬ #{i | y i = a} = 2) : Set (ι → κ)) =
      {y | #{i | y i = a} = 2}ᶜ := by
    rw [coe_filter]
    ext y
    simp
  rw [iSup_measure_sub_eq_sum_singleton,
    ← sum_filter_add_sum_filter_not univ (fun y : ι → κ => #{i | y i = a} = 2)]
  congr 1
  · have hterm : ∀ y ∈ univ.filter (fun y : ι → κ => #{i | y i = a} = 2),
        sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {y} -
            sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) {y} =
          (1 - 2 * ((Fintype.card κ).descFactorial (Fintype.card ι) /
              (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι)) *
            sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {y} := fun y hy =>
      sampleWithoutReplacement_dirac_update_id_singleton_sub_of_eq_mul fun f hf => by
        subst hf
        exact sampleWithReplacement_dirac_update_id_singleton_eq_two_mul hab hmn f
          (mem_filter.1 hy).2
    rw [sum_congr rfl hterm, ← mul_sum, sum_measure_singleton, hS2, hE2]
  · have hterm : ∀ y ∈ univ.filter (fun y : ι → κ => ¬ #{i | y i = a} = 2),
        sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {y} -
            sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) {y} =
          (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
              (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) *
            sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {y} := fun y hy =>
      sampleWithoutReplacement_dirac_update_id_singleton_sub_of_eq_mul fun f hf => by
        subst hf
        exact sampleWithReplacement_dirac_update_id_singleton_eq_mul_of_ne_two hab hmn f
          (mem_filter.1 hy).2
    rw [sum_congr rfl hterm, ← mul_sum, sum_measure_singleton, hS2c, hE2c]

/-- **Exact discrepancy for the one-pair population (excess form).** For distinct indices `a b : κ`
and `|ι| ≤ |κ|`, the largest eventwise excess of sampling `Function.update id b a` without
replacement over sampling with replacement is
`onePairSamplingExcess |ι| |κ| = 1 - p - t * min p (1 - p)`, where `m = |ι|`, `n = |κ|`,
`p = n_(m) / n^m`, and `t = m_(2) / n_(2)`. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq
    (hab : a ≠ b) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    (⨆ (A : Set (ι → κ)) (_ : MeasurableSet A),
        sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) A -
          sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) A) =
      ENNReal.ofReal (onePairSamplingExcess (Fintype.card ι) (Fintype.card κ)) := by
  have hκ2 : 2 ≤ Fintype.card κ := Fintype.one_lt_card_iff.2 ⟨a, b, hab⟩
  rw [iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq_ennreal hab hmn,
    ofReal_onePairSamplingExcess_eq hκ2 hmn]

/-- **Exact discrepancy for the one-pair population (`etvDist` form).** For distinct indices
`a b : κ` and `|ι| ≤ |κ|`, Mathlib's total variation distance between sampling
`Function.update id b a` without and with replacement is
`2 * onePairSamplingExcess |ι| |κ|`. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_update_id_eq
    (hab : a ≠ b) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    etvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)))
        (sampleWithReplacement (ι := ι) (Measure.dirac (update id b a))) =
      2 * ENNReal.ofReal (onePairSamplingExcess (Fintype.card ι) (Fintype.card κ)) := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  let _ : Nonempty (ι → κ) := ⟨e⟩
  let _ := isProbabilityMeasure_sampleWithoutReplacement (Measure.dirac (update id b a)) e
  let _ := isProbabilityMeasure_sampleWithReplacement (ι := ι) (Measure.dirac (update id b a))
  rw [etvDist_eq_two_mul_iSup_sub (by rw [measure_univ, measure_univ]),
    iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq hab hmn]

end Discrepancy

end Probability

end TauCeti

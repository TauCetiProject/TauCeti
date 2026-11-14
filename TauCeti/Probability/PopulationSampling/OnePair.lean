/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
counts the index maps and the embeddings producing a given word, and assembles from them the exact
discrepancy between sampling the one-pair population without and with replacement.

Write `r` for the number of `i` with `Function.update id b a (f i) = a`, that is with
`f i ∈ {a, b}`. For an injective `f`, `r ≤ 2`, and `r = 2` exactly when `a` and `b` both lie in the
range of `f`. The word of `f` is produced by `2 ^ r` index maps, and, when `f` is an embedding, by
one embedding if `r = 0` and by two (namely `f` and `Equiv.swap a b ∘ f`) otherwise.

Consequently, on the support of the without-replacement law `P` (`|ι| ≤ |κ|`), the ratio of the
with-replacement singleton mass `Q {y}` to `P {y}` is `p = (|κ|)_|ι| / |κ| ^ |ι|` when `r ≤ 1` and
`2 * p` when `r = 2`. Since `r = 2` occurs under `P` with the two-hit probability
`t = (|ι|)_2 / (|κ|)_2` (`uniformOn_injective_mem_range_and_mem_range`), summing the positive parts
of `P {y} - Q {y}` gives the exact largest eventwise excess `1 - p - t * min p (1 - p)`, and twice
that value for Mathlib's total variation distance `etvDist`.

## Main declarations

* `card_filter_update_id_apply_eq_le_two`, `card_filter_update_id_apply_eq_eq_two_iff`: an
  injective index map meets `{a, b}` at most twice, and twice exactly when it hits both;
* `natCard_update_id_comp_eq_update_id_comp`: the number of index maps with the same word is
  `2 ^ r`;
* `natCard_embedding_update_id_comp_eq_update_id_comp`: the number of embeddings with the same
  word is `1` if `r = 0` and `2` otherwise;
* `sampleWithoutReplacement_dirac_update_id_apply_singleton_comp`,
  `sampleWithReplacement_dirac_update_id_apply_singleton_comp`,
  `sampleWithReplacement_dirac_update_id_apply_singleton_comp_eq_mul_sampleWithoutReplacement`:
  singleton masses and likelihood ratio on the support of the without-replacement law;
* `sampleWithoutReplacement_dirac_update_id_card_filter_eq_two`: probability `t` of observing `a`
  twice under sampling without replacement;
* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq`,
  `iSup_sampleWithReplacement_sub_sampleWithoutReplacement_dirac_update_id_eq`,
  `etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_update_id_eq`: exact largest
  excesses and total variation distance for the one-pair population.

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
word `update id b a ∘ f` of an embedding `f : ι ↪ κ` has mass `1 / (|κ|)_|ι|` when `f` avoids
`{a, b}`, and `2 / (|κ|)_|ι|` when `f` meets `{a, b}`. -/
theorem sampleWithoutReplacement_dirac_update_id_apply_singleton_comp (hab : a ≠ b)
    (f : ι ↪ κ) :
    sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {update id b a ∘ f} =
      ((if #{i | update id b a (f i) = a} = 0 then 1 else 2 : ℕ) : ℝ≥0∞) /
        (Fintype.card κ).descFactorial (Fintype.card ι) := by
  rw [sampleWithoutReplacement_dirac_apply_singleton,
    natCard_embedding_update_id_comp_eq_update_id_comp hab f]

/-- Under sampling with replacement from the one-pair population `Function.update id b a`, the
word `update id b a ∘ f` of an index map `f : ι → κ` has mass `2 ^ r / |κ| ^ |ι|`, where `r` is
the number of indices `f` sends into `{a, b}`. -/
theorem sampleWithReplacement_dirac_update_id_apply_singleton_comp (hab : a ≠ b) (f : ι → κ) :
    sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) {update id b a ∘ f} =
      ((2 ^ #{i | update id b a (f i) = a} : ℕ) : ℝ≥0∞) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι := by
  rw [sampleWithReplacement_dirac_apply_singleton,
    natCard_update_id_comp_eq_update_id_comp hab f]

/-- On the support of `sampleWithoutReplacement (Measure.dirac (update id b a))`, the
with-replacement singleton mass equals `p` times the without-replacement singleton mass when the
word takes the value `a` at most once, and `2 * p` times it when the word takes the value `a`
twice. -/
theorem sampleWithReplacement_dirac_update_id_apply_singleton_comp_eq_mul_sampleWithoutReplacement
    (hab : a ≠ b) (f : ι ↪ κ) :
    sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) {update id b a ∘ f} =
      (if #{i | update id b a (f i) = a} = 2 then 2 else 1) *
        ((Fintype.card κ).descFactorial (Fintype.card ι) /
          (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) *
        sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))
          {update id b a ∘ f} := by
  have hr : (2 ^ #{i | update id b a (f i) = a} : ℕ) =
      (if #{i | update id b a (f i) = a} = 2 then 2 else 1) *
        if #{i | update id b a (f i) = a} = 0 then 1 else 2 := by
    have hr2 := card_filter_update_id_apply_eq_le_two (a := a) (b := b) f.injective
    generalize #{i | update id b a (f i) = a} = r at hr2 ⊢
    match r, hr2 with
    | 0, _ | 1, _ | 2, _ => rfl
  have hd0 : ((Fintype.card κ).descFactorial (Fintype.card ι) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast
      Nat.descFactorial_eq_zero_iff_lt.not.2 (not_lt.2 (Fintype.card_le_of_embedding f))
  rw [sampleWithReplacement_dirac_update_id_apply_singleton_comp hab f,
    sampleWithoutReplacement_dirac_update_id_apply_singleton_comp hab f, hr]
  push_cast
  simp only [div_eq_mul_inv]
  calc
    _ = ((if #{i | update id b a (f i) = a} = 2 then (2 : ℝ≥0∞) else 1) *
          (if #{i | update id b a (f i) = a} = 0 then (1 : ℝ≥0∞) else 2) *
          ((Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι)⁻¹) *
        (((Fintype.card κ).descFactorial (Fintype.card ι) : ℝ≥0∞) *
          ((Fintype.card κ).descFactorial (Fintype.card ι) : ℝ≥0∞)⁻¹) := by
      rw [ENNReal.mul_inv_cancel hd0 (ENNReal.natCast_ne_top _), mul_one]
    _ = _ := by
      split_ifs <;> ring

private theorem sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_singleton
    (hab : a ≠ b) (y : ι → κ) :
    sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {y} -
        sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) {y} =
      (if #{i | y i = a} = 2 then
          1 - 2 * ((Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι)
        else
          1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) *
        sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {y} := by
  by_cases hy : Nonempty {f : ι ↪ κ // update id b a ∘ f = y}
  · obtain ⟨⟨f, rfl⟩⟩ := hy
    let := isProbabilityMeasure_sampleWithoutReplacement (Measure.dirac (update id b a)) f
    rw [sampleWithReplacement_dirac_update_id_apply_singleton_comp_eq_mul_sampleWithoutReplacement
      hab f]
    conv_lhs =>
      lhs
      rw [← one_mul (sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) _)]
    rw [← ENNReal.sub_mul fun _ _ => measure_ne_top _ _]
    congr 1
    simp only [Function.comp_apply]
    split_ifs
    · rfl
    · rw [one_mul]
  · have : IsEmpty {f : ι ↪ κ // update id b a ∘ f = y} := not_nonempty_iff.1 hy
    have h0 : sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {y} = 0 := by
      rw [sampleWithoutReplacement_dirac_apply_singleton]
      simp
    rw [h0, zero_tsub, mul_zero]

/-- Sampling the one-pair population `Function.update id b a` without replacement produces a word
taking the value `a` twice with probability `(|ι|)_2 / (|κ|)_2`. -/
theorem sampleWithoutReplacement_dirac_update_id_card_filter_eq_two (hab : a ≠ b)
    (hmn : Fintype.card ι ≤ Fintype.card κ) :
    sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))
        {y | #{i | y i = a} = 2} =
      (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2 := by
  rw [sampleWithoutReplacement_dirac,
    Measure.map_apply (measurable_readPopulation _) .of_discrete,
    ← uniformOn_inter_self (Set.toFinite _),
    ← uniformOn_injective_mem_range_and_mem_range hab hmn]
  symm
  rw [← uniformOn_inter_self (Set.toFinite _)]
  congr 1
  ext k
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
  exact and_congr_right fun hk => (card_filter_update_id_apply_eq_eq_two_iff hk hab).symm

/-- For probabilities `p, t ∈ [0, 1]`, the two-point mixture `(1 - 2p)₊ t + (1 - p)(1 - t)` in
`ℝ≥0∞` equals `ENNReal.ofReal (1 - p - t * min p (1 - p))`. -/
private theorem one_sub_two_mul_ofReal_mul_add_eq_ofReal {p t : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - 2 * ENNReal.ofReal p) * ENNReal.ofReal t +
        (1 - ENNReal.ofReal p) * (1 - ENNReal.ofReal t) =
      ENNReal.ofReal (1 - p - t * min p (1 - p)) := by
  rcases le_total p (1 - p) with hle | hle
  · have h2p : 0 ≤ 1 - 2 * p := by linarith
    have hEq : 1 - p - t * min p (1 - p) = (1 - 2 * p) * t + (1 - p) * (1 - t) := by
      rw [min_eq_left hle]
      ring
    rw [hEq, ENNReal.ofReal_add (mul_nonneg h2p ht0)
      (mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 ht1))]
    simp [ENNReal.ofReal_sub, hp0, ht0, sub_nonneg.2 hp1, h2p, mul_nonneg zero_le_two hp0]
  · have h2p : 1 ≤ 2 * p := by linarith
    have h0 : 1 - 2 * ENNReal.ofReal p = 0 :=
      tsub_eq_zero_of_le (by simpa using ENNReal.ofReal_le_ofReal h2p)
    have hEq : 1 - p - t * min p (1 - p) = (1 - p) * (1 - t) := by
      rw [min_eq_right hle]
      ring
    rw [h0, zero_mul, zero_add, hEq]
    simp [ENNReal.ofReal_sub, hp0, ht0, sub_nonneg.2 hp1]

/-- For the population `Function.update id b a` identifying one distinct pair of indices, the
largest excess of sampling without replacement over sampling with replacement is
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
  set P := sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))
  set Q := sampleWithReplacement (ι := ι) (Measure.dirac (update id b a))
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  let := isProbabilityMeasure_sampleWithoutReplacement (Measure.dirac (update id b a)) e
  set m := Fintype.card ι
  set n := Fintype.card κ
  set p₀ : ℝ≥0∞ := n.descFactorial m / (n : ℝ≥0∞) ^ m
  set t₀ : ℝ≥0∞ := m.descFactorial 2 / n.descFactorial 2
  set p : ℝ := (n.descFactorial m : ℝ) / (n : ℝ) ^ m
  set t : ℝ := (m.descFactorial 2 : ℝ) / (n.descFactorial 2 : ℝ)
  -- Partition the finite sum of singleton excesses into the two-hit event `{r = 2}` and its
  -- complement.
  have hsing (y : ι → κ) :
      P {y} - Q {y} = (if #{i | y i = a} = 2 then 1 - 2 * p₀ else 1 - p₀) * P {y} :=
    sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_singleton hab y
  have hsum : (⨆ (A : Set (ι → κ)) (_ : MeasurableSet A), P A - Q A) =
      (1 - 2 * p₀) * t₀ + (1 - p₀) * (1 - t₀) := by
    rw [iSup_measure_sub_eq_sum]
    simp_rw [hsing, ite_mul, sum_ite, ← mul_sum, sum_measure_singleton]
    have hH : (↑({y : ι → κ | #{i | y i = a} = 2} : Finset (ι → κ)) : Set (ι → κ)) =
        {y | #{i | y i = a} = 2} := by simp
    have hHc : (↑({y : ι → κ | ¬ #{i | y i = a} = 2} : Finset (ι → κ)) : Set (ι → κ)) =
        {y | #{i | y i = a} = 2}ᶜ := by
      ext y
      simp
    rw [hH, hHc, prob_compl_eq_one_sub .of_discrete,
      sampleWithoutReplacement_dirac_update_id_card_filter_eq_two hab hmn]
  have hn2 : 2 ≤ n := Fintype.one_lt_card_iff.2 ⟨a, b, hab⟩
  have hpow_pos : (0 : ℝ) < (n : ℝ) ^ m := pow_pos (Nat.cast_pos.2 (by omega)) m
  have hdesc2_pos : (0 : ℝ) < (n.descFactorial 2 : ℝ) :=
    Nat.cast_pos.2 (Nat.descFactorial_pos.2 hn2)
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 :=
    div_le_one_of_le₀ (by exact_mod_cast Nat.descFactorial_le_pow n m) hpow_pos.le
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 :=
    div_le_one_of_le₀ (by exact_mod_cast Nat.descFactorial_le 2 hmn) hdesc2_pos.le
  have hp_ofReal : p₀ = ENNReal.ofReal p := by simp [p₀, p, ENNReal.ofReal_div_of_pos hpow_pos]
  have ht_ofReal : t₀ = ENNReal.ofReal t := by
    simp only [t₀, t, ENNReal.ofReal_div_of_pos hdesc2_pos, ENNReal.ofReal_natCast]
  rw [hsum, hp_ofReal, ht_ofReal, one_sub_two_mul_ofReal_mul_add_eq_ofReal hp0 hp1 ht0 ht1]

/-- The converse largest excess of sampling with replacement over sampling without replacement for
the one-pair population `Function.update id b a` equals the same quantity
`1 - p - t * min p (1 - p)`. -/
theorem iSup_sampleWithReplacement_sub_sampleWithoutReplacement_dirac_update_id_eq
    (hab : a ≠ b) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    (⨆ (A : Set (ι → κ)) (_ : MeasurableSet A),
      sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) A -
        sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) A) =
      ENNReal.ofReal
        (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ) ^ Fintype.card ι
         let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
         1 - p - t * min p (1 - p)) := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  let : Nonempty (ι → κ) := ⟨e⟩
  let := isProbabilityMeasure_sampleWithoutReplacement (Measure.dirac (update id b a)) e
  let := isProbabilityMeasure_sampleWithReplacement (ι := ι) (Measure.dirac (update id b a))
  rw [← Measure.toJordanDecomposition_toSignedMeasure_sub_negPart_univ_eq_iSup,
    ← Measure.toJordanDecomposition_toSignedMeasure_sub_posPart_univ_eq_negPart_univ_iff.2
      (by rw [measure_univ, measure_univ]),
    Measure.toJordanDecomposition_toSignedMeasure_sub_posPart_univ_eq_iSup,
    iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq hab hmn]

/-- For the population `Function.update id b a` identifying one distinct pair of indices,
Mathlib's total variation distance between sampling without and with replacement is
`2 * (1 - p - t * min p (1 - p))`. -/
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
  let : Nonempty (ι → κ) := ⟨e⟩
  let := isProbabilityMeasure_sampleWithoutReplacement (Measure.dirac (update id b a)) e
  let := isProbabilityMeasure_sampleWithReplacement (ι := ι) (Measure.dirac (update id b a))
  rw [etvDist_eq_two_mul_iSup_sub (by rw [measure_univ, measure_univ]),
    iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq hab hmn]

end Discrepancy

end Probability

end TauCeti

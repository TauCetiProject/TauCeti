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
one embedding if `r = 0` and by two (namely `f` and `Equiv.swap a b ∘ f`) otherwise. Consequently,
on the support of the without-replacement law `P q`, the likelihood ratio `Q q {y} / P q {y}` is
`p = n_(m) / n^m` when `r ≤ 1` and `2 * p` when `r = 2`, while the two regimes have `P q`-masses
`1 - t` and `t = m_(2) / n_(2)`. Summing singleton excesses over `ι → κ` gives the exact excess
`1 - p - t * min p (1 - p)` whenever `m ≤ n`, and `etvDist` is twice that value.

## Main declarations

* `card_filter_update_id_apply_eq_le_two`, `card_filter_update_id_apply_eq_eq_two_iff`: an
  injective index map meets `{a, b}` at most twice, and twice exactly when it hits both;
* `natCard_update_id_comp_eq_update_id_comp`: the number of index maps with the same word is
  `2 ^ r`;
* `natCard_embedding_update_id_comp_eq_update_id_comp`: the number of embeddings with the same
  word is `1` if `r = 0` and `2` otherwise;
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

/-- On the support of sampling `Function.update id b a` without replacement, the with-replacement
singleton mass is `p` times the without-replacement mass when `a` appears at most once and
`2 * p` times it when `a` appears twice. -/
private theorem sampleWithReplacement_dirac_update_id_singleton_eq_mul (hab : a ≠ b)
    (hmn : Fintype.card ι ≤ Fintype.card κ) (f : ι ↪ κ) :
    sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) {update id b a ∘ f} =
      (let p : ℝ≥0∞ := (Fintype.card κ).descFactorial (Fintype.card ι) /
         (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι
       if #{i | update id b a (f i) = a} = 2 then 2 * p else p) *
        sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))
          {update id b a ∘ f} := by
  set p : ℝ≥0∞ := (Fintype.card κ).descFactorial (Fintype.card ι) /
    (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι
  have hd0 : ((Fintype.card κ).descFactorial (Fintype.card ι) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.2 hmn).ne'
  rw [sampleWithoutReplacement_dirac_singleton, sampleWithReplacement_dirac_singleton,
    natCard_embedding_update_id_comp_eq_update_id_comp hab f,
    natCard_update_id_comp_eq_update_id_comp hab f]
  have hcancel (c : ℝ≥0∞) :
      p * (c / ((Fintype.card κ).descFactorial (Fintype.card ι) : ℝ≥0∞)) =
        c / (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι := by
    calc
      p * (c / ((Fintype.card κ).descFactorial (Fintype.card ι) : ℝ≥0∞))
          = ((Fintype.card κ).descFactorial (Fintype.card ι) : ℝ≥0∞) *
              ((Fintype.card κ).descFactorial (Fintype.card ι) : ℝ≥0∞)⁻¹ *
              (c * ((Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι)⁻¹) := by
        simp only [p, div_eq_mul_inv]; ac_rfl
      _ = c / (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι := by
        rw [ENNReal.mul_inv_cancel hd0 (ENNReal.natCast_ne_top _), one_mul, div_eq_mul_inv]
  have hr : #{i | update id b a (f i) = a} ≤ 2 := card_filter_update_id_apply_eq_le_two f.injective
  set r : ℕ := #{i | update id b a (f i) = a}
  interval_cases r
  · simpa using (hcancel 1).symm
  · simpa using (hcancel 2).symm
  · simp only [↓reduceIte, OfNat.ofNat_ne_zero]
    rw [mul_assoc, hcancel, ← mul_div_assoc]
    norm_num

/-- On each word `y : ι → κ`, the truncated singleton excess of sampling `Function.update id b a`
without replacement over sampling with replacement scales the without-replacement singleton mass
by `1 - 2 * p` when `a` appears twice in `y`, and by `1 - p` otherwise. -/
private theorem sampleWithoutReplacement_dirac_update_id_singleton_sub (hab : a ≠ b)
    (hmn : Fintype.card ι ≤ Fintype.card κ) (y : ι → κ) :
    sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {y} -
        sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) {y} =
      (let p : ℝ≥0∞ := (Fintype.card κ).descFactorial (Fintype.card ι) /
         (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι
       if #{i | y i = a} = 2 then 1 - 2 * p else 1 - p) *
        sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {y} := by
  by_cases hy : ∃ f : ι ↪ κ, update id b a ∘ f = y
  · obtain ⟨f, rfl⟩ := hy
    rw [sampleWithReplacement_dirac_update_id_singleton_eq_mul hab hmn f]
    dsimp only [Function.comp_apply]
    set p : ℝ≥0∞ := (Fintype.card κ).descFactorial (Fintype.card ι) /
      (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι
    set c : ℝ≥0∞ := if #{i | update id b a (f i) = a} = 2 then 2 * p else p
    have hsub : (1 - c) *
          sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))
            {update id b a ∘ f} =
        sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {update id b a ∘ f} -
          c * sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))
            {update id b a ∘ f} := by
      rw [ENNReal.sub_mul fun _ _ => measure_ne_top _ _, one_mul]
    rw [← hsub]
    congr 1
    dsimp only [c]
    split_ifs <;> rfl
  · have : IsEmpty {f : ι ↪ κ // update id b a ∘ f = y} := ⟨fun f => hy ⟨f.1, f.2⟩⟩
    have hP0 : sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {y} = 0 := by
      rw [sampleWithoutReplacement_dirac_singleton, Nat.card_eq_fintype_card, Fintype.card_eq_zero]
      simp
    rw [hP0, zero_tsub, mul_zero]

/-- Splitting the singleton-excess sum of `Function.update id b a` by whether `a` occurs twice
expresses the largest excess in `ℝ≥0∞` as `(1 - 2 * p) * t + (1 - p) * (1 - t)`. -/
private theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq_ennreal
    (hab : a ≠ b) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    let p : ℝ≥0∞ := (Fintype.card κ).descFactorial (Fintype.card ι) /
      (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι
    let t : ℝ≥0∞ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
    (⨆ (A : Set (ι → κ)) (_ : MeasurableSet A),
        sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) A -
          sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) A) =
      (1 - 2 * p) * t + (1 - p) * (1 - t) := by
  classical
  let P := sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))
  let Q := sampleWithReplacement (ι := ι) (Measure.dirac (update id b a))
  let p : ℝ≥0∞ := (Fintype.card κ).descFactorial (Fintype.card ι) /
    (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι
  let t : ℝ≥0∞ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  let _ : IsProbabilityMeasure P :=
    isProbabilityMeasure_sampleWithoutReplacement (Measure.dirac (update id b a)) e
  have hE2 : P {y | #{i | y i = a} = 2} = t :=
    sampleWithoutReplacement_dirac_update_id_card_filter_eq_two hab hmn
  have hE2c : P {y | #{i | y i = a} = 2}ᶜ = 1 - t := by
    rw [prob_compl_eq_one_sub (Set.toFinite _).measurableSet, hE2]
  rw [iSup_measure_sub_eq_sum_singleton,
    ← sum_filter_add_sum_filter_not univ (fun y : ι → κ => #{i | y i = a} = 2)]
  congr 1
  · have hterm : ∀ y ∈ univ.filter (fun y : ι → κ => #{i | y i = a} = 2),
        P {y} - Q {y} = (1 - 2 * p) * P {y} := fun y hy => by
      rw [sampleWithoutReplacement_dirac_update_id_singleton_sub hab hmn y]
      simp only [(mem_filter.1 hy).2, ↓reduceIte, P, p]
    rw [sum_congr rfl hterm, ← mul_sum, sum_measure_singleton]
    simpa only [coe_filter, mem_univ, true_and] using congrArg ((1 - 2 * p) * ·) hE2
  · have hterm : ∀ y ∈ univ.filter (fun y : ι → κ => ¬ #{i | y i = a} = 2),
        P {y} - Q {y} = (1 - p) * P {y} := fun y hy => by
      rw [sampleWithoutReplacement_dirac_update_id_singleton_sub hab hmn y]
      simp only [(mem_filter.1 hy).2, ↓reduceIte, P, p]
    rw [sum_congr rfl hterm, ← mul_sum, sum_measure_singleton]
    simpa only [coe_filter, mem_univ, true_and, Set.compl_def, Set.mem_ofPred_eq] using
      congrArg ((1 - p) * ·) hE2c

/-- **Exact discrepancy for the one-pair population (excess form).** For distinct indices `a b : κ`
and `|ι| ≤ |κ|`, the largest eventwise excess of sampling `Function.update id b a` without
replacement over sampling with replacement is `1 - p - t * min p (1 - p)`, where
`p = n_(m) / n^m` and `t = m_(2) / n_(2)`. -/
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
  let m := Fintype.card ι
  let n := Fintype.card κ
  let p : ℝ := n.descFactorial m / (n : ℝ) ^ m
  let t : ℝ := m.descFactorial 2 / n.descFactorial 2
  have hκ2 : 2 ≤ n := Fintype.one_lt_card_iff.2 ⟨a, b, hab⟩
  have hn_pos : (0 : ℝ) < n := by positivity
  have hpow_pos : (0 : ℝ) < (n : ℝ) ^ m := by positivity
  have hn2_pos : (0 : ℝ) < n.descFactorial 2 := by
    exact_mod_cast Nat.descFactorial_pos.2 hκ2
  have hp_eq : (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m = ENNReal.ofReal p := by
    simp only [p, ENNReal.ofReal_div_of_pos hpow_pos, ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow hn_pos.le]
  have ht_eq : (m.descFactorial 2 : ℝ≥0∞) / (n.descFactorial 2 : ℝ≥0∞) = ENNReal.ofReal t := by
    simp only [t, ENNReal.ofReal_div_of_pos hn2_pos, ENNReal.ofReal_natCast]
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := (div_le_one hpow_pos).2 (by exact_mod_cast Nat.descFactorial_le_pow n m)
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := (div_le_one hn2_pos).2 (by exact_mod_cast Nat.descFactorial_le 2 hmn)
  have hp_sub : 1 - ENNReal.ofReal p = ENNReal.ofReal (1 - p) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hp0]
  have ht_sub : 1 - ENNReal.ofReal t = ENNReal.ofReal (1 - t) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 ht0]
  have h2p : 1 - 2 * ENNReal.ofReal p = ENNReal.ofReal (1 - 2 * p) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by positivity)]
  have halg : (1 - 2 * ENNReal.ofReal p) * ENNReal.ofReal t +
      (1 - ENNReal.ofReal p) * (1 - ENNReal.ofReal t) =
      ENNReal.ofReal (1 - p - t * min p (1 - p)) := by
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
  rw [iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq_ennreal hab hmn,
    hp_eq, ht_eq]
  exact halg

/-- **Exact discrepancy for the one-pair population (`etvDist` form).** For distinct indices
`a b : κ` and `|ι| ≤ |κ|`, Mathlib's total variation distance between sampling
`Function.update id b a` without and with replacement is `2 * (1 - p - t * min p (1 - p))`. -/
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
  let _ : Nonempty (ι → κ) := ⟨e⟩
  let _ := isProbabilityMeasure_sampleWithoutReplacement (Measure.dirac (update id b a)) e
  let _ := isProbabilityMeasure_sampleWithReplacement (ι := ι) (Measure.dirac (update id b a))
  rw [etvDist_eq_two_mul_iSup_sub (by rw [measure_univ, measure_univ]),
    iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq hab hmn]

end Discrepancy

end Probability

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PopulationSampling.Finite
public import TauCeti.MeasureTheory.Measure.TotalVariation.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Preimage
import TauCeti.Logic.Function.Update
import TauCeti.MeasureTheory.Measure.TotalVariation.Countable

/-!
# The one-pair population: fibres and exact sampling discrepancy

For distinct indices `a b : κ`, the *one-pair population* `Function.update id b a : κ → κ` sends
`b` to `a` and fixes every other index; it is the population with exactly one repeated value.
Sampling it along an index map `f : ι → κ` gives the word `Function.update id b a ∘ f`. This file
counts the index maps and embeddings producing a given word, and uses those counts to compute the
exact discrepancy between sampling the one-pair population without replacement and with
replacement.

Write `r` for the number of `i` with `Function.update id b a (f i) = a`, that is with
`f i ∈ {a, b}`. For an injective `f`, `r ≤ 2`, and `r = 2` exactly when `a` and `b` both lie in the
range of `f`. The word of `f` is produced by `2 ^ r` index maps, and, when `f` is an embedding, by
one embedding if `r = 0` and by two (namely `f` and `Equiv.swap a b ∘ f`) otherwise.

Consequently, on the support of the without-replacement sampling law `P`, the likelihood ratio
`Q {y} / P {y}` against the with-replacement law `Q` equals `p = |κ|.descFactorial |ι| / |κ| ^ |ι|`
when `#{i | y i = a} ≤ 1` and `2 * p` when `#{i | y i = a} = 2`. When `|ι| ≤ |κ|`, the two-hit
part of the support has `P`-mass `t = |ι|.descFactorial 2 / |κ|.descFactorial 2` and its complement
has `P`-mass `1 - t`, so summing `P {y} - Q {y}` over all words gives the exact largest excess
`ENNReal.ofReal (1 - p - t * min p (1 - p))`, and twice that for `etvDist`.

## Main declarations

* `card_filter_update_id_apply_eq_le_two`, `card_filter_update_id_apply_eq_eq_two_iff`: an
  injective index map meets `{a, b}` at most twice, and twice exactly when it hits both;
* `natCard_update_id_comp_eq_update_id_comp`: the number of index maps with the same word is
  `2 ^ r`;
* `natCard_embedding_update_id_comp_eq_update_id_comp`: the number of embeddings with the same
  word is `1` if `r = 0` and `2` otherwise;
* `sampleWithoutReplacement_dirac_update_id_card_filter_eq_two`: a word sampled without replacement
  from `Function.update id b a` takes the value `a` twice with probability `t`;
* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq`,
  `etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_update_id_eq`,
  `tvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_update_id_eq`: exact largest
  eventwise excess and extended and real total variation distances between without-replacement and
  with-replacement sampling of `Function.update id b a`.

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

/-- Rewrites the weighted `ℝ≥0∞` sum over the two-hit and at-most-one-hit parts of the support into
`ENNReal.ofReal (1 - p - t * min p (1 - p))`, handling the truncation of `1 - 2 * p` when
`1 / 2 ≤ p`. -/
private theorem ennreal_one_pair_formula {p t : ℝ} (hp₀ : 0 ≤ p) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    ENNReal.ofReal t * (1 - 2 * ENNReal.ofReal p) +
        (1 - ENNReal.ofReal t) * (1 - ENNReal.ofReal p) =
      ENNReal.ofReal (1 - p - t * min p (1 - p)) := by
  have h1t : (1 : ℝ≥0∞) - ENNReal.ofReal t = ENNReal.ofReal (1 - t) := by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_sub 1 ht₀]
  have h1p : (1 : ℝ≥0∞) - ENNReal.ofReal p = ENNReal.ofReal (1 - p) := by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_sub 1 hp₀]
  have h2p : 2 * ENNReal.ofReal p = ENNReal.ofReal (2 * p) := by
    rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
  rw [h1t, h1p, h2p]
  rcases le_total p (1 - p) with hp | hp
  · have h12p : (1 : ℝ≥0∞) - ENNReal.ofReal (2 * p) = ENNReal.ofReal (1 - 2 * p) := by
      rw [← ENNReal.ofReal_one, ENNReal.ofReal_sub 1 (by linarith)]
    rw [h12p, ← ENNReal.ofReal_mul ht₀, ← ENNReal.ofReal_mul (sub_nonneg.2 ht₁),
      ← ENNReal.ofReal_add (mul_nonneg ht₀ (by linarith))
        (mul_nonneg (sub_nonneg.2 ht₁) (by linarith)), min_eq_left hp]
    congr 1
    ring
  · have hzero : (1 : ℝ≥0∞) - ENNReal.ofReal (2 * p) = 0 :=
      tsub_eq_zero_of_le <| by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by linarith)
    rw [hzero, mul_zero, zero_add, ← ENNReal.ofReal_mul (sub_nonneg.2 ht₁), min_eq_right hp]
    congr 1
    ring

section Discrepancy

variable [Fintype ι] [Fintype κ] [DecidableEq κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- Under without-replacement sampling of the one-pair population `Function.update id b a`, the
sampled word takes the value `a` exactly twice with probability
`(|ι|).descFactorial 2 / (|κ|).descFactorial 2`. -/
theorem sampleWithoutReplacement_dirac_update_id_card_filter_eq_two (hab : a ≠ b)
    (hmn : Fintype.card ι ≤ Fintype.card κ) :
    sampleWithoutReplacement (Measure.dirac (update id b a))
        {y : ι → κ | #{i | y i = a} = 2} =
      (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2 := by
  rw [sampleWithoutReplacement_dirac,
    Measure.map_apply (measurable_readPopulation _) (Set.toFinite _).measurableSet,
    ← uniformOn_inter_self (Set.toFinite {k : ι → κ | Injective k})]
  have heq : {k : ι → κ | Injective k} ∩
        ((fun k i => update id b a (k i)) ⁻¹' {y : ι → κ | #{i | y i = a} = 2}) =
      {k : ι → κ | Injective k} ∩ {k : ι → κ | a ∈ Set.range k ∧ b ∈ Set.range k} := by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    exact and_congr_right fun hk => card_filter_update_id_apply_eq_eq_two_iff hk hab
  rw [heq, uniformOn_inter_self (Set.toFinite _),
    uniformOn_injective_mem_range_and_mem_range hab hmn]

/-- Pointwise singleton excess of without-replacement over with-replacement sampling for
`Function.update id b a`: on the support of `P`, `Q {y}` is `P {y} * p` when `y` hits `a` at most
once and `P {y} * (2 * p)` when `y` hits `a` twice; outside the support both sides vanish. -/
private theorem sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_singleton
    (y : ι → κ) :
    sampleWithoutReplacement (Measure.dirac (update id b a)) {y} -
        sampleWithReplacement (Measure.dirac (update id b a)) {y} =
      sampleWithoutReplacement (Measure.dirac (update id b a)) {y} *
        (if #{i | y i = a} = 2 then
          1 - 2 * ((Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι)
        else
          1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) := by
  rcases isEmpty_or_nonempty {f : ι ↪ κ // update id b a ∘ f = y} with hemp | ⟨⟨f, rfl⟩⟩
  · have hP : sampleWithoutReplacement (Measure.dirac (update id b a)) {y} = 0 := by
      rw [sampleWithoutReplacement_dirac_apply_singleton]
      simp
    rw [hP, zero_tsub, zero_mul]
  · let d : ℝ≥0∞ := ((Fintype.card κ).descFactorial (Fintype.card ι) : ℝ≥0∞)
    let N : ℝ≥0∞ := (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι
    have hd₀ : d ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.descFactorial_pos.2 (Fintype.card_le_of_embedding f)).ne'
    have hd_top : d ≠ ∞ := ENNReal.natCast_ne_top _
    have hcancel (c : ℝ≥0∞) : c / d * (d / N) = c / N := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ← mul_assoc d⁻¹,
        ENNReal.inv_mul_cancel hd₀ hd_top, one_mul, ← div_eq_mul_inv]
    have hPne : sampleWithoutReplacement (Measure.dirac (update id b a))
        {update id b a ∘ f} ≠ ∞ := measure_ne_top _ _
    have hQ : sampleWithReplacement (Measure.dirac (update id b a)) {update id b a ∘ f} =
        sampleWithoutReplacement (Measure.dirac (update id b a)) {update id b a ∘ f} *
          (if #{i | (update id b a ∘ f) i = a} = 2 then 2 * (d / N) else d / N) := by
      rw [sampleWithReplacement_dirac_apply_singleton,
        sampleWithoutReplacement_dirac_apply_singleton]
      rcases eq_or_ne a b with rfl | hab
      · have hid : update id a a = id := update_eq_self a id
        have hle : #{i | f i = a} ≤ 1 := card_le_one.2 fun i hi j hj =>
          f.injective ((mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm)
        have hne2 : #{i | f i = a} ≠ 2 := by omega
        simp only [hid, Function.comp_apply, id_eq, hne2, ↓reduceIte]
        simp_rw [id_comp, DFunLike.coe_fn_eq, Nat.card_unique, Nat.cast_one]
        simpa only [d, N] using (hcancel 1).symm
      · have hr := card_filter_update_id_apply_eq_le_two f.injective (a := a) (b := b)
        rw [natCard_update_id_comp_eq_update_id_comp hab f,
          natCard_embedding_update_id_comp_eq_update_id_comp hab f]
        simp only [Function.comp_apply] at hr ⊢
        interval_cases #{i | update id b a (f i) = a}
        · norm_num
          simpa only [one_div, d, N] using (hcancel 1).symm
        · norm_num
          exact (hcancel 2).symm
        · simp only [↓reduceIte, OfNat.ofNat_ne_zero, Nat.cast_ofNat, pow_two]
          rw [← mul_assoc, mul_comm (_ / d) 2, mul_assoc, hcancel 2, ← mul_div_assoc]
          norm_num [N]
    rw [hQ]
    split_ifs <;> rw [ENNReal.mul_sub (fun _ _ => hPne), mul_one]

/-- For distinct `a b : κ` and `|ι| ≤ |κ|`, the largest excess of sampling the one-pair population
`Function.update id b a` without replacement over sampling it with replacement is
`1 - p - t * min p (1 - p)`, where `p = |κ|.descFactorial |ι| / |κ| ^ |ι|` and
`t = |ι|.descFactorial 2 / |κ|.descFactorial 2`. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq
    (hab : a ≠ b) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    (⨆ (A : Set (ι → κ)) (_ : MeasurableSet A),
        sampleWithoutReplacement (Measure.dirac (update id b a)) A -
          sampleWithReplacement (Measure.dirac (update id b a)) A) =
      ENNReal.ofReal
        (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ) ^ Fintype.card ι
         let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
         1 - p - t * min p (1 - p)) := by
  classical
  let μ : Measure (ι → κ) := sampleWithoutReplacement (Measure.dirac (update id b a))
  let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
    (Fintype.card κ : ℝ) ^ Fintype.card ι
  let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  let _ : IsProbabilityMeasure μ := isProbabilityMeasure_sampleWithoutReplacement _ e
  have hκ : 2 ≤ Fintype.card κ := Fintype.one_lt_card_iff.2 ⟨a, b, hab⟩
  have hp_enn : ENNReal.ofReal p =
      (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι := by
    have hpos : (0 : ℝ) < (Fintype.card κ : ℝ) ^ Fintype.card ι :=
      pow_pos (Nat.cast_pos.2 (by omega)) _
    rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have ht_enn : ENNReal.ofReal t =
      (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2 := by
    have hpos : (0 : ℝ) < (Fintype.card κ).descFactorial 2 :=
      Nat.cast_pos.2 (Nat.descFactorial_pos.2 hκ)
    rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  have ht₁ : t ≤ 1 := div_le_one_of_le₀
    (by exact_mod_cast Nat.descFactorial_le 2 hmn) (by positivity)
  rw [iSup_measure_sub_eq_sum_singleton]
  simp_rw [sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_singleton (a := a)
    (b := b), ← hp_enn]
  rw [← sum_filter_add_sum_filter_not univ (fun y : ι → κ => #{i | y i = a} = 2)]
  have hE₁ : ∑ y ∈ univ.filter (fun y : ι → κ => #{i | y i = a} = 2), μ {y} *
        (if #{i | y i = a} = 2 then 1 - 2 * ENNReal.ofReal p else 1 - ENNReal.ofReal p) =
      ENNReal.ofReal t * (1 - 2 * ENNReal.ofReal p) := by
    rw [sum_congr rfl fun y hy => by rw [ite_eq_left (mem_filter.1 hy).2], ← sum_mul,
      sum_measure_singleton, coe_filter_univ,
      sampleWithoutReplacement_dirac_update_id_card_filter_eq_two hab hmn, ht_enn]
  have hE₂ : ∑ y ∈ univ.filter (fun y : ι → κ => ¬#{i | y i = a} = 2), μ {y} *
        (if #{i | y i = a} = 2 then 1 - 2 * ENNReal.ofReal p else 1 - ENNReal.ofReal p) =
      (1 - ENNReal.ofReal t) * (1 - ENNReal.ofReal p) := by
    rw [sum_congr rfl fun y hy => by rw [ite_eq_right (mem_filter.1 hy).2], ← sum_mul,
      sum_measure_singleton, coe_filter_univ, ← Set.compl_ofPred,
      prob_compl_eq_one_sub (Set.toFinite _).measurableSet,
      sampleWithoutReplacement_dirac_update_id_card_filter_eq_two hab hmn, ht_enn]
  rw [hE₁, hE₂, ennreal_one_pair_formula (by positivity) (by positivity) ht₁]

/-- For distinct `a b : κ` and `|ι| ≤ |κ|`, the extended total variation distance between sampling
the one-pair population `Function.update id b a` without replacement and with replacement is
`2 * ENNReal.ofReal (1 - p - t * min p (1 - p))`. -/
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

/-- For distinct `a b : κ` and `|ι| ≤ |κ|`, the real-valued total variation distance between
sampling the one-pair population `Function.update id b a` without replacement and with replacement
is `2 * (1 - p - t * min p (1 - p))`. -/
theorem tvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_update_id_eq
    (hab : a ≠ b) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    tvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)))
        (sampleWithReplacement (ι := ι) (Measure.dirac (update id b a))) =
      2 *
        (let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ) ^ Fintype.card ι
         let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
         1 - p - t * min p (1 - p)) := by
  let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
    (Fintype.card κ : ℝ) ^ Fintype.card ι
  let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
  have hp₁ : p ≤ 1 := div_le_one_of_le₀
    (by exact_mod_cast Nat.descFactorial_le_pow (Fintype.card κ) (Fintype.card ι)) (by positivity)
  have ht₁ : t ≤ 1 := div_le_one_of_le₀
    (by exact_mod_cast Nat.descFactorial_le 2 hmn) (by positivity)
  have hnonneg : 0 ≤ 1 - p - t * min p (1 - p) := by
    have hmul : t * min p (1 - p) ≤ 1 * (1 - p) :=
      mul_le_mul ht₁ (min_le_right _ _) (le_min (by positivity) (sub_nonneg.2 hp₁)) zero_le_one
    linarith
  rw [tvDist, etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_update_id_eq hab hmn,
    ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hnonneg]

end Discrepancy

end Probability

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PopulationSampling.Finite
public import TauCeti.MeasureTheory.Measure.TotalVariation.Basic
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Set.Card
import TauCeti.Logic.Function.Update
import TauCeti.MeasureTheory.Measure.TotalVariation.Countable

/-!
# The one-pair population: fibres and exact sampling discrepancy

For distinct indices `a b : κ`, the *one-pair population* `Function.update id b a : κ → κ` sends
`b` to `a` and fixes every other index; it is the population with exactly one repeated value.
Sampling it along an index map `f : ι → κ` gives the word `Function.update id b a ∘ f`. This file
counts the index maps and embeddings producing a given word, and uses those counts to compute the
exact discrepancy between sampling the one-pair population without and with replacement.

Write `r` for the number of `i` with `Function.update id b a (f i) = a`, that is with
`f i ∈ {a, b}`. For an injective `f`, `r ≤ 2`, and `r = 2` exactly when `a` and `b` both lie in the
range of `f`. The word of `f` is produced by `2 ^ r` index maps, and, when `f` is an embedding, by
one embedding if `r = 0` and by two (namely `f` and `Equiv.swap a b ∘ f`) otherwise.

Consequently, when `m = |ι| ≤ |κ| = n`, on the support of the without-replacement law `P` the
with-replacement/without-replacement singleton ratio is `p = n.descFactorial m / n ^ m` where
`r ≤ 1` and `2 * p` where `r = 2`, while the two parts of the support have `P`-masses `1 - t` and
`t = m.descFactorial 2 / n.descFactorial 2`. Summing the positive singleton differences gives the
exact largest event excess `1 - p - t * min p (1 - p)`, and twice that value for Mathlib's total
variation distance.

## Main declarations

* `card_filter_update_id_apply_eq_le_two`, `card_filter_update_id_apply_eq_eq_two_iff`: an
  injective index map meets `{a, b}` at most twice, and twice exactly when it hits both;
* `natCard_update_id_comp_eq_update_id_comp`: the number of index maps with the same word is
  `2 ^ r`;
* `natCard_embedding_update_id_comp_eq_update_id_comp`: the number of embeddings with the same
  word is `1` if `r = 0` and `2` otherwise;
* `one_sub_descFactorial_div_pow_sub_mul_min_nonneg`: the error `1 - p - t * min p (1 - p)` is
  nonnegative for every sample and population size;
* `descFactorial_div_mul_min_pos`: for `2 ≤ m ≤ n` the correction `t * min p (1 - p)` is
  positive;
* `sampleWithoutReplacement_dirac_update_id_apply_setOf_card_filter_eq_two`: under
  without-replacement sampling of the one-pair population, the probability of seeing `a` twice
  is `t`;
* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq`: the exact largest
  event excess `1 - p - t * min p (1 - p)`;
* `etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_update_id_eq`,
  `tvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_update_id_eq`: the extended and
  real total variation distances, equal to twice that excess.

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

/-- The with-replacement/without-replacement singleton ratio `n.descFactorial m / n ^ m` for
sample size `m` and population size `n`. -/
private def onePairP (m n : ℕ) : ℝ :=
  n.descFactorial m / (n : ℝ) ^ m

/-- The without-replacement probability `m.descFactorial 2 / n.descFactorial 2` of drawing both
elements of a fixed pair in a sample of size `m` from a population of size `n`. -/
private def onePairT (m n : ℕ) : ℝ :=
  m.descFactorial 2 / n.descFactorial 2

private theorem onePairP_nonneg (m n : ℕ) : 0 ≤ onePairP m n := by
  unfold onePairP
  positivity

private theorem onePairT_nonneg (m n : ℕ) : 0 ≤ onePairT m n := by
  unfold onePairT
  positivity

private theorem onePairP_le_one (m n : ℕ) : onePairP m n ≤ 1 := by
  unfold onePairP
  exact descFactorial_div_pow_le_one m n

private theorem onePairT_le_one {m n : ℕ} (hmn : m ≤ n) : onePairT m n ≤ 1 :=
  div_le_one_of_le₀ (by exact_mod_cast Nat.descFactorial_le 2 hmn) (by positivity)

/-- Algebraic rearrangement uniting the two-hit and at-most-one-hit contributions to the one-pair
excess into `1 - p - t * min p (1 - p)`. -/
private theorem max_one_sub_two_mul_mul_add_eq (p t : ℝ) :
    max (1 - 2 * p) 0 * t + (1 - p) * (1 - t) = 1 - p - t * min p (1 - p) := by
  rcases le_total p (1 - p) with hp | hp
  · rw [max_eq_left (by linarith), min_eq_left hp]
    ring
  · rw [max_eq_right (by linarith), min_eq_right hp]
    ring

/-- `ENNReal.ofReal` form of `max_one_sub_two_mul_mul_add_eq` for `p, t ≤ 1` with `0 ≤ t`. -/
private theorem ofReal_one_sub_two_mul_mul_add_eq {p t : ℝ} (hp1 : p ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    ENNReal.ofReal (1 - 2 * p) * ENNReal.ofReal t +
        ENNReal.ofReal (1 - p) * ENNReal.ofReal (1 - t) =
      ENNReal.ofReal (1 - p - t * min p (1 - p)) := by
  have hmax : ENNReal.ofReal (1 - 2 * p) = ENNReal.ofReal (max (1 - 2 * p) 0) := by
    rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, _root_.max_zero]
  rw [hmax, ← ENNReal.ofReal_mul (le_max_right _ _), ← ENNReal.ofReal_mul (sub_nonneg.2 hp1),
    ← ENNReal.ofReal_add (mul_nonneg (le_max_right _ _) ht0)
      (mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 ht1)),
    max_one_sub_two_mul_mul_add_eq]

/-- The sampling-discrepancy error `1 - p - t * min p (1 - p)`, where
`p = n.descFactorial m / n ^ m` and `t = m.descFactorial 2 / n.descFactorial 2`, is nonnegative
for every sample size `m` and population size `n`: for `m ≤ n` both `p` and `t` lie in `[0, 1]`,
and for `n < m` it equals `1`. -/
theorem one_sub_descFactorial_div_pow_sub_mul_min_nonneg (m n : ℕ) :
    0 ≤ 1 - (n.descFactorial m / (n : ℝ) ^ m) -
      (m.descFactorial 2 / n.descFactorial 2 : ℝ) *
        min (n.descFactorial m / (n : ℝ) ^ m) (1 - n.descFactorial m / (n : ℝ) ^ m) := by
  rcases le_or_gt m n with hmn | hnm
  · rw [← onePairP, ← onePairT, ← max_one_sub_two_mul_mul_add_eq]
    exact add_nonneg (mul_nonneg (le_max_right _ _) (onePairT_nonneg m n))
      (mul_nonneg (sub_nonneg.2 (onePairP_le_one m n))
        (sub_nonneg.2 (onePairT_le_one hmn)))
  · simp [Nat.descFactorial_eq_zero_iff_lt.2 hnm]

/-- For `2 ≤ m ≤ n`, the correction `t * min p (1 - p)`, where
`p = n.descFactorial m / n ^ m` and `t = m.descFactorial 2 / n.descFactorial 2`, is positive, so
the sampling-discrepancy error `1 - p - t * min p (1 - p)` is strictly below `1 - p`. -/
theorem descFactorial_div_mul_min_pos {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    0 < (m.descFactorial 2 / n.descFactorial 2 : ℝ) *
      min (n.descFactorial m / (n : ℝ) ^ m) (1 - n.descFactorial m / (n : ℝ) ^ m) := by
  have hn : 0 < n := by omega
  have hpow : (0 : ℝ) < (n : ℝ) ^ m := by positivity
  have hd : (0 : ℝ) < n.descFactorial m := by exact_mod_cast Nat.descFactorial_pos.2 hmn
  have hp1 : (n.descFactorial m / (n : ℝ) ^ m) < 1 :=
    (div_lt_one hpow).2 (by exact_mod_cast Nat.descFactorial_lt_pow hn.ne' hm)
  have ht : (0 : ℝ) < m.descFactorial 2 / n.descFactorial 2 :=
    div_pos (by exact_mod_cast Nat.descFactorial_pos.2 hm)
      (by exact_mod_cast Nat.descFactorial_pos.2 (hm.trans hmn))
  exact mul_pos ht (lt_min (div_pos hd hpow) (sub_pos.2 hp1))

variable [Fintype ι] [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] [DecidableEq κ]

/-- Under without-replacement sampling of the one-pair population `Function.update id b a` with
`a ≠ b` and `|ι| ≤ |κ|`, the event of sampling `a` twice has probability
`|ι|.descFactorial 2 / |κ|.descFactorial 2`. -/
theorem sampleWithoutReplacement_dirac_update_id_apply_setOf_card_filter_eq_two
    (hab : a ≠ b) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))
      {y : ι → κ | #{i | y i = a} = 2} =
      (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2 := by
  have hinter : {k : ι → κ | Injective k} ∩
      ((fun k i => update id b a (k i)) ⁻¹' {y : ι → κ | #{i | y i = a} = 2}) =
      {k : ι → κ | Injective k} ∩ {k | a ∈ Set.range k ∧ b ∈ Set.range k} := by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    exact and_congr_right fun hk => card_filter_update_id_apply_eq_eq_two_iff hk hab
  rw [sampleWithoutReplacement_dirac,
    Measure.map_apply (measurable_readPopulation _) .of_discrete,
    ← uniformOn_inter_self (Set.toFinite _), hinter, uniformOn_inter_self (Set.toFinite _),
    uniformOn_injective_mem_range_and_mem_range hab hmn]

/-- For an embedding `f : ι ↪ κ`, the with-replacement singleton mass of the word
`Function.update id b a ∘ f` is `ENNReal.ofReal (2 * p)` times its without-replacement singleton
mass when `f` hits `{a, b}` twice, and `ENNReal.ofReal p` times its without-replacement singleton
mass otherwise, where `p = onePairP |ι| |κ|`. -/
private theorem sampleWithReplacement_dirac_update_id_singleton_eq_mul
    (hab : a ≠ b) (f : ι ↪ κ) :
    sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) {update id b a ∘ f} =
      ENNReal.ofReal (if #{i | update id b a (f i) = a} = 2 then
          2 * onePairP (Fintype.card ι) (Fintype.card κ)
        else onePairP (Fintype.card ι) (Fintype.card κ)) *
        sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {update id b a ∘ f} := by
  have hd_ne : ((Fintype.card κ).descFactorial (Fintype.card ι) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.descFactorial_pos.2 (Fintype.card_le_of_embedding f)).ne'
  have hpow_ne : (Fintype.card κ : ℝ) ^ Fintype.card ι ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨a⟩).ne')
  have hp_nonneg : 0 ≤ onePairP (Fintype.card ι) (Fintype.card κ) := onePairP_nonneg _ _
  let _ := isProbabilityMeasure_sampleWithoutReplacement (Measure.dirac (update id b a)) f
  -- Compare both finite singleton masses through `ENNReal.toReal`.
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    sampleWithReplacement_dirac_apply_singleton, natCard_update_id_comp_eq_update_id_comp hab f,
    sampleWithoutReplacement_dirac_apply_singleton,
    natCard_embedding_update_id_comp_eq_update_id_comp hab f,
    ENNReal.toReal_ofReal_mul _ _ (by split_ifs <;> positivity)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  set r := #{i : ι | update id b a (f i) = a}
  have hr : r ≤ 2 := card_filter_update_id_apply_eq_le_two f.injective
  have hpow2 : ((2 ^ r : ℕ) : ℝ) =
      (if r = 2 then 2 else 1) * ((if r = 0 then 1 else 2 : ℕ) : ℝ) := by
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with h | h | h <;> norm_num [h]
  rw [hpow2, onePairP]
  by_cases hr2 : r = 2 <;>
    · simp only [hr2, ↓reduceIte]
      field_simp [hd_ne, hpow_ne]

/-- For every word `y : ι → κ`, the truncated singleton excess of without-replacement over
with-replacement sampling from `Function.update id b a` is `ENNReal.ofReal (1 - 2 * p)` times its
without-replacement mass when `y` takes `a` twice, and `ENNReal.ofReal (1 - p)` times its
without-replacement mass otherwise, where `p = onePairP |ι| |κ|`. Words outside the
without-replacement support satisfy both sides as `0`. -/
private theorem sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_singleton
    (hab : a ≠ b) (y : ι → κ) :
    sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {y} -
      sampleWithReplacement (ι := ι) (Measure.dirac (update id b a)) {y} =
      (if #{i | y i = a} = 2 then
          ENNReal.ofReal (1 - 2 * onePairP (Fintype.card ι) (Fintype.card κ))
       else ENNReal.ofReal (1 - onePairP (Fintype.card ι) (Fintype.card κ))) *
        sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)) {y} := by
  set P := sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))
  set Q := sampleWithReplacement (ι := ι) (Measure.dirac (update id b a))
  set p := onePairP (Fintype.card ι) (Fintype.card κ)
  by_cases hPy : P {y} = 0
  · simp [hPy]
  -- A word of positive without-replacement mass is realized by some embedding `f : ι ↪ κ`.
  have hcard_ne : Nat.card {f : ι ↪ κ // update id b a ∘ f = y} ≠ 0 := by
    intro h0
    apply hPy
    rw [sampleWithoutReplacement_dirac_apply_singleton, h0]
    simp
  obtain ⟨⟨⟨f, rfl⟩⟩, -⟩ := Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hcard_ne)
  have hp_nonneg : 0 ≤ p := onePairP_nonneg _ _
  let _ := isProbabilityMeasure_sampleWithoutReplacement (Measure.dirac (update id b a)) f
  simp only [Function.comp_apply]
  calc
    P {update id b a ∘ f} - Q {update id b a ∘ f}
        = 1 * P {update id b a ∘ f} -
            ENNReal.ofReal (if #{i | update id b a (f i) = a} = 2 then 2 * p else p) *
              P {update id b a ∘ f} := by
      rw [one_mul, sampleWithReplacement_dirac_update_id_singleton_eq_mul hab f]
    _ = (1 - ENNReal.ofReal (if #{i | update id b a (f i) = a} = 2 then 2 * p else p)) *
          P {update id b a ∘ f} :=
      (ENNReal.sub_mul fun _ _ => measure_ne_top P _).symm
    _ = (if #{i | update id b a (f i) = a} = 2 then ENNReal.ofReal (1 - 2 * p)
         else ENNReal.ofReal (1 - p)) * P {update id b a ∘ f} := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by split_ifs <;> positivity),
        apply_ite (fun x => ENNReal.ofReal (1 - x))]

/-- **The one-pair formula, excess form.** For distinct indices `a b : κ` and `|ι| ≤ |κ|`, the
largest excess of without-replacement over with-replacement sampling from the one-pair population
`Function.update id b a` is `1 - p - t * min p (1 - p)`, where
`p = |κ|.descFactorial |ι| / |κ| ^ |ι|` and `t = |ι|.descFactorial 2 / |κ|.descFactorial 2`. -/
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
  dsimp only
  rw [← onePairP, ← onePairT]
  let P := sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a))
  set t : ℝ := onePairT (Fintype.card ι) (Fintype.card κ)
  let E₂ : Set (ι → κ) := {y | #{i | y i = a} = 2}
  -- Express the two-hit event mass `P E₂` and its complement in terms of `t`.
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hmn
  let _ : IsProbabilityMeasure P := isProbabilityMeasure_sampleWithoutReplacement _ e
  have ht0 : 0 ≤ t := onePairT_nonneg _ _
  have hPE₂ : P E₂ = ENNReal.ofReal t := by
    rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top P _) ENNReal.ofReal_ne_top,
      sampleWithoutReplacement_dirac_update_id_apply_setOf_card_filter_eq_two hab hmn,
      ENNReal.toReal_ofReal ht0]
    simp only [t, onePairT, ENNReal.toReal_div, ENNReal.toReal_natCast]
  have hPE₂c : P E₂ᶜ = ENNReal.ofReal (1 - t) := by
    rw [prob_compl_eq_one_sub .of_discrete, hPE₂, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ ht0]
  -- Sum the singleton excesses over `E₂` and `E₂ᶜ` and combine the two pieces.
  rw [iSup_measure_sub_eq_sum_singleton]
  simp_rw [sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_singleton hab,
    ite_mul]
  rw [sum_ite, ← mul_sum, ← mul_sum]
  simp only [sum_measure_singleton, coe_filter_univ, ← Set.compl_ofPred]
  rw [hPE₂, hPE₂c,
    ofReal_one_sub_two_mul_mul_add_eq (onePairP_le_one _ _) ht0
      (onePairT_le_one hmn)]

/-- **The one-pair formula, total-variation form.** For distinct indices `a b : κ` and
`|ι| ≤ |κ|`, Mathlib's extended total variation distance between sampling the one-pair population
`Function.update id b a` without and with replacement is
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
  let _ : Nonempty (ι → κ) := ⟨e⟩
  let _ := isProbabilityMeasure_sampleWithoutReplacement (Measure.dirac (update id b a)) e
  let _ := isProbabilityMeasure_sampleWithReplacement (ι := ι) (Measure.dirac (update id b a))
  rw [etvDist_eq_two_mul_iSup_sub (by rw [measure_univ, measure_univ]),
    iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_eq hab hmn]

/-- **The one-pair formula, real total-variation form.** For distinct indices `a b : κ` and
`|ι| ≤ |κ|`, the real-valued total variation distance between sampling the one-pair population
`Function.update id b a` without and with replacement is `2 * (1 - p - t * min p (1 - p))`. -/
theorem tvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_update_id_eq
    (hab : a ≠ b) (hmn : Fintype.card ι ≤ Fintype.card κ) :
    tvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac (update id b a)))
      (sampleWithReplacement (ι := ι) (Measure.dirac (update id b a))) =
      let p : ℝ := (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ) ^ Fintype.card ι
      let t : ℝ := (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2
      2 * (1 - p - t * min p (1 - p)) := by
  rw [tvDist, etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_update_id_eq hab hmn,
    ENNReal.toReal_mul, ENNReal.toReal_ofNat]
  dsimp only
  rw [ENNReal.toReal_ofReal (one_sub_descFactorial_div_pow_sub_mul_min_nonneg _ _)]

end Discrepancy

end Probability

end TauCeti

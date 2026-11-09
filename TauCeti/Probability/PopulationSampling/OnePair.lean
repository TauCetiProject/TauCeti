/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.UniformOn
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import TauCeti.Data.Fintype.CardEmbedding

/-!
# The one-pair population: fibres and the two-hit mass

For distinct indices `a b : κ`, the *one-pair population* `Function.update id b a : κ → κ` sends
`b` to `a` and fixes every other index; it is the population with exactly one repeated value.
Sampling it along an index map `f : ι → κ` gives the word `Function.update id b a ∘ f`. This file
counts the index maps and the embeddings producing a given word, and computes the probability that
a uniform injective index map hits both `a` and `b`. These are the combinatorial inputs for the
exact discrepancy between sampling the one-pair population with and without replacement: the
singleton masses of the two sampling laws are fibre counts divided by `|κ| ^ |ι|`, respectively by
the number of injective index maps.

Write `r` for the number of `i` with `Function.update id b a (f i) = a`, that is with
`f i ∈ {a, b}`. For an injective `f`, `r ≤ 2`, and `r = 2` exactly when `a` and `b` both lie in the
range of `f`. The word of `f` is produced by `2 ^ r` index maps, and, when `f` is an embedding, by
one embedding if `r = 0` and by two (namely `f` and `Equiv.swap a b ∘ f`) otherwise.

## Main declarations

* `update_id_apply_eq_iff`: the one-pair population takes the value `a` exactly at `a`
  and `b`;
* `card_filter_update_id_apply_eq_le_two`, `card_filter_update_id_apply_eq_eq_two_iff`: an
  injective index map meets `{a, b}` at most twice, and twice exactly when it hits both;
* `natCard_update_id_comp_eq_update_id_comp`: the number of index maps with the same word is
  `2 ^ r`;
* `natCard_embedding_update_id_comp_eq_update_id_comp`: the number of embeddings with the same
  word is `1` if `r = 0` and `2` otherwise;
* `uniformOn_injective_mem_range_and_mem_range`: a uniform injective index map hits both `a`
  and `b` with probability `|ι| (|ι| - 1) / (|κ| (|κ| - 1))`, written with `Nat.descFactorial`.
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

/-- The one-pair population takes the value `a` exactly at the two indices `a` and `b`. -/
@[simp]
theorem update_id_apply_eq_iff {x : κ} : update id b a x = a ↔ x = a ∨ x = b := by
  rw [update_apply]
  split_ifs with h <;> simp [h]

/-- Two indices have the same one-pair value exactly when they agree up to swapping `a` and `b`.
-/
private theorem update_id_apply_eq_update_id_apply_iff {x y : κ} :
    update id b a y = update id b a x ↔ y = x ∨ y = Equiv.swap a b x := by
  simp only [update_apply, id_eq, Equiv.swap_apply_def]
  split_ifs <;> grind

/-- The one-pair population is invariant under swapping the two identified indices. -/
private theorem update_id_swap_apply (x : κ) :
    update id b a (Equiv.swap a b x) = update id b a x :=
  update_id_apply_eq_update_id_apply_iff.2 (Or.inr rfl)

/-- The values of an injective index map at the indices it sends to `a` or `b` are distinct
elements of `{a, b}`, so they number the elements of `{a, b}` in its range. -/
private theorem card_filter_update_id_apply_eq_eq_card_filter_mem_range [Fintype ι] {f : ι → κ}
    (hf : Injective f) :
    #{i | update id b a (f i) = a} = #(({a, b} : Finset κ).filter (· ∈ Set.range f)) := by
  classical
  refine card_nbij f (fun i hi => ?_) hf.injOn fun x hx => ?_
  · simp_all
  · simp only [coe_filter, mem_insert, mem_singleton] at hx
    obtain ⟨hx, i, rfl⟩ := hx
    exact ⟨i, by simpa using hx, rfl⟩

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
    · refine Set.ncard_pair fun he => ?_
      rw [update_id_apply_eq_iff] at h
      rcases h with h | h <;> simp [h, hab, hab.symm, Equiv.swap_apply_left,
        Equiv.swap_apply_right] at he
    · have he : Equiv.swap a b (f i) = f i := by
        rw [update_id_apply_eq_iff, not_or] at h
        exact Equiv.swap_apply_of_ne_of_ne h.1 h.2
      rw [he, Set.pair_eq_singleton, Set.ncard_singleton]
  have e : {g : ι → κ // update id b a ∘ g = update id b a ∘ f} ≃
      ∀ i, {y : κ // update id b a y = update id b a (f i)} :=
    (Equiv.subtypeEquivRight fun g => funext_iff).trans
      (Equiv.subtypePiEquivPi (p := fun i y => update id b a y = update id b a (f i)))
  rw [Nat.card_congr e, Nat.card_pi]
  simp_rw [hfib]
  rw [prod_ite, prod_const_one, mul_one, prod_const]

/-- The embeddings with the same one-pair word as an embedding `f` are `f` and
`Equiv.swap a b ∘ f`. -/
private theorem embedding_update_id_comp_eq_update_id_comp_iff (f g : ι ↪ κ) :
    update id b a ∘ g = update id b a ∘ f ↔ g = f ∨ g = f.trans (Equiv.swap a b).toEmbedding := by
  constructor
  · intro h
    have hpt (i : ι) : g i = f i ∨ g i = Equiv.swap a b (f i) :=
      update_id_apply_eq_update_id_apply_iff.1 (congrFun h i)
    by_contra hne
    simp only [not_or, DFunLike.ext_iff, not_forall, Embedding.trans_apply,
      Equiv.coe_toEmbedding] at hne
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hne
    have hi' : g i = Equiv.swap a b (f i) := (hpt i).resolve_left hi
    have hj' : g j = f j := (hpt j).resolve_right hj
    -- Both `f i` and `f j` are moved by the swap, so they are `a` and `b` in some order, and
    -- then `g i = g j`.
    have hfi : f i = a ∨ f i = b := by
      by_contra h
      rw [not_or] at h
      exact hi (hi'.trans (Equiv.swap_apply_of_ne_of_ne h.1 h.2))
    have hfj : f j = a ∨ f j = b := by
      by_contra h
      rw [not_or] at h
      exact hj (hj'.trans (Equiv.swap_apply_of_ne_of_ne h.1 h.2).symm)
    have hij : i ≠ j := by
      rintro rfl
      exact hi hj'
    have hfij : f i ≠ f j := f.injective.ne hij
    apply g.injective.ne hij
    rw [hi', hj']
    rcases hfi with hfi | hfi <;> rcases hfj with hfj | hfj <;>
      simp_all [Equiv.swap_apply_left, Equiv.swap_apply_right]
  · rintro (rfl | rfl)
    · rfl
    · funext i
      exact update_id_swap_apply (f i)

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
    simp [embedding_update_id_comp_eq_update_id_comp_iff]
  have hfix : f.trans (Equiv.swap a b).toEmbedding = f ↔ #{i | update id b a (f i) = a} = 0 := by
    simp only [DFunLike.ext_iff, Embedding.trans_apply, Equiv.coe_toEmbedding, card_eq_zero,
      filter_eq_empty_iff, mem_univ, true_implies, update_id_apply_eq_iff, not_or]
    refine forall_congr' fun i => ⟨fun h => ?_, fun h => Equiv.swap_apply_of_ne_of_ne h.1 h.2⟩
    constructor <;> rintro hi <;> rw [hi] at h <;>
      simp [Equiv.swap_apply_left, Equiv.swap_apply_right, hab, hab.symm] at h
  rw [← Set.coe_ofPred, Nat.card_coe_set_eq, hset]
  split_ifs with h
  · rw [hfix.2 h, Set.pair_eq_singleton, Set.ncard_singleton]
  · exact Set.ncard_pair fun he => h (hfix.1 he.symm)

end Fibres

section TwoHit

variable [Fintype ι] [Fintype κ]

section Count

variable [DecidableEq ι] [DecidableEq κ]

/-- Relabelling the population by a permutation `σ` shows that the number of injective index
maps whose range contains two given distinct indices does not depend on which two. -/
private theorem card_filter_injective_mem_range_and_mem_range_eq {c d : κ} (hab : a ≠ b)
    (hcd : c ≠ d) [DecidablePred fun k : ι → κ => Injective k] :
    #{k : ι → κ | Injective k ∧ (c ∈ Set.range k ∧ d ∈ Set.range k)} =
      #{k : ι → κ | Injective k ∧ (a ∈ Set.range k ∧ b ∈ Set.range k)} := by
  classical
  -- A permutation sending `a` to `c` and `b` to `d`.
  let σ : Equiv.Perm κ := (Equiv.swap a c).trans (Equiv.swap (Equiv.swap a c b) d)
  have hσa : σ a = c := by
    have : c ≠ Equiv.swap a c b := fun h => hab (by
      rw [eq_comm, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
      exact h.symm)
    simp only [σ, Equiv.trans_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne this hcd
  have hσb : σ b = d := by simp [σ]
  -- Postcomposition with `σ` carries the maps hitting `a` and `b` to those hitting `c` and `d`.
  refine card_nbij' (σ.symm ∘ ·) (σ ∘ ·) (fun k hk => ?_) (fun k hk => ?_)
    (fun k _ => by ext; simp) (fun k _ => by ext; simp)
  · simp only [coe_filter, mem_univ, true_and] at hk ⊢
    refine ⟨σ.symm.injective.comp hk.1, ?_⟩
    simpa [Set.mem_range, Equiv.symm_apply_eq, hσa, hσb] using hk.2
  · simp only [coe_filter, mem_univ, true_and] at hk ⊢
    refine ⟨σ.injective.comp hk.1, ?_⟩
    simpa [Set.mem_range, ← hσa, ← hσb] using hk.2

/-- Double counting the triples `(k, c, d)` with `k` injective and `c ≠ d` both in the range of
`k`: each injective `k` contributes `|ι| (|ι| - 1)` pairs, and each of the `|κ| (|κ| - 1)` pairs
is hit by the same number of injective maps. -/
private theorem descFactorial_two_mul_card_filter_injective_mem_range_and_mem_range
    (hab : a ≠ b) [DecidablePred fun k : ι → κ => Injective k] :
    (Fintype.card κ).descFactorial 2 *
        #{k : ι → κ | Injective k ∧ (a ∈ Set.range k ∧ b ∈ Set.range k)} =
      (Fintype.card κ).descFactorial (Fintype.card ι) * (Fintype.card ι).descFactorial 2 := by
  classical
  let I : Finset (ι → κ) := {k | Injective k}
  have hI : #I = (Fintype.card κ).descFactorial (Fintype.card ι) := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_subtype_injective
  have hd (x : ℕ) : x.descFactorial 2 = x * x - x := by
    rw [Nat.descFactorial_succ, Nat.descFactorial_one, mul_comm, Nat.mul_sub_one]
  -- Count the pairs `(p, k)` with `p` off the diagonal and both coordinates in the range of `k`.
  have hdouble : ∑ p ∈ (univ : Finset κ).offDiag,
        #{k ∈ I | p.1 ∈ Set.range k ∧ p.2 ∈ Set.range k} =
      ∑ k ∈ I, #{p ∈ (univ : Finset κ).offDiag | p.1 ∈ Set.range k ∧ p.2 ∈ Set.range k} := by
    exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (r := fun (p : κ × κ) (k : ι → κ) => p.1 ∈ Set.range k ∧ p.2 ∈ Set.range k)
  have hleft : ∑ p ∈ (univ : Finset κ).offDiag,
        #{k ∈ I | p.1 ∈ Set.range k ∧ p.2 ∈ Set.range k} =
      (Fintype.card κ).descFactorial 2 *
        #{k : ι → κ | Injective k ∧ (a ∈ Set.range k ∧ b ∈ Set.range k)} := by
    rw [sum_congr rfl fun p hp => ?_, sum_const, smul_eq_mul, offDiag_card, card_univ, hd]
    rw [filter_filter]
    exact card_filter_injective_mem_range_and_mem_range_eq hab (mem_offDiag.1 hp).2.2
  have hright (k : ι → κ) (hk : k ∈ I) :
      #{p ∈ (univ : Finset κ).offDiag | p.1 ∈ Set.range k ∧ p.2 ∈ Set.range k} =
        (Fintype.card ι).descFactorial 2 := by
    have hk : Injective k := by simpa [I] using hk
    have hfilt : {p ∈ (univ : Finset κ).offDiag | p.1 ∈ Set.range k ∧ p.2 ∈ Set.range k} =
        (univ.image k).offDiag := by
      ext p
      simp only [mem_filter, mem_offDiag, mem_univ, true_and, mem_image, Set.mem_range]
      tauto
    rw [hfilt, offDiag_card, card_image_of_injective _ hk, card_univ, hd]
  rw [← hleft, hdouble, sum_congr rfl hright, sum_const, smul_eq_mul, hI]

end Count

/-- **Two-hit mass.** For distinct indices `a b : κ` and `|ι| ≤ |κ|`, a uniform injective index
map `k : ι → κ` has both `a` and `b` in its range with probability
`|ι| (|ι| - 1) / (|κ| (|κ| - 1))`.

Without `|ι| ≤ |κ|` there is no injective index map, the left side is `0`, and the right side is
positive once `|ι| ≥ 2`. -/
theorem uniformOn_injective_mem_range_and_mem_range [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (hab : a ≠ b) (hικ : Fintype.card ι ≤ Fintype.card κ) :
    uniformOn {k : ι → κ | Injective k} {k | a ∈ Set.range k ∧ b ∈ Set.range k} =
      (Fintype.card ι).descFactorial 2 / (Fintype.card κ).descFactorial 2 := by
  classical
  have hκ : 2 ≤ Fintype.card κ := Fintype.one_lt_card_iff.2 ⟨a, b, hab⟩
  have h2 : ((Fintype.card κ).descFactorial 2 : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_eq_zero_iff_lt.not.2 (not_lt.2 hκ))
  have hm : ((Fintype.card κ).descFactorial (Fintype.card ι) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_eq_zero_iff_lt.not.2 (not_lt.2 hικ))
  have hset : {k : ι → κ | Injective k} = (({k | Injective k} : Finset (ι → κ)) : Set _) := by
    simp
  have hevt : {k : ι → κ | a ∈ Set.range k ∧ b ∈ Set.range k} =
      (({k | a ∈ Set.range k ∧ b ∈ Set.range k} : Finset (ι → κ)) : Set _) := by
    simp
  rw [hset, hevt, uniformOn_apply_finset, ← filter_and,
    ← Fintype.card_subtype (fun k : ι → κ => Injective k), Fintype.card_subtype_injective,
    ENNReal.div_eq_div_iff h2 (ENNReal.natCast_ne_top _) hm (ENNReal.natCast_ne_top _)]
  exact_mod_cast descFactorial_two_mul_card_filter_injective_mem_range_and_mem_range hab

end TwoHit

end Probability

end TauCeti

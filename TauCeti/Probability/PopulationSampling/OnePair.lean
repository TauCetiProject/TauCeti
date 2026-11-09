/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Preimage

/-!
# The one-pair population: fibres

For distinct indices `a b : κ`, the *one-pair population* `Function.update id b a : κ → κ` sends
`b` to `a` and fixes every other index; it is the population with exactly one repeated value.
Sampling it along an index map `f : ι → κ` gives the word `Function.update id b a ∘ f`. This file
counts the index maps and the embeddings producing a given word. These are the combinatorial inputs
for the exact discrepancy between sampling the one-pair population with and without replacement:
the singleton masses of the two sampling laws are fibre counts divided by `|κ| ^ |ι|`, respectively
by the number of injective index maps. The probability that a uniform injective index map hits
both `a` and `b` is `uniformOn_injective_mem_range_and_mem_range` in
`TauCeti.Probability.UniformSampling`.

Write `r` for the number of `i` with `Function.update id b a (f i) = a`, that is with
`f i ∈ {a, b}`. For an injective `f`, `r ≤ 2`, and `r = 2` exactly when `a` and `b` both lie in the
range of `f`. The word of `f` is produced by `2 ^ r` index maps, and, when `f` is an embedding, by
one embedding if `r = 0` and by two (namely `f` and `Equiv.swap a b ∘ f`) otherwise.

## Main declarations

* `update_id_apply_eq_iff`: the one-pair population takes the value `a` exactly at `a`
  and `b`;
* `update_id_apply_eq_update_id_apply_iff`, `update_id_swap_apply`: two indices have the same
  one-pair value exactly when they agree up to `Equiv.swap a b`;
* `card_filter_update_id_apply_eq_le_two`, `card_filter_update_id_apply_eq_eq_two_iff`: an
  injective index map meets `{a, b}` at most twice, and twice exactly when it hits both;
* `natCard_update_id_comp_eq_update_id_comp`: the number of index maps with the same word is
  `2 ^ r`;
* `embedding_update_id_comp_eq_update_id_comp_iff`: the embeddings with the same word as an
  embedding `f` are `f` and `Equiv.swap a b ∘ f`;
* `natCard_embedding_update_id_comp_eq_update_id_comp`: the number of embeddings with the same
  word is `1` if `r = 0` and `2` otherwise.
-/

public section

noncomputable section

open Finset Function

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
theorem update_id_apply_eq_update_id_apply_iff {x y : κ} :
    update id b a y = update id b a x ↔ y = x ∨ y = Equiv.swap a b x := by
  simp only [update_apply, id_eq, Equiv.swap_apply_def]
  split_ifs <;> grind

/-- The one-pair population is invariant under swapping the two identified indices. -/
@[simp]
theorem update_id_swap_apply (x : κ) :
    update id b a (Equiv.swap a b x) = update id b a x :=
  update_id_apply_eq_update_id_apply_iff.2 (Or.inr rfl)

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
theorem embedding_update_id_comp_eq_update_id_comp_iff (f g : ι ↪ κ) :
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

end Probability

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic

/-!
# Cardinalities of set differences and fiberwise filters of finsets

* `Finset.card_sdiff_insert_add_one`: adding an element `a ∈ T \ S` to `S` lowers the number of
  elements of `T` outside `S` by one.
* `Finset.subset_induction`: downward induction on `S ⊆ T`, from `T` itself and steps from
  `S ∪ {a}` to `S`. Mathlib's `Finset.induction_on'` is the upward analogue.
* `Finset.card_sdiff_lt_of_card_eq_min`: if `F ⊆ U` has `min k #U` elements of a nonempty `U`
  and `T ⊆ U` has fewer than `k`, then fewer elements of `T` lie outside `F` than in `F`.
* `Finset.card_filter_apply_eq_sum_card_filter`: counting elements `e ∈ s` satisfying `P (f e) e`
  splits fiberwise along `f` over any `t` containing the relevant image values.
-/

public section

namespace Finset

variable {ι : Type*} [DecidableEq ι]

/-- Adding an element `a ∈ T \ S` to `S` lowers the number of elements of `T` outside `S` by
one. -/
theorem card_sdiff_insert_add_one {S T : Finset ι} {a : ι} (ha : a ∈ T \ S) :
    #(T \ insert a S) + 1 = #(T \ S) := by
  rw [sdiff_insert, card_erase_add_one ha]

/-- Downward induction on `S ⊆ T`: a property holding at `T`, and passing from `S ∪ {a}` to `S`,
holds for every `S ⊆ T`. -/
theorem subset_induction {T : Finset ι} {P : ∀ S, S ⊆ T → Prop}
    (self : P T Subset.rfl)
    (step : ∀ S a, a ∉ S → ∀ h : insert a S ⊆ T,
      P (insert a S) h → P S ((S.subset_insert a).trans h)) (S : Finset ι) (h : S ⊆ T) :
    P S h := by
  induction hk : #(T \ S) generalizing S with
  | zero =>
    obtain rfl := Subset.antisymm h (sdiff_eq_empty_iff_subset.1 (card_eq_zero.1 hk))
    exact self
  | succ k ih =>
    obtain ⟨a, ha⟩ := card_pos.1 (by omega : 0 < #(T \ S))
    have h' : insert a S ⊆ T := insert_subset (mem_sdiff.1 ha).1 h
    exact step S a (mem_sdiff.1 ha).2 h'
      (ih _ h' (by have := card_sdiff_insert_add_one ha; omega))

/-- If `F` has `min k #U` of the elements of a nonempty set `U`, and `T ⊆ U` has fewer than `k`
elements, then fewer elements of `T` lie outside `F` than in `F`. -/
theorem card_sdiff_lt_of_card_eq_min {F T U : Finset ι} {k : ℕ}
    (hFU : F ⊆ U) (hTU : T ⊆ U) (hU : U.Nonempty) (hF : #F = min k #U) (hT : #T < k) :
    #(T \ F) < #F := by
  by_cases hkU : k ≤ #U
  · exact (card_le_card sdiff_subset).trans_lt (by omega)
  · rw [eq_of_subset_of_card_le hFU (by omega), sdiff_eq_empty_iff_subset.2 hTU, card_empty]
    exact hU.card_pos

omit [DecidableEq ι] in
/-- Partitioning `s` along `f : ι → κ` splits the count of elements `e ∈ s` satisfying
`P (f e) e` into a sum over any `t : Finset κ` containing `f e` on those elements. -/
theorem card_filter_apply_eq_sum_card_filter {κ : Type*} [DecidableEq κ] {f : ι → κ}
    {s : Finset ι} {t : Finset κ} (P : κ → ι → Prop) [∀ c e, Decidable (P c e)]
    (h : ∀ e ∈ s, P (f e) e → f e ∈ t) :
    #{e ∈ s | P (f e) e} = ∑ c ∈ t, #{e ∈ s | f e = c ∧ P c e} := by
  rw [card_eq_sum_card_fiberwise (f := f) (t := t) fun e he ↦
    h e (mem_filter.1 he).1 (mem_filter.1 he).2]
  refine sum_congr rfl fun c _ ↦ congrArg card (ext fun e ↦ ?_)
  simp only [mem_filter]
  exact ⟨fun ⟨⟨he, hP⟩, hf⟩ ↦ ⟨he, hf, hf ▸ hP⟩, fun ⟨he, hf, hP⟩ ↦ ⟨⟨he, hf.symm ▸ hP⟩, hf⟩⟩

end Finset

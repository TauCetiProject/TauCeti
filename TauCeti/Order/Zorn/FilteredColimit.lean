/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Preorder.Chain

import Mathlib.Order.Zorn

/-!
# Downward Zorn induction along filtered colimits

This file provides a downward Zorn induction principle on a partial order and its injective and
surjective applications to natural transformations between functors α ⥤ AddCommGrpCat whose
values along nonempty chains satisfy the elementwise filtered-colimit properties.

## Main results

* TauCeti.forall_gt_of_chain_counterexample: downward Zorn induction on a partial order.
* TauCeti.injective_of_filtered_colimit_of_map_eq_zero: injective half for a natural family of
  additive homomorphisms π a : G.obj a →+ K.obj a.
* TauCeti.surjective_of_filtered_colimit_of_exists_lift: surjective half for π a.

## References

* grh-lean, https://github.com/lsernau/grh-lean (commit
  72fead102f663d5c7a407964a13dc0cf9d977207), file
  src/Lib/Cohomology/Etale/ProperFunctors.lean (declarations
  New.Variety.forall_gt_of_chain_counterexample,
  New.Variety.injective_of_isFilteredColimit_of_map_eq_zero, and
  New.Variety.surjective_of_isFilteredColimit_of_exists_lift); Apache 2.0, Copyright 2026
  Anthropic, PBC.
-/

public section

open CategoryTheory

namespace TauCeti

/-- Downward induction by Zorn's lemma. Let P be a property of the elements above . If every
nonempty chain of counterexamples has an upper bound that is a counterexample, and P holds at m
as soon as it holds strictly above m, then P holds everywhere above . -/
theorem forall_gt_of_chain_counterexample {α : Type*} [PartialOrder α] {a : α}
    {P : ∀ b : α, a < b → Prop}
    (h_chain : ∀ c : Set α,
      (∀ b ∈ c, ∃ h : a < b, ¬P b h) →
      IsChain (· ≤ ·) c → c.Nonempty →
      ∃ (m : α) (h : a < m), ¬P m h ∧ ∀ b ∈ c, b ≤ m)
    (h_step : ∀ (m : α) (h : a < m), (∀ (b : α) (hb : m < b), P b (h.trans hb)) → P m h)
    (b : α) (hb : a < b) : P b hb := by
  by_contra h_fail
  obtain ⟨m, -, h_max⟩ : ∃ m : α, b ≤ m ∧ Maximal (· ∈ {b : α | ∃ h : a < b, ¬P b h}) m := by
    refine zorn_le_nonempty₀ _ (fun c hc_sub hc_chain z hz ↦ ?_) b ⟨hb, h_fail⟩
    obtain ⟨ub, ha_ub, hub_fail, h_le_ub⟩ := h_chain c hc_sub hc_chain ⟨z, hz⟩
    exact ⟨ub, ⟨ha_ub, hub_fail⟩, h_le_ub⟩
  obtain ⟨ha_m, hm_fail⟩ := h_max.prop
  refine hm_fail (h_step m ha_m fun d hd ↦ ?_)
  by_contra hd_fail
  exact h_max.not_gt ⟨ha_m.trans hd, hd_fail⟩ hd

/-- Downward induction, injective half. Let π a : G.obj a →+ K.obj a be natural in  on a
partial order α. Suppose every nonempty chain c has an upper bound 	 such that any element
of G.obj z (z ∈ c) vanishing in G.obj t already vanishes at some  ∈ c with z ≤ b. If
every element of ker (π a) vanishing at all  > a is zero, then π a is injective. -/
theorem injective_of_filtered_colimit_of_map_eq_zero {α : Type*} [PartialOrder α]
    {G K : α ⥤ AddCommGrpCat} {π : ∀ a : α, G.obj a →+ K.obj a}
    (h_nat : ∀ {a b : α} (f : a ⟶ b) (x : G.obj a), K.map f (π a x) = π b (G.map f x))
    (h_colim : ∀ c : Set α, IsChain (· ≤ ·) c → c.Nonempty →
      ∃ (t : α) (ht : ∀ b ∈ c, b ≤ t),
        ∀ z (hz : z ∈ c) (x : G.obj z), G.map (homOfLE (ht z hz)) x = 0 →
          ∃ (b : α) (_ : b ∈ c) (hzb : z ≤ b), G.map (homOfLE hzb) x = 0)
    (h_step : ∀ (a : α) (x : G.obj a), π a x = 0 →
      (∀ (b : α) (hab : a < b), G.map (homOfLE hab.le) x = 0) → x = 0)
    (a : α) : Function.Injective (π a) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ h_step a x hx ?_
  refine forall_gt_of_chain_counterexample (P := fun b hab ↦ G.map (homOfLE hab.le) x = 0) ?_ ?_
  · intro c hc_sub h_chain ⟨z, hz⟩
    obtain ⟨t, ht, hG_ker⟩ := h_colim c h_chain ⟨z, hz⟩
    obtain ⟨haz, -⟩ := hc_sub z hz
    refine ⟨t, haz.trans_le (ht z hz), fun h_zero ↦ ?_, ht⟩
    have h_zero_t : G.map (homOfLE (ht z hz)) (G.map (homOfLE haz.le) x) = 0 := by
      have hc : homOfLE haz.le ≫ homOfLE (ht z hz) = homOfLE (haz.trans_le (ht z hz)).le := rfl
      rw [← ConcreteCategory.comp_apply, ← G.map_comp, hc]
      exact h_zero
    obtain ⟨b, hb, hzb, h_zero_b⟩ := hG_ker z hz (G.map (homOfLE haz.le) x) h_zero_t
    obtain ⟨hab, hb_survives⟩ := hc_sub b hb
    have hc : homOfLE haz.le ≫ homOfLE hzb = homOfLE hab.le := rfl
    rw [← ConcreteCategory.comp_apply, ← G.map_comp, hc] at h_zero_b
    exact hb_survives h_zero_b
  · intro m ham hm
    refine h_step m (G.map (homOfLE ham.le) x) (by rw [← h_nat, hx, map_zero]) fun b hb ↦ ?_
    have hc : homOfLE ham.le ≫ homOfLE hb.le = homOfLE (ham.trans hb).le := rfl
    rw [← ConcreteCategory.comp_apply, ← G.map_comp, hc]
    exact hm b hb

/-- Downward induction, surjective half. Let π a : G.obj a →+ K.obj a be natural in  on a
partial order α. Suppose every nonempty chain c has an upper bound 	 where every element of
G.obj t comes from some  ∈ c, and every element of K.obj b ( ∈ c) vanishing in K.obj t
already vanishes at some d ∈ c with  ≤ d. If every y ∈ K.obj a whose images in K.obj b
lift along π b for all  > a itself lifts along π a, then π a is surjective. -/
theorem surjective_of_filtered_colimit_of_exists_lift {α : Type*} [PartialOrder α]
    {G K : α ⥤ AddCommGrpCat} {π : ∀ a : α, G.obj a →+ K.obj a}
    (h_nat : ∀ {a b : α} (f : a ⟶ b) (x : G.obj a), K.map f (π a x) = π b (G.map f x))
    (h_colim : ∀ c : Set α, IsChain (· ≤ ·) c → c.Nonempty →
      ∃ (t : α) (ht : ∀ b ∈ c, b ≤ t),
        (∀ x₀ : G.obj t, ∃ (b : α) (hb : b ∈ c) (x : G.obj b),
          G.map (homOfLE (ht b hb)) x = x₀) ∧
        (∀ b (hb : b ∈ c) (y : K.obj b), K.map (homOfLE (ht b hb)) y = 0 →
          ∃ (d : α) (_ : d ∈ c) (hbd : b ≤ d), K.map (homOfLE hbd) y = 0))
    (h_step : ∀ (a : α) (y : K.obj a),
      (∀ (b : α) (hab : a < b), ∃ x : G.obj b, π b x = K.map (homOfLE hab.le) y) →
      ∃ x : G.obj a, π a x = y)
    (a : α) : Function.Surjective (π a) := by
  intro y
  refine h_step a y ?_
  refine forall_gt_of_chain_counterexample
    (P := fun b hab ↦ ∃ x : G.obj b, π b x = K.map (homOfLE hab.le) y) ?_ ?_
  · intro c hc_sub h_chain ⟨z, hz⟩
    obtain ⟨t, ht, hG_surj, hK_ker⟩ := h_colim c h_chain ⟨z, hz⟩
    obtain ⟨haz, -⟩ := hc_sub z hz
    refine ⟨t, haz.trans_le (ht z hz), ?_, ht⟩
    rintro ⟨x₀, hx₀⟩
    obtain ⟨b, hb, x, rfl⟩ := hG_surj x₀
    obtain ⟨hab, -⟩ := hc_sub b hb
    have h_diff_t : K.map (homOfLE (ht b hb)) (π b x - K.map (homOfLE hab.le) y) = 0 := by
      have hc : homOfLE hab.le ≫ homOfLE (ht b hb) = homOfLE (haz.trans_le (ht z hz)).le := rfl
      rw [map_sub, ← ConcreteCategory.comp_apply, ← K.map_comp, hc, sub_eq_zero]
      exact (h_nat _ x).trans hx₀
    obtain ⟨d, hd, hbd, h_diff_d⟩ := hK_ker b hb _ h_diff_t
    obtain ⟨had, hd_no_lift⟩ := hc_sub d hd
    have hc : homOfLE hab.le ≫ homOfLE hbd = homOfLE had.le := rfl
    rw [map_sub, ← ConcreteCategory.comp_apply, ← K.map_comp, hc, sub_eq_zero, h_nat] at h_diff_d
    exact hd_no_lift ⟨G.map (homOfLE hbd) x, h_diff_d⟩
  · intro m ham hm
    refine h_step m (K.map (homOfLE ham.le) y) fun b hb ↦ ?_
    have hc : homOfLE ham.le ≫ homOfLE hb.le = homOfLE (ham.trans hb).le := rfl
    rw [← ConcreteCategory.comp_apply, ← K.map_comp, hc]
    exact hm b hb

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Uniqueness of ordered couplings

A nonnegative finitely supported function on a product of partial orders whose support is a
chain is determined by its two marginals. Its mass on a rectangle of lower sets equals one
marginal mass and is bounded by the other; when infima exist, it is their infimum.
An additive identity between four such rectangles recovers each coefficient by cancellation.
This is the uniqueness property underlying the staircase triangulation of a product of simplices.
No normalization of the total mass or finiteness of the ambient orders is required.
The marginal sums use Mathlib's `Finsupp.sum_mapDomain_index`.
-/

public section

noncomputable section

namespace Finsupp

open Set

variable {α β G : Type*}

/-- Support domination makes a rectangle mass equal the second-coordinate mass, which is
bounded by the first-coordinate mass. No order or chain hypothesis on the coordinates is needed. -/
theorem sum_indicator_prod_eq_right_and_le_of_support_imp {δ : Type*} [AddCommMonoid G]
    [Preorder G] [IsOrderedAddMonoid G] (w : δ →₀ G) (hw : ∀ p, 0 ≤ w p)
    (f : δ → α) (g : δ → β) {s : Set α} {t : Set β}
    (hsub : ∀ p ∈ w.support, g p ∈ t → f p ∈ s) :
    (w.sum (fun p r => (s ×ˢ t).indicator (fun _ => r) (f p, g p)) =
      w.sum (fun p r => t.indicator (fun _ => r) (g p))) ∧
    w.sum (fun p r => t.indicator (fun _ => r) (g p)) ≤
      w.sum (fun p r => s.indicator (fun _ => r) (f p)) := by
  classical
  constructor
  · apply Finsupp.sum_congr
    intro p hp
    by_cases hpt : g p ∈ t <;> simp [hpt, hsub p hp]
  · simp only [Finsupp.sum]
    apply Finset.sum_le_sum
    intro p hp
    by_cases hpt : g p ∈ t
    · simp [hpt, hsub p hp hpt]
    · by_cases hps : f p ∈ s <;> simp [hpt, hps, hw p]

/-- The mass of a lower rectangle in a nonnegative chain-supported coupling equals one
coordinate lower-set mass, and that mass is at most the other. -/
theorem sum_indicator_prod_eq_left_or_right [Preorder α] [Preorder β] [AddCommMonoid G]
    [Preorder G] [IsOrderedAddMonoid G] (w : (α × β) →₀ G) (hw : ∀ p, 0 ≤ w p)
    (hc : IsChain (· ≤ ·) (w.support : Set (α × β)))
    {s : Set α} {t : Set β} (hs : IsLowerSet s) (ht : IsLowerSet t) :
    (w.sum (fun p r => (s ×ˢ t).indicator (fun _ => r) p) =
        w.sum (fun p r => s.indicator (fun _ => r) p.1) ∧
      w.sum (fun p r => s.indicator (fun _ => r) p.1) ≤
        w.sum (fun p r => t.indicator (fun _ => r) p.2)) ∨
    (w.sum (fun p r => (s ×ˢ t).indicator (fun _ => r) p) =
        w.sum (fun p r => t.indicator (fun _ => r) p.2) ∧
      w.sum (fun p r => t.indicator (fun _ => r) p.2) ≤
        w.sum (fun p r => s.indicator (fun _ => r) p.1)) := by
  classical
  -- A chain cannot meet both off-diagonal rectangles; one coordinate lower set contains the other.
  by_cases h : ∃ p ∈ w.support, p.1 ∈ s ∧ p.2 ∉ t
  · obtain ⟨p, hp, hps, hpt⟩ := h
    have hsub : ∀ q ∈ w.support, q.2 ∈ t → q.1 ∈ s := by
      intro q hq hqt
      by_cases hpq : p = q
      · simpa [← hpq] using hps
      · rcases hc hp hq hpq with hpq | hqp
        · exact (hpt (ht hpq.2 hqt)).elim
        · exact hs hqp.1 hps
    exact Or.inr (sum_indicator_prod_eq_right_and_le_of_support_imp w hw
      Prod.fst Prod.snd hsub)
  · have hsub : ∀ p ∈ w.support, p.1 ∈ s → p.2 ∈ t := by
      intro p hp hps
      by_contra hpt
      exact h ⟨p, hp, hps, hpt⟩
    refine Or.inl ?_
    simpa only [Set.indicator_apply, Set.mem_prod, and_comm] using
      sum_indicator_prod_eq_right_and_le_of_support_imp w hw Prod.snd Prod.fst hsub

/-- The mass of a lower rectangle in a nonnegative chain-supported coupling is the infimum
of the masses of its two coordinate lower sets. -/
theorem sum_indicator_prod_eq_inf [Preorder α] [Preorder β] [AddCommMonoid G] [SemilatticeInf G]
    [IsOrderedAddMonoid G] (w : (α × β) →₀ G) (hw : ∀ p, 0 ≤ w p)
    (hc : IsChain (· ≤ ·) (w.support : Set (α × β)))
    {s : Set α} {t : Set β} (hs : IsLowerSet s) (ht : IsLowerSet t) :
    w.sum (fun p r => (s ×ˢ t).indicator (fun _ => r) p) =
      (w.sum fun p r => s.indicator (fun _ => r) p.1) ⊓
        (w.sum fun p r => t.indicator (fun _ => r) p.2) := by
  rcases sum_indicator_prod_eq_left_or_right w hw hc hs ht with ⟨heq, hle⟩ | ⟨heq, hle⟩
  · rw [heq, inf_eq_left.mpr hle]
  · rw [heq, inf_eq_right.mpr hle]

/-- The masses of the closed and open lower rectangles sum to the masses of the two mixed
rectangles plus the coefficient at their common upper bound. -/
theorem sum_indicator_Iic_prod_add_sum_indicator_Iio_prod [PartialOrder α] [PartialOrder β]
    [AddCommMonoid G] (u : (α × β) →₀ G) (a : α) (b : β) :
    u.sum (fun p r => (Iic (a, b)).indicator (fun _ => r) p) +
      u.sum (fun p r => (Iio a ×ˢ Iio b).indicator (fun _ => r) p) =
      u.sum (fun p r => (Iio a ×ˢ Iic b).indicator (fun _ => r) p) +
        u.sum (fun p r => (Iic a ×ˢ Iio b).indicator (fun _ => r) p) + u (a, b) := by
  classical
  rw [← Iic_prod_Iic]
  calc
    _ = u.sum (fun p r => (Iio a ×ˢ Iic b).indicator (fun _ => r) p +
        (Iic a ×ˢ Iio b).indicator (fun _ => r) p + if p = (a, b) then r else 0) := by
      rw [← Finsupp.sum_add]
      apply Finsupp.sum_congr
      intro p _
      -- Equal coordinates account for the boundary terms; off the corner the strict and
      -- non-strict inequalities agree after excluding coordinate equality.
      by_cases ha : p.1 = a <;> by_cases hb : p.2 = b <;>
        simp [Set.indicator_apply, mem_prod, mem_Iic, mem_Iio, ha, hb,
          Prod.ext_iff, Prod.le_def, lt_iff_le_and_ne]
    _ = _ := by
      rw [Finsupp.sum_add, Finsupp.sum_add, Finsupp.sum_ite_self_eq']

/-- Two nonnegative chain-supported couplings with equal marginals coincide. -/
theorem eq_of_mapDomain_eq_of_isChain_support [PartialOrder α] [PartialOrder β]
    [AddCancelCommMonoid G] [PartialOrder G]
    [IsOrderedAddMonoid G] (w v : (α × β) →₀ G)
    (hw : ∀ p, 0 ≤ w p) (hv : ∀ p, 0 ≤ v p)
    (hcw : IsChain (· ≤ ·) (w.support : Set (α × β)))
    (hcv : IsChain (· ≤ ·) (v.support : Set (α × β)))
    (hfst : mapDomain Prod.fst w = mapDomain Prod.fst v)
    (hsnd : mapDomain Prod.snd w = mapDomain Prod.snd v) : w = v := by
  classical
  have hrect {s : Set α} {t : Set β} (hs : IsLowerSet s) (ht : IsLowerSet t) :
      w.sum (fun p r => (s ×ˢ t).indicator (fun _ => r) p) =
        v.sum (fun p r => (s ×ˢ t).indicator (fun _ => r) p) := by
    have hf := congrArg (fun u : α →₀ G =>
      u.sum (fun a r => s.indicator (fun _ => r) a)) hfst
    have hg := congrArg (fun u : β →₀ G =>
      u.sum (fun b r => t.indicator (fun _ => r) b)) hsnd
    rw [sum_mapDomain_index (h := fun a r => s.indicator (fun _ => r) a)
      (by simp) (by simp [indicator_add]),
      sum_mapDomain_index (h := fun a r => s.indicator (fun _ => r) a)
        (by simp) (by simp [indicator_add])] at hf
    rw [sum_mapDomain_index (h := fun b r => t.indicator (fun _ => r) b)
      (by simp) (by simp [indicator_add]),
      sum_mapDomain_index (h := fun b r => t.indicator (fun _ => r) b)
        (by simp) (by simp [indicator_add])] at hg
    have hwmass := sum_indicator_prod_eq_left_or_right w hw hcw hs ht
    have hvmass := sum_indicator_prod_eq_left_or_right v hv hcv hs ht
    rw [hf, hg] at hwmass
    rcases hwmass with ⟨hwrect, hwle⟩ | ⟨hwrect, hwle⟩ <;>
      rcases hvmass with ⟨hvrect, hvle⟩ | ⟨hvrect, hvle⟩
    · exact hwrect.trans hvrect.symm
    · exact hwrect.trans ((le_antisymm hwle hvle).trans hvrect.symm)
    · exact hwrect.trans ((le_antisymm hwle hvle).trans hvrect.symm)
    · exact hwrect.trans hvrect.symm
  ext ⟨a, b⟩
  have hwrect := sum_indicator_Iic_prod_add_sum_indicator_Iio_prod w a b
  have hvrect := sum_indicator_Iic_prod_add_sum_indicator_Iio_prod v a b
  simp only [← Iic_prod_Iic] at hwrect hvrect
  rw [hrect (isLowerSet_Iic a) (isLowerSet_Iic b),
    hrect (isLowerSet_Iio a) (isLowerSet_Iic b),
    hrect (isLowerSet_Iic a) (isLowerSet_Iio b),
    hrect (isLowerSet_Iio a) (isLowerSet_Iio b)] at hwrect
  exact add_left_cancel (hwrect.symm.trans hvrect)

end Finsupp

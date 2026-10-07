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
chain is determined by its two marginals. Its mass on a rectangle of lower sets is the infimum
of the two marginal masses. Taking differences of four such rectangles recovers each coefficient.
This is the uniqueness property underlying the staircase triangulation of a product of simplices.
No normalization of the total mass or finiteness of the ambient orders is required.
The marginal sums use Mathlib's `Finsupp.sum_mapDomain_index`.
-/

public section

noncomputable section

namespace Finsupp

open Set

variable {α β G : Type*}

/-- The mass of a lower rectangle in a nonnegative chain-supported coupling is the infimum
of the masses of its two coordinate lower sets. -/
theorem sum_indicator_prod_eq_inf [Preorder α] [Preorder β] [AddCommMonoid G] [SemilatticeInf G]
    [IsOrderedAddMonoid G] (w : (α × β) →₀ G) (hw : ∀ p, 0 ≤ w p)
    (hc : IsChain (· ≤ ·) (w.support : Set (α × β)))
    {s : Set α} {t : Set β} (hs : IsLowerSet s) (ht : IsLowerSet t) :
    w.sum (fun p r => (s ×ˢ t).indicator (fun _ => r) p) =
      (w.sum fun p r => s.indicator (fun _ => r) p.1) ⊓
        (w.sum fun p r => t.indicator (fun _ => r) p.2) := by
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
    have heq : w.sum (fun p r => (s ×ˢ t).indicator (fun _ => r) p) =
        w.sum (fun p r => t.indicator (fun _ => r) p.2) := by
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hqt : q.2 ∈ t <;> simp [hqt, hsub q hq]
    have hle : w.sum (fun p r => t.indicator (fun _ => r) p.2) ≤
        w.sum (fun p r => s.indicator (fun _ => r) p.1) := by
      apply Finset.sum_le_sum
      intro q hq
      by_cases hqt : q.2 ∈ t
      · simp [hqt, hsub q hq hqt]
      · by_cases hqs : q.1 ∈ s <;> simp [hqt, hqs, hw q]
    rw [heq, inf_eq_right.mpr hle]
  · have hsub : ∀ p ∈ w.support, p.1 ∈ s → p.2 ∈ t := by
      intro p hp hps
      by_contra hpt
      exact h ⟨p, hp, hps, hpt⟩
    have heq : w.sum (fun p r => (s ×ˢ t).indicator (fun _ => r) p) =
        w.sum (fun p r => s.indicator (fun _ => r) p.1) := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hps : p.1 ∈ s <;> simp [hps, hsub p hp]
    have hle : w.sum (fun p r => s.indicator (fun _ => r) p.1) ≤
        w.sum (fun p r => t.indicator (fun _ => r) p.2) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hps : p.1 ∈ s
      · simp [hps, hsub p hp hps]
      · by_cases hpt : p.2 ∈ t <;> simp [hps, hpt, hw p]
    rw [heq, inf_eq_left.mpr hle]

/-- A coefficient is the alternating sum of the masses of the four lower rectangles whose
upper bounds use strict or non-strict comparison with that coefficient's coordinates. -/
@[simp]
theorem sum_indicator_Iic_prod_sub_sub_add [PartialOrder α] [PartialOrder β]
    [AddCommGroup G] (u : (α × β) →₀ G) (a : α) (b : β) :
    u.sum (fun p r => (Iic (a, b)).indicator (fun _ => r) p) -
      u.sum (fun p r => (Iio a ×ˢ Iic b).indicator (fun _ => r) p) -
      u.sum (fun p r => (Iic a ×ˢ Iio b).indicator (fun _ => r) p) +
      u.sum (fun p r => (Iio a ×ˢ Iio b).indicator (fun _ => r) p) = u (a, b) := by
  classical
  rw [← Iic_prod_Iic]
  simp only [Finsupp.sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  calc
    _ = ∑ p ∈ u.support, if p = (a, b) then u p else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      simp only [Set.indicator, mem_prod, mem_Iic, mem_Iio]
      by_cases ha : p.1 ≤ a <;> by_cases hb : p.2 ≤ b <;>
        by_cases ha' : p.1 < a <;> by_cases hb' : p.2 < b <;>
        simp_all [Prod.ext_iff, lt_iff_le_and_ne] <;> grind
    _ = u (a, b) := by
      simp [Finsupp.mem_support_iff, eq_comm]

/-- Two nonnegative chain-supported couplings with equal marginals coincide. -/
theorem eq_of_mapDomain_eq_of_isChain_support [PartialOrder α] [PartialOrder β]
    [AddCommGroup G] [SemilatticeInf G]
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
    rw [sum_indicator_prod_eq_inf w hw hcw hs ht,
      sum_indicator_prod_eq_inf v hv hcv hs ht, hf, hg]
  ext ⟨a, b⟩
  rw [← sum_indicator_Iic_prod_sub_sub_add w a b, ← sum_indicator_Iic_prod_sub_sub_add v a b]
  simp only [← Iic_prod_Iic]
  rw [hrect (isLowerSet_Iic a) (isLowerSet_Iic b),
    hrect (isLowerSet_Iio a) (isLowerSet_Iic b),
    hrect (isLowerSet_Iic a) (isLowerSet_Iio b),
    hrect (isLowerSet_Iio a) (isLowerSet_Iio b)]

end Finsupp

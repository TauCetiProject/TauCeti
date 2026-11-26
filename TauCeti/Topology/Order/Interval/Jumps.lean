/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Order.Compact
import Mathlib.Topology.DiscreteSubset
import TauCeti.Topology.Order.Interval.Basic

/-!
# Additive interval functions as sums of jumps

Let `F s t` be a function of the subintervals `[s, t]` of `[a, b]` in a densely ordered order
topology, which adds over adjacent subintervals, `F s t = F s m + F m t`, and vanishes over every
subinterval avoiding a set of exceptional points. If at each exceptional point `s` the value
`F t₁ t₂` equals a fixed jump `g s` for all `t₁` just below and `t₂` just above `s`, then `F a b` is
the sum of the jumps, provided the exceptional points are finitely many and lie in `(a, b)`.

The exceptional points are indeed finitely many when the property `p` defining the ordinary
points holds at `a` and `b`, holds near each point of `[a, b]` where it holds, and holds on a
punctured neighbourhood of each point of `(a, b)` where it fails.

This is the combinatorial step of the regular-crossing formula for the spectral flow, where `F` is
the spectral flow, the exceptional points are the crossings and the jumps are the signatures of the
crossing forms.

## Main results

* `TauCeti.finite_setOf_not_of_eventually`: the points of `[a, b]` at which a property fails are
  finitely many if they are isolated and the property is open in `[a, b]` where it holds.
* `TauCeti.eq_sum_of_eventually_eq_of_add`: `F a b` is the sum of the jumps over a finite set of
  exceptional points in `(a, b)`.
* `TauCeti.eq_finsum_of_eventually_eq_of_add`: `F a b` is the sum of the jumps over `(a, b)`, for
  jumps vanishing off the finitely many points at which a property fails.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- **Isolated failures of an open property in `[a, b]` are finitely many.** Let `p` hold at `a`
and `b`, hold near each point of `[a, b]` (within `[a, b]`) at which it holds, and hold on a
punctured neighbourhood of each point of `(a, b)` at which it fails. Then `p` fails at only
finitely many points of `[a, b]`. -/
theorem finite_setOf_not_of_eventually {α : Type*} [PartialOrder α] [TopologicalSpace α]
    [CompactIccSpace α] {p : α → Prop} {a b : α} (ha : p a) (hb : p b)
    (hopen : ∀ z ∈ Icc a b, p z → ∀ᶠ t in 𝓝[Icc a b] z, p t)
    (hiso : ∀ z ∈ Ioo a b, ¬p z → ∀ᶠ t in 𝓝[≠] z, p t) :
    {t ∈ Icc a b | ¬p t}.Finite := by
  rw [← inter_ofPred_eq_sep, ← compl_ofPred, ← sdiff_eq]
  -- The points of `[a, b]` at which `p` holds are codiscrete in the compact interval `[a, b]`.
  refine isCompact_Icc.finite_sdiff_of_mem_codiscreteWithin <|
    mem_codiscreteWithin_iff_forall_mem_nhdsNE.2 fun z hz ↦ ?_
  suffices h : ∀ᶠ t in 𝓝[≠] z, t ∈ Icc a b → p t from
    mem_of_superset h fun t ht ↦ (em (t ∈ Icc a b)).imp ht id
  by_cases hpz : p z
  · exact nhdsWithin_le_nhds (eventually_nhdsWithin_iff.1 (hopen z hz hpz))
  · exact (hiso z (mem_Ioo_of_mem_Icc_of_not p ha hb hz hpz) hpz).mono fun _ ht _ ↦ ht

variable {α M : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
  [AddCommMonoid M] {F : α → α → M} {g : α → M} {a b : α}

/-- **An additive interval function is the sum of its jumps.** Let `F s t` add over adjacent
subintervals of `[a, b]` and vanish over every subinterval of `[a, b]` avoiding a finite set
`S ⊆ (a, b)`. If at each `s ∈ S`, `F t₁ t₂ = g s` for all `t₁` just below and `t₂` just above `s`,
then `F a b` is the sum of the jumps `g s` over `s ∈ S`. -/
theorem eq_sum_of_eventually_eq_of_add (S : Finset α) (hab : a ≤ b) (hS : ∀ s ∈ S, s ∈ Ioo a b)
    (hadd : ∀ ⦃s m t⦄, a ≤ s → s ≤ m → m ≤ t → t ≤ b → F s t = F s m + F m t)
    (hzero : ∀ ⦃s t⦄, a ≤ s → s ≤ t → t ≤ b → (∀ u ∈ S, u ∉ Icc s t) → F s t = 0)
    (hjump : ∀ s ∈ S, ∀ᶠ t₁ in 𝓝[<] s, ∀ᶠ t₂ in 𝓝[>] s, F t₁ t₂ = g s) :
    F a b = ∑ s ∈ S, g s := by
  classical
  induction S using Finset.induction_on_max generalizing b with
  | empty => simpa using hzero le_rfl hab le_rfl (by simp)
  | insert s S hlt ih =>
    obtain ⟨has, hsb⟩ := hS s (Finset.mem_insert_self s S)
    have : (𝓝[<] s).NeBot := nhdsLT_neBot_of_exists_lt ⟨a, has⟩
    have : (𝓝[>] s).NeBot := nhdsGT_neBot_of_exists_gt ⟨b, hsb⟩
    -- Choose `t₁ < s < t₂`, with `t₁` above every other point of `S`, such that `F t₁ t₂` is the
    -- jump at `s`.
    have hleft : ∀ᶠ t in 𝓝[<] s, t ∈ Ioo a s ∧ ∀ x ∈ S, x < t :=
      (eventually_mem_set.2 (Ioo_mem_nhdsLT has)).and <| (eventually_all_finset S).2 fun x hx ↦
        (eventually_mem_set.2 (Ioo_mem_nhdsLT (hlt x hx))).mono fun t ht ↦ ht.1
    obtain ⟨t₁, ⟨⟨hat₁, ht₁s⟩, hSt₁⟩, hjump₁⟩ :=
      (hleft.and (hjump s (Finset.mem_insert_self s S))).exists
    obtain ⟨t₂, ⟨hst₂, ht₂b⟩, hjump₂⟩ :=
      ((eventually_mem_set.2 (Ioo_mem_nhdsGT hsb)).and hjump₁).exists
    have ht₁b : t₁ ≤ b := (ht₁s.trans hsb).le
    have ht₁t₂ : t₁ ≤ t₂ := (ht₁s.trans hst₂).le
    -- Every point of `S` lies below `s`, so `[t₂, b]` avoids all of them.
    have hright : F t₂ b = 0 := hzero (has.trans hst₂).le ht₂b.le le_rfl fun u hu hu' ↦ by
      have hus : u ≤ s := by
        rcases Finset.mem_insert.1 hu with rfl | hu
        exacts [le_rfl, (hlt u hu).le]
      exact (hus.trans_lt hst₂).not_ge hu'.1
    -- Over `[a, t₁]` the exceptional points are those of `S`, and the induction hypothesis applies.
    have hinit : F a t₁ = ∑ x ∈ S, g x :=
      ih hat₁.le (fun x hx ↦ ⟨(hS x (Finset.mem_insert_of_mem hx)).1, hSt₁ x hx⟩)
        (fun _ _ _ h₁ h₂ h₃ h₄ ↦ hadd h₁ h₂ h₃ (h₄.trans ht₁b))
        (fun _ _ h₁ h₂ h₃ hS' ↦ hzero h₁ h₂ (h₃.trans ht₁b) fun u hu hu' ↦ by
          rcases Finset.mem_insert.1 hu with rfl | hu
          exacts [((hu'.2.trans h₃).trans_lt ht₁s).false, hS' u hu hu'])
        fun x hx ↦ hjump x (Finset.mem_insert_of_mem hx)
    rw [hadd le_rfl (hat₁.le.trans ht₁t₂) ht₂b.le le_rfl, hadd le_rfl hat₁.le ht₁t₂ ht₂b.le, hinit,
      hjump₂, hright, add_zero, Finset.sum_insert fun h ↦ (hlt s h).false, add_comm]

/-- **An additive interval function is the sum of its jumps over `(a, b)`.** Let `p` hold at `a`
and `b` and fail at only finitely many points of `[a, b]`. Let `F s t` add over adjacent
subintervals of `[a, b]` and vanish over every subinterval of `[a, b]` on which `p` holds. If at
each `s ∈ (a, b)` at which `p` fails, `F t₁ t₂ = g s` for all `t₁` just below and `t₂` just above
`s`, and `g` vanishes where `p` holds, then `F a b = ∑ᶠ t ∈ (a, b), g t`. -/
theorem eq_finsum_of_eventually_eq_of_add {p : α → Prop} (hab : a ≤ b)
    (hfin : {t ∈ Icc a b | ¬p t}.Finite) (ha : p a) (hb : p b)
    (hadd : ∀ ⦃s m t⦄, a ≤ s → s ≤ m → m ≤ t → t ≤ b → F s t = F s m + F m t)
    (hzero : ∀ ⦃s t⦄, a ≤ s → s ≤ t → t ≤ b → (∀ u ∈ Icc s t, p u) → F s t = 0)
    (hjump : ∀ s ∈ Ioo a b, ¬p s → ∀ᶠ t₁ in 𝓝[<] s, ∀ᶠ t₂ in 𝓝[>] s, F t₁ t₂ = g s)
    (hg : ∀ t ∈ Ioo a b, p t → g t = 0) :
    F a b = ∑ᶠ t ∈ Ioo a b, g t := by
  have hS : ∀ t, t ∈ hfin.toFinset ↔ t ∈ Icc a b ∧ ¬p t := by simp
  have hIoo : ∀ t ∈ hfin.toFinset, t ∈ Ioo a b := fun t ht ↦
    mem_Ioo_of_mem_Icc_of_not p ha hb ((hS t).1 ht).1 ((hS t).1 ht).2
  rw [eq_sum_of_eventually_eq_of_add hfin.toFinset hab hIoo hadd
    (fun s t has hst htb hS' ↦ hzero has hst htb fun u hu ↦ not_not.1 fun hpu ↦
      hS' u ((hS u).2 ⟨⟨has.trans hu.1, hu.2.trans htb⟩, hpu⟩) hu)
    fun s hs ↦ hjump s (hIoo s hs) ((hS s).1 hs).2]
  refine (finsum_mem_eq_sum_of_inter_support_eq _ ?_).symm
  ext t
  simp only [mem_inter_iff, Finset.mem_coe, Function.mem_support]
  refine and_congr_left fun hgt ↦ ⟨fun ht ↦ (hS t).2 ⟨Ioo_subset_Icc_self ht, fun hpt ↦
    hgt (hg t ht hpt)⟩, hIoo t⟩

end TauCeti

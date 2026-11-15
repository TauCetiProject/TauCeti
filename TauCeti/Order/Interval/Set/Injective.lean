/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Monotone.Defs

/-!
# Injectivity on order intervals

A function on a linear order which is injective on `Iic a`, `Icc a b` and `Ici b`, sends the two
outer pieces into disjoint sets, and meets those sets inside `Icc a b` only at the endpoint values,
is injective.

If a function is injective on `Ico a b` and has equal endpoint values, its value at a point
of `Ioo a b` is attained nowhere else on `Icc a b`.

## Main results

* `Set.InjOn.eq_of_mem_Ioo_of_mem_Icc`: uniqueness of values at points of an open interval.
* `TauCeti.injective_of_injOn_Iic_Icc_Ici`: injectivity from the three injective pieces.
-/

public section

open Set

/-- If `γ` is injective on `Ico a b` and `γ a = γ b`, then any `t ∈ Icc a b` with
`γ t = γ t₀` for `t₀ ∈ Ioo a b` equals `t₀`. -/
theorem Set.InjOn.eq_of_mem_Ioo_of_mem_Icc {ι α : Type*} [PartialOrder ι]
    {γ : ι → α} {a b t₀ t : ι}
    (hinj : InjOn γ (Ico a b)) (hclosed : γ a = γ b) (ht₀ : t₀ ∈ Ioo a b) (ht : t ∈ Icc a b)
    (heq : γ t = γ t₀) : t = t₀ := by
  rcases ht.2.eq_or_lt with rfl | htb
  · exact absurd (hinj ⟨le_rfl, ht₀.1.trans ht₀.2⟩ (Ioo_subset_Ico_self ht₀) (hclosed.trans heq))
      ht₀.1.ne
  · exact hinj ⟨ht.1, htb⟩ (Ioo_subset_Ico_self ht₀) heq

namespace TauCeti

/-- **Injectivity from three injective pieces.** Let `f` be injective on each of `Iic a`, `Icc a b`
and `Ici b`, with `a ≤ b`. If `f` maps `Iic a` into `S` and `Ici b` into `T` with `S` and `T`
disjoint, and a point of `Icc a b` mapped into `S` (respectively `T`) has the value `f a`
(respectively `f b`), then `f` is injective. -/
theorem injective_of_injOn_Iic_Icc_Ici {ι X : Type*} [LinearOrder ι] {f : ι → X} {a b : ι}
    {S T : Set X} (hab : a ≤ b) (hl : InjOn f (Iic a)) (hm : InjOn f (Icc a b))
    (hr : InjOn f (Ici b)) (hS : ∀ x ≤ a, f x ∈ S) (hT : ∀ x, b ≤ x → f x ∈ T)
    (hST : Disjoint S T) (hSa : ∀ y ∈ Icc a b, f y ∈ S → f y = f a)
    (hTb : ∀ y ∈ Icc a b, f y ∈ T → f y = f b) : Function.Injective f := by
  apply Function.Injective.of_lt_imp_ne
  intro x y hxy heq
  by_cases hy₀ : y ≤ a
  · exact hxy.ne (hl (hxy.le.trans hy₀) hy₀ heq)
  by_cases hxn : b ≤ x
  · exact hxy.ne (hr hxn (hxn.trans hxy.le) heq)
  have hya := lt_of_not_ge hy₀
  have hxb := lt_of_not_ge hxn
  by_cases hx₀ : x ≤ a
  · by_cases hyn : b ≤ y
    · exact Set.disjoint_left.mp hST (hS x hx₀) (heq ▸ hT y hyn)
    · have hy := hSa y ⟨hya.le, (lt_of_not_ge hyn).le⟩ (heq ▸ hS x hx₀)
      exact hya.ne' (hm ⟨hya.le, (lt_of_not_ge hyn).le⟩ ⟨le_rfl, hab⟩ hy)
  · by_cases hyn : b ≤ y
    · have hx := hTb x ⟨(lt_of_not_ge hx₀).le, hxb.le⟩ (heq ▸ hT y hyn)
      exact hxb.ne (hm ⟨(lt_of_not_ge hx₀).le, hxb.le⟩ ⟨hab, le_rfl⟩ hx)
    · exact hxy.ne (hm ⟨(lt_of_not_ge hx₀).le, hxb.le⟩ ⟨hya.le, (lt_of_not_ge hyn).le⟩ heq)

end TauCeti

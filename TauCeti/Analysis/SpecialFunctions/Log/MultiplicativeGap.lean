/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Set.Card

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

/-!
# Counting points with a multiplicative gap in a window

Let `X > 0` and `ρ > 1`. If `x₀ < x₁ < ⋯ < x_{k - 1}` are real numbers in the window `(X, A X]`
and each is at least `ρ` times the previous one, then `ρ ^ (k - 1) X < x_{k - 1} ≤ A X`, so that
`k ≤ ⌈log A / log ρ⌉`. The number of points does not depend on `X`, only on the width `A` of the
window measured on the logarithmic scale.

This is how a gap principle becomes a count. In Diophantine approximation the points are the
heights of the solutions of an inequality, which are sorted into finitely many classes, and a gap
principle says that two distinct solutions in one class have heights at least a factor `ρ` apart.
The solutions in a window are then at most `⌈log A / log ρ⌉` times the number of classes.

## Main results

* `Finset.exists_pow_card_sub_one_mul_lt_of_gap`: the largest of `k` points above `X` with
  pairwise multiplicative gaps `ρ > 0` exceeds `ρ ^ (k - 1) X`.
* `Finset.card_le_ceil_of_gap`: at most `⌈log A / log ρ⌉` reals in `(X, A X]` with pairwise
  multiplicative gaps `ρ`.
* `Set.ncard_le_ceil_mul_ncard_of_gap`: the same count for points of any type, measured by a
  real function `h` and sorted by a labelling `c`, with gaps between points of one label only.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), Lemma 6.5.6.
* `Set.ncard_le_ceil_mul_ncard_of_gap` follows the lemma of the same name in Ralf Stephan's
  formalization `DiophantineApproximation/CountingApproximations.lean` in `rwst/Subspace-Theorems`
  at `09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0).
-/

public section

open Real

namespace Finset

/-- The largest of `k` points above `X` with pairwise multiplicative gaps `ρ > 0` exceeds
`ρ ^ (k - 1) X`. -/
theorem exists_pow_card_sub_one_mul_lt_of_gap {t : Finset ℝ} {X ρ : ℝ} (hρ : 0 < ρ)
    (ht : ∀ x ∈ t, X < x) (hgap : ∀ x ∈ t, ∀ y ∈ t, x < y → ρ * x ≤ y) (hne : t.Nonempty) :
    ∃ y ∈ t, ρ ^ (#t - 1) * X < y := by
  classical
  induction t using Finset.induction_on_max with
  | empty => exact absurd hne (by simp)
  | insert a s hlt ih =>
    have has : a ∉ s := fun h ↦ (hlt a h).false
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨a, mem_insert_self a ∅, by simpa using ht a (mem_insert_self a ∅)⟩
    obtain ⟨y, hy, hXy⟩ := ih (fun x hx ↦ ht x (mem_insert_of_mem hx))
      (fun x hx z hz ↦ hgap x (mem_insert_of_mem hx) z (mem_insert_of_mem hz)) hs
    refine ⟨a, mem_insert_self a s, ?_⟩
    have hya := hgap y (mem_insert_of_mem hy) a (mem_insert_self a s) (hlt y hy)
    rw [card_insert_of_notMem has, Nat.add_sub_cancel,
      ← Nat.sub_add_cancel (one_le_card.mpr hs), pow_succ', mul_assoc]
    exact (mul_lt_mul_of_pos_left hXy hρ).trans_le hya

/-- **Points with a multiplicative gap in a window.** Real numbers in `(X, A X]`, with `X > 0`,
any two of which differ by a factor at least `ρ > 1`, number at most `⌈log A / log ρ⌉`. -/
theorem card_le_ceil_of_gap {t : Finset ℝ} {X A ρ : ℝ} (hX : 0 < X) (hρ : 1 < ρ)
    (ht : ∀ x ∈ t, x ∈ Set.Ioc X (A * X)) (hgap : ∀ x ∈ t, ∀ y ∈ t, x < y → ρ * x ≤ y) :
    #t ≤ ⌈log A / log ρ⌉₊ := by
  rcases t.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨y, hy, hXy⟩ := exists_pow_card_sub_one_mul_lt_of_gap (zero_lt_one.trans hρ)
    (fun x hx ↦ (ht x hx).1) hgap hne
  have hpow : ρ ^ (#t - 1) < A := lt_of_mul_lt_mul_right (hXy.trans_le (ht y hy).2) hX.le
  have hlog : ((#t - 1 : ℕ) : ℝ) < log A / log ρ := by
    rw [lt_div_iff₀ (log_pos hρ), ← log_pow]
    exact log_lt_log (pow_pos (zero_lt_one.trans hρ) _) hpow
  have := Nat.lt_ceil.mpr hlog
  omega

end Finset

namespace Set

/-- **Counting by classes with a multiplicative gap.** Let `h` measure the points of `s` in the
window `(X, A X]`, with `X > 0`, and let `c` sort them into classes. If two distinct points of one
class always have values at least a factor `ρ > 1` apart, then the number of points of `s` is at
most `⌈log A / log ρ⌉` times the number `(c '' s).ncard` of classes. The bound is stated with
`Set.ncard`, which is `0` on infinite sets, so it says nothing when `s` or `c '' s` is infinite. -/
theorem ncard_le_ceil_mul_ncard_of_gap {ι γ : Type*} {s : Set ι} (h : ι → ℝ) (c : ι → γ)
    {X A ρ : ℝ} (hX : 0 < X) (hρ : 1 < ρ) (hs : ∀ x ∈ s, h x ∈ Ioc X (A * X))
    (hgap : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → c x = c y → h x ≤ h y → ρ * h x ≤ h y) :
    s.ncard ≤ ⌈log A / log ρ⌉₊ * (c '' s).ncard := by
  classical
  rcases s.finite_or_infinite with hfin | hinf
  swap
  · simp [hinf.ncard]
  lift s to Finset ι using hfin
  rw [ncard_coe_finset, ← Finset.coe_image, ncard_coe_finset]
  refine Finset.card_le_mul_card_image s _ fun b _ ↦ ?_
  set u := {a ∈ s | c a = b}
  have hu {x} (hx : x ∈ u) : x ∈ s ∧ c x = b := Finset.mem_filter.mp hx
  -- Two distinct points of one class have distinct values, since a value is positive.
  have hinj : InjOn h u := by
    intro x hx y hy hxy
    by_contra hne
    have hpos : 0 < h x := hX.trans (hs x (hu hx).1).1
    have := hgap x (hu hx).1 y (hu hy).1 hne ((hu hx).2.trans (hu hy).2.symm) hxy.le
    nlinarith
  rw [← Finset.card_image_of_injOn hinj]
  refine Finset.card_le_ceil_of_gap hX hρ ?_ ?_
  · simp only [Finset.mem_image]
    rintro _ ⟨x, hx, rfl⟩
    exact hs x (hu hx).1
  · simp only [Finset.mem_image]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hlt
    exact hgap x (hu hx).1 y (hu hy).1 (fun he ↦ hlt.ne (he ▸ rfl))
      ((hu hx).2.trans (hu hy).2.symm) hlt.le

end Set

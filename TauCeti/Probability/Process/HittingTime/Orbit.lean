/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Probability.Process.HittingTime
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Hitting times of deterministic iterate and cyclic orbits

This module evaluates `MeasureTheory.hittingAfter` for the coordinate process on `ℕ → β` along
deterministic trajectories:

* Along the forward iterate trajectory `n ↦ f^[n] x`, the first positive return time (`≥ 1`) to
  `{x}` is `Function.minimalPeriod f x` when `x ∈ Function.periodicPts f` and `⊤` otherwise
  (`MeasureTheory.hittingAfter_one_iterate`).
* Along the cyclic trajectory `k ↦ x + (k : Fin n)` on `Fin n` (`n ≠ 0`), the first entrance
  time (`≥ 0`) to `{y}` is `(y - x).val` (`MeasureTheory.hittingAfter_zero_add_natCast`), and the
  first positive-time visit (`≥ 1`) to `{y}` is `n` when `y = x` and `(y - x).val` when `y ≠ x`
  (`MeasureTheory.hittingAfter_one_add_natCast`).

## Main statements

* `MeasureTheory.hittingAfter_one_iterate`
* `MeasureTheory.hittingAfter_zero_add_natCast`
* `MeasureTheory.hittingAfter_one_add_natCast`
-/

public section

open scoped Fin.NatCast

namespace MeasureTheory

open scoped Classical in
/-- Along the forward iterate trajectory `n ↦ f^[n] x`, the first positive return time to `x` is
`Function.minimalPeriod f x` when `x` is a periodic point of `f`, and `⊤` otherwise. -/
@[simp]
theorem hittingAfter_one_iterate {β : Type*} (f : β → β) (x : β) :
    hittingAfter (fun n (w : ℕ → β) => w n) {x} 1 (fun n => f^[n] x) =
      if x ∈ Function.periodicPts f then (Function.minimalPeriod f x : WithTop ℕ) else ⊤ := by
  have hex :
      (∃ j : ℕ, 1 ≤ j ∧ f^[j] x ∈ ({x} : Set β)) ↔ x ∈ Function.periodicPts f := by
    simp [Function.mem_periodicPts, Nat.pos_iff_ne_zero, Nat.one_le_iff_ne_zero,
      Function.IsPeriodicPt, Function.IsFixedPt]
  have hset : {i : ℕ | 1 ≤ i ∧ f^[i] x ∈ ({x} : Set β)} =
      {n : ℕ | 0 < n ∧ Function.IsPeriodicPt f n x} := by
    ext i
    simp [Nat.pos_iff_ne_zero, Nat.one_le_iff_ne_zero, Function.IsPeriodicPt, Function.IsFixedPt]
  rw [hittingAfter_def]
  dsimp only
  by_cases hx : x ∈ Function.periodicPts f
  · rw [ite_eq_left (hex.mpr hx), ite_eq_left hx, hset,
      ← Function.minimalPeriod_eq_sInf_n_pos_IsPeriodicPt]
    exact (Nat.cast_withTop _).symm
  · rw [ite_eq_right (mt hex.mp hx), ite_eq_right hx]

/-- Along the cyclic trajectory `k ↦ x + k` on `Fin n`, the first entrance time to `y` is
`(y - x).val`. -/
@[simp]
theorem hittingAfter_zero_add_natCast {n : ℕ} [NeZero n] (x y : Fin n) :
    hittingAfter (fun k (ω : ℕ → Fin n) => ω k) {y} 0 (fun k : ℕ => x + (k : Fin n)) =
      ((y - x).val : WithTop ℕ) := by
  refine le_antisymm (hittingAfter_le_of_mem (Nat.zero_le _) (by simp)) ?_
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨j, ⟨_, hjlt⟩, hmem⟩ :=
    hittingAfter_lt_iff.mp (Nat.cast_withTop (y - x).val ▸ hlt)
  rw [Set.mem_singleton_iff] at hmem
  have hjeq : (j : Fin n) = y - x := eq_sub_iff_add_eq'.mpr hmem
  have hjval : (j : Fin n).val = j := Nat.mod_eq_of_lt (hjlt.trans (y - x).isLt)
  exact hjlt.ne (hjval.symm.trans (congrArg Fin.val hjeq))

/-- Along the cyclic trajectory `k ↦ x + k` on `Fin n`, the first positive-time visit to `y` is
`n` when `y = x`, and `(y - x).val` when `y ≠ x`. -/
@[simp]
theorem hittingAfter_one_add_natCast {n : ℕ} [NeZero n] (x y : Fin n) :
    hittingAfter (fun k (ω : ℕ → Fin n) => ω k) {y} 1 (fun k : ℕ => x + (k : Fin n)) =
      if y = x then (n : WithTop ℕ) else ((y - x).val : WithTop ℕ) := by
  by_cases hyx : y = x
  · subst hyx
    have hfun :
        (fun k : ℕ => y + (k : Fin n)) = (fun k : ℕ => (fun z : Fin n => z + 1)^[k] y) := by
      funext k
      simp [add_right_iterate, nsmul_one]
    have hperPt : Function.IsPeriodicPt (fun z : Fin n => z + 1) n y := by
      simp [Function.IsPeriodicPt, Function.IsFixedPt, add_right_iterate, nsmul_one]
    have hper : y ∈ Function.periodicPts (fun z : Fin n => z + 1) :=
      Function.mk_mem_periodicPts (NeZero.pos n) hperPt
    have hmin : Function.minimalPeriod (fun z : Fin n => z + 1) y = n := by
      apply Nat.dvd_antisymm hperPt.minimalPeriod_dvd
      have hfix := Function.iterate_minimalPeriod (f := fun z : Fin n => z + 1) (x := y)
      simp only [add_right_iterate, nsmul_one, add_eq_left, Fin.natCast_eq_zero] at hfix
      exact hfix
    rw [hfun, hittingAfter_one_iterate, ite_eq_left hper, hmin, ite_eq_left rfl]
  · rw [ite_eq_right hyx]
    have h1 : 1 ≤ (y - x).val :=
      Nat.one_le_iff_ne_zero.mpr (Fin.val_ne_zero_iff.mpr (sub_ne_zero.mpr hyx))
    exact le_antisymm (hittingAfter_le_of_mem h1 (by simp))
      (hittingAfter_zero_add_natCast x y ▸ hittingAfter_apply_mono _ {y} _ (Nat.zero_le 1))

end MeasureTheory

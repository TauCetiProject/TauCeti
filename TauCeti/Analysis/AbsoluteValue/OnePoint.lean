/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import TauCeti.Topology.Compactification.OnePoint.SubInv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Local approximation to finite targets and infinity

`AbsoluteValue.onePointApprox w β t` is the truncated local approximation factor for a target
`t : OnePoint F`: it is `min 1 (w (β - a))` at a finite target `a`, and
`(max 1 (w β))⁻¹` at infinity. In particular the factor at infinity is `1`, not `0`, at `β = 0`.

The change of variable `β ↦ (β - c)⁻¹`, with `c` different from every finite target, turns each
target `t` into the finite target `t.subInv c`. The theorem
`AbsoluteValue.exists_pos_forall_min_one_sub_inv_sub_le` bounds its local distortion by a positive
constant independent of `β`. The finite-product version handles
several absolute values and their multiplicities at once. These estimates allow finiteness
results for approximation to finite targets to be transported to targets at infinity.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, §6.2, especially (6.2.5).
-/

public section

open scoped OnePoint

namespace AbsoluteValue

variable {F : Type*}

section Ring

variable [Ring F]

/-- The truncated approximation factor at a finite target, or at infinity. -/
noncomputable def onePointApprox (w : AbsoluteValue F ℝ) (β : F) (t : OnePoint F) : ℝ :=
  t.elim (max 1 (w β))⁻¹ fun a ↦ min 1 (w (β - a))

/-- At a finite target, the approximation factor is the truncated absolute value of the error. -/
@[simp]
theorem onePointApprox_coe (w : AbsoluteValue F ℝ) (β a : F) :
    w.onePointApprox β (a : OnePoint F) = min 1 (w (β - a)) := (rfl)

/-- At infinity, use the reciprocal of the maximum, including when `β = 0`. -/
@[simp]
theorem onePointApprox_infty (w : AbsoluteValue F ℝ) (β : F) :
    w.onePointApprox β ∞ = (max 1 (w β))⁻¹ := (rfl)

/-- Every local approximation factor is nonnegative. -/
theorem onePointApprox_nonneg (w : AbsoluteValue F ℝ) (β : F) (t : OnePoint F) :
    0 ≤ w.onePointApprox β t := by
  induction t using OnePoint.rec <;> simp [le_max_iff, w.nonneg, onePointApprox]

/-- Every local approximation factor is at most one. -/
theorem onePointApprox_le_one (w : AbsoluteValue F ℝ) (β : F) (t : OnePoint F) :
    w.onePointApprox β t ≤ 1 := by
  induction t using OnePoint.rec with
  | infty => exact inv_le_one_of_one_le₀ (le_max_left _ _)
  | coe a => exact min_le_left _ _

/-- The local factor vanishes exactly at a finite target equal to the approximating point. -/
@[simp]
theorem onePointApprox_eq_zero_iff (w : AbsoluteValue F ℝ) (β : F) (t : OnePoint F) :
    w.onePointApprox β t = 0 ↔ t = (β : OnePoint F) := by
  induction t using OnePoint.rec with
  | infty => simp [ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 (w β)))]
  | coe a =>
    simp only [onePointApprox_coe, min_eq_iff, one_ne_zero, false_and, false_or,
      OnePoint.coe_eq_coe, w.map_sub_eq_zero_iff]
    constructor
    · exact fun h ↦ h.1.symm
    · rintro rfl
      simp

/-- Away from the approximating point, the local factor is strictly positive. -/
@[simp]
theorem onePointApprox_pos_iff (w : AbsoluteValue F ℝ) (β : F) (t : OnePoint F) :
    0 < w.onePointApprox β t ↔ t ≠ (β : OnePoint F) := by
  rw [lt_iff_le_and_ne, and_iff_right (w.onePointApprox_nonneg β t), ne_comm,
    ne_eq, w.onePointApprox_eq_zero_iff]

end Ring

section DivisionRing

variable [DivisionRing F]

/-- Inversion has uniformly bounded distortion for truncated errors near a fixed nonzero target.
No nonvanishing hypothesis on `x` is needed, even with the convention `0⁻¹ = 0`. -/
theorem exists_pos_forall_min_one_inv_sub_inv_le (w : AbsoluteValue F ℝ) {a : F}
    (ha : a ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : F, min 1 (w (x⁻¹ - a⁻¹)) ≤ C * min 1 (w (x - a)) := by
  have hA : 0 < w a := w.pos ha
  let C := max 1 (max (2 / w a) (2 / (w a) ^ 2))
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC2 : 2 / w a ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC3 : 2 / (w a) ^ 2 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, lt_of_lt_of_le zero_lt_one hC1, fun x ↦ ?_⟩
  by_cases hd1 : 1 ≤ w (x - a)
  · rw [min_eq_left hd1]
    exact (min_le_left _ _).trans (by simpa using hC1)
  rw [min_eq_right (le_of_not_ge hd1)]
  by_cases hd : w a / 2 ≤ w (x - a)
  · have h := (div_le_iff₀ hA).mp hC2
    nlinarith [min_le_left 1 (w (x⁻¹ - a⁻¹)),
      mul_le_mul_of_nonneg_left hd (le_trans zero_le_one hC1)]
  have hx : w a / 2 ≤ w x := by
    have := w.le_sub a x
    rw [w.map_sub a x] at this
    linarith
  have hx0 : x ≠ 0 := by
    intro h
    simp only [h, map_zero] at hx
    linarith
  have hden : 0 < w x * w a := mul_pos (w.pos hx0) hA
  have hinv : w (x⁻¹ - a⁻¹) = w (x - a) / (w x * w a) := by
    rw [inv_sub_inv' hx0 ha, map_mul, map_mul, map_inv₀, map_inv₀, w.map_sub a x]
    ring
  have hsmall : w (x - a) / (w x * w a) ≤ (2 / (w a) ^ 2) * w (x - a) := by
    rw [div_le_iff₀ hden]
    have hmul : (w a) ^ 2 / 2 ≤ w x * w a := by nlinarith
    have h := mul_le_mul_of_nonneg_left hmul (w.nonneg (x - a))
    field_simp
    nlinarith
  exact (min_le_right _ _).trans (hinv ▸ hsmall.trans
    (mul_le_mul_of_nonneg_right hC3 (w.nonneg (x - a))))

/-- Translating and inverting sends infinity to the finite target zero, with bounded local
approximation distortion. -/
theorem min_one_inv_sub_le_onePointApprox_infty (w : AbsoluteValue F ℝ) (β c : F) :
    min 1 (w ((β - c)⁻¹)) ≤ (1 + w c) * w.onePointApprox β ∞ := by
  rw [onePointApprox_infty]
  have htri : w β ≤ w (β - c) + w c := by
    simpa using w.sub_le β c 0
  have hC : 0 < 1 + w c := by linarith [w.nonneg c]
  by_cases hβ : β = c
  · simp [hβ, le_of_lt hC]
  have hB : 0 < w (β - c) := w.pos (sub_ne_zero.mpr hβ)
  have hmax : 0 < max 1 (w β) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [map_inv₀]
  by_cases h : w (β - c) ≤ 1
  · have hm : max 1 (w β) ≤ 1 + w c := max_le (by linarith [w.nonneg c]) (by linarith)
    apply (min_le_left _ _).trans
    rw [← div_eq_mul_inv, le_div_iff₀ hmax]
    simpa using hm
  · have hm : max 1 (w β) ≤ (1 + w c) * w (β - c) := by
      apply max_le <;> nlinarith [w.nonneg c]
    apply (min_le_right _ _).trans
    rw [← div_eq_mul_inv, le_div_iff₀ hmax, inv_mul_le_iff₀' hB]
    exact hm

/-- The Möbius change of variable `β ↦ (β - c)⁻¹` turns a target different from `c` into a
finite target with bounded local distortion. Its new target is zero at infinity and
`(a - c)⁻¹` at a finite target `a`; the bound is uniform in `β`. -/
theorem exists_pos_forall_min_one_sub_inv_sub_le (w : AbsoluteValue F ℝ) (c : F)
    (t : OnePoint F) (ht : t ≠ (c : OnePoint F)) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : F,
      min 1 (w ((β - c)⁻¹ - t.subInv c)) ≤ C * w.onePointApprox β t := by
  induction t using OnePoint.rec with
  | infty =>
    exact ⟨1 + w c, by linarith [w.nonneg c], fun β ↦ by
      simpa using w.min_one_inv_sub_le_onePointApprox_infty β c⟩
  | coe a =>
    obtain ⟨C, hC, h⟩ := w.exists_pos_forall_min_one_inv_sub_inv_le
      (sub_ne_zero.mpr (fun h ↦ ht (congrArg OnePoint.some h)))
    exact ⟨C, hC, fun β ↦ by simpa using h (β - c)⟩

/-- A finite weighted product of local approximation factors has bounded distortion under one
translation and inversion. The bound is independent of the approximating point. -/
theorem exists_pos_forall_prod_min_one_sub_inv_sub_le {ι : Type*} [Fintype ι]
    (w : ι → AbsoluteValue F ℝ) (c : F) (t : ι → OnePoint F) (m : ι → ℕ)
    (ht : ∀ i, t i ≠ (c : OnePoint F)) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : F,
      (∏ i, min 1 (w i ((β - c)⁻¹ - (t i).subInv c)) ^ m i) ≤
        C * ∏ i, (w i).onePointApprox β (t i) ^ m i := by
  classical
  choose C hC h using fun i ↦
    (w i).exists_pos_forall_min_one_sub_inv_sub_le c (t i) (ht i)
  refine ⟨∏ i, C i ^ m i, Finset.prod_pos (fun i _ ↦ pow_pos (hC i) _), fun β ↦ ?_⟩
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀
    (fun i _ ↦ pow_nonneg (le_min zero_le_one ((w i).nonneg _)) _)
    (fun i _ ↦ by simpa only [mul_pow] using
      pow_le_pow_left₀ (le_min zero_le_one ((w i).nonneg _)) (h i β) (m i))

end DivisionRing

/-- Infinity is not an exact target for the point zero. -/
example [Ring F] (w : AbsoluteValue F ℝ) : w.onePointApprox 0 ∞ = 1 := by
  simp

/-- Avoiding the finite target is necessary for a uniform inversion bound: inversion at zero
turns arbitrarily small nonzero errors into truncated errors equal to one. -/
example : ¬ ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, min 1 |β⁻¹| ≤ C * min 1 |β| := by
  rintro ⟨C, hC, h⟩
  have hp : 0 < C + 1 := by linarith
  have hi : 0 < (C + 1)⁻¹ := inv_pos.mpr hp
  have hi1 : (C + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hb := h (C + 1)⁻¹
  rw [inv_inv, abs_of_pos hp, abs_of_pos hi, min_eq_left (by linarith), min_eq_right hi1,
    le_mul_inv_iff₀ hp, one_mul] at hb
  linarith

end AbsoluteValue

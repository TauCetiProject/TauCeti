/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Archimedean valuations

This file records general lemmas for valuations whose value group with zero `v.ValueGroup₀` is
multiplicatively Archimedean (`MulArchimedean v.ValueGroup₀`): powers of a nonzero element with
valuation `< 1` make any element smaller than `1`, and two nontrivial rank-one valuations on a
division ring are equivalent as soon as one is bounded by `1` on the open unit ball of the other.

## Main results

* `Valuation.exists_pow_mul_lt_one`: for a valuation with Archimedean value group, powers of an
  element with `0 < w x < 1` make any element smaller than `1`.
* `Valuation.isEquiv_of_forall_lt_one_le_one`: two nontrivial valuations with Archimedean value
  groups on a division ring are equivalent if one is bounded by `1` on the open unit ball of the
  other.
-/

public section

namespace Valuation

section Ring

variable {R Γ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ]

/-- For a valuation with Archimedean value group, powers of any element with `0 < w x < 1` make
any element `y` smaller than `1`. -/
theorem exists_pow_mul_lt_one (w : Valuation R Γ) [MulArchimedean w.ValueGroup₀]
    {x : R} (hx0 : w x ≠ 0) (hx : w x < 1) (y : R) : ∃ n : ℕ, w (x ^ n * y) < 1 := by
  have hrx0 : w.restrict x ≠ 0 := by
    simpa only [ne_eq, Valuation.restrict_eq_zero_iff] using hx0
  have hrx1 : w.restrict x < 1 := by
    rw [← MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.lt_iff_lt, map_one,
      Valuation.restrict_def, MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀,
      coe_toMonoidWithZeroHom]
    exact hx
  have hxinv : 1 < (w.restrict x)⁻¹ := one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr hrx0, hrx1⟩
  obtain ⟨n, hn⟩ := MulArchimedean.arch (w.restrict y) hxinv
  refine ⟨n + 1, ?_⟩
  have hlt : w.restrict y < (w.restrict x)⁻¹ ^ (n + 1) :=
    hn.trans_lt (pow_lt_pow_right₀ hxinv n.lt_succ_self)
  have hpos : 0 < w.restrict x ^ (n + 1) := pow_pos (zero_lt_iff.mpr hrx0) _
  have hlt' : w.restrict (x ^ (n + 1) * y) < 1 := by
    rw [map_mul, map_pow]
    simpa [inv_pow, mul_inv_cancel₀ hpos.ne'] using mul_lt_mul_of_pos_left hlt hpos
  simpa only [map_one, Valuation.restrict_def,
    MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀, coe_toMonoidWithZeroHom] using
    MonoidWithZeroHom.ValueGroup₀.embedding_strictMono hlt'

end Ring

section DivisionRing

variable {K Γ₀ Γ : Type*} [DivisionRing K]
  [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ]

/-- Two nontrivial rank-one valuations on a division ring are equivalent as soon as one is bounded
by `1` on the open unit ball of the other. -/
theorem isEquiv_of_forall_lt_one_le_one (v : Valuation K Γ) [v.IsNontrivial]
    [MulArchimedean v.ValueGroup₀] (v₀ : Valuation K Γ₀) [v₀.IsNontrivial]
    [MulArchimedean v₀.ValueGroup₀] (hle : ∀ {y : K}, v₀ y < 1 → v y ≤ 1) :
    v.IsEquiv v₀ := by
  refine isEquiv_iff_val_lt_one.mpr fun {x} ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · -- If `v x < 1` and `1 ≤ v₀ x`, pick `a` with `0 < v₀ a < 1`. Large powers of `x⁻¹` make
    -- `v (a * x⁻¹ ^ n) > 1` while keeping `v₀ (a * x⁻¹ ^ n) ≤ v₀ a < 1`.
    by_contra hx1
    rw [not_lt] at hx1
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx1
    obtain ⟨a, ha0, ha1⟩ := IsNontrivial.exists_lt_one (v := v₀)
    obtain ⟨n, hn⟩ := exists_pow_mul_lt_one v (v.ne_zero_iff.mpr hx0) hx a⁻¹
    have hv0_lt : v₀ (a * x⁻¹ ^ n) < 1 := by
      rw [map_mul, map_pow, map_inv₀]
      exact (mul_le_of_le_one_right zero_le
        (pow_le_one₀ zero_le (inv_le_one_of_one_le₀ hx1))).trans_lt ha1
    have hpos : 0 < v (x ^ n * a⁻¹) :=
      zero_lt_iff.mpr (v.ne_zero_iff.mpr (mul_ne_zero (pow_ne_zero n hx0) (inv_ne_zero ha0)))
    have hv_gt : 1 < v (a * x⁻¹ ^ n) := by
      have heq : v (a * x⁻¹ ^ n) = (v (x ^ n * a⁻¹))⁻¹ := by
        simp [map_mul, map_pow, map_inv₀]
      rw [heq]
      exact one_lt_inv_iff₀.mpr ⟨hpos, hn⟩
    exact hv_gt.not_ge (hle hv0_lt)
  · -- If `v₀ x < 1` and `x ≠ 0` with `v x = 1`, pick `b` with `0 < v b < 1`. Large powers of `x`
    -- make `v₀ (x ^ n * b⁻¹) < 1` while `v (x ^ n * b⁻¹) = v b⁻¹ > 1`.
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    refine lt_of_le_of_ne (hle hx) fun hvx1 ↦ ?_
    obtain ⟨b, hb0, hb1⟩ := IsNontrivial.exists_lt_one (v := v)
    obtain ⟨n, hn⟩ := exists_pow_mul_lt_one v₀ (v₀.ne_zero_iff.mpr hx0) hx b⁻¹
    have hgt : 1 < v b⁻¹ := by
      rw [map_inv₀]
      exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr (v.ne_zero_iff.mpr hb0), hb1⟩
    have hv_eq : v (x ^ n * b⁻¹) = v b⁻¹ := by
      rw [map_mul, map_pow, hvx1, one_pow, one_mul]
    exact hgt.not_ge (hv_eq ▸ hle hn)

end DivisionRing

end Valuation

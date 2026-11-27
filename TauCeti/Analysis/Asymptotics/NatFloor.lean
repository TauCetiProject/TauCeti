/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# One-sided power bounds from integer samples

An upper bound on the integer samples of a function extends to large real arguments if the
increase from `⌊x⌋₊` to `x` is bounded by a multiple of `1/x`. A strictly larger exponent absorbs
both the interpolation error and the constant in the integer bound. This lets estimates for
normalized Riesz remainders at integer cutoffs give one-sided bounds at real cutoffs.

The application to prime remainders is `New.eventually_primeRemainder_le_rpow` in
`grh/src/New/Reduction/OneSidedBound.lean` of the shorter GRH formalization
(<https://github.com/lsernau/grh-lean>, commit `72fead102f663d5c7a407964a13dc0cf9d977207`).
-/

public section

open Asymptotics Filter
open scoped Nat

namespace TauCeti

/-- If on each sufficiently large unit interval the increase from the left endpoint `n` to `x`
is at most `L * (x - n) / n`, then the increase from `⌊x⌋₊` to `x` is eventually at most
`2 * |L| / x`. Only the upper bound on the increase is needed. -/
theorem eventually_sub_nat_floor_le_div {f : ℝ → ℝ} {L : ℝ}
    (h : ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, (n : ℝ) ≤ x → x < (n : ℝ) + 1 →
      f x - f n ≤ L * (x - n) / n) :
    ∀ᶠ x : ℝ in atTop, f x - f ⌊x⌋₊ ≤ 2 * |L| / x := by
  filter_upwards [(tendsto_nat_floor_atTop (α := ℝ)).eventually h,
    eventually_ge_atTop (2 : ℝ)] with x hx hx₂
  have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hgap := Nat.lt_floor_add_one x
  have hhalf : x / 2 ≤ (⌊x⌋₊ : ℝ) := by linarith
  calc
    _ ≤ L * (x - ⌊x⌋₊) / ⌊x⌋₊ := hx x hfloor hgap
    _ ≤ |L| / ⌊x⌋₊ := by
      gcongr
      calc
        L * (x - ⌊x⌋₊) ≤ |L| * (x - ⌊x⌋₊) := by gcongr; exact le_abs_self _
        _ ≤ |L| := mul_le_of_le_one_right (abs_nonneg _) (by linarith)
    _ ≤ |L| / (x / 2) := div_le_div_of_nonneg_left (abs_nonneg _) (by linarith) hhalf
    _ = 2 * |L| / x := by ring

/-- An eventual upper bound `C * n ^ β` at natural arguments gives the upper bound `x ^ α`
at large real arguments if the upward floor error is at most `D / x` and `α` exceeds both `β`
and `-1`. Neither the function nor the bounding constants need be nonnegative. -/
theorem eventually_le_rpow_of_nat_floor {f : ℝ → ℝ} {α β C D : ℝ}
    (hβα : β < α) (hα : -1 < α)
    (hn : ∀ᶠ n : ℕ in atTop, f n ≤ C * (n : ℝ) ^ β)
    (herr : ∀ᶠ x : ℝ in atTop, f x - f ⌊x⌋₊ ≤ D / x) :
    ∀ᶠ x : ℝ in atTop, f x ≤ x ^ α := by
  have hfloor : (fun x : ℝ ↦ (⌊x⌋₊ : ℝ) ^ β) =O[atTop] fun x ↦ x ^ β :=
    (isEquivalent_nat_floor.symm.rpow (fun _ ↦ Nat.cast_nonneg _) (r := β)).symm.isBigO
  have h₁ := (hfloor.trans_isLittleO (isLittleO_rpow_rpow_atTop hβα)).const_mul_left C
  have h₂ : (fun x : ℝ ↦ D / x) =o[atTop] fun x ↦ x ^ α := by
    simpa only [Real.rpow_neg_one, div_eq_mul_inv] using
      (isLittleO_rpow_rpow_atTop hα).const_mul_left D
  filter_upwards [(tendsto_nat_floor_atTop (α := ℝ)).eventually hn, herr,
    (h₁.add h₂).bound zero_lt_one, eventually_ge_atTop (0 : ℝ)] with x hnx hex hox hx
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hx _)] at hox
  calc
    f x ≤ f ⌊x⌋₊ + D / x := le_add_of_sub_left_le hex
    _ ≤ C * (⌊x⌋₊ : ℝ) ^ β + D / x := by gcongr
    _ ≤ x ^ α := (Real.le_norm_self _).trans hox

/-- An eventual power bound with arbitrary positive exponent loss is equivalent on real and
natural arguments, provided the upward floor error is `O(1/x)` in the one-sided sense and the
base exponent is at least `-1`. The constants in the bounds on natural arguments may depend on
the exponent loss. -/
theorem eventually_le_rpow_add_iff_natCast {f : ℝ → ℝ} {a D : ℝ} (ha : -1 ≤ a)
    (herr : ∀ᶠ x : ℝ in atTop, f x - f ⌊x⌋₊ ≤ D / x) :
    (∀ ε > 0, ∀ᶠ x : ℝ in atTop, f x ≤ x ^ (a + ε)) ↔
      (∀ ε > 0, ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, f n ≤ C * (n : ℝ) ^ (a + ε)) := by
  constructor
  · intro h ε hε
    exact ⟨1, by simpa only [one_mul] using (h ε hε).natCast_atTop⟩
  · intro h ε hε
    obtain ⟨C, hC⟩ := h (ε / 2) (half_pos hε)
    exact eventually_le_rpow_of_nat_floor (by linarith) (by linarith) hC herr

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
import TauCeti.Analysis.PSeries
import Mathlib.Order.Interval.Set.Nat

/-!
# Logarithmically weighted summability on sparse sets

A power saving in the counting function of a set of natural numbers suffices for convergence
of the series with weight `log n / n`. This lets one discard sparse exceptional sets from
families whose series with that weight diverges.
-/

public section

open Filter Asymptotics

namespace Set

/-- If the number of members of `S` up to `x` is `O(x ^ B)` for `B < 1`, then
`∑ n ∈ S, log n / n` converges. The term at zero is zero. -/
theorem summable_log_div_of_ncard_isBigO (S : Set ℕ) {B : ℝ} (hB : B < 1)
    (hcount : (fun x : ℝ ↦ ({n ∈ S | (n : ℝ) ≤ x}.ncard : ℝ)) =O[atTop] (· ^ B)) :
    Summable (fun n : S ↦ Real.log (n : ℝ) / (n : ℝ)) := by
  let p : ℝ := (max B 0 + 1) / 2
  have hp₀ : 0 ≤ p := by dsimp [p]; linarith [le_max_right B 0]
  have hp₁ : p < 1 := by dsimp [p]; linarith [max_lt hB zero_lt_one]
  have hBp : B < p := by dsimp [p]; linarith [le_max_left B 0, max_lt hB zero_lt_one]
  -- Clamping the radius at one preserves the large sublevel sets and includes the zero term.
  let r (n : S) : ℝ := max 1 (n : ℝ)
  have hfinite (x : ℝ) : {n : S | r n ≤ x}.Finite := by
    refine ((finite_Iic ⌊x⌋₊).preimage Subtype.val_injective.injOn).subset ?_
    intro n hn
    have hnx : (n : ℝ) ≤ x := (le_max_right _ _).trans hn
    exact Nat.le_floor (α := ℝ) hnx
  obtain ⟨C, -, hC⟩ := hcount.exists_nonneg
  have hsum := TauCeti.summable_mul_rpow_of_count_growth r (fun _ ↦ 1)
    (fun _ ↦ le_max_left _ _) (fun _ ↦ zero_le_one) hfinite hp₀ hBp (C := C) (by
      filter_upwards [hC.bound, eventually_ge_atTop (1 : ℝ)] with x hx hx₁
      let _ := (hfinite x).fintype
      let e : {n : S | r n ≤ x} ≃ {n ∈ S | (n : ℝ) ≤ x} :=
        (Equiv.subtypeEquivRight fun _ ↦ max_le_iff.trans (and_iff_right hx₁)).trans
          (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ S) fun n : ℕ ↦ (n : ℝ) ≤ x)
      simpa [tsum_fintype, ← Nat.card_eq_fintype_card, Nat.card_congr e,
        Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx₁) B)] using hx)
  refine (hsum.mul_left (1 - p)⁻¹).of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_)
  · exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  · rcases Nat.eq_zero_or_pos n.val with hn | hn
    · simp [hn, r, inv_nonneg.mpr (sub_nonneg.mpr hp₁.le)]
    have hn₁ : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    calc
      _ ≤ (((n : ℝ) ^ (1 - p)) / (1 - p)) / n :=
        div_le_div_of_nonneg_right (Real.log_le_rpow_div (Nat.cast_nonneg _) (sub_pos.mpr hp₁))
          (Nat.cast_nonneg _)
      _ = (1 - p)⁻¹ * (1 * r n ^ (-p)) := by
        dsimp only [r]
        rw [max_eq_right hn₁, one_mul, div_right_comm, ← Real.rpow_sub_one (by positivity),
          sub_sub_cancel_left, div_eq_inv_mul]

end Set

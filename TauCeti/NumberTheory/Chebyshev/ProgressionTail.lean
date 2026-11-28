/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# Logarithmic power sums in the two sign classes

For the classes `±1` modulo `4t`, grouping the integers by the quotient of `p + 1` by `4t`
exhibits the decay `log t / t³` of the sum with weights `log p / p³`. Primality is not needed.
This decay bounds the odd conjugate type-prime cost in estimates for chains of theta lifts:
it absorbs a factor as large as `t^(5/2)`. The type-prime normalization is that of Levent Alpöge's
`Formalism.MainNotions.LocalQuadraticParts.adm11`.
-/

public section

open Finset

namespace TauCeti

-- In the `j`-th block, the smallest eligible integer is `4 * t * j - 1`.
private theorem log_div_cube_le_of_block {t j p : ℕ}
    (ht : 0 < t) (hj : 0 < j) (hp : 4 * t * j ≤ p + 1) :
    Real.log p / (p : ℝ) ^ 3 ≤ (Real.log (3 * t) / (3 * t) ^ 3) * ((j : ℝ) ^ 2)⁻¹ := by
  have htj : 0 < t * j := Nat.mul_pos ht hj
  have hblock : 3 * t * j ≤ p := by
    have hq : 4 * t * j = 3 * t * j + t * j := by ring
    omega
  have hb : 3 * (t : ℝ) * j ≤ p := by exact_mod_cast hblock
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hbase : 3 * (t : ℝ) ≤ 3 * t * j := by nlinarith
  have hexp : Real.exp 1 ≤ 3 * (t : ℝ) := Real.exp_one_lt_three.le.trans (by linarith)
  have hlog₀ : 0 ≤ Real.log (3 * (t : ℝ)) := Real.log_nonneg (by linarith)
  have hlog : Real.log p / (p : ℝ) ≤ Real.log (3 * t) / (3 * t) :=
    Real.log_div_self_antitoneOn hexp (hexp.trans (hbase.trans hb)) (hbase.trans hb)
  have hsq : ((p : ℝ) ^ 2)⁻¹ ≤ ((3 * (t : ℝ) * j) ^ 2)⁻¹ := by gcongr
  calc
    _ = (Real.log p / (p : ℝ)) * ((p : ℝ) ^ 2)⁻¹ := by ring
    _ ≤ (Real.log (3 * t) / (3 * t)) * ((3 * (t : ℝ) * j) ^ 2)⁻¹ := by
      exact mul_le_mul hlog hsq (by positivity) (by positivity)
    _ = _ := by ring

-- Each positive quotient contributes at most two eligible integers, one per remainder.
private theorem sum_log_div_cube_le_of_succ_remainders {s : Finset ℕ} {t : ℕ}
    (hr : ∀ p ∈ s, (p + 1) % (4 * t) ∈ ({0, 2} : Finset ℕ)) :
    ∑ p ∈ s, Real.log p / (p : ℝ) ^ 3 ≤ 4 * (Real.log (3 * t) / (3 * t) ^ 3) := by
  let q := 4 * t
  let e (p : ℕ) := ((p + 1) / q, (p + 1) % q)
  let C := Real.log (3 * t) / (3 * t) ^ 3
  have hlog : 0 ≤ Real.log (3 * (t : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using Real.log_natCast_nonneg (3 * t)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrec (p : ℕ) : q * (e p).1 + (e p).2 = p + 1 := Nat.div_add_mod _ _
  have hrem (p : ℕ) (h : p ∈ s) : (e p).2 ≤ 2 := by
    have := hr p h
    simp only [mem_insert, mem_singleton] at this
    rcases this with h0 | h2 <;> simp [e, q, *]
  calc
    _ ≤ ∑ i ∈ Ico 0 (s.sup id + 2) ×ˢ ({0, 2} : Finset ℕ), C * ((i.1 : ℝ) ^ 2)⁻¹ := by
      refine sum_le_sum_of_injOn e (fun a _ b _ hab ↦ ?_) ?_ (fun p h ↦ ?_)
        (fun _ _ _ ↦ mul_nonneg hC (by positivity))
      · have := congrArg (fun i : ℕ × ℕ ↦ q * i.1 + i.2) hab
        simpa only [hrec, Nat.add_right_cancel_iff] using this
      · rintro _ hi
        obtain ⟨p, h, rfl⟩ := mem_image.mp hi
        refine mem_product.mpr ⟨mem_Ico.mpr ⟨Nat.zero_le _, ?_⟩, hr p h⟩
        have := (Nat.div_le_self (p + 1) q).trans (Nat.add_le_add_right (le_sup (f := id) h) 1)
        exact this.trans_lt (Nat.lt_succ_self _)
      · have hsum := hrec p
        by_cases hj : (e p).1 = 0
        · rw [hj, mul_zero, zero_add] at hsum
          have := hrem p h
          have hp : p = 0 ∨ p = 1 := by omega
          rcases hp with rfl | rfl <;> simp [hj]
        · have ht : 0 < t := by
            by_contra! hzero
            have hz : t = 0 := by omega
            simp [e, q, hz] at hj
          exact log_div_cube_le_of_block ht (Nat.pos_of_ne_zero hj)
            ((Nat.le_add_right _ _).trans_eq hsum)
    _ = 2 * C * ∑ j ∈ Ioo 0 (s.sup id + 2), ((j : ℝ) ^ 2)⁻¹ := by
      rw [sum_product, Ico_eq_cons_Ioo (by omega : 0 < s.sup id + 2), sum_cons, mul_sum]
      simp [← two_mul, mul_assoc]
    _ ≤ _ := by
      have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (s.sup id + 2)
      simp only [Nat.cast_zero, zero_add, div_one] at h
      calc
        _ ≤ 2 * C * 2 := mul_le_mul_of_nonneg_left h (mul_nonneg (by norm_num) hC)
        _ = _ := by ring

-- The bound before absorbing `log 3` works also for the positive scale `t = 1`.
private theorem sum_log_div_cube_le_sign_classes {s : Finset ℕ} {t : ℕ}
    (hs : ∀ p ∈ s, (p : ZMod (4 * t)) = 1 ∨ (p : ZMod (4 * t)) = -1) :
    ∑ p ∈ s, Real.log p / (p : ℝ) ^ 3 ≤ 4 * (Real.log (3 * t) / (3 * t) ^ 3) := by
  refine sum_log_div_cube_le_of_succ_remainders fun p h ↦ ?_
  simp only [mem_insert, mem_singleton]
  rcases hs p h with hplus | hminus
  · right
    have hcast : ((p + 1 : ℕ) : ZMod (4 * t)) = ((2 : ℕ) : ZMod (4 * t)) := by
      push_cast
      rw [hplus, one_add_one_eq_two]
    have hrem : (p + 1) % (4 * t) = 2 % (4 * t) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
    refine hrem.trans ?_
    by_cases ht : t = 0
    · simp [ht]
    · exact Nat.mod_eq_of_lt (by omega)
  · left
    have hcast : ((p + 1 : ℕ) : ZMod (4 * t)) = 0 := by simp [Nat.cast_succ, hminus]
    exact Nat.dvd_iff_mod_eq_zero.mp ((ZMod.natCast_eq_zero_iff _ _).mp hcast)

/-- The sum of `log p / p³` over a finite set in the sign classes modulo `4t` is bounded
by `log t / t³`, with no upper cutoff or primality assumption. -/
theorem sum_log_div_cube_le_of_natCast_eq_one_or_eq_neg_one {s : Finset ℕ} {t : ℕ} (ht : 2 ≤ t)
    (hs : ∀ p ∈ s, (p : ZMod (4 * t)) = 1 ∨ (p : ZMod (4 * t)) = -1) :
    ∑ p ∈ s, Real.log p / (p : ℝ) ^ 3 ≤ Real.log t / (t : ℝ) ^ 3 := by
  have ht' : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by positivity
  have hlog : Real.log (3 * t) ≤ 3 * Real.log t := by
    have ht3 : 3 * (t : ℝ) ≤ t ^ 3 := by
      nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr ht')]
    simpa [Real.log_pow] using Real.log_le_log (by positivity) ht3
  calc
    _ ≤ 4 * (Real.log (3 * t) / (3 * t) ^ 3) := sum_log_div_cube_le_sign_classes hs
    _ ≤ 4 * (3 * Real.log t / (3 * t) ^ 3) := by gcongr
    _ = (4 / 9) * (Real.log t / (t : ℝ) ^ 3) := by ring
    _ ≤ _ := mul_le_of_le_one_left (div_nonneg (Real.log_natCast_nonneg _) (by positivity))
      (by norm_num)

/-- A multiplier at most `t^(5/2)` is absorbed by the decay of the sign-class sum. -/
theorem mul_sum_log_div_cube_le_of_natCast_eq_one_or_eq_neg_one {s : Finset ℕ} {t : ℕ} {k : ℝ}
    (hs : ∀ p ∈ s, (p : ZMod (4 * t)) = 1 ∨ (p : ZMod (4 * t)) = -1)
    (hk : k ≤ (t : ℝ) ^ (5 / 2 : ℝ)) : k * (∑ p ∈ s, Real.log p / (p : ℝ) ^ 3) ≤ 2 := by
  by_cases hsmall : t < 2
  · have ht' : (t : ℝ) ≤ 1 := by exact_mod_cast (by omega : t ≤ 1)
    have hk₁ : k ≤ 1 := hk.trans (Real.rpow_le_one (by positivity) ht' (by norm_num))
    have hsum := sum_log_div_cube_le_sign_classes hs
    have hcases : t = 0 ∨ t = 1 := by omega
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    exact (mul_le_of_le_one_left (by positivity) hk₁).trans (by
      rcases hcases with rfl | rfl <;> norm_num at hsum <;> linarith)
  have ht : 2 ≤ t := le_of_not_gt hsmall
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  calc
    _ ≤ (t : ℝ) ^ (5 / 2 : ℝ) * (∑ p ∈ s, Real.log p / (p : ℝ) ^ 3) := by gcongr
    _ ≤ (t : ℝ) ^ (5 / 2 : ℝ) * (Real.log t / (t : ℝ) ^ 3) := by
      gcongr
      exact sum_log_div_cube_le_of_natCast_eq_one_or_eq_neg_one ht hs
    _ = ((t : ℝ) ^ (5 / 2 : ℝ) * Real.log t) / (t : ℝ) ^ 3 := by ring
    _ ≤ 2 := by
      rw [div_le_iff₀ (pow_pos ht0 3)]
      calc
        _ ≤ (t : ℝ) ^ (5 / 2 : ℝ) * ((t : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) := by
          gcongr
          exact Real.log_le_rpow_div ht0.le (by norm_num)
        _ = 2 * (t : ℝ) ^ 3 := by
          rw [mul_div_assoc', ← Real.rpow_add ht0]
          norm_num [Real.rpow_ofNat, div_eq_mul_inv, mul_comm]

end TauCeti

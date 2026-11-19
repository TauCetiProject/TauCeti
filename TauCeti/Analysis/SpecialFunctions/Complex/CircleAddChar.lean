/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.Data.ZMod.Count

/-!
# Values of the standard circle character of `ZMod N`

Mathlib's `ZMod.toCircle` sends `j : ZMod N` to `exp (2πij/N)`. This file records its value at
the half-way point of an even level: at level `2n` it sends `n` to `exp (πi) = -1`.

It also bounds the incomplete geometric sums of the standard additive character
`e(x) = ZMod.stdAddChar x`. For a nonzero residue `b` modulo `N`, the values `e(b k)` for
`k = 0, 1, …` run through a nontrivial geometric progression on the unit circle, so their partial
sums stay bounded independently of the length. Explicitly, with `v = b.val` and `N - v = (-b).val`,

`‖∑_{k < H} e(b k)‖ ≤ 2 / ‖e(b) - 1‖ = 1 / sin (π v / N) ≤ (N / 2) (1 / v + 1 / (N - v))`,

using `sin (π t) ≥ 2 min (t, 1 - t) ≥ 2 t (1 - t)` on `[0, 1]`. Summed over the nonzero residues,
these bounds give `N` times the harmonic number `H_{N-1}`. This is the additive-character input
of the Pólya–Vinogradov inequality for character sums over intervals.

## Main results

* `ZMod.coe_toCircle_natCast_self`: `ZMod.toCircle (n : ZMod (2n)) = -1`.
* `ZMod.four_mul_val_mul_val_neg_div_sq_le_norm_stdAddChar_sub_one`: the distance of `e(b)`
  from `1` is at least `4 b.val (N - b.val) / N²`.
* `ZMod.norm_sum_range_stdAddChar_mul_le`: the bound on one incomplete geometric sum.
* `ZMod.sum_norm_sum_range_stdAddChar_mul_le`: the sum of these norms over the nonzero residues
  is at most `N * harmonic (N - 1)`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 23.
-/

public section

namespace ZMod

open scoped Real

/-- The standard circle character of `ZMod (2n)` sends `n` to `exp (πi) = -1`. -/
theorem coe_toCircle_natCast_self (n : ℕ) [NeZero n] :
    ((toCircle ((n : ℕ) : ZMod (2 * n)) : Circle) : ℂ) = -1 := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [toCircle_natCast, Nat.cast_mul, Nat.cast_two]
  have : 2 * π * Complex.I * n / (2 * n) = π * Complex.I := by
    field_simp
  rw [this, Complex.exp_pi_mul_I]

/-! ### Incomplete geometric sums of the standard additive character -/

open Finset Real

variable {N : ℕ} [NeZero N]

/-- **The distance from `1` of a value of the standard additive character.** With
`(-b).val = N - b.val` for `b ≠ 0`, the value `e(b)` lies at distance
`2 sin (π b.val / N) ≥ 4 b.val (N - b.val) / N²` from `1`. -/
theorem four_mul_val_mul_val_neg_div_sq_le_norm_stdAddChar_sub_one (b : ZMod N) :
    4 * ((b.val : ℕ) : ℝ) * (((-b).val : ℕ) : ℝ) / N ^ 2 ≤ ‖stdAddChar b - 1‖ := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have : NeZero b := ⟨hb⟩
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hvN : b.val < N := val_lt b
  rw [val_neg_of_ne_zero, Nat.cast_sub hvN.le]
  set v : ℝ := ((b.val : ℕ) : ℝ) with hv_def
  have hvN' : v < N := Nat.cast_lt.mpr hvN
  have ht0 : 0 ≤ v / N := by positivity
  have ht1 : v / N ≤ 1 := (div_le_one hN).mpr hvN'.le
  -- `sin (π t) ≥ 2 t (1 - t)` for `t = v / N`, from Jordan's inequality on each half of `[0, 1]`.
  have hsin : 2 * (v / N) * (1 - v / N) ≤ Real.sin (π * (v / N)) := by
    rcases le_total (v / N) (1 / 2) with ht | ht
    · have h := mul_le_sin (x := π * (v / N)) (by positivity) (by nlinarith [pi_pos])
      rw [← mul_assoc, div_mul_cancel₀ _ pi_ne_zero] at h
      nlinarith
    · have h := mul_le_sin (x := π * (1 - v / N)) (by nlinarith [pi_pos]) (by nlinarith [pi_pos])
      rw [← mul_assoc, div_mul_cancel₀ _ pi_ne_zero,
        show π * (1 - v / N) = π - π * (v / N) by ring, sin_pi_sub] at h
      nlinarith
  have hz : stdAddChar b = Complex.exp (Complex.I * ((2 * π * (v / N) : ℝ) : ℂ)) := by
    rw [stdAddChar_apply, toCircle_apply, hv_def]
    push_cast
    ring_nf
  rw [hz, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_two,
    show 2 * π * (v / N) / 2 = π * (v / N) by ring, Real.norm_eq_abs,
    show 4 * v * (N - v) / N ^ 2 = 2 * (2 * (v / N) * (1 - v / N)) by field_simp; ring]
  nlinarith [le_abs_self (Real.sin (π * (v / N)))]

/-- **Incomplete geometric sums of the standard additive character.** For a nonzero residue `b`
modulo `N`, every partial sum of `k ↦ e(b k)` has norm at most
`(N / 2) (1 / b.val + 1 / (N - b.val))`, written with `(-b).val = N - b.val`. -/
theorem norm_sum_range_stdAddChar_mul_le {b : ZMod N} (hb : b ≠ 0) (H : ℕ) :
    ‖∑ k ∈ range H, stdAddChar (b * (k : ZMod N))‖ ≤
      N / 2 * (((b.val : ℕ) : ℝ)⁻¹ + (((-b).val : ℕ) : ℝ)⁻¹) := by
  have : NeZero b := ⟨hb⟩
  have hv : (0 : ℝ) < b.val := Nat.cast_pos.mpr ((val_pos).mpr hb)
  have hw : (0 : ℝ) < (-b).val := Nat.cast_pos.mpr ((val_pos).mpr (neg_ne_zero.mpr hb))
  set z : ℂ := stdAddChar b with hz_def
  have hpow (k : ℕ) : stdAddChar (b * (k : ZMod N)) = z ^ k := by
    rw [mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
  have hz1 : z ≠ 1 := fun h ↦ hb <| injective_stdAddChar (h.trans (AddChar.map_zero_eq_one _).symm)
  have hznorm : ‖z‖ = 1 := by rw [hz_def, stdAddChar_apply, Circle.norm_coe]
  have hpos : 0 < 4 * ((b.val : ℕ) : ℝ) * (((-b).val : ℕ) : ℝ) / N ^ 2 := by
    have : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
    positivity
  calc
    _ = ‖(z ^ H - 1) / (z - 1)‖ := by simp_rw [hpow, geom_sum_eq hz1]
    _ ≤ 2 / ‖z - 1‖ := by
      rw [norm_div]
      gcongr
      calc
        _ ≤ ‖z ^ H‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hznorm]; norm_num
    _ ≤ 2 / (4 * ((b.val : ℕ) : ℝ) * (((-b).val : ℕ) : ℝ) / N ^ 2) :=
      div_le_div_of_nonneg_left zero_le_two hpos
        (four_mul_val_mul_val_neg_div_sq_le_norm_stdAddChar_sub_one b)
    _ = N / 2 * (((b.val : ℕ) : ℝ)⁻¹ + (((-b).val : ℕ) : ℝ)⁻¹) := by
      have hvw : ((b.val : ℕ) : ℝ) + (((-b).val : ℕ) : ℝ) = N := by
        rw [val_neg_of_ne_zero, Nat.cast_sub (val_lt b).le, add_sub_cancel]
      field_simp
      linear_combination -4 * (N : ℝ) * hvw

/-- **The total size of the incomplete geometric sums.** Summed over the nonzero residues `b`
modulo `N`, the norms of the partial sums of `k ↦ e(b k)` of a fixed length are at most `N`
times the harmonic number `H_{N-1}`. -/
theorem sum_norm_sum_range_stdAddChar_mul_le (H : ℕ) :
    ∑ b ∈ univ.erase (0 : ZMod N), ‖∑ k ∈ range H, stdAddChar (b * (k : ZMod N))‖ ≤
      N * (harmonic (N - 1) : ℝ) := by
  set f : ZMod N → ℝ := fun b ↦ N / 2 * (((b.val : ℕ) : ℝ)⁻¹ + (((-b).val : ℕ) : ℝ)⁻¹)
  have hf0 : f 0 = 0 := by simp [f]
  calc
    _ ≤ ∑ b ∈ univ.erase (0 : ZMod N), f b :=
      sum_le_sum fun b hb ↦ norm_sum_range_stdAddChar_mul_le (ne_of_mem_erase hb) H
    _ = ∑ b, f b := sum_erase _ hf0
    _ = N / 2 * (∑ b : ZMod N, ((b.val : ℕ) : ℝ)⁻¹ + ∑ b : ZMod N, (((-b).val : ℕ) : ℝ)⁻¹) := by
      rw [← sum_add_distrib, mul_sum]
    _ = N * (harmonic (N - 1) : ℝ) := by
      have hneg : ∑ b : ZMod N, (((-b).val : ℕ) : ℝ)⁻¹ = ∑ b : ZMod N, ((b.val : ℕ) : ℝ)⁻¹ :=
        Equiv.sum_comp (Equiv.neg (ZMod N)) fun b ↦ ((b.val : ℕ) : ℝ)⁻¹
      rw [hneg, sum_inv_val_eq_harmonic]
      ring

end ZMod

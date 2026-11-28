/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.Algebra.Group.AddChar.Prod

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.Analysis.SpecificLimits.Normed
import TauCeti.Data.ZMod.Count

/-!
# Values of the standard circle character of `ZMod N`

Mathlib's `ZMod.toCircle` sends `j : ZMod N` to `exp (2πij/N)`. At level `2n` it sends `n`
to `exp (πi) = -1`. The distance from `1` to a character value is bounded below using the distance
of the corresponding residue to zero around the circle. The resulting reciprocal-chord and
geometric-sum bounds give `N` times the harmonic number `H_{N-1}`, and hence a logarithmic
estimate, after summing over nonzero frequencies.

## Main results

* `ZMod.coe_toCircle_natCast_self`: `ZMod.toCircle (n : ZMod (2n)) = -1`.
* `ZMod.le_norm_stdAddChar_sub_one`: a lower bound for the distance to `1`.
* `ZMod.map_stdAddChar_of_map_stdAddChar_one`: a multiplicative map of `ℂ` sending `ζ_N` to
  `ζ_N^d` sends every character value `stdAddChar j` to `stdAddChar (d * j)`.
* `ZMod.isPrimitiveRoot_stdAddChar_one`: `ζ_N = stdAddChar 1` is a primitive `N`-th root of unity.
* `ZMod.stdAddChar_intCast_natCast_mul`: the standard character modulo `m n` at `n x` is the
  standard character modulo `m` at `x`.
* `ZMod.stdAddChar_intCast_eq_mul_of_add_eq_one`: if `u n + v m = 1`, then
  `e(k / (m n)) = e(u k / m) e(v k / n)` for every integer `k`.
* `ZMod.stdAddChar_eq_mul_of_coprime`: for coprime `c₁, c₂`, the standard character modulo
  `c₁ c₂` is `e(c₂' x / c₁) e(c₁' x / c₂)` with `c₂' c₂ ≡ 1 (mod c₁)` and `c₁' c₁ ≡ 1 (mod c₂)`.
* `ZMod.stdAddChar_compAddMonoidHom_chineseRemainder_symm`: the same statement for characters,
  along the inverse of `ZMod.chineseRemainder` and with `AddChar.coprodEquiv`.
* `ZMod.exists_map_stdAddChar_one_eq`: every ring endomorphism of `ℂ` sends `ζ_N` to `ζ_N^d` for
  a unit `d` of `ZMod N`.
* `ZMod.two_div_norm_stdAddChar_sub_one_le`: an upper bound for the reciprocal chord length.
* `ZMod.norm_sum_range_stdAddChar_mul_add_le`: a geometric-sum bound at nonzero frequency.
* `ZMod.sum_norm_sum_range_stdAddChar_mul_add_le_harmonic`: the summed geometric-sum bound,
  in terms of the harmonic number `H_{N-1}`.
* `ZMod.sum_norm_sum_range_stdAddChar_mul_add_le`: the summed geometric-sum bound, in terms of
  the logarithm of the modulus.
-/

public section

namespace ZMod

open Finset
open scoped Real

/-- The standard circle character of `ZMod (2n)` sends `n` to `exp (πi) = -1`. -/
theorem coe_toCircle_natCast_self (n : ℕ) [NeZero n] :
    ((toCircle ((n : ℕ) : ZMod (2 * n)) : Circle) : ℂ) = -1 := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [toCircle_natCast, Nat.cast_mul, Nat.cast_two]
  have : 2 * π * Complex.I * n / (2 * n) = π * Complex.I := by
    field_simp
  rw [this, Complex.exp_pi_mul_I]

/-- The chord from `1` to the standard character at `k` has length at least four times
the absolute value of the centered residue divided by the modulus. -/
theorem le_norm_stdAddChar_sub_one {N : ℕ} [NeZero N] (k : ZMod N) :
    4 * (k.valMinAbs.natAbs : ℝ) / N ≤ ‖stdAddChar k - 1‖ := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hk : (k.valMinAbs.natAbs : ℝ) * 2 ≤ N := by
    exact_mod_cast Nat.le_div_two_iff_mul_two_le.mp k.natAbs_valMinAbs_le
  have habs : |(k.valMinAbs : ℝ)| = k.valMinAbs.natAbs := by
    simp only [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  have hchar : stdAddChar k = Complex.exp (Complex.I * (↑(2 * (π *
      ((k.valMinAbs : ℝ) / N))) : ℂ)) := by
    calc
      stdAddChar k = stdAddChar (k.valMinAbs : ZMod N) := by rw [coe_valMinAbs]
      _ = _ := by
        rw [stdAddChar_coe]
        push_cast
        congr 1
        ring
  have harg : |π * ((k.valMinAbs : ℝ) / N)| = π * ((k.valMinAbs.natAbs : ℝ) / N) := by
    rw [abs_mul, abs_of_pos Real.pi_pos, abs_div, habs, abs_of_pos hN]
  have hhalf : |π * ((k.valMinAbs : ℝ) / N)| ≤ π / 2 := by
    rw [harg, div_eq_mul_inv π 2]
    exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hN).mpr (by linarith)) Real.pi_pos.le
  rw [hchar, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    mul_div_cancel_left₀ _ two_ne_zero, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ = 2 * (2 / π * |π * ((k.valMinAbs : ℝ) / N)|) := by
      rw [harg]
      field_simp [Real.pi_ne_zero]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.mul_abs_le_abs_sin hhalf) (by norm_num)

variable {N : ℕ} [NeZero N]

/-- A multiplicative map of `ℂ` sending the generator `ζ_N = stdAddChar 1` to
`stdAddChar d = ζ_N^d` sends every value `stdAddChar j` to `stdAddChar (d * j)`. -/
theorem map_stdAddChar_of_map_stdAddChar_one {F : Type*} [FunLike F ℂ ℂ]
    [MonoidHomClass F ℂ ℂ] {σ : F} {d : ZMod N} (hσ : σ (stdAddChar (1 : ZMod N)) = stdAddChar d)
    (j : ZMod N) : σ (stdAddChar j) = stdAddChar (d * j) := by
  have hj : stdAddChar j = stdAddChar (1 : ZMod N) ^ j.val := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_one, natCast_zmod_val]
  rw [hj, map_pow, hσ, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, natCast_zmod_val, mul_comm]

variable (N) in
/-- The generator `ζ_N = stdAddChar 1 = exp (2πi/N)` is a primitive `N`-th root of unity. -/
theorem isPrimitiveRoot_stdAddChar_one : IsPrimitiveRoot (stdAddChar (1 : ZMod N)) N := by
  have h : stdAddChar (1 : ZMod N) = Complex.exp (2 * π * Complex.I / N) := by
    simpa using stdAddChar_coe (N := N) 1
  rw [h]
  exact Complex.isPrimitiveRoot_exp N (NeZero.ne N)

/-- Every ring endomorphism of `ℂ` sends `ζ_N = stdAddChar 1` to `ζ_N^d = stdAddChar d` for a
unit `d` of `ZMod N`, since it sends primitive `N`-th roots of unity to primitive ones. -/
theorem exists_map_stdAddChar_one_eq {F : Type*} [FunLike F ℂ ℂ] [RingHomClass F ℂ ℂ] (σ : F) :
    ∃ d : (ZMod N)ˣ, σ (stdAddChar (1 : ZMod N)) = stdAddChar (d : ZMod N) := by
  have hζ := isPrimitiveRoot_stdAddChar_one N
  have hσ := hζ.map_of_injective (f := σ) (by simpa using RingHom.injective (σ : ℂ →+* ℂ))
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hσ.pow_eq_one
  refine ⟨unitOfCoprime i ((hζ.pow_iff_coprime (NeZero.pos N) i).mp (hi ▸ hσ)), ?_⟩
  rw [coe_unitOfCoprime, ← hi, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_one]

/-- **The standard additive character at a multiple.** The standard additive character modulo
`m n` at `n x` is the standard additive character modulo `m` at `x`: both are `e^(2π i x / m)`. -/
theorem stdAddChar_intCast_natCast_mul {m n : ℕ} [NeZero m] [NeZero n] (x : ℤ) :
    stdAddChar (((n * x : ℤ) : ZMod (m * n))) = stdAddChar (x : ZMod m) := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [stdAddChar_coe, stdAddChar_coe]
  congr 1
  push_cast
  field_simp

/-- `stdAddChar_intCast_natCast_mul` for a modulus `N` equal to `m n`, for example `N = n m`. -/
private theorem stdAddChar_intCast_natCast_mul_of_eq {N m n : ℕ} [NeZero N] [NeZero m]
    [NeZero n] (hN : N = m * n) (x : ℤ) :
    stdAddChar (((n * x : ℤ) : ZMod N)) = stdAddChar (x : ZMod m) := by
  subst hN
  exact stdAddChar_intCast_natCast_mul x

/-- **The standard character at an integer, for coprime moduli.** If `u n + v m = 1`, then
`e(k / (m n)) = e(u k / m) e(v k / n)`, where `e(t) = exp (2πi t)`. The computation is adapted
from the coprime case of the quadratic Gauss sum, `Matrix.sum_stdAddChar_dotProduct_mulVec_mul`. -/
theorem stdAddChar_intCast_eq_mul_of_add_eq_one {m n : ℕ} [NeZero m] [NeZero n] {u v : ℤ}
    (huv : u * n + v * m = 1) (k : ℤ) :
    stdAddChar (k : ZMod (m * n)) =
      stdAddChar ((u * k : ℤ) : ZMod m) * stdAddChar ((v * k : ℤ) : ZMod n) := by
  have hk : k = n * (u * k) + m * (v * k) := by linear_combination (-k) * huv
  conv_lhs => rw [hk]
  rw [Int.cast_add, AddChar.map_add_eq_mul, stdAddChar_intCast_natCast_mul,
    stdAddChar_intCast_natCast_mul_of_eq (mul_comm m n)]

/-- **The standard character modulo a product of coprime moduli** is the product of two standard
characters, one modulo each factor: `e(x / (c₁ c₂)) = e(c₂' x₁ / c₁) e(c₁' x₂ / c₂)`, where
`e(t) = exp (2πi t)`. For the factor modulo `c₁`, reduce `x` modulo `c₁` to `x₁`, multiply by
`c₂' = c₂⁻¹` modulo `c₁`, and evaluate the standard character modulo `c₁`. The factor modulo `c₂`
uses `x₂`, the reduction of `x` modulo `c₂`, and `c₁' = c₁⁻¹` modulo `c₂`. -/
theorem stdAddChar_eq_mul_of_coprime {c₁ c₂ : ℕ} [NeZero c₁] [NeZero c₂] (h : c₁.Coprime c₂)
    (x : ZMod (c₁ * c₂)) :
    stdAddChar x =
      stdAddChar ((c₂ : ZMod c₁)⁻¹ * castHom (Nat.dvd_mul_right c₁ c₂) (ZMod c₁) x) *
        stdAddChar ((c₁ : ZMod c₂)⁻¹ * castHom (Nat.dvd_mul_left c₂ c₁) (ZMod c₂) x) := by
  set u := Nat.gcdA c₁ c₂
  set v := Nat.gcdB c₁ c₂
  have huv : (c₁ : ℤ) * u + c₂ * v = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, h.gcd_eq_one, Nat.cast_one]
  -- The two inverses are `v` modulo `c₁` and `u` modulo `c₂`.
  have hv : (c₂ : ZMod c₁)⁻¹ = v := by
    refine ZMod.inv_eq_of_mul_eq_one _ _ _ ?_
    have := congrArg (Int.cast : ℤ → ZMod c₁) huv
    push_cast at this
    rwa [ZMod.natCast_self, zero_mul, zero_add] at this
  have hu : (c₁ : ZMod c₂)⁻¹ = u := by
    refine ZMod.inv_eq_of_mul_eq_one _ _ _ ?_
    have := congrArg (Int.cast : ℤ → ZMod c₂) huv
    push_cast at this
    rwa [ZMod.natCast_self, zero_mul, add_zero] at this
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  rw [hv, hu]
  simp only [map_intCast, ← Int.cast_mul]
  exact stdAddChar_intCast_eq_mul_of_add_eq_one (by linear_combination huv) k

/-- **The Chinese remainder theorem for the standard character.** The standard character modulo
`c₁ c₂`, composed with the inverse of `ZMod.chineseRemainder`, is the character
`(x₁, x₂) ↦ e(c₂' x₁ / c₁) e(c₁' x₂ / c₂)` of `ZMod c₁ × ZMod c₂`: the image under
`AddChar.coprodEquiv` of the standard characters shifted by `c₂' = c₂⁻¹` modulo `c₁` and by
`c₁' = c₁⁻¹` modulo `c₂`. -/
theorem stdAddChar_compAddMonoidHom_chineseRemainder_symm {c₁ c₂ : ℕ} [NeZero c₁] [NeZero c₂]
    (h : c₁.Coprime c₂) :
    stdAddChar.compAddMonoidHom (chineseRemainder h).symm.toAddEquiv.toAddMonoidHom =
      AddChar.coprodEquiv
        (stdAddChar.mulShift (c₂ : ZMod c₁)⁻¹, stdAddChar.mulShift (c₁ : ZMod c₂)⁻¹) := by
  ext x
  obtain ⟨y, rfl⟩ := (chineseRemainder h).surjective x
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective y
  simp only [AddChar.compAddMonoidHom_apply, AddChar.coprodEquiv_apply, AddChar.mulShift_apply]
  rw [AddEquiv.coe_toAddMonoidHom, RingEquiv.toAddEquiv_eq_coe, RingEquiv.coe_toAddEquiv,
    RingEquiv.symm_apply_apply, stdAddChar_eq_mul_of_coprime h]
  simp only [map_intCast, Prod.fst_intCast, Prod.snd_intCast]

/-- The reciprocal chord bound in terms of the least nonnegative representatives of a
nonzero residue and its negative. -/
theorem two_div_norm_stdAddChar_sub_one_le (k : ZMod N) (hk : k ≠ 0) :
    2 / ‖ZMod.stdAddChar k - 1‖ ≤
      (N : ℝ) / 2 * ((k.val : ℝ)⁻¹ + ((-k).val : ℝ)⁻¹) := by
  have : NeZero k := ⟨hk⟩
  have hkpos : (0 : ℝ) < k.val := Nat.cast_pos.mpr (ZMod.val_pos.mpr hk)
  have hnegpos : (0 : ℝ) < (-k).val := Nat.cast_pos.mpr (ZMod.val_pos.mpr (neg_ne_zero.mpr hk))
  have hm : (0 : ℝ) < min (k.val : ℝ) ((-k).val : ℝ) := lt_min hkpos hnegpos
  have hc := ZMod.le_norm_stdAddChar_sub_one k
  rw [ZMod.valMinAbs_natAbs_eq_min, ← ZMod.val_neg_of_ne_zero k, Nat.cast_min] at hc
  calc
    2 / ‖ZMod.stdAddChar k - 1‖ ≤
        2 / (4 * min (k.val : ℝ) ((-k).val : ℝ) / N) :=
      div_le_div_of_nonneg_left (by norm_num)
        (div_pos (mul_pos (by norm_num) hm) (Nat.cast_pos.mpr (NeZero.pos N))) hc
    _ = (N : ℝ) / 2 * (min (k.val : ℝ) ((-k).val : ℝ))⁻¹ := by
      field_simp
      ring
    _ ≤ _ := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rcases le_total (k.val : ℝ) ((-k).val : ℝ) with h | h
      · rw [min_eq_left h]
        exact le_add_of_nonneg_right (by positivity)
      · rw [min_eq_right h]
        exact le_add_of_nonneg_left (by positivity)

/-- A geometric sum of standard additive-character values on an interval is bounded by
the reciprocal chord length of its nonzero frequency. -/
theorem norm_sum_range_stdAddChar_mul_add_le (a k : ZMod N) (H : ℕ)
    (hk : k ≠ 0) :
    ‖∑ j ∈ range H, stdAddChar (k * (a + (j : ZMod N)))‖ ≤
      2 / ‖stdAddChar k - 1‖ := by
  have hz : stdAddChar k ≠ 1 := by
    intro h
    apply hk
    apply injective_stdAddChar
    simpa only [AddChar.map_zero_eq_one] using h
  have heq : ∑ j ∈ range H, stdAddChar (k * (a + (j : ZMod N))) =
      stdAddChar (k * a) * ∑ j ∈ range H, (stdAddChar k) ^ j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    simp only [mul_add, AddChar.map_add_eq_mul]
    congr 1
    simpa only [nsmul_eq_mul, mul_comm] using
      (stdAddChar (N := N)).map_nsmul_eq_pow j k
  rw [heq, norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul]
  exact TauCeti.norm_geom_sum_le (by simp [ZMod.stdAddChar_apply]) hz H

/-- Summing the norms of interval sums of the standard additive character over nonzero
frequencies is bounded by the modulus times the harmonic number `H_{N-1}`. -/
theorem sum_norm_sum_range_stdAddChar_mul_add_le_harmonic (a : ZMod N) (H : ℕ) :
    ∑ k ∈ univ.erase (0 : ZMod N),
        ‖∑ j ∈ range H, stdAddChar (k * (a + (j : ZMod N)))‖ ≤
      N * (harmonic (N - 1) : ℝ) := by
  have hneg : ∑ k ∈ univ.erase (0 : ZMod N), ((-k).val : ℝ)⁻¹ =
      ∑ k ∈ univ.erase (0 : ZMod N), (k.val : ℝ)⁻¹ := by
    apply sum_equiv (Equiv.neg (ZMod N))
    · intro k
      simp only [mem_erase, mem_univ, and_true, Equiv.neg_apply, neg_ne_zero]
    · intro k _
      rfl
  calc
    _ ≤ ∑ k ∈ univ.erase (0 : ZMod N),
        (N : ℝ) / 2 * ((k.val : ℝ)⁻¹ + ((-k).val : ℝ)⁻¹) := by
      apply sum_le_sum
      intro k hk
      exact (norm_sum_range_stdAddChar_mul_add_le a k H (mem_erase.mp hk).1).trans
        (two_div_norm_stdAddChar_sub_one_le k (mem_erase.mp hk).1)
    _ = (N : ℝ) * ∑ k ∈ univ.erase (0 : ZMod N), (k.val : ℝ)⁻¹ := by
      rw [← mul_sum, sum_add_distrib, hneg]
      ring
    _ = _ := by rw [sum_erase _ (by simp), sum_inv_val_eq_harmonic]

/-- Summing the norms of interval sums of the standard additive character over nonzero
frequencies is bounded by the modulus times one plus its logarithm. -/
theorem sum_norm_sum_range_stdAddChar_mul_add_le (a : ZMod N) (H : ℕ) :
    ∑ k ∈ univ.erase (0 : ZMod N),
        ‖∑ j ∈ range H, stdAddChar (k * (a + (j : ZMod N)))‖ ≤
      N * (1 + Real.log N) := by
  refine (sum_norm_sum_range_stdAddChar_mul_add_le_harmonic a H).trans
    (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N))
  rw [← sum_inv_val_eq_harmonic (n := N),
    ← sum_erase (f := fun k : ZMod N ↦ (k.val : ℝ)⁻¹) (a := 0) _ (by simp)]
  exact sum_inv_val_le_one_add_log

end ZMod

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Peetre's inequality for the Japanese bracket

The Japanese bracket `⟨x⟩ = (1 + ‖x‖ ^ 2) ^ (1 / 2)` is submultiplicative up to the factor `√2`:
since `‖x + y‖ ^ 2 ≤ 2 ‖x‖ ^ 2 + 2 ‖y‖ ^ 2`,

`1 + ‖x + y‖ ^ 2 ≤ 2 (1 + ‖x‖ ^ 2) (1 + ‖y‖ ^ 2)`.

Raising this to the power `s / 2` gives, for `s ≥ 0`, `⟨x + y⟩ ^ s ≤ 2 ^ (s / 2) ⟨x⟩ ^ s ⟨y⟩ ^ s`.
For `s < 0` the same bound for `-s`, applied to the decomposition `x = (x + y) + (-y)`, gives
`⟨x + y⟩ ^ s ≤ 2 ^ (-s / 2) ⟨x⟩ ^ s ⟨y⟩ ^ (-s)`. Both cases are **Peetre's inequality**

`⟨x + y⟩ ^ s ≤ 2 ^ (|s| / 2) ⟨x⟩ ^ s ⟨y⟩ ^ |s|`, for every real `s`.

It says that translating a frequency by `y` changes the weight `⟨ξ⟩ ^ s` of the Bessel-potential
space `H^s` by at most the factor `2 ^ (|s| / 2) ⟨y⟩ ^ |s|`. This is the estimate behind the
boundedness of multiplication by Schwartz functions on `H^s` for every real `s`, and behind the
commutator estimates of the pseudodifferential calculus.

The brackets are written out as `(1 + ‖x‖ ^ 2) ^ (s / 2)`, the weight of Mathlib's
`TemperedDistribution.besselPotential`.

## Main declarations

* `TauCeti.one_add_norm_add_sq_le`: `1 + ‖x + y‖ ^ 2 ≤ 2 (1 + ‖x‖ ^ 2) (1 + ‖y‖ ^ 2)`.
* `TauCeti.one_add_norm_add_sq_rpow_le_mul`: Peetre's inequality
  `⟨x + y⟩ ^ s ≤ 2 ^ (|s| / 2) ⟨x⟩ ^ s ⟨y⟩ ^ |s|`.
* `TauCeti.one_add_norm_sq_rpow_le_mul_sub`: the equivalent form
  `⟨x⟩ ^ s ≤ 2 ^ (|s| / 2) ⟨x - y⟩ ^ |s| ⟨y⟩ ^ s`.
* `TauCeti.one_add_norm_sq_rpow_le_of_norm_eq_mul`: rescaling by `c ≥ 1` changes the weight
  `⟨x⟩ ^ s` by at most the factor `c ^ |s|`.
* `TauCeti.one_add_norm_add_sq_rpow_le`: the subadditive form
  `⟨x + y⟩ ^ s ≤ 2 ^ s (⟨x⟩ ^ s + ⟨y⟩ ^ s)` for `s ≥ 0`, which splits the weight of a convolution
  between its two factors.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  §9.3 (Peetre's inequality, used for multiplication by Schwartz functions on `H_s`).
-/

public section

namespace TauCeti

variable {E : Type*} [SeminormedAddGroup E]

/-- The square of the Japanese bracket is submultiplicative up to the factor `2`:
`1 + ‖x + y‖ ^ 2 ≤ 2 (1 + ‖x‖ ^ 2) (1 + ‖y‖ ^ 2)`. -/
theorem one_add_norm_add_sq_le (x y : E) :
    1 + ‖x + y‖ ^ 2 ≤ 2 * ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2)) := by
  have h : ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2).trans add_sq_le
  nlinarith [mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖y‖)]

/-- Peetre's inequality for nonnegative exponents. -/
private theorem one_add_norm_add_sq_rpow_le_mul_of_nonneg {s : ℝ} (hs : 0 ≤ s) (x y : E) :
    (1 + ‖x + y‖ ^ 2) ^ (s / 2) ≤
      2 ^ (s / 2) * (1 + ‖x‖ ^ 2) ^ (s / 2) * (1 + ‖y‖ ^ 2) ^ (s / 2) := by
  rw [← Real.mul_rpow (by positivity) (by positivity),
    ← Real.mul_rpow (by positivity) (by positivity), mul_assoc]
  exact Real.rpow_le_rpow (by positivity) (one_add_norm_add_sq_le x y) (by linarith)

/-- **Peetre's inequality.** For every real `s`, the Japanese bracket `⟨x⟩ = (1 + ‖x‖ ^ 2) ^ (1/2)`
satisfies `⟨x + y⟩ ^ s ≤ 2 ^ (|s| / 2) ⟨x⟩ ^ s ⟨y⟩ ^ |s|`. -/
theorem one_add_norm_add_sq_rpow_le_mul (s : ℝ) (x y : E) :
    (1 + ‖x + y‖ ^ 2) ^ (s / 2) ≤
      2 ^ (|s| / 2) * (1 + ‖x‖ ^ 2) ^ (s / 2) * (1 + ‖y‖ ^ 2) ^ (|s| / 2) := by
  rcases le_or_gt 0 s with hs | hs
  · rw [abs_of_nonneg hs]
    exact one_add_norm_add_sq_rpow_le_mul_of_nonneg hs x y
  · rw [abs_of_neg hs]
    -- Apply the nonnegative case to `x = (x + y) + (-y)` with exponent `-s`, then invert.
    have h := one_add_norm_add_sq_rpow_le_mul_of_nonneg (neg_nonneg.2 hs.le) (x + y) (-y)
    rw [add_neg_cancel_right, norm_neg] at h
    set a := 1 + ‖x + y‖ ^ 2
    set b := 1 + ‖x‖ ^ 2
    set c := 1 + ‖y‖ ^ 2
    have ha : 0 < a := by positivity
    have hb : 0 < b := by positivity
    have hs2 : s / 2 = -(-s / 2) := by ring
    rw [hs2, Real.rpow_neg ha.le, Real.rpow_neg hb.le]
    have hA : 0 < a ^ (-s / 2) := Real.rpow_pos_of_pos ha _
    have hB : 0 < b ^ (-s / 2) := Real.rpow_pos_of_pos hb _
    rw [inv_le_iff_one_le_mul₀ hA]
    calc (1 : ℝ) = b ^ (-s / 2) * (b ^ (-s / 2))⁻¹ := (mul_inv_cancel₀ hB.ne').symm
      _ ≤ 2 ^ (-s / 2) * a ^ (-s / 2) * c ^ (-s / 2) * (b ^ (-s / 2))⁻¹ := by gcongr
      _ = 2 ^ (-s / 2) * (b ^ (-s / 2))⁻¹ * c ^ (-s / 2) * a ^ (-s / 2) := by ring

omit [SeminormedAddGroup E] in
/-- **Peetre's inequality**, in the form `⟨x⟩ ^ s ≤ 2 ^ (|s| / 2) ⟨x - y⟩ ^ |s| ⟨y⟩ ^ s` for every
real `s`. -/
theorem one_add_norm_sq_rpow_le_mul_sub [SeminormedAddCommGroup E] (s : ℝ) (x y : E) :
    (1 + ‖x‖ ^ 2) ^ (s / 2) ≤
      2 ^ (|s| / 2) * (1 + ‖x - y‖ ^ 2) ^ (|s| / 2) * (1 + ‖y‖ ^ 2) ^ (s / 2) := by
  have h := one_add_norm_add_sq_rpow_le_mul s y (x - y)
  rw [add_sub_cancel] at h
  linarith

omit [SeminormedAddGroup E] in
/-- Rescaling by a factor `c ≥ 1` changes the Japanese bracket weight by at most `c ^ |s|`: if
`‖x‖ = c ‖y‖`, then `(1 + ‖x‖ ^ 2) ^ (s / 2) ≤ c ^ |s| (1 + ‖y‖ ^ 2) ^ (s / 2)` for every real `s`.
For `s ≥ 0` this uses `‖x‖ ≤ c ‖y‖`, and for `s < 0` it uses `‖y‖ ≤ ‖x‖`. -/
theorem one_add_norm_sq_rpow_le_of_norm_eq_mul [SeminormedAddGroup E] {F : Type*}
    [SeminormedAddGroup F] {c : ℝ} (hc : 1 ≤ c) (s : ℝ) {x : E} {y : F} (h : ‖x‖ = c * ‖y‖) :
    (1 + ‖x‖ ^ 2) ^ (s / 2) ≤ c ^ |s| * (1 + ‖y‖ ^ 2) ^ (s / 2) := by
  have hy := norm_nonneg y
  rw [h]
  rcases le_or_gt 0 s with hs | hs
  · rw [abs_of_nonneg hs]
    calc (1 + (c * ‖y‖) ^ 2) ^ (s / 2) ≤ (c ^ 2 * (1 + ‖y‖ ^ 2)) ^ (s / 2) :=
          Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)
      _ = c ^ s * (1 + ‖y‖ ^ 2) ^ (s / 2) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast c 2,
            ← Real.rpow_mul (by linarith)]
          congr 2
          push_cast
          ring
  · have hcy : ‖y‖ ^ 2 ≤ (c * ‖y‖) ^ 2 := by
      rw [mul_pow]
      exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hc)
    calc (1 + (c * ‖y‖) ^ 2) ^ (s / 2) ≤ (1 + ‖y‖ ^ 2) ^ (s / 2) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      _ ≤ c ^ |s| * (1 + ‖y‖ ^ 2) ^ (s / 2) :=
          le_mul_of_one_le_left (by positivity) (Real.one_le_rpow hc (abs_nonneg s))

/-- **Peetre's inequality, subadditive form.** The Japanese bracket weight
`(1 + ‖x‖ ^ 2) ^ (s / 2)` is subadditive up to a constant: for `s ≥ 0`,
`(1 + ‖x + y‖ ^ 2) ^ (s / 2) ≤ 2 ^ s ((1 + ‖x‖ ^ 2) ^ (s / 2) + (1 + ‖y‖ ^ 2) ^ (s / 2))`. -/
theorem one_add_norm_add_sq_rpow_le {s : ℝ} (hs : 0 ≤ s) (x y : E) :
    (1 + ‖x + y‖ ^ 2) ^ (s / 2) ≤
      2 ^ s * ((1 + ‖x‖ ^ 2) ^ (s / 2) + (1 + ‖y‖ ^ 2) ^ (s / 2)) := by
  -- `1 + ‖x + y‖ ^ 2` is at most four times the larger of `1 + ‖x‖ ^ 2` and `1 + ‖y‖ ^ 2`.
  set a := 1 + ‖x‖ ^ 2
  set b := 1 + ‖y‖ ^ 2
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hs2 : 0 ≤ s / 2 := by positivity
  have hle : 1 + ‖x + y‖ ^ 2 ≤ 4 * max a b := by
    have hxy : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
    nlinarith [le_max_left a b, le_max_right a b, sq_nonneg (‖x‖ - ‖y‖)]
  have h4 : (4 : ℝ) ^ (s / 2) = 2 ^ s := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    ring_nf
  calc (1 + ‖x + y‖ ^ 2) ^ (s / 2) ≤ (4 * max a b) ^ (s / 2) :=
        Real.rpow_le_rpow (by positivity) hle hs2
    _ = 2 ^ s * max (a ^ (s / 2)) (b ^ (s / 2)) := by
      rw [Real.mul_rpow (by norm_num) (le_max_of_le_left ha), h4,
        (Real.monotoneOn_rpow_Ici_of_exponent_nonneg hs2).map_max ha hb]
    _ ≤ 2 ^ s * (a ^ (s / 2) + b ^ (s / 2)) := by
      gcongr
      exact max_le_add_of_nonneg (by positivity) (by positivity)

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Module.Convex

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
* `TauCeti.one_add_norm_sq_rpow_le_of_mem_segment`: along a segment, `⟨ξ⟩ ≤ √2 (1 + ‖w‖) ⟨ξ - η⟩`
  for `w` between `ξ` and `η`.
* `TauCeti.one_add_norm_sq_rpow_mul_rpow_le_mul_sub_left`,
  `TauCeti.one_add_norm_sq_rpow_mul_rpow_le_mul_sub_right`: the two-weight forms
  `⟨x⟩ ^ r ⟨y⟩ ^ (-s) ≤ 2 ^ (|s| / 2) ⟨x - y⟩ ^ |s| ⟨x⟩ ^ (r - s)` and
  `⟨x⟩ ^ r ⟨y⟩ ^ (-s) ≤ 2 ^ (|r| / 2) ⟨x - y⟩ ^ |r| ⟨y⟩ ^ (r - s)`, which bound the Fourier
  kernel of an operator from `H^s` to `H^r` by a function of `x - y` times a weight of order
  `r - s` in either variable.
* `TauCeti.one_add_norm_sq_rpow_le_of_norm_sub_le_one`: for `‖x - y‖ ≤ 1`,
  `⟨x⟩ ^ s ≤ 2 ^ |s| ⟨y⟩ ^ s`.
* `TauCeti.one_add_norm_sq_rpow_le_of_norm_le_mul`: if `‖x‖ ≤ c ‖y‖` and `‖y‖ ≤ c ‖x‖` with
  `c ≥ 1`, then `⟨x⟩ ^ s ≤ c ^ |s| ⟨y⟩ ^ s`; in particular
  (`TauCeti.one_add_norm_sq_rpow_le_of_norm_eq_mul`) rescaling by `c ≥ 1` changes the weight
  `⟨x⟩ ^ s` by at most the factor `c ^ |s|`.
* `TauCeti.one_add_norm_smul_sq_rpow_le`: the same for the scalar multiple `c • x`,
  `⟨c • x⟩ ^ s ≤ c ^ |s| ⟨x⟩ ^ s`.
* `TauCeti.exists_one_add_norm_smul_sq_rpow_le`: rescaling by any `c ≠ 0` changes
  `(1 + ‖x‖ ^ 2) ^ r` by at most a constant factor.
* `TauCeti.one_add_norm_add_smul_sq_rpow_le`: Peetre's inequality for the shift `ξ + c • θ`
  with `c ≥ 1`, `⟨ξ + c • θ⟩ ^ s ≤ 2 ^ (|s| / 2) c ^ |s| ⟨ξ⟩ ^ s ⟨θ⟩ ^ |s|`.
* `TauCeti.one_add_norm_add_sq_rpow_le`: the subadditive form
  `⟨x + y⟩ ^ s ≤ 2 ^ s (⟨x⟩ ^ s + ⟨y⟩ ^ s)` for `s ≥ 0`, which splits the weight of a convolution
  between its two factors.
* `TauCeti.one_add_norm_sq_rpow_le_one_add_norm_pow`: `⟨x⟩ ^ N ≤ (1 + ‖x‖) ^ N` for natural `N`.
* `TauCeti.one_add_norm_sq_rpow_le_mul_one_add_norm_pow`: `⟨x⟩ ^ a ≤ ⟨x⟩ ^ b (1 + ‖x‖) ^ N` for
  `a ≤ b + N`.
* `TauCeti.one_add_norm_sq_rpow_add`: `⟨x⟩ ^ (s + t) = ⟨x⟩ ^ s ⟨x⟩ ^ t`.
* `TauCeti.one_add_norm_sq_rpow_le_one`: `⟨x⟩ ^ s ≤ 1` for `s ≤ 0`.
* `TauCeti.one_add_norm_sq_rpow_neg_mul_rpow`: `⟨x⟩ ^ (-s) ⟨x⟩ ^ s = 1`.
* `TauCeti.one_add_norm_sq_rpow_le_of_mul_norm_le_norm_sub`: if `c ‖x‖ ≤ ‖x - y‖`, then
  `⟨y⟩ ^ s ≤ (c⁻¹ + 1) ^ |s| (1 + ‖x - y‖) ^ |s|`; this separates frequencies outside a cone
  from those inside it.
* `TauCeti.one_add_norm_sq_rpow_le_one_add_norm_pow_of_le`: `⟨x⟩ ^ s ≤ (1 + ‖x‖) ^ N` for real
  `s ≤ N`.
* `TauCeti.one_add_norm_sq_rpow_le_one_add_norm_rpow`: the bracket is at most the
  inhomogeneous norm, `⟨x⟩ ^ r ≤ (1 + ‖x‖) ^ r` for `r ≥ 0`.
* `TauCeti.one_add_norm_sq_rpow_le_two_pow_mul_one_add_norm_pow`: the comparison
  `⟨x⟩ ^ N ≤ 2 ^ N (1 + ‖x‖ ^ N)` of a natural power of the bracket with a power of the norm.
* `TauCeti.one_add_norm_sq_rpow_le_max_mul_rpow`: where `a R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ≤ b R ^ 2` with
  `a, R > 0`, every power `⟨ξ⟩ ^ u` is at most a constant times `R ^ u`.
* `TauCeti.one_add_norm_smul_sq_rpow_le_max_mul_rpow`: on an annulus `0 < c ≤ ‖ζ‖ ≤ d`, the
  bracket power `(1 + ‖t ζ‖ ^ 2) ^ (u / 2)` is `O(t ^ u)` for `t ≥ 1`.

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
/-- **Peetre's inequality along a segment**: for `w` on the segment from `ξ` to `η`,
`⟨ξ⟩ ≤ √2 (1 + ‖w‖) ⟨ξ - η⟩`. -/
theorem one_add_norm_sq_rpow_le_of_mem_segment [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {ξ η w : E} (hw : w ∈ segment ℝ ξ η) :
    (1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) ≤ √2 * (1 + ‖w‖) * (1 + ‖ξ - η‖ ^ 2) ^ (1 / 2 : ℝ) := by
  have hP := one_add_norm_add_sq_rpow_le_mul 1 w (ξ - w)
  rw [add_sub_cancel, abs_one, ← Real.sqrt_eq_rpow 2] at hP
  have hw' : (1 + ‖w‖ ^ 2) ^ (1 / 2 : ℝ) ≤ 1 + ‖w‖ := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by positivity)]
    nlinarith [norm_nonneg w]
  have hseg : ‖ξ - w‖ ≤ ‖ξ - η‖ := by
    simpa only [norm_sub_rev w ξ, norm_sub_rev η ξ] using norm_sub_le_of_mem_segment hw
  refine hP.trans ?_
  gcongr

omit [SeminormedAddGroup E] in
/-- **Peetre's inequality** for a pair of weights, with the decay in `x`:
`⟨x⟩ ^ r ⟨y⟩ ^ (-s) ≤ 2 ^ (|s| / 2) ⟨x - y⟩ ^ |s| ⟨x⟩ ^ (r - s)` for all real `r` and `s`. -/
theorem one_add_norm_sq_rpow_mul_rpow_le_mul_sub_left [SeminormedAddCommGroup E] (r s : ℝ)
    (x y : E) :
    (1 + ‖x‖ ^ 2) ^ (r / 2) * (1 + ‖y‖ ^ 2) ^ (-s / 2) ≤
      2 ^ (|s| / 2) * (1 + ‖x - y‖ ^ 2) ^ (|s| / 2) * (1 + ‖x‖ ^ 2) ^ ((r - s) / 2) := by
  have hP := one_add_norm_sq_rpow_le_mul_sub (-s) y x
  rw [abs_neg, norm_sub_rev] at hP
  have hx : 0 < 1 + ‖x‖ ^ 2 := by positivity
  calc (1 + ‖x‖ ^ 2) ^ (r / 2) * (1 + ‖y‖ ^ 2) ^ (-s / 2)
      ≤ (1 + ‖x‖ ^ 2) ^ (r / 2) *
          (2 ^ (|s| / 2) * (1 + ‖x - y‖ ^ 2) ^ (|s| / 2) * (1 + ‖x‖ ^ 2) ^ (-s / 2)) := by
        gcongr
    _ = 2 ^ (|s| / 2) * (1 + ‖x - y‖ ^ 2) ^ (|s| / 2) *
          ((1 + ‖x‖ ^ 2) ^ (r / 2) * (1 + ‖x‖ ^ 2) ^ (-s / 2)) := by ring
    _ = _ := by rw [← Real.rpow_add hx]; ring_nf

omit [SeminormedAddGroup E] in
/-- **Peetre's inequality** for a pair of weights, with the decay in `y`:
`⟨x⟩ ^ r ⟨y⟩ ^ (-s) ≤ 2 ^ (|r| / 2) ⟨x - y⟩ ^ |r| ⟨y⟩ ^ (r - s)` for all real `r` and `s`. -/
theorem one_add_norm_sq_rpow_mul_rpow_le_mul_sub_right [SeminormedAddCommGroup E] (r s : ℝ)
    (x y : E) :
    (1 + ‖x‖ ^ 2) ^ (r / 2) * (1 + ‖y‖ ^ 2) ^ (-s / 2) ≤
      2 ^ (|r| / 2) * (1 + ‖x - y‖ ^ 2) ^ (|r| / 2) * (1 + ‖y‖ ^ 2) ^ ((r - s) / 2) := by
  have hP := one_add_norm_sq_rpow_le_mul_sub r x y
  have hy : 0 < 1 + ‖y‖ ^ 2 := by positivity
  calc (1 + ‖x‖ ^ 2) ^ (r / 2) * (1 + ‖y‖ ^ 2) ^ (-s / 2)
      ≤ (2 ^ (|r| / 2) * (1 + ‖x - y‖ ^ 2) ^ (|r| / 2) * (1 + ‖y‖ ^ 2) ^ (r / 2)) *
          (1 + ‖y‖ ^ 2) ^ (-s / 2) := by
        gcongr
    _ = 2 ^ (|r| / 2) * (1 + ‖x - y‖ ^ 2) ^ (|r| / 2) *
          ((1 + ‖y‖ ^ 2) ^ (r / 2) * (1 + ‖y‖ ^ 2) ^ (-s / 2)) := by ring
    _ = _ := by rw [← Real.rpow_add hy]; ring_nf

omit [SeminormedAddGroup E] in
/-- Within distance one of `y`, the weight `⟨x⟩ ^ s` is at most `2 ^ |s| ⟨y⟩ ^ s`, for every real
`s`. -/
theorem one_add_norm_sq_rpow_le_of_norm_sub_le_one [SeminormedAddCommGroup E] {x y : E}
    (h : ‖x - y‖ ≤ 1) (s : ℝ) :
    (1 + ‖x‖ ^ 2) ^ (s / 2) ≤ 2 ^ |s| * (1 + ‖y‖ ^ 2) ^ (s / 2) := by
  have hb : (1 + ‖x - y‖ ^ 2) ^ (|s| / 2) ≤ 2 ^ (|s| / 2) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith [norm_nonneg (x - y)]) (by positivity)
  calc (1 + ‖x‖ ^ 2) ^ (s / 2)
      ≤ 2 ^ (|s| / 2) * (1 + ‖x - y‖ ^ 2) ^ (|s| / 2) * (1 + ‖y‖ ^ 2) ^ (s / 2) :=
        one_add_norm_sq_rpow_le_mul_sub s x y
    _ ≤ 2 ^ (|s| / 2) * 2 ^ (|s| / 2) * (1 + ‖y‖ ^ 2) ^ (s / 2) := by gcongr
    _ = 2 ^ |s| * (1 + ‖y‖ ^ 2) ^ (s / 2) := by
        rw [← Real.rpow_add two_pos]
        ring_nf

omit [SeminormedAddGroup E] in
/-- Comparable norms give comparable Japanese bracket weights: if `‖x‖ ≤ c ‖y‖` and `‖y‖ ≤ c ‖x‖`
with `c ≥ 1`, then `(1 + ‖x‖ ^ 2) ^ (s / 2) ≤ c ^ |s| (1 + ‖y‖ ^ 2) ^ (s / 2)` for every real `s`.
For `s ≥ 0` this uses `‖x‖ ≤ c ‖y‖`, and for `s < 0` it uses `‖y‖ ≤ c ‖x‖`. This applies to
`y = A x` for a continuous linear equivalence `A` with `c ≥ max 1 (max ‖A‖ ‖A⁻¹‖)`. -/
theorem one_add_norm_sq_rpow_le_of_norm_le_mul [SeminormedAddGroup E] {F : Type*}
    [SeminormedAddGroup F] {c : ℝ} (hc : 1 ≤ c) (s : ℝ) {x : E} {y : F} (hxy : ‖x‖ ≤ c * ‖y‖)
    (hyx : ‖y‖ ≤ c * ‖x‖) :
    (1 + ‖x‖ ^ 2) ^ (s / 2) ≤ c ^ |s| * (1 + ‖y‖ ^ 2) ^ (s / 2) := by
  -- In both cases one bracket is at most `c ^ 2` times the other.
  have hc1 : 1 * 1 ≤ c * c := mul_self_le_mul_self zero_le_one hc
  have hsq : ∀ {a b : ℝ}, 0 ≤ a → a ≤ c * b → 1 + a ^ 2 ≤ c ^ 2 * (1 + b ^ 2) :=
    fun {a b} ha hab ↦ by nlinarith [sq_nonneg b, mul_self_le_mul_self ha hab]
  have hpow : (c ^ 2) ^ (s / 2) = c ^ s := by
    rw [← Real.rpow_natCast c 2, ← Real.rpow_mul (by linarith)]
    congr 1
    push_cast
    ring
  rcases le_or_gt 0 s with hs | hs
  · rw [abs_of_nonneg hs, ← hpow, ← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) (hsq (norm_nonneg x) hxy) (by positivity)
  · rw [abs_of_neg hs, Real.rpow_neg (by linarith), ← hpow,
      ← Real.inv_rpow (by positivity), ← Real.mul_rpow (by positivity) (by positivity)]
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
    rw [← div_eq_inv_mul, div_le_iff₀ (by positivity), mul_comm]
    exact hsq (norm_nonneg y) hyx

omit [SeminormedAddGroup E] in
/-- Rescaling by a factor `c ≥ 1` changes the Japanese bracket weight by at most `c ^ |s|`: if
`‖x‖ = c ‖y‖`, then `(1 + ‖x‖ ^ 2) ^ (s / 2) ≤ c ^ |s| (1 + ‖y‖ ^ 2) ^ (s / 2)` for every real `s`.
-/
theorem one_add_norm_sq_rpow_le_of_norm_eq_mul [SeminormedAddGroup E] {F : Type*}
    [SeminormedAddGroup F] {c : ℝ} (hc : 1 ≤ c) (s : ℝ) {x : E} {y : F} (h : ‖x‖ = c * ‖y‖) :
    (1 + ‖x‖ ^ 2) ^ (s / 2) ≤ c ^ |s| * (1 + ‖y‖ ^ 2) ^ (s / 2) :=
  one_add_norm_sq_rpow_le_of_norm_le_mul hc s h.le <| by
    rw [h]
    nlinarith [norm_nonneg y, mul_self_le_mul_self zero_le_one hc]

omit [SeminormedAddGroup E] in
/-- Scaling by `c ≥ 1` changes the Japanese bracket weight by at most `c ^ |s|`:
`(1 + ‖c • x‖ ^ 2) ^ (s / 2) ≤ c ^ |s| (1 + ‖x‖ ^ 2) ^ (s / 2)` for every real `s`. -/
theorem one_add_norm_smul_sq_rpow_le [SeminormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ}
    (hc : 1 ≤ c) (s : ℝ) (x : E) :
    (1 + ‖c • x‖ ^ 2) ^ (s / 2) ≤ c ^ |s| * (1 + ‖x‖ ^ 2) ^ (s / 2) :=
  one_add_norm_sq_rpow_le_of_norm_eq_mul hc s
    (by rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans hc)])

omit [SeminormedAddGroup E] in
/-- Rescaling the argument by `c ≠ 0` changes `(1 + ‖x‖ ^ 2) ^ r` by at most a constant factor. -/
theorem exists_one_add_norm_smul_sq_rpow_le [SeminormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ}
    (hc : c ≠ 0) (r : ℝ) :
    ∃ C, ∀ x : E, (1 + ‖c • x‖ ^ 2) ^ r ≤ C * (1 + ‖x‖ ^ 2) ^ r := by
  have hc0 : 0 < |c| := abs_pos.2 hc
  refine ⟨max 1 (max |c| |c|⁻¹) ^ |2 * r|, fun x ↦ ?_⟩
  have h := one_add_norm_sq_rpow_le_of_norm_le_mul (le_max_left 1 (max |c| |c|⁻¹)) (2 * r)
    (x := c • x) (y := x) ?_ ?_
  · rwa [mul_div_cancel_left₀ r two_ne_zero] at h
  · rw [norm_smul, Real.norm_eq_abs]
    gcongr
    exact (le_max_left _ _).trans (le_max_right _ _)
  · calc ‖x‖ = |c|⁻¹ * ‖c • x‖ := by
          rw [norm_smul, Real.norm_eq_abs, inv_mul_cancel_left₀ hc0.ne']
      _ ≤ max 1 (max |c| |c|⁻¹) * ‖c • x‖ := by
          gcongr
          exact (le_max_right _ _).trans (le_max_right _ _)

omit [SeminormedAddGroup E] in
/-- Peetre's inequality for the shift `ξ + c • θ` by a multiple of `θ` with `c ≥ 1`:
`(1 + ‖ξ + c • θ‖ ^ 2) ^ (m / 2) ≤ 2 ^ (|m| / 2) c ^ |m| (1 + ‖ξ‖ ^ 2) ^ (m / 2)
(1 + ‖θ‖ ^ 2) ^ (|m| / 2)` for every real `m`. -/
theorem one_add_norm_add_smul_sq_rpow_le [SeminormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ}
    (hc : 1 ≤ c) (m : ℝ) (ξ θ : E) :
    (1 + ‖ξ + c • θ‖ ^ 2) ^ (m / 2) ≤
      2 ^ (|m| / 2) * c ^ |m| * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖θ‖ ^ 2) ^ (|m| / 2) := by
  refine (one_add_norm_add_sq_rpow_le_mul m ξ (c • θ)).trans ?_
  have := one_add_norm_smul_sq_rpow_le hc |m| θ
  rw [abs_abs] at this
  calc 2 ^ (|m| / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖c • θ‖ ^ 2) ^ (|m| / 2)
      ≤ 2 ^ (|m| / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (c ^ |m| * (1 + ‖θ‖ ^ 2) ^ (|m| / 2)) := by
        gcongr
    _ = _ := by ring

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

/-- A natural power of the Japanese bracket is at most the same power of `1 + ‖x‖`:
`(1 + ‖x‖ ^ 2) ^ (N / 2) ≤ (1 + ‖x‖) ^ N`. -/
theorem one_add_norm_sq_rpow_le_one_add_norm_pow (x : E) (N : ℕ) :
    (1 + ‖x‖ ^ 2) ^ ((N : ℝ) / 2) ≤ (1 + ‖x‖) ^ N :=
  calc (1 + ‖x‖ ^ 2) ^ ((N : ℝ) / 2) ≤ ((1 + ‖x‖) ^ 2) ^ ((N : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity)
          (by rw [add_sq, one_pow, mul_one]; linarith [norm_nonneg x]) (by positivity)
    _ = (1 + ‖x‖) ^ N := by
        rw [← Real.rpow_natCast (1 + ‖x‖) 2, ← Real.rpow_mul (by positivity),
          ← Real.rpow_natCast]
        ring_nf

/-- A real power of the Japanese bracket is at most every larger natural power of `1 + ‖x‖`: if
`s ≤ N`, then `(1 + ‖x‖ ^ 2) ^ (s / 2) ≤ (1 + ‖x‖) ^ N`. -/
theorem one_add_norm_sq_rpow_le_one_add_norm_pow_of_le (x : E) {s : ℝ} {N : ℕ} (hs : s ≤ N) :
    (1 + ‖x‖ ^ 2) ^ (s / 2) ≤ (1 + ‖x‖) ^ N :=
  (Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (by positivity)) (by linarith)).trans
    (one_add_norm_sq_rpow_le_one_add_norm_pow x N)

/-- Raising the order of the Japanese bracket by at most a natural number `N` costs at most the
factor `(1 + ‖x‖) ^ N`: `(1 + ‖x‖ ^ 2) ^ (a / 2) ≤ (1 + ‖x‖ ^ 2) ^ (b / 2) (1 + ‖x‖) ^ N` for
`a ≤ b + N`. -/
theorem one_add_norm_sq_rpow_le_mul_one_add_norm_pow (x : E) {a b : ℝ} {N : ℕ}
    (h : a ≤ b + N) : (1 + ‖x‖ ^ 2) ^ (a / 2) ≤ (1 + ‖x‖ ^ 2) ^ (b / 2) * (1 + ‖x‖) ^ N :=
  calc (1 + ‖x‖ ^ 2) ^ (a / 2) ≤ (1 + ‖x‖ ^ 2) ^ ((b + N) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (by positivity)) (by linarith)
    _ = (1 + ‖x‖ ^ 2) ^ (b / 2) * (1 + ‖x‖ ^ 2) ^ ((N : ℝ) / 2) := by
        rw [add_div, Real.rpow_add (by positivity)]
    _ ≤ (1 + ‖x‖ ^ 2) ^ (b / 2) * (1 + ‖x‖) ^ N := by
        gcongr
        exact one_add_norm_sq_rpow_le_one_add_norm_pow x N

/-- The Japanese bracket is at most the inhomogeneous norm: for `r ≥ 0`,
`(1 + ‖x‖ ^ 2) ^ (r / 2) ≤ (1 + ‖x‖) ^ r`. -/
theorem one_add_norm_sq_rpow_le_one_add_norm_rpow (x : E) {r : ℝ} (hr : 0 ≤ r) :
    (1 + ‖x‖ ^ 2) ^ (r / 2) ≤ (1 + ‖x‖) ^ r :=
  calc (1 + ‖x‖ ^ 2) ^ (r / 2) ≤ ((1 + ‖x‖) ^ 2) ^ (r / 2) :=
        Real.rpow_le_rpow (by positivity)
          (by rw [add_sq, one_pow, mul_one]; linarith [norm_nonneg x]) (by positivity)
    _ = (1 + ‖x‖) ^ r := by
        rw [← Real.rpow_natCast (1 + ‖x‖) 2, ← Real.rpow_mul (by positivity)]
        ring_nf

/-- The powers of the Japanese bracket multiply: `⟨x⟩ ^ (s + t) = ⟨x⟩ ^ s ⟨x⟩ ^ t`. -/
theorem one_add_norm_sq_rpow_add (x : E) (s t : ℝ) :
    (1 + ‖x‖ ^ 2) ^ ((s + t) / 2) = (1 + ‖x‖ ^ 2) ^ (s / 2) * (1 + ‖x‖ ^ 2) ^ (t / 2) := by
  rw [← Real.rpow_add (by positivity)]
  ring_nf

/-- A nonpositive power of the Japanese bracket is at most `1`: `⟨x⟩ ^ s ≤ 1` for `s ≤ 0`. -/
theorem one_add_norm_sq_rpow_le_one (x : E) {s : ℝ} (hs : s ≤ 0) : (1 + ‖x‖ ^ 2) ^ (s / 2) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by linarith)

/-- Opposite powers of the Japanese bracket cancel: `⟨x⟩ ^ (-s) ⟨x⟩ ^ s = 1`. -/
theorem one_add_norm_sq_rpow_neg_mul_rpow (x : E) (s : ℝ) :
    (1 + ‖x‖ ^ 2) ^ (-s / 2) * (1 + ‖x‖ ^ 2) ^ (s / 2) = 1 := by
  rw [← one_add_norm_sq_rpow_add, neg_add_cancel, zero_div, Real.rpow_zero]

/-- **The bracket away from a cone.** If `y` lies outside the open ball of radius `c ‖x‖` about
`x`, `c > 0`, then `‖y‖` is controlled by `‖x - y‖`, and so is the bracket at `y`:
`⟨y⟩ ^ s ≤ (c⁻¹ + 1) ^ |s| (1 + ‖x - y‖) ^ |s|` for every real `s`. -/
theorem one_add_norm_sq_rpow_le_of_mul_norm_le_norm_sub {c : ℝ} (hc : 0 < c) {x y : E}
    (h : c * ‖x‖ ≤ ‖x - y‖) (s : ℝ) :
    (1 + ‖y‖ ^ 2) ^ (s / 2) ≤ (c⁻¹ + 1) ^ |s| * (1 + ‖x - y‖) ^ |s| := by
  have hx : ‖x‖ ≤ c⁻¹ * ‖x - y‖ := by
    rw [inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
    exact h
  have hy : 1 + ‖y‖ ≤ (c⁻¹ + 1) * (1 + ‖x - y‖) := by
    have := norm_le_norm_add_norm_sub' y x
    rw [norm_sub_rev] at this
    have hc1 : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
    nlinarith [norm_nonneg (x - y)]
  calc (1 + ‖y‖ ^ 2) ^ (s / 2) ≤ (1 + ‖y‖ ^ 2) ^ (|s| / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖y‖])
          (by linarith [le_abs_self s])
    _ ≤ (1 + ‖y‖) ^ |s| := one_add_norm_sq_rpow_le_one_add_norm_rpow y (abs_nonneg s)
    _ ≤ ((c⁻¹ + 1) * (1 + ‖x - y‖)) ^ |s| := by gcongr
    _ = (c⁻¹ + 1) ^ |s| * (1 + ‖x - y‖) ^ |s| := Real.mul_rpow (by positivity) (by positivity)

/-- A natural power of the Japanese bracket is comparable to the same power of the norm:
`(1 + ‖x‖ ^ 2) ^ (N / 2) ≤ 2 ^ N (1 + ‖x‖ ^ N)`. -/
theorem one_add_norm_sq_rpow_le_two_pow_mul_one_add_norm_pow (x : E) (N : ℕ) :
    (1 + ‖x‖ ^ 2) ^ ((N : ℝ) / 2) ≤ 2 ^ N * (1 + ‖x‖ ^ N) :=
  calc (1 + ‖x‖ ^ 2) ^ ((N : ℝ) / 2) ≤ (1 + ‖x‖) ^ N :=
        one_add_norm_sq_rpow_le_one_add_norm_pow x N
    _ ≤ 2 ^ (N - 1) * (1 ^ N + ‖x‖ ^ N) := add_pow_le zero_le_one (norm_nonneg x) N
    _ ≤ 2 ^ N * (1 + ‖x‖ ^ N) := by
        rw [one_pow]
        gcongr
        exacts [one_le_two, N.sub_le 1]

/-- For `a > 0` and `R > 0`, where `a R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ≤ b R ^ 2`, every power
`(1 + ‖ξ‖ ^ 2) ^ (u / 2)` of the Japanese bracket is at most
`max (a ^ (u / 2)) (b ^ (u / 2)) R ^ u`. -/
theorem one_add_norm_sq_rpow_le_max_mul_rpow {a b R : ℝ} (ha : 0 < a) (hR : 0 < R) {ξ : E}
    (hξ : a * R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ∧ 1 + ‖ξ‖ ^ 2 ≤ b * R ^ 2) (u : ℝ) :
    (1 + ‖ξ‖ ^ 2) ^ (u / 2) ≤ max (a ^ (u / 2)) (b ^ (u / 2)) * R ^ u := by
  have hb : 0 < b := pos_of_mul_pos_left ((mul_pos ha (by positivity)).trans_le
    (hξ.1.trans hξ.2)) (by positivity)
  have hRu (c : ℝ) (hc : 0 < c) : (c * R ^ 2) ^ (u / 2) = c ^ (u / 2) * R ^ u := by
    rw [Real.mul_rpow hc.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    congr 2
    push_cast
    ring
  rcases le_total 0 u with hu | hu
  · calc (1 + ‖ξ‖ ^ 2) ^ (u / 2) ≤ (b * R ^ 2) ^ (u / 2) :=
          Real.rpow_le_rpow (by positivity) hξ.2 (by positivity)
      _ ≤ _ := by
          rw [hRu b hb]
          gcongr
          exact le_max_right _ _
  · calc (1 + ‖ξ‖ ^ 2) ^ (u / 2) ≤ (a * R ^ 2) ^ (u / 2) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hξ.1 (by linarith)
      _ ≤ _ := by
          rw [hRu a ha]
          gcongr
          exact le_max_left _ _

omit [SeminormedAddGroup E] in
/-- On the annulus `0 < c ≤ ‖ζ‖ ≤ d`, every power of the Japanese bracket of `t ζ` with `t ≥ 1` is
at most a multiple of `t ^ u`: `(1 + ‖t ζ‖ ^ 2) ^ (u / 2) ≤ max ((c ^ 2) ^ (u / 2))
((1 + d ^ 2) ^ (u / 2)) t ^ u`. -/
theorem one_add_norm_smul_sq_rpow_le_max_mul_rpow [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {c d t : ℝ} (hc : 0 < c) (ht : 1 ≤ t) {ζ : E} (hζ : c ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ d) (u : ℝ) :
    (1 + ‖t • ζ‖ ^ 2) ^ (u / 2) ≤ max ((c ^ 2) ^ (u / 2)) ((1 + d ^ 2) ^ (u / 2)) * t ^ u := by
  have ht0 : 0 < t := one_pos.trans_le ht
  have htζ : ‖t • ζ‖ = t * ‖ζ‖ := by rw [norm_smul, Real.norm_of_nonneg ht0.le]
  have hlo := mul_self_le_mul_self (by positivity) (mul_le_mul_of_nonneg_left hζ.1 ht0.le)
  have hhi := mul_self_le_mul_self (by positivity) (mul_le_mul_of_nonneg_left hζ.2 ht0.le)
  exact one_add_norm_sq_rpow_le_max_mul_rpow (by positivity) ht0
    ⟨by rw [htζ]; nlinarith, by rw [htζ]; nlinarith [one_le_pow₀ (n := 2) ht]⟩ u

end TauCeti

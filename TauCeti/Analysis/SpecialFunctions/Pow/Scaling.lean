/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real powers of a ratio of radii

Scaling arguments compare a quantity on a ball of radius `r` with the same quantity on a larger
ball of radius `R`, and the comparison is expressed through real powers of the ratio `r / R`.
This file collects the rearrangements of such powers that these arguments need, together with
comparisons of powers of two comparable quantities, such as a time and a time step.

* A power of `r` is a power of `r / R` times a power of `R`. So a bound `c R^a ≤ M` on a
  dimensionless constant gives `r^{2a} c² ≤ (r / R)^{2a} M²`, and a bound `c² R^{d+2a} ≤ V` gives
  `r^{2a} c² r^d ≤ V (r / R)^{d+2a}`.
* For `b ≤ a`, such a quantity also decays like `(r / R)^{d+2b}`, with the constant
  `(R^{a-b} c)² R^{d+2b}`.
* A power `(r / R)^γ` of the ratio splits as `R^{-γ} r^γ`, common radii cancel via
  `(a R)^{-γ} (b R)^γ = (b / a)^γ`, and shrinking the outer radius by a factor `θ` multiplies it
  by `θ^{-γ}`.
* Shrinking a radius `R` to `R / N`, `N ≥ 1`, costs at most a factor `N` in `R^{-α}` for `α ≤ 1`.
* A bound `βR ≤ σλ` on a dimensionless ratio gives `(1 + (βR/λ)²)ⁿ ≤ (1 + σ²)ⁿ`.
* A constant of the form `(R^{d/2+a} Q)²`, which is the natural scale of an `L²` quantity on a
  ball of radius `R` in dimension `d`, equals `R^d (R^a Q)²` and bounds `c² R^{d+2a}` for
  `0 ≤ c ≤ Q`. So for `b ≤ a` and `R^{a-b} c ≤ Q`, a quantity `r^{2a} c² r^d` of order
  `r^{d+2a}` is at most `(R^{d/2+b} Q)² (r / R)^{d+2b}`.
* For `0 ≤ p` and `0 ≤ h`, a nonnegative quantity `r ≤ A h` has `r ^ p ≤ A ^ p h ^ p`. This is
  how, in a temporal Hölder estimate with exponent `p`, a time at most `A` times the time step `h`
  is bounded by a multiple of `h ^ p`. Consequently, if two points `x` and `y` of a pseudometric
  space lie within `c t ^ p` and `c t' ^ p` of a common point, with `0 ≤ c`, `0 ≤ p`,
  `0 ≤ t ≤ A h` and `0 ≤ t' ≤ h`, then `dist x y ≤ (A ^ p + 1) c h ^ p`.
* For every real exponent `s`, a quantity `x` with `a y ≤ x ≤ b y`, `0 < a` and `0 ≤ y` has
  `x ^ s ≤ max (a ^ s) (b ^ s) y ^ s`. For `0 < y`, so that `a ≤ b`, the factor is `b ^ s` for
  `s ≥ 0` and `a ^ s` for `s ≤ 0`; for `y = 0` the hypotheses force `x = 0`, and `b` is
  unconstrained. At `y = 1` this bounds a power on an interval `[a, b]` by its larger endpoint
  value. For `a = 1 / 2` and `b = 2` it gives `TauCeti.rpow_le_two_rpow_abs_mul`:
  `y ^ p ≤ 2 ^ |p| x ^ p` for `x / 2 ≤ y ≤ 2 x` and every real `p`.
-/

public section

namespace Real

/-- `r^{2a} c² ≤ (r / R)^{2a} M²` when `c R^a ≤ M`. -/
theorem rpow_mul_sq_le {r R c M a : ℝ} (hr : 0 < r) (hR : 0 < R) (hc : 0 ≤ c)
    (hM : c * R ^ a ≤ M) : r ^ (2 * a) * c ^ 2 ≤ (r / R) ^ (2 * a) * M ^ 2 := by
  have h1 : r ^ (2 * a) = (r / R) ^ (2 * a) * (R ^ a) ^ 2 := by
    rw [div_rpow hr.le hR.le, ← rpow_natCast, ← rpow_mul hR.le, Nat.cast_two,
      mul_comm a 2, div_mul_cancel₀ _ (rpow_pos_of_pos hR _).ne']
  rw [h1, mul_assoc, ← mul_pow, mul_comm (R ^ a)]
  gcongr

/-- `r^{2a} c² r^d ≤ V (r / R)^{d+2a}` when `c² R^{d+2a} ≤ V`. -/
theorem rpow_mul_mul_rpow_le {r R c V a d : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hc : c ^ 2 * R ^ (d + 2 * a) ≤ V) :
    r ^ (2 * a) * (c ^ 2 * r ^ d) ≤ V * (r / R) ^ (d + 2 * a) := by
  have h1 : r ^ (2 * a) * (c ^ 2 * r ^ d) =
      (r / R) ^ (d + 2 * a) * (c ^ 2 * R ^ (d + 2 * a)) := by
    rw [div_rpow hr.le hR.le, add_comm d, rpow_add hr]
    field_simp
  rw [h1, mul_comm V]
  gcongr

/-- `r^{2a} c² r^d ≤ (R^{a-b} c)² R^{d+2b} (r / R)^{d+2b}` for `0 < r ≤ R` and `b ≤ a`: a quantity
of order `r^{d+2a}` decays at least with the smaller exponent `d + 2b`, at the cost of the
dimensionless factor `R^{a-b}`. -/
theorem rpow_mul_mul_rpow_le_mul_rpow_of_le {r R c a b d : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hba : b ≤ a) :
    r ^ (2 * a) * (c ^ 2 * r ^ d) ≤
      (R ^ (a - b) * c) ^ 2 * R ^ (d + 2 * b) * (r / R) ^ (d + 2 * b) := by
  have hR : 0 < R := hr.trans_le hrR
  have hc : (R ^ (a - b) * c) ^ 2 * R ^ (d + 2 * b) = c ^ 2 * R ^ (d + 2 * a) := by
    rw [mul_pow, ← rpow_mul_natCast hR.le, mul_right_comm, ← rpow_add hR]
    ring_nf
  rw [hc]
  refine (rpow_mul_mul_rpow_le hr hR le_rfl).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact rpow_le_rpow_of_exponent_ge (div_pos hr hR) (div_le_one_of_le₀ hrR hR.le) (by linarith)

/-- `(r / R)^γ = R^{-γ} r^γ`. -/
theorem div_rpow_eq_rpow_neg_mul_rpow {r R γ : ℝ} (hr : 0 ≤ r) (hR : 0 < R) :
    (r / R) ^ γ = R ^ (-γ) * r ^ γ := by
  rw [div_rpow hr hR.le, rpow_neg hR.le, div_eq_inv_mul]

/-- `(a * R)^{-γ} * (b * R)^γ = (b / a)^γ`. -/
theorem mul_rpow_neg_mul_mul_rpow {a b R γ : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hR : 0 < R) :
    (a * R) ^ (-γ) * (b * R) ^ γ = (b / a) ^ γ := by
  rw [← div_rpow_eq_rpow_neg_mul_rpow (mul_nonneg hb hR.le) (mul_pos ha hR),
    mul_div_mul_right _ _ hR.ne']

/-- `(r / (θ R))^γ = θ^{-γ} (r / R)^γ`. -/
theorem div_mul_rpow_eq {r θ R γ : ℝ} (hr : 0 ≤ r) (hθ : 0 < θ) (hR : 0 < R) :
    (r / (θ * R)) ^ γ = θ ^ (-γ) * (r / R) ^ γ := by
  rw [div_mul_eq_div_div_swap, div_eq_inv_mul (r / R), mul_rpow (inv_nonneg.2 hθ.le)
    (div_nonneg hr hR.le), inv_rpow hθ.le, rpow_neg hθ.le]

/-- Shrinking the radius from `R` to `R / N`, `N ≥ 1`, costs at most a factor `N` in `R^{-α}` for
`α ≤ 1`: `(R / N)^{-α} ≤ N R^{-α}`. -/
theorem div_rpow_neg_le_mul_rpow_neg {N R α : ℝ} (hα1 : α ≤ 1) (hN : 1 ≤ N) (hR : 0 ≤ R) :
    (R / N) ^ (-α) ≤ N * R ^ (-α) := by
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  rw [div_rpow hR hN0, rpow_neg hN0, div_inv_eq_mul, mul_comm]
  gcongr
  exact rpow_le_self_of_one_le hN hα1

/-- `(1 + (x/λ)²)ⁿ ≤ (1 + σ²)ⁿ` for `0 ≤ x`, `0 < λ` and `x ≤ σλ`. -/
theorem one_add_div_sq_pow_le {x lam σ : ℝ} (n : ℕ) (hx : 0 ≤ x) (hlam : 0 < lam)
    (hxσ : x ≤ σ * lam) : (1 + (x / lam) ^ 2) ^ n ≤ (1 + σ ^ 2) ^ n := by
  gcongr
  exact (div_le_iff₀ hlam).2 hxσ

/-- `(R^{d/2+a} Q)² = R^d (R^a Q)²`. -/
theorem rpow_div_two_add_mul_sq {R d a : ℝ} (Q : ℝ) (hR : 0 < R) :
    (R ^ (d / 2 + a) * Q) ^ 2 = R ^ d * (R ^ a * Q) ^ 2 := by
  rw [mul_pow, mul_pow, ← rpow_mul_natCast hR.le, ← rpow_mul_natCast hR.le, Nat.cast_two,
    add_mul, div_mul_cancel₀ _ two_ne_zero, rpow_add hR]
  ring

/-- `c² R^{d+2a} ≤ (R^{d/2+a} Q)²` when `0 ≤ c ≤ Q`. -/
theorem sq_mul_rpow_add_two_mul_le {R c Q d a : ℝ} (hR : 0 < R) (hc : 0 ≤ c) (hcQ : c ≤ Q) :
    c ^ 2 * R ^ (d + 2 * a) ≤ (R ^ (d / 2 + a) * Q) ^ 2 := by
  have h : R ^ (d + 2 * a) = (R ^ (d / 2 + a)) ^ 2 := by
    rw [← rpow_mul_natCast hR.le, Nat.cast_two, add_mul, div_mul_cancel₀ _ two_ne_zero, mul_comm]
  rw [h, mul_pow, mul_comm]
  gcongr

/-- `r^{2a} c² r^d ≤ (R^{d/2+b} Q)² (r / R)^{d+2b}` for `0 < r ≤ R`, `b ≤ a` and
`0 ≤ R^{a-b} c ≤ Q`: a quantity of order `r^{d+2a}` decays with the smaller exponent `d + 2b`,
measured at the `L²` scale `(R^{d/2+b} Q)²` of a ball of radius `R` in dimension `d`. -/
theorem rpow_mul_mul_rpow_le_rpow_div_two_add_mul_sq_mul_rpow {r R c Q a b d : ℝ} (hr : 0 < r)
    (hrR : r ≤ R) (hba : b ≤ a) (hc : 0 ≤ c) (hcQ : R ^ (a - b) * c ≤ Q) :
    r ^ (2 * a) * (c ^ 2 * r ^ d) ≤ (R ^ (d / 2 + b) * Q) ^ 2 * (r / R) ^ (d + 2 * b) := by
  have hR : 0 < R := hr.trans_le hrR
  exact (rpow_mul_mul_rpow_le_mul_rpow_of_le hr hrR hba).trans (mul_le_mul_of_nonneg_right
    (sq_mul_rpow_add_two_mul_le hR (mul_nonneg (rpow_nonneg hR.le _) hc) hcQ) (by positivity))

/-- For `0 ≤ p` and `0 ≤ h`, a nonnegative quantity at most `A h` has `p`-th power at most
`A ^ p h ^ p`. -/
theorem rpow_le_rpow_mul_rpow_of_le_mul (r : ℝ) {A h p : ℝ} (hr : 0 ≤ r) (hh : 0 ≤ h)
    (hrh : r ≤ A * h) (hp : 0 ≤ p) : r ^ p ≤ A ^ p * h ^ p := by
  rcases le_or_gt 0 A with hA | hA
  · exact (rpow_le_rpow hr hrh hp).trans_eq (mul_rpow hA hh)
  -- For `A < 0` the hypotheses force `r = h = 0`.
  obtain rfl : h = 0 := le_antisymm (by nlinarith) hh
  obtain rfl : r = 0 := le_antisymm (by simpa using hrh) hr
  rcases hp.eq_or_lt with rfl | hp
  · simp
  · simp [zero_rpow hp.ne']

/-- Powers of comparable quantities are comparable: if `a y ≤ x ≤ b y` with `0 < a` and
`0 ≤ y`, then `x ^ s ≤ max (a ^ s) (b ^ s) * y ^ s` for every real exponent `s`. For `0 < y` the
hypotheses give `a ≤ b`, so the maximum is `b ^ s` for `s ≥ 0` and `a ^ s` for `s ≤ 0`. For
`y = 0` they force `x = 0` and leave `b` unconstrained. -/
theorem rpow_le_max_mul_rpow {a b x y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) (hax : a * y ≤ x)
    (hxb : x ≤ b * y) (s : ℝ) : x ^ s ≤ max (a ^ s) (b ^ s) * y ^ s := by
  rcases hy.eq_or_lt with rfl | hy
  · -- For `y = 0` the hypotheses force `x = 0`.
    obtain rfl : x = 0 := le_antisymm (by simpa using hxb) (by simpa using hax)
    rcases eq_or_ne s 0 with rfl | hs
    · simp
    · simp [zero_rpow hs]
  have hb : 0 ≤ b := by
    by_contra hb
    nlinarith [mul_pos ha hy]
  rcases le_total 0 s with hs | hs
  · calc x ^ s ≤ (b * y) ^ s := rpow_le_rpow (by nlinarith [mul_pos ha hy]) hxb hs
      _ = b ^ s * y ^ s := mul_rpow hb hy.le
      _ ≤ max (a ^ s) (b ^ s) * y ^ s := by
          gcongr
          exact le_max_right _ _
  · calc x ^ s ≤ (a * y) ^ s := rpow_le_rpow_of_nonpos (mul_pos ha hy) hax hs
      _ = a ^ s * y ^ s := mul_rpow ha.le hy.le
      _ ≤ max (a ^ s) (b ^ s) * y ^ s := by
          gcongr
          exact le_max_left _ _

end Real

namespace TauCeti

/-- If `x / 2 ≤ y ≤ 2 x`, then `y ^ p ≤ 2 ^ |p| x ^ p`, for positive and negative exponents
alike: the case `a = 1 / 2`, `b = 2` of `Real.rpow_le_max_mul_rpow`. -/
theorem rpow_le_two_rpow_abs_mul {x y p : ℝ} (hxy : x / 2 ≤ y) (hyx : y ≤ 2 * x) :
    y ^ p ≤ 2 ^ |p| * x ^ p := by
  rcases (by linarith : (0 : ℝ) ≤ x).eq_or_lt with rfl | hx
  · have hy : y = 0 := by linarith
    rw [hy]
    exact le_mul_of_one_le_left (Real.rpow_nonneg le_rfl p)
      (Real.one_le_rpow (by norm_num) (abs_nonneg p))
  refine (Real.rpow_le_max_mul_rpow (a := 1 / 2) (b := 2) (by norm_num) hx.le (by linarith)
    hyx p).trans (mul_le_mul_of_nonneg_right (max_le ?_ ?_) (Real.rpow_nonneg hx.le p))
  · rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_abs p)
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_abs_self p)

/-- If `x` lies within `c t ^ β` and `y` within `c t' ^ β` of a point `z`, where `0 ≤ c`,
`0 ≤ β`, `0 ≤ t ≤ A h` and `0 ≤ t' ≤ h`, then `dist x y ≤ (A ^ β + 1) c h ^ β`. -/
theorem dist_le_rpow_add_one_mul_mul_rpow_of_le_mul {X : Type*} [PseudoMetricSpace X]
    {x y z : X} {c β A h t t' : ℝ} (hc : 0 ≤ c) (hβ : 0 ≤ β) (ht : 0 ≤ t) (hth : t ≤ A * h)
    (ht' : 0 ≤ t') (ht'h : t' ≤ h) (hx : dist x z ≤ c * t ^ β) (hy : dist y z ≤ c * t' ^ β) :
    dist x y ≤ (A ^ β + 1) * c * h ^ β := by
  have h₁ : t ^ β ≤ A ^ β * h ^ β :=
    Real.rpow_le_rpow_mul_rpow_of_le_mul t ht (ht'.trans ht'h) hth hβ
  have h₂ : t' ^ β ≤ h ^ β := Real.rpow_le_rpow ht' ht'h hβ
  calc dist x y ≤ dist x z + dist y z := dist_triangle_right x y z
    _ ≤ c * (A ^ β * h ^ β) + c * h ^ β :=
        add_le_add (hx.trans (mul_le_mul_of_nonneg_left h₁ hc))
          (hy.trans (mul_le_mul_of_nonneg_left h₂ hc))
    _ = (A ^ β + 1) * c * h ^ β := by ring

end TauCeti

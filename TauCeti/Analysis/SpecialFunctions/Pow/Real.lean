/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real powers

The inverse square root is the real power with exponent `-1/2`: `(√x)⁻¹ = x ^ (-2⁻¹)`. Like
Mathlib's `Real.sqrt_eq_rpow`, this holds for every real `x`. For `x < 0` both sides vanish: the
square root is `0`, and `x ^ y = exp (log x * y) * cos (y * π)` has the factor `cos (-π / 2) = 0`.
This is the form in which a kernel `1 / √d` is compared with the singular powers `|x - c| ^ (-1/2)`.

Eventually along a filter on which `x` is positive, the power `x ^ q` is `exp (q * log x)`. This is
the form in which power weights `x ^ q` are compared with exponential tilting weights.

The square root of a natural power of a nonnegative real is the real power with half the exponent:
`√(x ^ n) = x ^ (n / 2)`. This is the form in which a determinant `det (c • G) = c ^ n det G` of
an `n × n` matrix contributes to a volume density `√(det G)`.

A natural power `b ^ n` with `1 ≤ b` and `n ≤ δ r` is at most `(b ^ δ) ^ r`, which turns a degree
bound with a real factor `δ` into a bound by an `r`-th power.

A positive power `x ↦ x ^ a` maps the open unit interval onto itself, with inverse `y ↦ y ^ a⁻¹`.
This is the image needed when a change of variables `y = x ^ a` is performed on `(0, 1)`.

A positive real raised to a finitely supported sum of exponents is the product of the powers:
`a ^ (∑ᶠ i, f i) = ∏ᶠ i, a ^ f i`, the `finsum` form of `Real.rpow_sum_of_pos`.

## Main results

* `Real.inv_sqrt_eq_rpow`: `(√x)⁻¹ = x ^ (-2⁻¹)` for every real `x`.
* `Real.rpow_eventuallyEq_exp_mul_log`: `x ^ q = exp (q * log x)` eventually along a filter on
  which `x` is eventually positive.
* `Real.sqrt_pow_eq_rpow`: `√(x ^ n) = x ^ (n / 2)` for `0 ≤ x`.
* `Real.pow_le_rpow_pow_of_le_mul`: `b ^ n ≤ (b ^ δ) ^ r` when `1 ≤ b` and `n ≤ δ r`.
* `Real.image_rpow_Ioo_zero_one`: a positive power maps the open unit interval onto itself.
* `Function.HasFiniteSupport.hasFiniteMulSupport_fun_rpow`: real powers with finitely supported
  exponents have finite multiplicative support.
* `Real.rpow_finsum_of_pos`: `a ^ (∑ᶠ i, f i) = ∏ᶠ i, a ^ f i` for `0 < a` and finitely supported
  `f`.
-/

public section

namespace Real

/-- The inverse square root is the real power with exponent `-1/2`: `(√x)⁻¹ = x ^ (-2⁻¹)`, for
every real `x`. -/
theorem inv_sqrt_eq_rpow (x : ℝ) : (√x)⁻¹ = x ^ (-2⁻¹ : ℝ) := by
  rcases le_or_gt 0 x with hx | hx
  · rw [sqrt_eq_rpow, rpow_neg hx, one_div]
  · rw [sqrt_eq_zero'.mpr hx.le, inv_zero, rpow_def_of_neg hx, neg_mul, cos_neg, inv_mul_eq_div,
      cos_pi_div_two, mul_zero]

/-- Along a filter on which `x` is eventually positive, `x ^ q` is eventually `exp (q * log x)`. -/
theorem rpow_eventuallyEq_exp_mul_log {l : Filter ℝ} (hpos : ∀ᶠ x in l, 0 < x) (q : ℝ) :
    (fun x => x ^ q) =ᶠ[l] fun x => exp (q * log x) :=
  hpos.mono fun _ hx => (rpow_def_of_pos hx q).trans (congrArg exp (mul_comm _ _))

/-- The square root of a natural power of a nonnegative real is the real power with half the
exponent: `√(x ^ n) = x ^ (n / 2)`. -/
theorem sqrt_pow_eq_rpow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : √(x ^ n) = x ^ ((n : ℝ) / 2) := by
  rw [sqrt_eq_rpow, ← rpow_natCast, ← rpow_mul hx, mul_one_div]

/-- A natural power `b ^ n` with `1 ≤ b` and `n ≤ δ r` is at most `(b ^ δ) ^ r`. This converts a
degree bound `n ≤ δ r` with a real factor `δ` into a bound by an `r`-th power. -/
theorem pow_le_rpow_pow_of_le_mul {b δ : ℝ} (hb : 1 ≤ b) {n r : ℕ} (hn : (n : ℝ) ≤ δ * r) :
    b ^ n ≤ (b ^ δ) ^ r := by
  rw [← rpow_mul_natCast (by linarith), ← rpow_natCast]
  exact rpow_le_rpow_of_exponent_le hb hn

/-- A positive power `x ↦ x ^ a` maps the open unit interval onto itself. -/
theorem image_rpow_Ioo_zero_one {a : ℝ} (ha : 0 < a) :
    (fun x : ℝ ↦ x ^ a) '' Set.Ioo 0 1 = Set.Ioo 0 1 := by
  ext y
  refine ⟨?_, fun hy ↦ ⟨y ^ a⁻¹, ⟨rpow_pos_of_pos hy.1 _,
    rpow_lt_one hy.1.le hy.2 (inv_pos.mpr ha)⟩, rpow_inv_rpow hy.1.le ha.ne'⟩⟩
  rintro ⟨x, hx, rfl⟩
  exact ⟨rpow_pos_of_pos hx.1 a, rpow_lt_one hx.1.le hx.2 ha⟩

end Real

/-- Real powers `g i ^ f i` with finitely supported exponents `f` have finite multiplicative
support. -/
theorem Function.HasFiniteSupport.hasFiniteMulSupport_fun_rpow {α : Type*} (g : α → ℝ)
    {f : α → ℝ} (hf : f.HasFiniteSupport) : (fun i ↦ g i ^ f i).HasFiniteMulSupport :=
  hf.subset fun i hi h ↦ hi (by simp [h])

/-- A positive real raised to a finitely supported sum is the product of the powers. -/
theorem Real.rpow_finsum_of_pos {α : Type*} {a : ℝ} (ha : 0 < a) {f : α → ℝ}
    (hf : f.HasFiniteSupport) : a ^ (∑ᶠ i, f i) = ∏ᶠ i, a ^ f i := by
  rw [finsum_eq_sum f hf, finprod_eq_prod_of_mulSupport_subset _ (s := hf.toFinset)
    fun i hi ↦ hf.mem_toFinset.mpr fun h ↦ hi (by simp [h]), Real.rpow_sum_of_pos ha]

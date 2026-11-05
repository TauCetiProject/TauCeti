/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Real powers

The inverse square root is the real power with exponent `-1/2`: `(√x)⁻¹ = x ^ (-2⁻¹)`. Like
Mathlib's `Real.sqrt_eq_rpow`, this holds for every real `x`. For `x < 0` both sides vanish: the
square root is `0`, and `x ^ y = exp (log x * y) * cos (y * π)` has the factor `cos (-π / 2) = 0`.
This is the form in which a kernel `1 / √d` is compared with the singular powers `|x - c| ^ (-1/2)`.
For `0 ≤ t`, its natural powers are `(√t)⁻¹ ^ n = t ^ (-n/2)`, the factor of a parabolic scaling.

Eventually along a filter on which `x` is positive, the power `x ^ q` is `exp (q * log x)`. This is
the form in which power weights `x ^ q` are compared with exponential tilting weights.

The square root of a natural power of a nonnegative real is the real power with half the exponent:
`√(x ^ n) = x ^ (n / 2)`. This is the form in which a determinant `det (c • G) = c ^ n det G` of
an `n × n` matrix contributes to a volume density `√(det G)`.

A real power of a nonnegative base can also be written as a power of its square:
`(x ^ 2) ^ (s / 2) = x ^ s`.

For `i < d`, comparing the `(d - i)`-th root `x ^ (1 / (d - i))` with `y` is comparing `x` with
the natural power `y ^ (d - i)`, the form in which spectral values of polynomials are bounded.

For `n ≠ 0`, the `n`-th power of `x ^ (1 - 1/n)` is `x ^ (n - 1)` for nonnegative `x`, the form in
which the volume factor `V ^ (1 - 1/n)` of an isoperimetric inequality is raised to the `n`-th
power.

A natural power `b ^ n` with `1 ≤ b` and `n ≤ δ r` is at most `(b ^ δ) ^ r`, which turns a degree
bound with a real factor `δ` into a bound by an `r`-th power.

A positive power `x ↦ x ^ a` maps the open unit interval onto itself, with inverse `y ↦ y ^ a⁻¹`.
This is the image needed when a change of variables `y = x ^ a` is performed on `(0, 1)`.

A real number whose natural powers grow at most polynomially, `r ^ n ≤ C * (1 + n) ^ s` for all
`n`, is at most `1`. This is how a spectral radius bound is read off from polynomially growing
norms, as for the monomials of a weighted Sobolev algebra.

A two-sided real exponential with positive decay rate is little-o of every real power of
`|x|` outside compact subsets of the real line.

A positive real raised to a finitely supported sum of exponents is the product of the powers:
`a ^ (∑ᶠ i, f i) = ∏ᶠ i, a ^ f i`, the `finsum` form of `Real.rpow_sum_of_pos`.

An exponential upper bound on a nonnegative base passes to its nonnegative real powers: if
`0 ≤ A ≤ e^{-t}` and `0 ≤ c`, then `A ^ c ≤ e^{-c t}`. This is how a bound `|q| ≤ e^{-t}` on a
nome is turned into bounds on the fractional powers `|q| ^ c` in a product estimate.

## Main results

* `Real.inv_sqrt_eq_rpow`: `(√x)⁻¹ = x ^ (-2⁻¹)` for every real `x`.
* `Real.inv_sqrt_pow_eq_rpow`: `(√t)⁻¹ ^ n = t ^ (-n/2)` for `0 ≤ t`.
* `Real.rpow_eventuallyEq_exp_mul_log`: `x ^ q = exp (q * log x)` eventually along a filter on
  which `x` is eventually positive.
* `Real.sqrt_pow_eq_rpow`: `√(x ^ n) = x ^ (n / 2)` for `0 ≤ x`.
* `Real.sq_rpow_div_two`: `(x ^ 2) ^ (s / 2) = x ^ s` for `0 ≤ x`.
* `Real.rpow_one_div_natCast_sub_le_iff`: `x ^ (1 / (d - i)) ≤ y ↔ x ≤ y ^ (d - i)` for `i < d`
  and nonnegative `x`, `y`.
* `Real.rpow_one_sub_inv_natCast_pow`: `(x ^ (1 - 1/n)) ^ n = x ^ (n - 1)` for `0 ≤ x` and
  `n ≠ 0`.
* `Real.pow_le_rpow_pow_of_le_mul`: `b ^ n ≤ (b ^ δ) ^ r` when `1 ≤ b` and `n ≤ δ r`.
* `Real.image_rpow_Ioo_zero_one`: a positive power maps the open unit interval onto itself.
* `Real.le_one_of_forall_pow_le_mul_rpow`: `r ≤ 1` when `r ^ n ≤ C * (1 + n) ^ s` for all `n`.
* `TauCeti.exp_neg_mul_abs_isLittleO_abs_rpow_cocompact`: a positive-rate exponential beats every
  real power at both ends of the real line.
* `Real.rpow_le_exp_neg_mul`: `A ^ c ≤ e^{-c t}` when `0 ≤ A ≤ e^{-t}` and `0 ≤ c`.
* `Function.HasFiniteSupport.hasFiniteMulSupport_fun_rpow`: real powers with finitely supported
  exponents have finite multiplicative support.
* `Real.rpow_finsum_of_pos`: `a ^ (∑ᶠ i, f i) = ∏ᶠ i, a ^ f i` for `0 < a` and finitely supported
  `f`.
-/

public section

open Filter Topology Asymptotics

namespace Real

/-- The inverse square root is the real power with exponent `-1/2`: `(√x)⁻¹ = x ^ (-2⁻¹)`, for
every real `x`. -/
theorem inv_sqrt_eq_rpow (x : ℝ) : (√x)⁻¹ = x ^ (-2⁻¹ : ℝ) := by
  rcases le_or_gt 0 x with hx | hx
  · rw [sqrt_eq_rpow, rpow_neg hx, one_div]
  · rw [sqrt_eq_zero'.mpr hx.le, inv_zero, rpow_def_of_neg hx, neg_mul, cos_neg, inv_mul_eq_div,
      cos_pi_div_two, mul_zero]

/-- A natural power of the inverse square root is a real power: `(√t)⁻¹ ^ n = t ^ (-n/2)` for
`0 ≤ t`. This is the factor of a parabolic scaling `x ↦ (√t)⁻¹ • x` in dimension `n`. -/
theorem inv_sqrt_pow_eq_rpow {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : (√t)⁻¹ ^ n = t ^ (-(n : ℝ) / 2) := by
  rw [rpow_div_two_eq_sqrt _ ht, rpow_neg (sqrt_nonneg t), rpow_natCast, inv_pow]

/-- Along a filter on which `x` is eventually positive, `x ^ q` is eventually `exp (q * log x)`. -/
theorem rpow_eventuallyEq_exp_mul_log {l : Filter ℝ} (hpos : ∀ᶠ x in l, 0 < x) (q : ℝ) :
    (fun x => x ^ q) =ᶠ[l] fun x => exp (q * log x) :=
  hpos.mono fun _ hx => (rpow_def_of_pos hx q).trans (congrArg exp (mul_comm _ _))

/-- The square root of a natural power of a nonnegative real is the real power with half the
exponent: `√(x ^ n) = x ^ (n / 2)`. -/
theorem sqrt_pow_eq_rpow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : √(x ^ n) = x ^ ((n : ℝ) / 2) := by
  rw [sqrt_eq_rpow, ← rpow_natCast, ← rpow_mul hx, mul_one_div]

/-- For a nonnegative real number `a`, taking the real power `s / 2` of `a ^ 2` gives `a ^ s`. -/
@[simp]
theorem sq_rpow_div_two {a : ℝ} (ha : 0 ≤ a) (s : ℝ) : (a ^ 2) ^ (s / 2) = a ^ s := by
  rw [rpow_div_two_eq_sqrt s (sq_nonneg a), sqrt_sq ha]

/-- For `i < d`, the `(d - i)`-th root of a nonnegative `x` is at most a nonnegative `y` exactly
when `x ≤ y ^ (d - i)`. -/
theorem rpow_one_div_natCast_sub_le_iff {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {d i : ℕ}
    (h : i < d) : x ^ (1 / (d - i : ℝ)) ≤ y ↔ x ≤ y ^ (d - i) := by
  rw [← Nat.cast_sub h.le, one_div,
    rpow_inv_le_iff_of_pos hx hy (by exact_mod_cast Nat.sub_pos_of_lt h), rpow_natCast]

/-- For `n ≠ 0` and nonnegative `x`, the `n`-th power of `x ^ (1 - 1/n)` is `x ^ (n - 1)`. -/
theorem rpow_one_sub_inv_natCast_pow {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) :
    (x ^ (1 - (n : ℝ)⁻¹)) ^ n = x ^ (n - 1) := by
  rw [← rpow_mul_natCast hx, sub_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn), one_mul,
    ← Nat.cast_pred (Nat.pos_of_ne_zero hn), rpow_natCast]

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

/-- A real number whose natural powers grow at most polynomially is at most `1`: otherwise
`r ^ x = exp (log r * x)` with `log r > 0` outgrows every power of `1 + x`. -/
theorem le_one_of_forall_pow_le_mul_rpow {r C s : ℝ}
    (h : ∀ n : ℕ, r ^ n ≤ C * (1 + n) ^ s) : r ≤ 1 := by
  by_contra! h1
  have h0 : 0 < r := zero_lt_one.trans h1
  have hlim : Tendsto (fun n : ℕ ↦ C * r * ((1 + n) ^ s / r ^ (1 + (n : ℝ)))) atTop (𝓝 0) := by
    simpa [rpow_def_of_pos h0] using
      (((isLittleO_rpow_exp_pos_mul_atTop s (log_pos h1)).comp_tendsto
        (tendsto_atTop_add_const_left _ 1 tendsto_natCast_atTop_atTop)).tendsto_div_nhds_zero
          ).const_mul (C * r)
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds one_pos)).exists
  refine hn.not_ge ?_
  rw [rpow_add h0, rpow_one, rpow_natCast, mul_div_assoc', le_div_iff₀ (by positivity), one_mul]
  calc r * r ^ n ≤ r * (C * (1 + n) ^ s) := by gcongr; exact h n
    _ = C * r * (1 + n) ^ s := by ring

/-- If `0 ≤ A ≤ e^{-t}` and `0 ≤ c`, then `A ^ c ≤ e^{-c t}`. -/
theorem rpow_le_exp_neg_mul {A t c : ℝ} (hA : 0 ≤ A) (hAt : A ≤ exp (-t)) (hc : 0 ≤ c) :
    A ^ c ≤ exp (-(c * t)) := by
  refine (rpow_le_rpow hA hAt hc).trans_eq ?_
  rw [← exp_mul]
  ring_nf

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

/-! ### Two-sided exponential decay -/

namespace TauCeti

/-- **Rapid decay of the two-sided real exponential.** For any positive real rate `a`,
`exp (-(a * |x|))` is little-o of `|x| ^ s` at `cocompact ℝ`, for every real exponent `s`.

Adapted from `ForTauCeti/Analysis/Fourier/ExponentialAbs.lean` in
[AIQ-Kitware/aiq-dkps-formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Apache-2.0; copyright 2026 Kitware, Inc.; authors Jon Crall and GPT 5.6 High). -/
theorem exp_neg_mul_abs_isLittleO_abs_rpow_cocompact {a : ℝ} (ha : 0 < a) (s : ℝ) :
    (fun x : ℝ => Real.exp (-(a * |x|))) =o[cocompact ℝ]
      (fun x : ℝ => |x| ^ s) := by
  simpa only [Function.comp_def, Real.norm_eq_abs, neg_mul] using
    (isLittleO_exp_neg_mul_rpow_atTop ha s).comp_tendsto
      (tendsto_norm_cocompact_atTop (E := ℝ))

end TauCeti

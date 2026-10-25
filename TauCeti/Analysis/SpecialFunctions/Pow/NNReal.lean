/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Real powers in `ℝ≥0∞`

If `X ^ r ≤ C * X ^ (r - 1)` for a finite `X`, then `X ≤ C`: the factor `X ^ (r - 1)` cancels,
since it is neither `0` nor `∞` unless `X = 0`, in which case the conclusion is trivial. This is
the last step of every norming argument for `Lᵖ` norms, where `X` is a norm and `X ^ r` is its
pairing with the extremal function.

For an exponent `p ∈ [0, 1]` the powers `x ^ p` and `x ^ (1 - p)` multiply back to `x`, with no
finiteness or positivity hypothesis on `x`. This is the case `s = t` of geometric interpolations
`t ^ p s ^ (1 - p)`, such as the distortion coefficient `τ_{K,N}^{(t)}(θ)` with `p = 1 / N`.
For distinct `x` and `y` such a weighted geometric mean `x ^ (1 - p) * y ^ p` still dominates
`min x y`, which compares the hypotheses of the Prékopa–Leindler inequality and of its version
for the minimum.

A nonpositive real power is antitone on `ℝ≥0∞`. Because `0 ^ z = ∞` for `z < 0`, no positivity
hypothesis is needed, unlike its `ℝ≥0` counterpart `NNReal.rpow_le_rpow_of_nonpos`; this is what
makes `ℝ≥0∞`-valued bounds on weakly singular integrands such as `|x - c| ^ (-1/2)` hold
everywhere, the pole included. In the same spirit, the inverse square root of a real `x` is at
most `‖x‖ₑ ^ (-1/2)`, with equality for `x > 0`. Two bounds on kernels `1 / √d` with `d` a
product of three linear factors follow: at infinity the kernel decays like `y ^ (-3/2)`, and near
three distinct poles the product of the factors `‖z - eᵢ‖ₑ ^ (-1/2)` is controlled by their sum,
since at most one of them can be large.

A real power `y ↦ y ^ d` on `ℝ≥0∞` is upper semicontinuous from the right uniformly on intervals:
for `ε ≠ 0`, every `y ∈ [x, z]` satisfies `y ^ d ≤ x ^ d + ε` once `z` is close enough to `x`.
For `d ≥ 0` this is monotonicity and continuity; for `d < 0` the power is antitone. Enlarging a
set slightly thus changes its `d`-dimensional diameter sum by little, as in Hausdorff measure
approximations by open covers.

For a base in `ℝ≥0` greater than one, power comparisons also express rational bounds and
closed intervals for a reciprocal radius parameter `α / r`.

## Main declarations

* `ENNReal.le_of_rpow_le_mul_rpow_sub_one`: `X ^ r ≤ C * X ^ (r - 1)` gives `X ≤ C` for a finite
  `X`.
* `ENNReal.rpow_mul_rpow_one_sub`: `x ^ p * x ^ (1 - p) = x` for `p ∈ [0, 1]`.
* `ENNReal.sq_rpow_one_half`: `(x ^ 2) ^ (1 / 2) = x`, with no hypothesis on `x`.
* `ENNReal.min_le_rpow_one_sub_mul_rpow`: `min x y ≤ x ^ (1 - p) * y ^ p` for `p ∈ [0, 1]`.
* `ENNReal.rpow_le_rpow_of_nonpos`: `x ≤ y` gives `y ^ z ≤ x ^ z` for `z ≤ 0`.
* `ENNReal.eventually_forall_mem_Icc_rpow_le_add`: `y ^ d ≤ x ^ d + ε` for `y ∈ [x, z]` and `z`
  near `x`.
* `ENNReal.ofReal_inv_sqrt_le_enorm_rpow`: `ofReal (√x)⁻¹ ≤ ‖x‖ₑ ^ (-2⁻¹)` for every real `x`.
* `ENNReal.ofReal_inv_sqrt_le_of_pow_three_le`: `y³ ≤ 2 |d|` gives `1 / √d ≤ √2 y^(-3/2)`.
* `ENNReal.exists_enorm_sub_rpow_neg_half_mul_le`: for three distinct points `eᵢ`, the product of
  the `‖z - eᵢ‖ₑ ^ (-1/2)` is at most a constant times their sum.
* `NNReal.rpow_neg_mem_Icc_iff`: an interval of negative powers is equivalent to an interval
  for the reciprocal parameter `α / r`.
-/

public section

open scoped ENNReal Topology

namespace ENNReal

/-- If `X ^ r ≤ C * X ^ (r - 1)` for a finite `X`, then `X ≤ C`. -/
theorem le_of_rpow_le_mul_rpow_sub_one {X C : ℝ≥0∞} {r : ℝ} (hX : X ≠ ∞)
    (h : X ^ r ≤ C * X ^ (r - 1)) : X ≤ C := by
  rcases eq_or_ne X 0 with hX0 | hX0
  · simp [hX0]
  have hXr : X ^ r = X ^ (r - 1) * X := by
    conv_lhs => rw [show r = (r - 1) + 1 by ring]
    rw [rpow_add _ _ hX0 hX, rpow_one]
  have hpow0 : X ^ (r - 1) ≠ 0 := by simp [rpow_eq_zero_iff, hX0, hX]
  rw [hXr, mul_comm C] at h
  exact (ENNReal.mul_le_mul_iff_right hpow0 (rpow_ne_top_of_ne_zero hX0 hX)).1 h

/-- For `p ∈ [0, 1]`, the powers `x ^ p` and `x ^ (1 - p)` multiply back to `x`. -/
theorem rpow_mul_rpow_one_sub (x : ℝ≥0∞) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    x ^ p * x ^ (1 - p) = x := by
  rw [← rpow_add_of_nonneg _ _ hp₀ (sub_nonneg.2 hp₁), add_sub_cancel, rpow_one]

/-- The square root of a square in `ℝ≥0∞`, written as a real power: `(x ^ 2) ^ (1 / 2) = x`. -/
theorem sq_rpow_one_half (x : ℝ≥0∞) : (x ^ 2) ^ (1 / 2 : ℝ) = x := by
  rw [← rpow_two, ← rpow_mul]
  norm_num

/-- For `p ∈ [0, 1]`, the weighted geometric mean `x ^ (1 - p) * y ^ p` dominates `min x y`. -/
theorem min_le_rpow_one_sub_mul_rpow (x y : ℝ≥0∞) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    min x y ≤ x ^ (1 - p) * y ^ p :=
  calc min x y = min x y ^ (1 - p) * min x y ^ p := by
        rw [mul_comm, rpow_mul_rpow_one_sub _ hp₀ hp₁]
    _ ≤ x ^ (1 - p) * y ^ p := mul_le_mul' (rpow_le_rpow (min_le_left _ _) (sub_nonneg.2 hp₁))
        (rpow_le_rpow (min_le_right _ _) hp₀)

/-- A nonpositive real power is antitone on `ℝ≥0∞`: `x ≤ y` gives `y ^ z ≤ x ^ z` for `z ≤ 0`. -/
theorem rpow_le_rpow_of_nonpos {x y : ℝ≥0∞} {z : ℝ} (hxy : x ≤ y) (hz : z ≤ 0) :
    y ^ z ≤ x ^ z := by
  obtain ⟨w, hw, rfl⟩ : ∃ w, 0 ≤ w ∧ z = -w := ⟨-z, neg_nonneg.mpr hz, (neg_neg z).symm⟩
  rw [rpow_neg, rpow_neg]
  exact ENNReal.inv_le_inv.mpr (rpow_le_rpow hxy hw)

/-- For `ε ≠ 0`, every `y ∈ [x, z]` satisfies `y ^ d ≤ x ^ d + ε` once `z` is close enough to
`x`. -/
theorem eventually_forall_mem_Icc_rpow_le_add (x : ℝ≥0∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) (d : ℝ) :
    ∀ᶠ z in 𝓝 x, ∀ y ∈ Set.Icc x z, y ^ d ≤ x ^ d + ε := by
  rcases le_or_gt 0 d with hd | hd
  · rcases eq_or_ne (x ^ d) ∞ with hx | hx
    · exact Filter.Eventually.of_forall fun _ _ _ ↦ by simp [hx]
    filter_upwards [(continuous_rpow_const.tendsto x).eventually_lt_const
      (ENNReal.lt_add_right hx hε)] with z hz y hy
    exact (rpow_le_rpow hy.2 hd).trans hz.le
  · exact Filter.Eventually.of_forall fun _ y hy ↦
      (rpow_le_rpow_of_nonpos hy.1 hd.le).trans le_self_add

/-- The inverse square root of a real `x` is at most `‖x‖ₑ ^ (-1/2)`, as a value in `ℝ≥0∞`. The two
agree for `x > 0`; for `x ≤ 0` the left side is `0`. -/
theorem ofReal_inv_sqrt_le_enorm_rpow (x : ℝ) : ENNReal.ofReal (√x)⁻¹ ≤ ‖x‖ₑ ^ (-2⁻¹ : ℝ) := by
  rcases le_or_gt x 0 with hx | hx
  · simp [Real.sqrt_eq_zero'.mpr hx]
  rw [Real.inv_sqrt_eq_rpow, ← ofReal_rpow_of_pos hx, Real.enorm_of_nonneg hx.le]

/-- If `y > 0` and `y³ ≤ 2 |d|`, then `1 / √d ≤ √2 y^(-3/2)`, as values in `ℝ≥0∞`. This is the
decay at infinity of a kernel `1 / √d(x)` for a cubic `d` with leading coefficient `4`, with
`y = 1 + |x|`. -/
theorem ofReal_inv_sqrt_le_of_pow_three_le {d y : ℝ} (hy : 0 < y) (h : y ^ 3 ≤ 2 * |d|) :
    ENNReal.ofReal (√d)⁻¹ ≤ ENNReal.ofReal √2 * ENNReal.ofReal (y ^ (-(3 / 2 : ℝ))) := by
  rcases le_or_gt d 0 with hd | hd
  · simp [Real.sqrt_eq_zero'.mpr hd]
  rw [abs_of_pos hd] at h
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hy3 : 0 < y ^ 3 / 2 := by positivity
  calc (√d)⁻¹ ≤ (√(y ^ 3 / 2))⁻¹ :=
        inv_anti₀ (Real.sqrt_pos.mpr hy3) (Real.sqrt_le_sqrt (by linarith))
    _ = √2 * (y ^ 3) ^ (-2⁻¹ : ℝ) := by
        rw [Real.sqrt_div' _ zero_le_two, inv_div, div_eq_mul_inv, Real.inv_sqrt_eq_rpow]
    _ = √2 * y ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast_mul hy.le]; norm_num

/-- For three distinct points `e₁, e₂, e₃` of a normed additive group, at most one of the factors
`‖z - eᵢ‖ₑ ^ (-1/2)` is large: the product of the three is at most a constant times their sum. -/
theorem exists_enorm_sub_rpow_neg_half_mul_le {E : Type*} [NormedAddGroup E] {e₁ e₂ e₃ : E}
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃) : ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ z : E,
      ‖z - e₁‖ₑ ^ (-2⁻¹ : ℝ) * ‖z - e₂‖ₑ ^ (-2⁻¹ : ℝ) * ‖z - e₃‖ₑ ^ (-2⁻¹ : ℝ) ≤
        K * (‖z - e₁‖ₑ ^ (-2⁻¹ : ℝ) + ‖z - e₂‖ₑ ^ (-2⁻¹ : ℝ) + ‖z - e₃‖ₑ ^ (-2⁻¹ : ℝ)) := by
  set δ := min (min ‖e₁ - e₂‖ ‖e₁ - e₃‖) ‖e₂ - e₃‖
  have hδ : 0 < δ := lt_min (lt_min (norm_sub_pos_iff.mpr h₁₂) (norm_sub_pos_iff.mpr h₁₃))
    (norm_sub_pos_iff.mpr h₂₃)
  set k := ENNReal.ofReal (δ / 2) ^ (-2⁻¹ : ℝ)
  have hk : k ≠ ∞ := by simp [k, ENNReal.rpow_eq_top_iff, hδ]
  -- a point at distance at least `δ / 2` contributes a factor at most `k`
  have far {z e : E} (h : δ / 2 ≤ ‖z - e‖) : ‖z - e‖ₑ ^ (-2⁻¹ : ℝ) ≤ k :=
    ENNReal.rpow_le_rpow_of_nonpos (by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal h)
      (by norm_num)
  -- no point is within `δ / 2` of two of the `eᵢ`
  have near {z a b : E} (hab : δ ≤ ‖a - b‖) : δ / 2 ≤ ‖z - a‖ ∨ δ / 2 ≤ ‖z - b‖ := by
    by_contra! h
    have := norm_sub_le_norm_sub_add_norm_sub a z b
    rw [norm_sub_rev a z] at this
    linarith
  refine ⟨k * k, ENNReal.mul_ne_top hk hk, fun z ↦ ?_⟩
  set h₁ := ‖z - e₁‖ₑ ^ (-2⁻¹ : ℝ)
  set h₂ := ‖z - e₂‖ₑ ^ (-2⁻¹ : ℝ)
  set h₃ := ‖z - e₃‖ₑ ^ (-2⁻¹ : ℝ)
  have hδ₁₂ : δ ≤ ‖e₁ - e₂‖ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ₁₃ : δ ≤ ‖e₁ - e₃‖ := (min_le_left _ _).trans (min_le_right _ _)
  have hδ₂₃ : δ ≤ ‖e₂ - e₃‖ := min_le_right _ _
  by_cases f₁ : δ / 2 ≤ ‖z - e₁‖
  · by_cases f₂ : δ / 2 ≤ ‖z - e₂‖
    · calc h₁ * h₂ * h₃ ≤ k * k * h₃ := by gcongr <;> exact far ‹_›
        _ ≤ k * k * (h₁ + h₂ + h₃) := by gcongr; exact le_add_self
    · have f₃ := (near hδ₂₃).resolve_left f₂
      calc h₁ * h₂ * h₃ ≤ k * h₂ * k := by gcongr <;> exact far ‹_›
        _ = k * k * h₂ := by ring
        _ ≤ k * k * (h₁ + h₂ + h₃) := by gcongr; exact le_add_self.trans le_self_add
  · have f₂ := (near hδ₁₂).resolve_left f₁
    have f₃ := (near hδ₁₃).resolve_left f₁
    calc h₁ * h₂ * h₃ ≤ h₁ * k * k := by gcongr <;> exact far ‹_›
      _ = k * k * h₁ := by ring
      _ ≤ k * k * (h₁ + h₂ + h₃) := by gcongr; exact le_self_add.trans le_self_add

end ENNReal

namespace NNReal

/-- For a base greater than one, real powers are ordered exactly by their exponents. -/
theorem rpow_le_rpow_iff_of_one_lt {b : ℝ≥0} (hb : 1 < b) {x y : ℝ} :
    b ^ x ≤ b ^ y ↔ x ≤ y := by
  constructor
  · contrapose!
    exact rpow_lt_rpow_of_exponent_lt hb
  · exact rpow_le_rpow_of_exponent_le hb.le

/-- **Reciprocal radius interval dictionary.** For a base `c > 1`, the interval
`c ^ (-α/a) ≤ c ^ (-r) ≤ c ^ (-α/b)` is equivalent to `a ≤ α / r ≤ b` when
`r`, `a`, and `b` are positive. -/
theorem rpow_neg_mem_Icc_iff {c : ℝ≥0} (hc : 1 < c) (α r a b : ℝ)
    (hr : 0 < r) (ha : 0 < a) (hb : 0 < b) :
    c ^ (-r) ∈ Set.Icc (c ^ (-α / a)) (c ^ (-α / b)) ↔
      α / r ∈ Set.Icc a b := by
  simp only [Set.mem_Icc]
  rw [rpow_le_rpow_iff_of_one_lt hc, rpow_le_rpow_iff_of_one_lt hc]
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · apply (le_div_iff₀ hr).2
      have := (div_le_iff₀ ha).1 h₁
      nlinarith
    · apply (div_le_iff₀ hr).2
      have := (le_div_iff₀ hb).1 h₂
      nlinarith
  · rintro ⟨h₁, h₂⟩
    constructor
    · have := (le_div_iff₀ hr).1 h₁
      exact (div_le_iff₀ ha).2 (by nlinarith)
    · have := (div_le_iff₀ hr).1 h₂
      exact (le_div_iff₀ hb).2 (by nlinarith)

/-- A rational lower bound on the ratio `α / r`, expressed as a comparison of powers.

For `r > 0`, the inequality `(b ^ (-α)) ^ q.den ≤ (b ^ (-r)) ^ q.num` is equivalent to
`q ≤ α / r`; the base is arbitrary above one. -/
theorem rpow_num_den_le_iff {b : ℝ≥0} (hb : 1 < b) (r : ℝ) (hr : 0 < r)
    (α : ℝ) (q : ℚ≥0) :
    (b ^ (-α)) ^ q.den ≤ (b ^ (-r)) ^ q.num ↔ (q : ℝ) ≤ α / r := by
  rw [← rpow_mul_natCast, ← rpow_mul_natCast, rpow_le_rpow_iff_of_one_lt hb,
    NNRat.cast_def, div_le_div_iff₀ (by exact_mod_cast q.den_pos) hr]
  constructor <;> intro h <;> nlinarith

/-- A rational upper bound on the ratio `α / r`, expressed as a comparison of powers.

For `r > 0`, the inequality `(b ^ (-r)) ^ q.num ≤ (b ^ (-α)) ^ q.den` is equivalent to
`α / r ≤ q`; the base is arbitrary above one. -/
theorem rpow_den_num_le_iff {b : ℝ≥0} (hb : 1 < b) (r : ℝ) (hr : 0 < r)
    (α : ℝ) (q : ℚ≥0) :
    (b ^ (-r)) ^ q.num ≤ (b ^ (-α)) ^ q.den ↔ α / r ≤ (q : ℝ) := by
  rw [← rpow_mul_natCast, ← rpow_mul_natCast, rpow_le_rpow_iff_of_one_lt hb,
    NNRat.cast_def, div_le_div_iff₀ hr (by exact_mod_cast q.den_pos)]
  constructor <;> intro h <;> nlinarith

end NNReal

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.PseudoUniformizer
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The logarithmic gauge of a multiplicative pseudo-uniformiser

Let `R` be a seminormed ring with a multiplicative pseudo-uniformiser `ϖ`. The *logarithmic
gauge* of `ϖ` is
`v_ϖ(x) = log ‖x‖ / log ‖ϖ‖ = Real.logb ‖ϖ‖ ‖x‖`,
with the value `⊤` when `‖x‖ = 0`. It takes values in `WithTop ℝ`, the value type of the real
additive valuations used for Newton polygons. Since `0 < ‖ϖ‖ < 1`, it reverses the order of the
norm, and it recovers the norm by `‖x‖ = ‖ϖ‖ ^ v_ϖ(x)`. In particular `v_ϖ(x) ≥ 0` describes the
closed unit ball and `v_ϖ(x) > 0` its open unit ball.

The norm is only submultiplicative, so the logarithmic gauge is *superadditive* on products,
`v_ϖ(x) + v_ϖ(y) ≤ v_ϖ(x * y)`. It satisfies `v_ϖ(1) = 0` and `v_ϖ(ϖ) = 1`, and the exact scaling
law of `ϖ` makes it additive along the powers of `ϖ`: `v_ϖ(ϖ ^ n * x) = n + v_ϖ(x)` for `n ∈ ℤ`.
For an ultrametric norm it satisfies `min (v_ϖ x) (v_ϖ y) ≤ v_ϖ (x + y)`. For a multiplicative
norm it is additive on all products, so for a multiplicative ultrametric norm it is an additive
valuation `PseudoUniformizer.addValuation`; for a merely submultiplicative norm it need not be.

On a normed field the logarithmic gauge is `-log ‖x‖ / log b` at the base `b = ‖ϖ‖⁻¹`, the
normalisation taking the value one at `ϖ`; on a non-archimedean normed field it is the real
additive valuation at that base. On `ℚ_[p]` with `‖ϖ‖ = p⁻¹` it is
Mathlib's `Padic.addValuation`, see `TauCeti.NumberTheory.Padics.LogGauge`.

## Main definitions

* `TauCeti.NormedRing.PseudoUniformizer.logGauge`: the logarithmic gauge `v_ϖ`.
* `TauCeti.NormedRing.PseudoUniformizer.addValuation`: for a multiplicative ultrametric norm,
  the logarithmic gauge as an additive valuation with values in `WithTop ℝ`.

## Main results

* `TauCeti.NormedRing.PseudoUniformizer.logGauge_eq_coe_iff`: norm recovery,
  `v_ϖ(x) = t ↔ ‖x‖ = ‖ϖ‖ ^ t`.
* `TauCeti.NormedRing.PseudoUniformizer.logGauge_le_logGauge_iff`: the gauge reverses the order
  of the norm.
* `TauCeti.NormedRing.PseudoUniformizer.le_logGauge_mul`: superadditivity on products.
* `TauCeti.NormedRing.PseudoUniformizer.logGauge_zpow_mul`: `v_ϖ(ϖ ^ n * x) = n + v_ϖ(x)`.
* `TauCeti.NormedRing.PseudoUniformizer.min_le_logGauge_add`: the ultrametric inequality.
* `TauCeti.NormedRing.PseudoUniformizer.logGauge_mul`: additivity for a multiplicative norm.

## References

* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
* J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Chapter II, §§3–4.
-/

public section

namespace TauCeti.NormedRing.PseudoUniformizer

variable {R : Type*} [SeminormedRing R] (ϖ : PseudoUniformizer R)

/-- The **logarithmic gauge** `v_ϖ(x) = log ‖x‖ / log ‖ϖ‖` of a multiplicative
pseudo-uniformiser `ϖ`, with the value `⊤` on elements of norm zero. -/
noncomputable def logGauge (x : R) : WithTop ℝ :=
  if ‖x‖ = 0 then ⊤ else (Real.logb ‖(ϖ.unit : R)‖ ‖x‖ : ℝ)

variable {ϖ} {x y : R}

/-- The logarithmic gauge is infinite exactly on the elements of norm zero. -/
@[simp]
theorem logGauge_eq_top_iff : ϖ.logGauge x = ⊤ ↔ ‖x‖ = 0 := by
  unfold logGauge
  split_ifs with h <;> simp [h]

/-- The logarithmic gauge of an element of norm zero is `⊤`. -/
theorem logGauge_of_norm_eq_zero (hx : ‖x‖ = 0) : ϖ.logGauge x = ⊤ :=
  logGauge_eq_top_iff.2 hx

/-- The logarithmic gauge of an element of nonzero norm is `Real.logb ‖ϖ‖ ‖x‖`. -/
theorem logGauge_of_norm_ne_zero (hx : ‖x‖ ≠ 0) :
    ϖ.logGauge x = (Real.logb ‖(ϖ.unit : R)‖ ‖x‖ : ℝ) := by
  simp [logGauge, hx]

/-- **Norm recovery**: the logarithmic gauge takes the finite value `t` exactly when
`‖x‖ = ‖ϖ‖ ^ t`. -/
theorem logGauge_eq_coe_iff {t : ℝ} : ϖ.logGauge x = t ↔ ‖x‖ = ‖(ϖ.unit : R)‖ ^ t := by
  by_cases hx : ‖x‖ = 0
  · simp [logGauge_of_norm_eq_zero hx, hx, (Real.rpow_pos_of_pos ϖ.norm_pos t).ne]
  · rw [logGauge_of_norm_ne_zero hx, WithTop.coe_inj,
      Real.logb_eq_iff_rpow_eq ϖ.norm_pos ϖ.norm_lt_one.ne ((norm_nonneg x).lt_of_ne' hx),
      eq_comm]

/-- An element of nonzero norm has norm `‖ϖ‖ ^ v_ϖ(x)`. -/
theorem norm_eq_rpow_logGauge (hx : ‖x‖ ≠ 0) :
    ‖x‖ = ‖(ϖ.unit : R)‖ ^ (ϖ.logGauge x).untop (logGauge_eq_top_iff.not.2 hx) :=
  logGauge_eq_coe_iff.1 (WithTop.coe_untop _ _).symm

/-- **The logarithmic gauge reverses the order of the norm.** -/
theorem logGauge_le_logGauge_iff : ϖ.logGauge x ≤ ϖ.logGauge y ↔ ‖y‖ ≤ ‖x‖ := by
  by_cases hx : ‖x‖ = 0
  · simp [logGauge_of_norm_eq_zero hx, hx, (norm_nonneg y).ge_iff_eq']
  by_cases hy : ‖y‖ = 0
  · simp [logGauge_of_norm_eq_zero hy, hy]
  rw [logGauge_of_norm_ne_zero hx, logGauge_of_norm_ne_zero hy, WithTop.coe_le_coe,
    Real.logb_le_logb_of_base_lt_one ϖ.norm_pos ϖ.norm_lt_one ((norm_nonneg x).lt_of_ne' hx)
      ((norm_nonneg y).lt_of_ne' hy)]

/-- The logarithmic gauge strictly reverses the order of the norm. -/
theorem logGauge_lt_logGauge_iff : ϖ.logGauge x < ϖ.logGauge y ↔ ‖y‖ < ‖x‖ := by
  rw [lt_iff_not_ge, logGauge_le_logGauge_iff, not_le]

/-- The logarithmic gauge is at least `t` exactly when `‖x‖ ≤ ‖ϖ‖ ^ t`. -/
theorem coe_le_logGauge_iff {t : ℝ} :
    (t : WithTop ℝ) ≤ ϖ.logGauge x ↔ ‖x‖ ≤ ‖(ϖ.unit : R)‖ ^ t := by
  by_cases hx : ‖x‖ = 0
  · simp [logGauge_of_norm_eq_zero hx, hx, (Real.rpow_pos_of_pos ϖ.norm_pos t).le]
  · rw [logGauge_of_norm_ne_zero hx, WithTop.coe_le_coe,
      Real.le_logb_iff_rpow_le_of_base_lt_one ϖ.norm_pos ϖ.norm_lt_one
        ((norm_nonneg x).lt_of_ne' hx)]

/-- The logarithmic gauge is at most `t` exactly when `‖ϖ‖ ^ t ≤ ‖x‖`. -/
theorem logGauge_le_coe_iff {t : ℝ} : ϖ.logGauge x ≤ t ↔ ‖(ϖ.unit : R)‖ ^ t ≤ ‖x‖ := by
  by_cases hx : ‖x‖ = 0
  · simp [logGauge_of_norm_eq_zero hx, hx, Real.rpow_pos_of_pos ϖ.norm_pos t]
  · rw [logGauge_of_norm_ne_zero hx, WithTop.coe_le_coe,
      Real.logb_le_iff_le_rpow_of_base_lt_one ϖ.norm_pos ϖ.norm_lt_one
        ((norm_nonneg x).lt_of_ne' hx)]

/-- The logarithmic gauge exceeds `t` exactly when `‖x‖ < ‖ϖ‖ ^ t`. -/
theorem coe_lt_logGauge_iff {t : ℝ} :
    (t : WithTop ℝ) < ϖ.logGauge x ↔ ‖x‖ < ‖(ϖ.unit : R)‖ ^ t := by
  rw [lt_iff_not_ge, logGauge_le_coe_iff, not_le]

/-- The logarithmic gauge is nonnegative exactly on the closed unit ball. -/
theorem logGauge_nonneg_iff : 0 ≤ ϖ.logGauge x ↔ ‖x‖ ≤ 1 := by
  simpa using coe_le_logGauge_iff (ϖ := ϖ) (x := x) (t := 0)

/-- The logarithmic gauge is positive exactly on the open unit ball. -/
theorem logGauge_pos_iff : 0 < ϖ.logGauge x ↔ ‖x‖ < 1 := by
  simpa using coe_lt_logGauge_iff (ϖ := ϖ) (x := x) (t := 0)

variable (ϖ)

/-- The logarithmic gauge of zero is `⊤`. -/
@[simp]
theorem logGauge_zero : ϖ.logGauge 0 = ⊤ :=
  logGauge_of_norm_eq_zero norm_zero

/-- The logarithmic gauge of one is zero, since `‖1‖ = 1`. -/
@[simp]
theorem logGauge_one : ϖ.logGauge 1 = 0 := by
  rw [← WithTop.coe_zero, logGauge_eq_coe_iff, Real.rpow_zero, ϖ.norm_one]

/-- The logarithmic gauge is invariant under negation. -/
@[simp]
theorem logGauge_neg (x : R) : ϖ.logGauge (-x) = ϖ.logGauge x := by
  unfold logGauge
  rw [norm_neg]

/-- The logarithmic gauge of `ϖ` is one. -/
@[simp]
theorem logGauge_unit : ϖ.logGauge (ϖ.unit : R) = 1 := by
  rw [← WithTop.coe_one, logGauge_eq_coe_iff, Real.rpow_one]

/-- **Superadditivity on products**: since the norm is submultiplicative,
`v_ϖ(x) + v_ϖ(y) ≤ v_ϖ(x * y)`. -/
theorem le_logGauge_mul (x y : R) :
    ϖ.logGauge x + ϖ.logGauge y ≤ ϖ.logGauge (x * y) := by
  by_cases hxy : ‖x * y‖ = 0
  · simp [logGauge_of_norm_eq_zero hxy]
  have hpos : 0 < ‖x‖ * ‖y‖ := ((norm_nonneg _).lt_of_ne' hxy).trans_le (norm_mul_le x y)
  have hx : ‖x‖ ≠ 0 := left_ne_zero_of_mul hpos.ne'
  have hy : ‖y‖ ≠ 0 := right_ne_zero_of_mul hpos.ne'
  rw [logGauge_of_norm_ne_zero hx, logGauge_of_norm_ne_zero hy, logGauge_of_norm_ne_zero hxy,
    ← WithTop.coe_add, WithTop.coe_le_coe, ← Real.logb_mul hx hy,
    Real.logb_le_logb_of_base_lt_one ϖ.norm_pos ϖ.norm_lt_one hpos
      ((norm_nonneg _).lt_of_ne' hxy)]
  exact norm_mul_le x y

/-- **Exact scaling**: multiplication by `ϖ ^ n` adds `n` to the logarithmic gauge. -/
@[simp]
theorem logGauge_zpow_mul (n : ℤ) (x : R) :
    ϖ.logGauge (((ϖ.unit ^ n : Rˣ) : R) * x) = ((n : ℝ) : WithTop ℝ) + ϖ.logGauge x := by
  have hnorm : ‖((ϖ.unit ^ n : Rˣ) : R) * x‖ = ‖(ϖ.unit : R)‖ ^ n * ‖x‖ := by
    simpa only [smul_eq_mul] using ϖ.norm_zpow_smul n x
  by_cases hx : ‖x‖ = 0
  · rw [logGauge_of_norm_eq_zero hx, WithTop.add_top, logGauge_eq_top_iff, hnorm, hx, mul_zero]
  rw [logGauge_of_norm_ne_zero hx, ← WithTop.coe_add,
    logGauge_eq_coe_iff, hnorm, Real.rpow_add ϖ.norm_pos, Real.rpow_intCast,
    Real.rpow_logb ϖ.norm_pos ϖ.norm_lt_one.ne ((norm_nonneg x).lt_of_ne' hx)]

/-- Multiplication by `ϖ` adds one to the logarithmic gauge. -/
@[simp]
theorem logGauge_unit_mul (x : R) : ϖ.logGauge ((ϖ.unit : R) * x) = 1 + ϖ.logGauge x := by
  simpa using ϖ.logGauge_zpow_mul 1 x

/-- The logarithmic gauge of `ϖ ^ n` is `n`, for `n ∈ ℤ`. -/
@[simp]
theorem logGauge_zpow (n : ℤ) : ϖ.logGauge ((ϖ.unit ^ n : Rˣ) : R) = ((n : ℝ) : WithTop ℝ) := by
  simpa using ϖ.logGauge_zpow_mul n 1

/-- The logarithmic gauge of `ϖ ^ n` is `n`, for `n ∈ ℕ`. -/
@[simp]
theorem logGauge_unit_pow (n : ℕ) : ϖ.logGauge ((ϖ.unit : R) ^ n) = ((n : ℝ) : WithTop ℝ) := by
  simpa using ϖ.logGauge_zpow n

/-- **The ultrametric inequality** for the logarithmic gauge. -/
theorem min_le_logGauge_add [IsUltrametricDist R] (x y : R) :
    min (ϖ.logGauge x) (ϖ.logGauge y) ≤ ϖ.logGauge (x + y) := by
  simp only [min_le_iff, logGauge_le_logGauge_iff]
  exact le_max_iff.1 (IsUltrametricDist.norm_add_le_max x y)

section NormMulClass

variable [NormMulClass R]

/-- For a multiplicative norm the logarithmic gauge is additive on products. -/
@[simp]
theorem logGauge_mul (x y : R) : ϖ.logGauge (x * y) = ϖ.logGauge x + ϖ.logGauge y := by
  by_cases hx : ‖x‖ = 0
  · rw [logGauge_of_norm_eq_zero hx, WithTop.top_add, logGauge_eq_top_iff, _root_.norm_mul, hx,
      zero_mul]
  by_cases hy : ‖y‖ = 0
  · rw [logGauge_of_norm_eq_zero hy, WithTop.add_top, logGauge_eq_top_iff, _root_.norm_mul, hy,
      mul_zero]
  rw [logGauge_of_norm_ne_zero hx, logGauge_of_norm_ne_zero hy,
    logGauge_of_norm_ne_zero (by rw [_root_.norm_mul]; exact mul_ne_zero hx hy), _root_.norm_mul,
    Real.logb_mul hx hy, WithTop.coe_add]

/-- For a multiplicative ultrametric norm, the logarithmic gauge of `ϖ` as an **additive
valuation** with values in `WithTop ℝ`, normalised by `v_ϖ(ϖ) = 1`. -/
noncomputable def addValuation [IsUltrametricDist R] : AddValuation R (WithTop ℝ) :=
  AddValuation.of ϖ.logGauge ϖ.logGauge_zero ϖ.logGauge_one ϖ.min_le_logGauge_add ϖ.logGauge_mul

/-- The additive valuation `ϖ.addValuation` is the logarithmic gauge. -/
@[simp]
theorem addValuation_apply [IsUltrametricDist R] (x : R) : ϖ.addValuation x = ϖ.logGauge x :=
  AddValuation.of_apply _

end NormMulClass

end TauCeti.NormedRing.PseudoUniformizer

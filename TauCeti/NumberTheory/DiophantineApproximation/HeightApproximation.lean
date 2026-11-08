/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.NumberTheory.DiophantineApproximation.Exponent
public import TauCeti.NumberTheory.Height.Rat

import TauCeti.Data.Int.MaxAbs

/-!
# Rational approximation measured by height

The denominator and the naive height of a rational approximant give the same irrationality
exponent. Near a fixed real number `ξ`, the numerator of `m / n` is bounded by a constant times
`n`, so replacing `n` by `max |m| n` changes the approximation bound by only a constant.

`TauCeti.liouvilleWith_iff_frequently_max` makes this comparison without requiring reduced
fractions. `LiouvilleWith.infinite_setOf_abs_sub_lt_mulHeight₁_rpow_neg` absorbs the constant by
slightly decreasing the exponent. `Real.le_irrationalityExponent_iff` characterizes a lower bound
on the irrationality exponent by infinitely many rational approximations measured using
`Height.mulHeight₁`. The strict decrease in the exponent is essential: a supremum need not be
attained, and a constant cannot in general be removed at the endpoint.

`TauCeti.mul_max_abs_rpow_le_norm_sub_of_lt` transfers a lower bound on `‖ξ - α‖` for rationals `ξ`
in terms of `Height.mulHeight₁` to a lower bound on the integer linear form `x - α y` when
`|x| < 2 (‖α‖ + 1) |y|`.

## References

* Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), Chapter 3.

The constant-absorption argument follows Mathlib's `LiouvilleWith.frequently_lt_rpow_neg`;
the passage from denominator bounds to height bounds uses
`LiouvilleWith.infinite_setOf_abs_sub_lt_rpow_neg` and the height comparison previously used in
`IsAlgebraic.not_liouvilleWith`.
-/

public section

open Filter Height
open scoped ENNReal Topology

namespace TauCeti

/-- In the Liouville condition, one may replace the denominator by `max |m| n`, even for
fractions that are not reduced. -/
theorem liouvilleWith_iff_frequently_max {p ξ : ℝ} :
    LiouvilleWith p ξ ↔ ∃ C > 0, ∃ᶠ n : ℕ in atTop, 0 < n ∧
      ∃ m : ℤ, ξ ≠ m / n ∧ |ξ - m / n| < C / (max |(m : ℝ)| (n : ℝ)) ^ p := by
  wlog hp : 0 ≤ p generalizing p
  · refine iff_of_true ((liouvilleWith_one ξ).mono (by linarith)) ?_
    obtain ⟨C, hC, hf⟩ := (this (p := 0) le_rfl).mp
      ((liouvilleWith_one ξ).mono zero_le_one)
    refine ⟨C, hC, hf.mono ?_⟩
    rintro n ⟨hn, m, hne, hlt⟩
    refine ⟨hn, m, hne, hlt.trans_le ?_⟩
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_le_div_of_nonneg_left hC.le (by positivity)
      (Real.rpow_le_rpow_of_exponent_le (hn'.trans (le_max_right _ _)) (by linarith))
  constructor
  · intro h
    obtain ⟨C, hC, hf⟩ := h.exists_pos
    let A := |ξ| + C + 1
    have hA : 0 < A := by dsimp [A]; positivity
    refine ⟨C * A ^ p, by positivity, hf.mono ?_⟩
    rintro n ⟨hn, m, hne, hlt⟩
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by positivity
    have hsmall : |ξ - m / n| < C :=
      hlt.trans_le (div_le_self hC.le (Real.one_le_rpow hn' hp))
    have hm : |(m : ℝ)| ≤ (|ξ| + C) * n := by
      have habs : |(m : ℝ) / n| ≤ |ξ| + |ξ - m / n| := by
        simpa [abs_sub_comm, add_comm] using abs_sub_le ((m : ℝ) / n) ξ 0
      rw [abs_div, abs_of_pos hn0] at habs
      have := (div_le_iff₀ hn0).mp habs
      nlinarith
    have hmax : max |(m : ℝ)| (n : ℝ) ≤ A * n := by
      refine max_le (hm.trans ?_) ?_ <;> dsimp [A] <;> nlinarith [abs_nonneg ξ]
    refine ⟨hn, m, hne, hlt.trans_le ?_⟩
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc C * (max |(m : ℝ)| (n : ℝ)) ^ p ≤ C * (A * n) ^ p := by gcongr
      _ = C * A ^ p * (n : ℝ) ^ p := by rw [Real.mul_rpow hA.le hn0.le]; ring
  · rintro ⟨C, hC, hf⟩
    refine ⟨C, hf.mono ?_⟩
    rintro n ⟨hn, m, hne, hlt⟩
    refine ⟨m, hne, hlt.trans_le ?_⟩
    exact div_le_div_of_nonneg_left hC.le (by positivity)
      (Real.rpow_le_rpow (by positivity) (le_max_right _ _) hp)

open Real in
/-- The case `|x| < 2 (‖α‖ + 1) |y|` of the linear-form bound: if every rational `ξ ≠ α`
satisfies the rational approximation bound `c₀ H(ξ) ^ (-κ) ≤ ‖ξ - α‖`, then at integers `x`, `y`
with `|x| < 2 (‖α‖ + 1) |y|`, `x ≠ α y`, the linear form satisfies
`‖x - α y‖ ≥ c₀ / (2 (‖α‖ + 1)) max(|x|, |y|) ^ (1 - κ)`. -/
theorem mul_max_abs_rpow_le_norm_sub_of_lt {α : ℂ} {κ c₀ : ℝ} (hκ : 0 ≤ κ) (hc₀ : 0 ≤ c₀)
    (h : ∀ ξ : ℚ, (ξ : ℂ) ≠ α → c₀ * mulHeight₁ ξ ^ (-κ) ≤ ‖(ξ : ℂ) - α‖) {x y : ℤ}
    (hxy : (x : ℂ) - α * y ≠ 0)
    (hsmall : |(x : ℝ)| < 2 * (‖α‖ + 1) * |(y : ℝ)|) :
    c₀ / (2 * (‖α‖ + 1)) * max |(x : ℝ)| |(y : ℝ)| ^ (1 - κ) ≤ ‖(x : ℂ) - α * y‖ := by
  set A := ‖α‖ + 1
  have hA : 1 ≤ A := by linarith [norm_nonneg α]
  set M := max |(x : ℝ)| |(y : ℝ)|
  have hM₀ : 0 < M := by
    have : 1 ≤ M := Int.one_le_max_abs_cast (R := ℝ) <| by
      by_contra! h0
      exact hxy (by simp [h0.1, h0.2])
    linarith
  have hy : y ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, abs_zero, mul_zero] at hsmall
    linarith [abs_nonneg (x : ℝ)]
  have hMy : M ≤ 2 * A * |(y : ℝ)| := max_le hsmall.le (by nlinarith [abs_nonneg (y : ℝ)])
  set ξ : ℚ := (x : ℚ) / y
  have hξ : (ξ : ℂ) = x / y := by simp [ξ]
  have hsub : (x : ℂ) - α * y = y * ((ξ : ℂ) - α) := by
    rw [hξ]
    have hyR : (y : ℂ) ≠ 0 := Int.cast_ne_zero.2 hy
    field_simp
  have hξα : (ξ : ℂ) ≠ α := fun h ↦ hxy (by rw [hsub, h, sub_self, mul_zero])
  have hH : mulHeight₁ ξ ≤ M := Rat.mulHeight₁_intCast_div_le x hy
  have hHκ : M ^ (-κ) ≤ mulHeight₁ ξ ^ (-κ) :=
    rpow_le_rpow_of_nonpos (mulHeight₁_pos ξ) hH (by linarith)
  have hMκ : M ^ (1 - κ) = M * M ^ (-κ) := by
    rw [sub_eq_add_neg, rpow_add hM₀, rpow_one]
  rw [hsub, norm_mul, Complex.norm_intCast, hMκ]
  calc c₀ / (2 * A) * (M * M ^ (-κ))
      ≤ c₀ / (2 * A) * (2 * A * |(y : ℝ)| * M ^ (-κ)) := by gcongr
    _ = |(y : ℝ)| * (c₀ * M ^ (-κ)) := by field_simp
    _ ≤ |(y : ℝ)| * ‖(ξ : ℂ) - α‖ := by
        gcongr
        exact (mul_le_mul_of_nonneg_left hHκ hc₀).trans (h ξ hξα)

end TauCeti

namespace LiouvilleWith

/-- A Liouville number with exponent `p` has infinitely many rational approximations measured
by their multiplicative height, for every exponent strictly smaller than `p`. -/
theorem infinite_setOf_abs_sub_lt_mulHeight₁_rpow_neg {p q ξ : ℝ} (h : LiouvilleWith p ξ)
    (hqp : q < p) :
    {r : ℚ | |ξ - r| < mulHeight₁ r ^ (-q)}.Infinite := by
  wlog hp : 0 < p generalizing p
  · exact this (liouvilleWith_one ξ) (hqp.trans_le (by linarith)) zero_lt_one
  wlog hq : 0 < q generalizing q
  · refine (this (max_lt hqp (half_lt_self hp))
      (lt_max_of_lt_right (half_pos hp))).mono fun r hr ↦ ?_
    exact hr.trans_le (Real.rpow_le_rpow_of_exponent_le (one_le_mulHeight₁ r)
      (neg_le_neg (le_max_left q (p / 2))))
  -- Near `ξ`, height is at most a fixed multiple of the denominator. Absorb this
  -- multiple by choosing an intermediate exponent and discarding bounded heights.
  obtain ⟨q', hqq', hq'p⟩ := exists_between hqp
  set A := |ξ| + 1
  have hA : 1 ≤ A := by linarith [abs_nonneg ξ]
  obtain ⟨N, hN⟩ := exists_nat_ge (A ^ (q / (q' - q)))
  refine ((h.infinite_setOf_abs_sub_lt_rpow_neg hq'p).sdiff
    (Northcott.finite_le (h := mulHeight₁ (K := ℚ)) (A * N))).mono ?_
  rintro r ⟨hr, hrN⟩
  have hr : |ξ - r| < (r.den : ℝ) ^ (-q') := hr
  have hd : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
  have hr1 : |ξ - r| < 1 := hr.trans_le
    (Real.rpow_le_one_of_one_le_of_nonpos hd (by linarith))
  have hrA : |(r : ℝ)| ≤ A := by
    have := abs_sub_abs_le_abs_sub (r : ℝ) ξ
    rw [abs_sub_comm] at this
    linarith
  have hH : mulHeight₁ r ≤ A * r.den := (Rat.mulHeight₁_le_max_one_abs_mul_den r).trans
    (mul_le_mul_of_nonneg_right (max_le hA hrA) (by positivity))
  have hdN : (N : ℝ) ≤ r.den := by
    by_contra! hlt
    exact hrN (hH.trans (mul_le_mul_of_nonneg_left hlt.le (by positivity)))
  have hAd : A ^ q ≤ (r.den : ℝ) ^ (q' - q) :=
    calc A ^ q = (A ^ (q / (q' - q))) ^ (q' - q) := by
          rw [← Real.rpow_mul (by linarith), div_mul_cancel₀ _ (by linarith)]
      _ ≤ (N : ℝ) ^ (q' - q) := Real.rpow_le_rpow (by positivity) hN (by linarith)
      _ ≤ (r.den : ℝ) ^ (q' - q) := Real.rpow_le_rpow (by positivity) hdN (by linarith)
  refine hr.trans_le ?_
  calc (r.den : ℝ) ^ (-q') = (r.den : ℝ) ^ (-q) / (r.den : ℝ) ^ (q' - q) := by
        rw [← Real.rpow_sub (by positivity)]
        ring_nf
    _ ≤ (r.den : ℝ) ^ (-q) / A ^ q :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hAd
    _ = (A * r.den) ^ (-q) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.rpow_neg (by positivity : (0 : ℝ) ≤ A) q]
        ring
    _ ≤ mulHeight₁ r ^ (-q) :=
        Real.rpow_le_rpow_of_nonpos (mulHeight₁_pos r) hH (by linarith)

end LiouvilleWith

namespace Real

/-- An extended nonnegative real `μ` is at most the irrationality exponent of `ξ` exactly when,
for every real `ν` with `ENNReal.ofReal ν < μ`, infinitely many rational numbers approximate
`ξ` within `H(r) ^ (-ν)`. Here `H` is the rational height `max |num r| (den r)`; the case
`μ = ⊤` characterizes Liouville numbers. -/
theorem le_irrationalityExponent_iff (ξ : ℝ) {μ : ℝ≥0∞} :
    μ ≤ TauCeti.irrationalityExponent ξ ↔
      ∀ ν : ℝ, ENNReal.ofReal ν < μ →
        {r : ℚ | |ξ - r| < mulHeight₁ r ^ (-ν)}.Infinite := by
  constructor
  · intro h ν hνμ
    obtain ⟨p, _, hνp, hpμ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hνμ
    exact LiouvilleWith.infinite_setOf_abs_sub_lt_mulHeight₁_rpow_neg
      (TauCeti.liouvilleWith_of_lt_irrationalityExponent (hpμ.trans_le h))
      (ENNReal.ofReal_lt_ofReal_iff'.mp hνp).1
  · intro h
    refine le_of_forall_lt fun c hc ↦ ?_
    obtain ⟨ν, hν, hcν, hνμ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hc
    have hden : {r : ℚ | |ξ - r| < (r.den : ℝ) ^ (-ν)}.Infinite := by
      refine (h ν hνμ).mono ?_
      intro r hr
      exact hr.trans_le (Real.rpow_le_rpow_of_nonpos (by exact_mod_cast r.pos)
        (Rat.den_le_mulHeight₁ r) (neg_nonpos.mpr hν))
    exact hcν.trans_le (TauCeti.le_irrationalityExponent_of_liouvilleWith
      hden.liouvilleWith_of_abs_sub_lt_rpow_neg)

end Real

/-! ### Boundary checks -/

/-- Rational numbers still have infinitely many height approximations below exponent one. -/
example (ξ : ℚ) {ν : ℝ} (hν1 : ν < 1) :
    {r : ℚ | |(ξ : ℝ) - r| < mulHeight₁ r ^ (-ν)}.Infinite := by
  exact ((Real.le_irrationalityExponent_iff ξ (μ := 1)).mp
    (by simp [TauCeti.irrationalityExponent_ratCast])) ν
      (by simpa using (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr hν1)

/-- Dirichlet's lower bound is unchanged when approximation is measured by height. -/
example {ξ : ℝ} (hξ : Irrational ξ) {ν : ℝ} (hν2 : ν < 2) :
    {r : ℚ | |ξ - r| < mulHeight₁ r ^ (-ν)}.Infinite := by
  exact ((Real.le_irrationalityExponent_iff ξ (μ := 2)).mp
    ((TauCeti.two_le_irrationalityExponent_iff ξ).mpr hξ)) ν
      (by simpa using (ENNReal.ofReal_lt_ofReal_iff zero_lt_two).mpr hν2)

/-- For an unreduced fraction the maximum is only an upper bound on its rational height. -/
example : mulHeight₁ ((2 : ℚ) / 2) < max |(2 : ℝ)| (2 : ℝ) := by
  norm_num

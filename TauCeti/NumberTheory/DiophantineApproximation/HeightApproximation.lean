/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Exponent
public import TauCeti.NumberTheory.Height.Rat

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

## References

* Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), Chapter 3.

The constant-absorption argument follows Mathlib's `LiouvilleWith.frequently_lt_rpow_neg`;
the passage to infinitely many reduced fractions follows
`LiouvilleWith.infinite_setOf_abs_sub_lt_rpow_neg`.
-/

public section

open Filter Height
open scoped Topology

namespace TauCeti

/-- In the Liouville condition with nonnegative exponent, one may replace the denominator by
`max |m| n`, even for fractions that are not reduced. -/
theorem liouvilleWith_iff_frequently_max {p ξ : ℝ} (hp : 0 ≤ p) :
    LiouvilleWith p ξ ↔ ∃ C > 0, ∃ᶠ n : ℕ in atTop, 0 < n ∧
      ∃ m : ℤ, ξ ≠ m / n ∧ |ξ - m / n| < C / (max |(m : ℝ)| (n : ℝ)) ^ p := by
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

end TauCeti

namespace LiouvilleWith

/-- After strictly decreasing a positive exponent, the Liouville condition holds with constant
one and the maximum of numerator and denominator in place of the denominator. -/
theorem frequently_lt_max_rpow_neg {p q ξ : ℝ} (h : LiouvilleWith p ξ)
    (hq : 0 < q) (hqp : q < p) :
    ∃ᶠ n : ℕ in atTop, 0 < n ∧ ∃ m : ℤ, ξ ≠ m / n ∧
      |ξ - m / n| < (max |(m : ℝ)| (n : ℝ)) ^ (-q) := by
  obtain ⟨C, hC, hf⟩ := (TauCeti.liouvilleWith_iff_frequently_max (hq.trans hqp).le).mp h
  have hlarge : ∀ᶠ n : ℕ in atTop, C < (n : ℝ) ^ (p - q) :=
    ((tendsto_rpow_atTop (sub_pos.mpr hqp)).comp
      tendsto_natCast_atTop_atTop).eventually_gt_atTop C
  refine (hlarge.and_frequently hf).mono ?_
  rintro n ⟨hnC, hn, m, hne, hlt⟩
  have hn0 : (0 : ℝ) < n := by positivity
  have hmax : 0 < max |(m : ℝ)| (n : ℝ) := hn0.trans_le (le_max_right _ _)
  refine ⟨hn, m, hne, hlt.trans ?_⟩
  rw [div_lt_iff₀ (by positivity), ← Real.rpow_add hmax, neg_add_eq_sub]
  exact hnC.trans_le (Real.rpow_le_rpow hn0.le (le_max_right _ _) (sub_pos.mpr hqp).le)

/-- A Liouville number with exponent `p` has infinitely many rational approximations measured
by their multiplicative height, for every positive exponent strictly smaller than `p`. -/
theorem infinite_setOf_abs_sub_lt_mulHeight₁_rpow_neg {p q ξ : ℝ} (h : LiouvilleWith p ξ)
    (hq : 0 < q) (hqp : q < p) :
    {r : ℚ | |ξ - r| < mulHeight₁ r ^ (-q)}.Infinite := by
  intro hfin
  -- A finite set of approximants distinct from `ξ` has a positive separation from it.
  obtain ⟨M, hM⟩ := (hfin.image fun r : ℚ ↦ |ξ - r|⁻¹).bddAbove
  have hsmall : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-q) < (max M 1)⁻¹ :=
    ((tendsto_rpow_neg_atTop hq).comp tendsto_natCast_atTop_atTop).eventually
      (gt_mem_nhds (by positivity))
  obtain ⟨n, hnM, hn, m, hne, hlt⟩ :=
    (hsmall.and_frequently (h.frequently_lt_max_rpow_neg hq hqp)).exists
  let r : ℚ := (m : ℚ) / n
  have hr : (r : ℝ) = m / n := by simp [r]
  have hn0 : (0 : ℝ) < n := by positivity
  have hheight : mulHeight₁ r ≤ max |(m : ℝ)| (n : ℝ) := by
    simpa [r] using Rat.mulHeight₁_intCast_div_le m (y := (n : ℤ)) (by omega)
  have hmem : r ∈ {r : ℚ | |ξ - r| < mulHeight₁ r ^ (-q)} := by
    refine (hr ▸ hlt).trans_le ?_
    exact Real.rpow_le_rpow_of_nonpos (mulHeight₁_pos _) hheight (neg_nonpos.mpr hq.le)
  have hpos : 0 < |ξ - r| := abs_pos.mpr (sub_ne_zero.mpr (hr ▸ hne))
  have hsep : (max M 1)⁻¹ ≤ |ξ - r| := by
    rw [inv_le_comm₀ (by positivity) hpos]
    exact (hM ⟨r, hmem, rfl⟩).trans (le_max_left _ _)
  have hlt' : |ξ - r| < (n : ℝ) ^ (-q) := by
    refine (hr ▸ hlt).trans_le ?_
    exact Real.rpow_le_rpow_of_nonpos hn0 (le_max_right _ _) (neg_nonpos.mpr hq.le)
  exact (hsep.trans_lt (hlt'.trans hnM)).false

end LiouvilleWith

namespace Real

/-- A positive real number `μ` is at most the irrationality exponent of `ξ` exactly when, for
every positive `ν < μ`, infinitely many rational numbers approximate `ξ` within `H(r) ^ (-ν)`.
Here `H` is the rational height `max |num r| (den r)`. -/
theorem le_irrationalityExponent_iff (ξ : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    ENNReal.ofReal μ ≤ TauCeti.irrationalityExponent ξ ↔
      ∀ ν : ℝ, 0 < ν → ν < μ →
        {r : ℚ | |ξ - r| < mulHeight₁ r ^ (-ν)}.Infinite := by
  constructor
  · intro h ν hν hνμ
    obtain ⟨p, hνp, hpμ⟩ := exists_between hνμ
    have hp : ENNReal.ofReal p < TauCeti.irrationalityExponent ξ :=
      (ENNReal.ofReal_lt_ofReal_iff hμ).mpr hpμ |>.trans_le h
    exact LiouvilleWith.infinite_setOf_abs_sub_lt_mulHeight₁_rpow_neg
      (TauCeti.liouvilleWith_of_lt_irrationalityExponent hp) hν hνp
  · intro h
    refine le_of_forall_lt fun c hc ↦ ?_
    have hcμ : c.toReal < μ := (ENNReal.lt_ofReal_iff_toReal_lt hc.ne_top).mp hc
    obtain ⟨ν, hcν, hνμ⟩ := exists_between hcμ
    have hν : 0 < ν := ENNReal.toReal_nonneg.trans_lt hcν
    have hden : {r : ℚ | |ξ - r| < (r.den : ℝ) ^ (-ν)}.Infinite := by
      refine (h ν hν hνμ).mono ?_
      intro r hr
      simp only [Set.mem_ofPred_eq] at hr ⊢
      refine hr.trans_le ?_
      have hheight : (r.den : ℝ) ≤ mulHeight₁ r := by
        rw [Rat.mulHeight₁_eq_max]
        exact_mod_cast le_max_right r.num.natAbs r.den
      exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast r.pos) hheight
        (neg_nonpos.mpr hν.le)
    exact ((ENNReal.lt_ofReal_iff_toReal_lt hc.ne_top).mpr hcν).trans_le
      (TauCeti.le_irrationalityExponent_of_liouvilleWith
        hden.liouvilleWith_of_abs_sub_lt_rpow_neg)

end Real

/-! ### Boundary checks -/

/-- Rational numbers still have infinitely many height approximations below exponent one. -/
example (ξ : ℚ) {ν : ℝ} (hν : 0 < ν) (hν1 : ν < 1) :
    {r : ℚ | |(ξ : ℝ) - r| < mulHeight₁ r ^ (-ν)}.Infinite := by
  exact ((Real.le_irrationalityExponent_iff ξ zero_lt_one).mp
    (by simp [TauCeti.irrationalityExponent_ratCast])) ν hν hν1

/-- Dirichlet's lower bound is unchanged when approximation is measured by height. -/
example {ξ : ℝ} (hξ : Irrational ξ) {ν : ℝ} (hν : 0 < ν) (hν2 : ν < 2) :
    {r : ℚ | |ξ - r| < mulHeight₁ r ^ (-ν)}.Infinite := by
  exact ((Real.le_irrationalityExponent_iff ξ zero_lt_two).mp
    (by simpa using (TauCeti.two_le_irrationalityExponent_iff ξ).mpr hξ)) ν hν hν2

/-- For an unreduced fraction the maximum is only an upper bound on its rational height. -/
example : mulHeight₁ ((2 : ℚ) / 2) < max |(2 : ℝ)| (2 : ℝ) := by
  norm_num

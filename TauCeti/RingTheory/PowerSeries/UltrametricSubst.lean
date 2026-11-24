/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.Valued.NormedValued
import TauCeti.RingTheory.PowerSeries.Substitution
import TauCeti.RingTheory.PowerSeries.Trunc
import TauCeti.RingTheory.Valuation.Polynomial

/-!
# Evaluating a formal inverse in an ultrametric field

Let `f` and `g` be power series over an ultrametric normed field `K` with `f.subst g = X`, so that
`f` is a left inverse of `g` under formal composition. If their coefficients satisfy
`‖cₙ‖ R ^ (n - 1) ≤ 1` for every `n`, then at every `x` with `‖x‖ < R` at which the two series
converge, `f (g x) = x`.

The proof compares truncations. Below both truncation degrees, the composite of the truncation of
`f` with the truncation of `g` agrees with `X` (`PowerSeries.coeff_trunc_comp_trunc`). With
`A = ‖x‖` and `S = ‖x‖ / R < 1`, the coefficient bounds give every term of the composite at `x`
the weighted bound `‖c x ^ k‖ S ≤ A S ^ k` (`Valuation.map_coeff_comp_mul_pow_le`), so the
difference from `x` is at most `A S ^ (M - 1)` below degree `M`. Letting the truncation degrees
tend to infinity gives the identity. The argument adapts the proof of
`TauCeti.log_exp_of_mem_maximalIdeal_pow` (`TauCeti.NumberTheory.LocalField.ExpLog`), with norms in
place of the valuation of the valuative relation.

The coefficients of the exponential series and of the logarithm series satisfy the bound for the
radius `p ^ (-1 / (p - 1))` in every normed field over `ℚ_[p]`, by Legendre's formula, so this
proves that the `p`-adic exponential and logarithm are mutually inverse on the disc of that radius.

## Main results

* `PowerSeries.eq_of_hasSum_of_subst_eq_X`: if `f.subst g = X` and the coefficients of `f` and
  `g` satisfy `‖cₙ‖ R ^ (n - 1) ≤ 1`, then `f (g x) = x` for `‖x‖ < R`.
-/

public section

open Filter Topology NNReal

namespace PowerSeries

variable {K : Type*} [NormedField K]

/-- The coefficient bound `‖c‖ R ^ (n - 1) ≤ 1` is the weighted bound
`‖c‖ A ^ n S ≤ A S ^ n` with `S = A / R`. -/
private theorem nnNorm_mul_pow_mul_div_le {c : K} {n : ℕ} {R A : ℝ≥0} (hR : 0 < R)
    (hc0 : n = 0 → c = 0) (hc : ‖c‖ * (R : ℝ) ^ (n - 1) ≤ 1) :
    ‖c‖₊ * A ^ n * (A / R) ≤ A * (A / R) ^ n := by
  rcases n with _ | m
  · simp [hc0 rfl]
  have hc' : ‖c‖₊ * R ^ m ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    simpa using hc
  calc ‖c‖₊ * A ^ (m + 1) * (A / R) = (‖c‖₊ * R ^ m) * (A * (A / R) ^ (m + 1)) := by
        rw [div_pow]
        field_simp
        ring
    _ ≤ A * (A / R) ^ (m + 1) := mul_le_of_le_one_left zero_le hc'

/-- **The truncation estimate.** If `f.subst g = X`, the coefficients of `f` and `g` satisfy
`‖cₙ‖ R ^ (n - 1) ≤ 1` and `‖x‖ ≤ R`, then with `S = ‖x‖ / R`, the composite of the truncations of
`f` below degree `M` and of `g` below degree `N` takes a value at `x` within
`‖x‖ S ^ (min M N - 1)` of `x`. -/
private theorem nnNorm_eval_trunc_eval_trunc_sub_mul_le [IsUltrametricDist K] {f g : K⟦X⟧}
    (hf0 : coeff 0 f = 0) (hg0 : constantCoeff g = 0) (hfg : f.subst g = X) {R : ℝ≥0}
    (hR : 0 < R) (hf : ∀ n, ‖coeff n f‖ * (R : ℝ) ^ (n - 1) ≤ 1)
    (hg : ∀ n, ‖coeff n g‖ * (R : ℝ) ^ (n - 1) ≤ 1) {x : K} (hx : ‖x‖₊ ≤ R) (M N : ℕ) :
    ‖(trunc M f).eval ((trunc N g).eval x) - x‖₊ * (‖x‖₊ / R) ≤
      ‖x‖₊ * (‖x‖₊ / R) ^ min M N := by
  have hg0' : coeff 0 g = 0 := by simpa using hg0
  set A : ℝ≥0 := ‖x‖₊
  set S : ℝ≥0 := A / R
  rcases eq_or_ne A 0 with hA | hA
  · simp [S, hA]
  have hS0 : 0 < S := div_pos (pos_of_ne_zero hA) hR
  -- The truncations of `f` and of `g`, and `X`, have weight one at `x`.
  have hF (n : ℕ) : NormedField.valuation ((trunc M f).coeff n) * A ^ n * S ≤ A * S ^ n := by
    rw [coeff_trunc]
    split_ifs
    · exact nnNorm_mul_pow_mul_div_le hR (fun h ↦ h ▸ hf0) (hf n)
    · simp
  have hQ (k : ℕ) : NormedField.valuation ((trunc N g).coeff k * x ^ k) * S ≤ A * S ^ k := by
    rw [map_mul, map_pow, NormedField.valuation_apply x, coeff_trunc]
    split_ifs
    · exact nnNorm_mul_pow_mul_div_le hR (fun h ↦ h ▸ hg0') (hg k)
    · simp
  have hX (k : ℕ) :
      NormedField.valuation ((Polynomial.X : Polynomial K).coeff k * x ^ k) * S ≤ A * S ^ k := by
    rw [Polynomial.coeff_X]
    split_ifs with h
    · subst h
      simp [A]
    · simp
  -- `F ∘ Q - X` has weight one and vanishes below degree `min M N`.
  have hG : ((trunc M f).comp (trunc N g) - Polynomial.X).eval x =
      (trunc M f).eval ((trunc N g).eval x) - x := by
    simp [Polynomial.eval_comp]
  rw [← hG, ← NormedField.valuation_apply]
  refine Valuation.map_eval_mul_le ((div_le_one hR).mpr hx) (fun k hk ↦ ?_) (fun k ↦ ?_)
  · rw [Polynomial.coeff_sub, coeff_trunc_comp_trunc f hg0 (lt_min_iff.mp hk).1
      (lt_min_iff.mp hk).2, hfg, Polynomial.coeff_X, coeff_X]
    grind
  · have hcomp := Valuation.map_coeff_comp_mul_pow_le hF hQ k
    have hXk := hX k
    rw [Polynomial.coeff_sub, sub_mul]
    rw [← le_div_iff₀ hS0] at hcomp hXk ⊢
    exact Valuation.map_sub_le _ hcomp hXk

/-- **A formal left inverse is a left inverse on a disc.** Let `f` and `g` be power series over an
ultrametric normed field with `f.subst g = X`, whose coefficients satisfy `‖cₙ‖ R ^ (n - 1) ≤ 1`.
If `‖x‖ < R`, the series of `g` at `x` sums to `y` and the series of `f` at `y` sums to `z`,
then `z = x`. -/
theorem eq_of_hasSum_of_subst_eq_X [IsUltrametricDist K] {f g : K⟦X⟧} (hg0 : constantCoeff g = 0)
    (hfg : f.subst g = X) {R : ℝ} (hf : ∀ n, ‖coeff n f‖ * R ^ (n - 1) ≤ 1)
    (hg : ∀ n, ‖coeff n g‖ * R ^ (n - 1) ≤ 1) {x y z : K} (hx : ‖x‖ < R)
    (hy : HasSum (fun n ↦ coeff n g * x ^ n) y) (hz : HasSum (fun n ↦ coeff n f * y ^ n) z) :
    z = x := by
  -- The constant coefficient of `f` is that of `f.subst g = X`.
  have hf0 : coeff 0 f = 0 := by
    have h := coeff_trunc_comp_trunc f hg0 (M := 1) (N := 1) (k := 0) one_pos one_pos
    simpa [hfg, trunc_one] using h
  rcases eq_or_ne x 0 with rfl | hx0
  · -- At `x = 0` every term of both series vanishes.
    have hy0 : y = 0 := hy.unique (by
      convert hasSum_zero with n
      rcases n with _ | n <;> simp [hg0])
    subst hy0
    exact hz.unique (by
      convert hasSum_zero with n
      rcases n with _ | n <;> simp [hf0])
  have hR : 0 < R := (norm_nonneg x).trans_lt hx
  set R' : ℝ≥0 := ⟨R, hR.le⟩
  set A : ℝ≥0 := ‖x‖₊
  set S : ℝ≥0 := A / R'
  have hR' : 0 < R' := hR
  have hS0 : 0 < S := div_pos (nnNorm_pos.mpr hx0) hR'
  have hS1 : S < 1 := (div_lt_one hR').mpr hx
  have hkey := nnNorm_eval_trunc_eval_trunc_sub_mul_le hf0 hg0 hfg hR' hf hg hx.le
  -- Let the truncation degree of `g` tend to infinity.
  have hQlim : Tendsto (fun N ↦ (trunc N g).eval x) atTop (𝓝 y) :=
    hy.tendsto_sum_nat.congr fun N ↦ (eval_trunc N g x).symm
  have hM (M : ℕ) : ‖(trunc M f).eval y - x‖₊ * S ≤ A * S ^ M := by
    have hlim : Tendsto (fun N ↦ ‖(trunc M f).eval ((trunc N g).eval x) - x‖₊ * S) atTop
        (𝓝 (‖(trunc M f).eval y - x‖₊ * S)) :=
      ((((trunc M f).continuous.tendsto y).comp hQlim).sub_const x).nnNorm.mul_const S
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop M] with N hN
    simpa [min_eq_left hN] using hkey M N
  -- Let the truncation degree of `f` tend to infinity.
  have hFlim : Tendsto (fun M ↦ ‖(trunc M f).eval y - x‖₊ * S) atTop (𝓝 (‖z - x‖₊ * S)) :=
    ((hz.tendsto_sum_nat.congr fun M ↦ (eval_trunc M f y).symm).sub_const x).nnNorm.mul_const S
  have hzero : Tendsto (fun M : ℕ ↦ A * S ^ M) atTop (𝓝 0) := by
    simpa using (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hS1).const_mul A
  have hle : ‖z - x‖₊ * S ≤ 0 := le_of_tendsto_of_tendsto' hFlim hzero hM
  have hzx : ‖z - x‖₊ = 0 := by
    simpa [hS0.ne'] using le_antisymm hle zero_le
  exact sub_eq_zero.mp (nnNorm_eq_zero.mp hzx)

end PowerSeries

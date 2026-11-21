/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Polynomial
import TauCeti.Analysis.Normed.Group.Ultra
import TauCeti.Analysis.Polynomial.Ultra
import TauCeti.RingTheory.Polynomial.GaussNorm
import TauCeti.RingTheory.PowerSeries.Substitution
import TauCeti.RingTheory.PowerSeries.Trunc

/-!
# Evaluating a formal inverse in an ultrametric normed algebra

Let `f` and `g` be power series over an ultrametric normed field `K` with `f.subst g = X`, so that
`f` is a left inverse of `g` under formal composition. If their coefficients satisfy
`‖cₙ‖ R ^ (n - 1) ≤ 1` for every `n`, then in every ultrametric normed `K`-algebra `A`, at every
`x` with `‖x‖ < R` at which the two series converge, `f (g x) = x`. The algebra `A` need not be
commutative or a field, and its norm need only be submultiplicative, with `‖c • a‖ ≤ ‖c‖ ‖a‖`.

The proof compares truncations. Below both truncation degrees, the composite of the truncation of
`f` with the truncation of `g` agrees with `X` (`PowerSeries.coeff_trunc_comp_trunc`). The bound
`‖cₙ‖ Rⁿ ≤ R` says that a polynomial has Gauss norm at most `R` at radius `R`; since the Gauss
norm is nonarchimedean and submultiplicative, the composite of the truncations satisfies it too
(`Polynomial.gaussNorm_comp_le`). Hence, with `S = ‖x‖ / R < 1`, its value at `x` differs from
`x` by at most `R S ^ M` below degree `M` (`Polynomial.norm_aeval_le_mul_div_pow`).
Letting the truncation degrees tend to infinity gives the identity. The argument adapts the proof
of `TauCeti.log_exp_of_mem_maximalIdeal_pow` (`TauCeti.NumberTheory.LocalField.ExpLog`), with
norms in place of the valuation of the valuative relation.

The coefficients of the exponential series and of the logarithm series over `ℚ_[p]` satisfy the
bound for the radius `p ^ (-1 / (p - 1))`, by Legendre's formula, so this proves that the
`p`-adic exponential and logarithm are mutually inverse on the disc of that radius in every
complete ultrametric normed `ℚ_[p]`-algebra.

## Main results

* `PowerSeries.eq_of_hasSum_of_subst_eq_X`: if `f.subst g = X` and the coefficients of `f` and
  `g` satisfy `‖cₙ‖ R ^ (n - 1) ≤ 1`, then `f (g x) = x` for `‖x‖ < R` in an ultrametric normed
  algebra.
-/

public section

open Filter Topology

namespace PowerSeries

variable {K : Type*} [NormedField K]

variable {A : Type*} [NormedRing A] [NormedAlgebra K A] [IsUltrametricDist K] [IsUltrametricDist A]

/-- **The truncation estimate.** If `f.subst g = X`, the coefficients of `f` and `g` satisfy
`‖cₙ‖ R ^ (n - 1) ≤ 1` and `‖x‖ ≤ R`, then the composite of the truncations of `f` below degree
`M` and of `g` below degree `N` takes a value at `x` within `R (‖x‖ / R) ^ min M N` of `x`. -/
private theorem norm_aeval_trunc_aeval_trunc_sub_le {f g : K⟦X⟧} (hf0 : coeff 0 f = 0)
    (hg0 : coeff 0 g = 0) (hfg : f.subst g = X) {R : ℝ} (hR : 0 < R)
    (hf : ∀ n, ‖coeff n f‖ * R ^ (n - 1) ≤ 1) (hg : ∀ n, ‖coeff n g‖ * R ^ (n - 1) ≤ 1) {x : A}
    (hx : ‖x‖ ≤ R) (M N : ℕ) :
    ‖Polynomial.aeval (Polynomial.aeval x (trunc N g)) (trunc M f) - x‖ ≤
      R * (‖x‖ / R) ^ min M N := by
  have hg0' : constantCoeff g = 0 := by simpa using hg0
  have htrunc {h : K⟦X⟧} (hh0 : coeff 0 h = 0) (hh : ∀ n, ‖coeff n h‖ * R ^ (n - 1) ≤ 1)
      (L n : ℕ) : ‖(trunc L h).coeff n‖ * R ^ n ≤ R := by
    rw [coeff_trunc]
    split_ifs
    · exact TauCeti.norm_mul_pow_le_of_norm_mul_pow_sub_one_le hR.le (fun h ↦ h ▸ hh0) (hh n)
    · simpa using hR.le
  -- The bound `‖cₙ‖ Rⁿ ≤ R` says that the Gauss norm at radius `R` is at most `R`.
  set v := NormedField.toAbsoluteValue K
  have hle {P : Polynomial K} (hP : ∀ n, ‖P.coeff n‖ * R ^ n ≤ R) : P.gaussNorm v R ≤ R := by
    obtain ⟨i, hi⟩ := P.exists_eq_gaussNorm v R
    exact hi ▸ hP i
  have hcomp (k : ℕ) : ‖((trunc M f).comp (trunc N g)).coeff k‖ * R ^ k ≤ R :=
    (Polynomial.le_gaussNorm v _ hR.le k).trans <|
      (Polynomial.gaussNorm_comp_le IsUltrametricDist.isNonarchimedean_norm hR.le _
        (hle (htrunc hg0 hg N))).trans (hle (htrunc hf0 hf M))
  -- `F ∘ Q - X` vanishes below degree `min M N` and has coefficients bounded by `‖cₖ‖ Rᵏ ≤ R`.
  have hG : Polynomial.aeval x ((trunc M f).comp (trunc N g) - Polynomial.X) =
      Polynomial.aeval (Polynomial.aeval x (trunc N g)) (trunc M f) - x := by
    simp [Polynomial.aeval_comp]
  rw [← hG]
  have h0 : ((trunc M f).comp (trunc N g) - Polynomial.X).coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp [Polynomial.eval_comp, ← Polynomial.coeff_zero_eq_eval_zero, coeff_trunc, hf0, hg0]
  refine Polynomial.norm_aeval_le_mul_div_pow hR h0 (fun k hk ↦ ?_) (fun k ↦ ?_) hx
  · rw [Polynomial.coeff_sub, coeff_trunc_comp_trunc f hg0' (lt_min_iff.mp hk).1
      (lt_min_iff.mp hk).2, hfg, Polynomial.coeff_X, coeff_X]
    grind
  · rw [Polynomial.coeff_sub]
    refine (mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_sub_le_max _ _)
      (pow_nonneg hR.le k)).trans ?_
    rw [max_mul_of_nonneg _ _ (pow_nonneg hR.le k)]
    refine max_le (hcomp k) ?_
    rw [Polynomial.coeff_X]
    split_ifs with h
    · simp [← h]
    · simpa using hR.le

/-- **A formal left inverse is a left inverse on a disc.** Let `f` and `g` be power series over an
ultrametric normed field `K` with `f.subst g = X`, whose coefficients satisfy
`‖cₙ‖ R ^ (n - 1) ≤ 1`. Let `A` be an ultrametric normed `K`-algebra. If `x ∈ A` has `‖x‖ < R`,
the series of `g` at `x` sums to `y` and the series of `f` at `y` sums to `z`, then `z = x`. -/
theorem eq_of_hasSum_of_subst_eq_X {f g : K⟦X⟧} (hg0 : constantCoeff g = 0)
    (hfg : f.subst g = X) {R : ℝ} (hf : ∀ n, ‖coeff n f‖ * R ^ (n - 1) ≤ 1)
    (hg : ∀ n, ‖coeff n g‖ * R ^ (n - 1) ≤ 1) {x y z : A} (hx : ‖x‖ < R)
    (hy : HasSum (fun n ↦ coeff n g • x ^ n) y) (hz : HasSum (fun n ↦ coeff n f • y ^ n) z) :
    z = x := by
  -- The constant coefficient of `f` is that of `f.subst g = X`.
  have hf0 : coeff 0 f = 0 := by
    have h := coeff_trunc_comp_trunc f hg0 (M := 1) (N := 1) (k := 0) one_pos one_pos
    simpa [hfg, trunc_one] using h
  have hR : 0 < R := (norm_nonneg x).trans_lt hx
  have hS0 : 0 ≤ ‖x‖ / R := by positivity
  have hS1 : ‖x‖ / R < 1 := (div_lt_one hR).mpr hx
  have hkey := norm_aeval_trunc_aeval_trunc_sub_le hf0 (by simpa using hg0) hfg hR hf hg hx.le
  -- Let the truncation degree of `g` tend to infinity.
  have hQlim : Tendsto (fun N ↦ Polynomial.aeval x (trunc N g)) atTop (𝓝 y) :=
    hy.tendsto_sum_nat.congr fun N ↦ (aeval_trunc N g x).symm
  have hM (M : ℕ) : ‖Polynomial.aeval y (trunc M f) - x‖ ≤ R * (‖x‖ / R) ^ M := by
    have hlim : Tendsto (fun N ↦ ‖Polynomial.aeval (Polynomial.aeval x (trunc N g)) (trunc M f) -
        x‖) atTop (𝓝 ‖Polynomial.aeval y (trunc M f) - x‖) :=
      ((((trunc M f).continuous_aeval.tendsto y).comp hQlim).sub_const x).norm
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop M] with N hN
    simpa [min_eq_left hN] using hkey M N
  -- Let the truncation degree of `f` tend to infinity.
  have hFlim : Tendsto (fun M ↦ ‖Polynomial.aeval y (trunc M f) - x‖) atTop (𝓝 ‖z - x‖) :=
    ((hz.tendsto_sum_nat.congr fun M ↦ (aeval_trunc M f y).symm).sub_const x).norm
  have hzero : Tendsto (fun M : ℕ ↦ R * (‖x‖ / R) ^ M) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hS0 hS1).const_mul R
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (le_of_tendsto_of_tendsto' hFlim hzero hM))

end PowerSeries

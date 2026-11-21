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
import Mathlib.RingTheory.Polynomial.GaussNorm
import Mathlib.Topology.Algebra.Polynomial
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
norm is nonarchimedean and submultiplicative (`Polynomial.isNonarchimedean_gaussNorm`,
`Polynomial.gaussNorm_mul_le`), the composite of the truncations satisfies it too. Hence, with
`S = ‖x‖ / R < 1`, its value at `x` differs from `x` by at most `R S ^ M` below degree `M`.
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

open Polynomial in
/-- **Composition preserves the coefficient bound `‖cₙ‖ Rⁿ ≤ R`.** If the coefficients of the
polynomials `F` and `Q` over an ultrametric normed field satisfy `‖cₙ‖ Rⁿ ≤ R`, then so do those
of `F.comp Q`: each `C (F.coeff n) * Q ^ n` has Gauss norm at most `‖F.coeff n‖ Rⁿ ≤ R` at
radius `R`, and the Gauss norm is nonarchimedean. -/
private theorem norm_coeff_comp_mul_pow_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    {F Q : K[X]} {R : ℝ} (hR : 0 ≤ R) (hF : ∀ n, ‖F.coeff n‖ * R ^ n ≤ R)
    (hQ : ∀ n, ‖Q.coeff n‖ * R ^ n ≤ R) (k : ℕ) : ‖(F.comp Q).coeff k‖ * R ^ k ≤ R := by
  set v := NormedField.toAbsoluteValue K
  have hna : IsNonarchimedean v := IsUltrametricDist.isNonarchimedean_norm
  have hle {P : K[X]} (hP : ∀ n, ‖P.coeff n‖ * R ^ n ≤ R) : P.gaussNorm v R ≤ R := by
    obtain ⟨i, hi⟩ := P.exists_eq_gaussNorm v R
    exact hi ▸ hP i
  have hQn (n : ℕ) : (Q ^ n).gaussNorm v R ≤ R ^ n := by
    induction n with
    | zero => simp [← Polynomial.C_1, -map_one]
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (gaussNorm_mul_le v hna _ _ hR).trans (mul_le_mul ih (hle hQ)
        (Polynomial.gaussNorm_nonneg v _ hR) (pow_nonneg hR n))
  refine (Polynomial.le_gaussNorm v _ hR k).trans ?_
  rw [comp_eq_sum_left, Polynomial.sum_def]
  obtain ⟨n, -, hsum⟩ := (isNonarchimedean_gaussNorm v hna hR).finset_image_add
    (fun n ↦ Polynomial.C (F.coeff n) * Q ^ n) F.support fun P ↦ by
      simpa using Polynomial.gaussNorm_nonneg v P hR
  refine hsum.trans <| (gaussNorm_mul_le v hna _ _ hR).trans ?_
  rw [Polynomial.gaussNorm_C]
  exact (mul_le_mul_of_nonneg_left (hQn n) (norm_nonneg _)).trans (hF n)

/-- **Evaluating a polynomial with small coefficients.** In an ultrametric normed algebra over
an ultrametric normed field, a polynomial with vanishing constant coefficient, vanishing
coefficients below degree `m` and coefficients bounded by `‖cₖ‖ Rᵏ ≤ R` takes at `x` with
`‖x‖ ≤ R` a value of norm at most `R (‖x‖ / R) ^ m`. -/
private theorem norm_aeval_le {K A : Type*} [NormedField K] [NormedRing A] [NormedAlgebra K A]
    [IsUltrametricDist A] {P : Polynomial K} {R : ℝ} (hR : 0 < R) (hP0 : P.coeff 0 = 0) {m : ℕ}
    (hPm : ∀ k < m, P.coeff k = 0) (hP : ∀ k, ‖P.coeff k‖ * R ^ k ≤ R) {x : A}
    (hx : ‖x‖ ≤ R) : ‖Polynomial.aeval x P‖ ≤ R * (‖x‖ / R) ^ m := by
  have hS0 : 0 ≤ ‖x‖ / R := by positivity
  have hS1 : ‖x‖ / R ≤ 1 := (div_le_one hR).mpr hx
  rw [Polynomial.aeval_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ ↦ ?_
  rcases lt_or_ge k m with hk | hk
  · simpa [hPm k hk] using by positivity
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simpa [hP0] using by positivity
  calc ‖P.coeff k • x ^ k‖ ≤ ‖P.coeff k‖ * ‖x‖ ^ k :=
        (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_pow_le' x hk0) (norm_nonneg _))
    _ = ‖P.coeff k‖ * R ^ k * (‖x‖ / R) ^ k := by
        rw [div_pow, mul_assoc, mul_div_cancel₀ _ (pow_pos hR k).ne']
    _ ≤ R * (‖x‖ / R) ^ m :=
        mul_le_mul (hP k) (pow_le_pow_of_le_one hS0 hS1 hk) (by positivity) hR.le

variable {K : Type*} [NormedField K]

/-- The coefficient bound `‖c‖ R ^ (n - 1) ≤ 1` is the weighted bound `‖c‖ Rⁿ ≤ R` when the
constant coefficient vanishes. -/
private theorem norm_mul_pow_le_of_norm_mul_pow_sub_one_le {c : K} {n : ℕ} {R : ℝ} (hR : 0 < R)
    (hc0 : n = 0 → c = 0) (hc : ‖c‖ * R ^ (n - 1) ≤ 1) : ‖c‖ * R ^ n ≤ R := by
  rcases n with _ | m
  · simp [hc0 rfl, hR.le]
  rw [Nat.add_sub_cancel] at hc
  rw [pow_succ, ← mul_assoc]
  exact mul_le_of_le_one_left hR.le hc

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
    · exact norm_mul_pow_le_of_norm_mul_pow_sub_one_le hR (fun h ↦ h ▸ hh0) (hh n)
    · simpa using hR.le
  have hcomp := norm_coeff_comp_mul_pow_le hR.le (htrunc hf0 hf M) (htrunc hg0 hg N)
  -- `F ∘ Q - X` vanishes below degree `min M N` and has coefficients bounded by `‖cₖ‖ Rᵏ ≤ R`.
  have hG : Polynomial.aeval x ((trunc M f).comp (trunc N g) - Polynomial.X) =
      Polynomial.aeval (Polynomial.aeval x (trunc N g)) (trunc M f) - x := by
    simp [Polynomial.aeval_comp]
  rw [← hG]
  have h0 : ((trunc M f).comp (trunc N g) - Polynomial.X).coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_sub, Polynomial.eval_X, sub_zero,
      Polynomial.eval_comp, ← Polynomial.coeff_zero_eq_eval_zero, coeff_trunc, hg0, ite_self,
      ← Polynomial.coeff_zero_eq_eval_zero, coeff_trunc, hf0, ite_self]
  refine norm_aeval_le hR h0 (fun k hk ↦ ?_) (fun k ↦ ?_) hx
  · rw [Polynomial.coeff_sub, coeff_trunc_comp_trunc f hg0' (lt_min_iff.mp hk).1
      (lt_min_iff.mp hk).2, hfg, Polynomial.coeff_X, coeff_X]
    grind
  · have hsub (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
      simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max a (-b)
    rw [Polynomial.coeff_sub]
    refine (mul_le_mul_of_nonneg_right (hsub _ _) (pow_nonneg hR.le k)).trans ?_
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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import TauCeti.Analysis.Complex.IteratedDeriv
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.Contiguous
import TauCeti.RingTheory.Polynomial.Pochhammer
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Confluence of the regularized Gauss function

As the real upper parameter `t` tends to infinity, the rescaled Gauss function
`𝐅(a, t; c; z/t)` converges to the regularized Kummer function `𝐌(a, c, z)`, locally
uniformly in `z`. Regularization allows every complex lower parameter `c`.

The multiplier relating the two series terms of degree `n` is
`(t)ₙ / tⁿ = ∏_{j < n} (1 + j/t)`. It tends to one for each `n` and is nonincreasing
for positive `t`. Thus on the disk `‖z‖ ≤ R` any fixed `T > R` gives a summable majorant
from the Gauss series at `R/T`. Every fixed disk eventually lies in the domain of
holomorphy of the rescaled functions, so all argument derivatives converge locally uniformly
as well. Scaling the argument by a further factor of `1/t` gives the constant limit `1/Γ(c)`.

## References

* N. N. Lebedev, *Special Functions and Their Applications*, §9.9, (9.9.3).
-/

public section

open Filter Topology
open scoped BigOperators

namespace Complex

private theorem gauss_confluence_term (a c z : ℂ) {t : ℝ} (ht : t ≠ 0) (n : ℕ) :
    (regularizedGaussHGFunSeries a t c).coeff n * (z / t) ^ n =
      regularizedHGFunCoeff {a} {c} n * z ^ n *
        ((∏ j ∈ Finset.range n, (1 + (j : ℝ) / t) : ℝ) : ℂ) := by
  have h (j : ℕ) : 1 + (j : ℝ) / t = (t + j) / t := by field_simp
  simp_rw [h]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_range, ofReal_div, ofReal_prod, ofReal_pow,
    ofReal_add, ofReal_natCast, ← TauCeti.ascPochhammer_eval_eq_prod_range n (t : ℂ),
    coeff_regularizedGaussHGFunSeries, regularizedHGFunCoeff_singleton, div_pow]
  ring

private theorem norm_gauss_confluence_term_le (a c : ℂ) {t T R : ℝ} {z : ℂ}
    (hT : 0 < T) (ht : T ≤ t) (hz : ‖z‖ ≤ R) (n : ℕ) :
    ‖(regularizedGaussHGFunSeries a t c).coeff n * (z / t) ^ n‖ ≤
      ‖(regularizedGaussHGFunSeries a T c).coeff n * ((R : ℂ) / T) ^ n‖ := by
  have ht' := hT.trans_le ht
  have hR := (norm_nonneg z).trans hz
  rw [gauss_confluence_term a c z ht'.ne', gauss_confluence_term a c R hT.ne']
  have hpos {s : ℝ} (hs : 0 < s) : 0 ≤ ∏ j ∈ Finset.range n, (1 + (j : ℝ) / s) :=
    Finset.prod_nonneg fun _ _ ↦ by positivity
  simp only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_nonneg hR,
    abs_of_nonneg (hpos ht'), abs_of_nonneg (hpos hT)]
  gcongr

/-- The regularized Gauss functions with upper parameter `t → +∞` and argument `z/t`
converge locally uniformly in `z` to the regularized Kummer function. -/
theorem tendstoLocallyUniformly_regularizedGaussHGFun_div_atTop (a c : ℂ) :
    TendstoLocallyUniformly (fun (t : ℝ) (z : ℂ) ↦ regularizedGaussHGFun a t c (z / t))
      (regularizedHGFun {a} {c}) atTop := by
  rw [← tendstoLocallyUniformlyOn_univ,
    isOpen_univ.tendstoLocallyUniformlyOn_iff_forall_tendsto_of_continuousOn
      (differentiable_regularizedHGFun_of_card_le (by simp)).continuous.continuousOn]
  intro z _
  let R := ‖z‖ + 1
  let T := R + 1
  have hR : 0 < R := by positivity
  have hT : 0 < T := by positivity
  have hsum := summable_norm_regularizedGaussHGFun a T c (z := (R : ℂ) / T) (by
    rw [norm_div, norm_real, norm_real, Real.norm_of_nonneg hR.le, Real.norm_of_nonneg hT.le,
      div_lt_one hT]
    exact lt_add_one R)
  simp_rw [regularizedGaussHGFun_eq_tsum_coeff_mul_pow]
  rw [← (hasSum_regularizedHGFun (a := {a}) (b := {c}) (by simp) z).tsum_eq]
  apply tendsto_tsum_of_dominated_convergence hsum
  · intro n
    have hprod : Tendsto (fun t : ℝ ↦ ∏ j ∈ Finset.range n, (1 + (j : ℝ) / t))
        atTop (𝓝 1) := by
      simpa using tendsto_finsetProd (Finset.range n) (fun j _ ↦
        ((tendsto_const_nhds (x := (j : ℝ))).div_atTop tendsto_id).const_add 1)
    have hw : Tendsto (fun p : ℝ × ℂ ↦ p.2) (atTop ×ˢ 𝓝 z) (𝓝 z) := tendsto_snd
    have hterm := ((hw.pow n).const_mul (regularizedHGFunCoeff {a} {c} n)).mul
      ((continuous_ofReal.tendsto 1).comp (hprod.comp tendsto_fst))
    simp only [ofReal_one, mul_one] at hterm
    apply hterm.congr'
    filter_upwards [tendsto_fst.eventually (eventually_gt_atTop (0 : ℝ))] with p hp
    exact (gauss_confluence_term a c p.2 hp.ne' n).symm
  · have hz : ∀ᶠ w in 𝓝 z, ‖w‖ < R :=
      continuous_norm.continuousAt.eventually_lt continuousAt_const (lt_add_one _)
    filter_upwards [tendsto_fst.eventually (eventually_ge_atTop T),
      tendsto_snd.eventually hz] with p hp hw n
    exact norm_gauss_confluence_term_le a c hT hp hw.le n

/-- Gauss's confluence limit at any fixed complex argument, including at poles of `Γ(c)`. -/
theorem tendsto_regularizedGaussHGFun_div_atTop (a c z : ℂ) :
    Tendsto (fun t : ℝ ↦ regularizedGaussHGFun a t c (z / t)) atTop
      (𝓝 (regularizedHGFun {a} {c} z)) :=
  (tendstoLocallyUniformly_regularizedGaussHGFun_div_atTop a c).tendsto_at z

/-- With argument `z/t²`, the regularized Gauss function tends to the constant term of
the Kummer series. -/
theorem tendsto_regularizedGaussHGFun_div_sq_atTop (a c z : ℂ) :
    Tendsto (fun t : ℝ ↦ regularizedGaussHGFun a t c (z / (t : ℂ) ^ 2)) atTop
      (𝓝 (Gamma c)⁻¹) := by
  have hz : Tendsto (fun t : ℝ ↦ z / (t : ℂ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).ofReal.const_mul z
  simpa [div_div, ← sq, regularizedHGFun_zero, regularizedHGFunCoeff_singleton_zero] using
    (tendstoLocallyUniformly_regularizedGaussHGFun_div_atTop a c).tendsto_comp
      (differentiable_regularizedHGFun_of_card_le (by simp)).continuous.continuousAt hz

/-- All argument derivatives of the rescaled Gauss functions converge locally uniformly to
the corresponding Kummer derivatives. In particular this applies to both derivatives in
the hypergeometric differential equation. -/
theorem tendstoLocallyUniformly_iteratedDeriv_regularizedGaussHGFun_div_atTop (a c : ℂ) (k : ℕ) :
    TendstoLocallyUniformly
      (fun t : ℝ ↦ iteratedDeriv k (fun z : ℂ ↦ regularizedGaussHGFun a t c (z / t)))
      (iteratedDeriv k (regularizedHGFun {a} {c})) atTop := by
  rw [← tendstoLocallyUniformlyOn_univ, ← Metric.iUnion_ball_nat (0 : ℂ)]
  refine tendstoLocallyUniformlyOn_iUnion (fun _ ↦ Metric.isOpen_ball) fun n ↦ ?_
  have h := tendstoLocallyUniformly_regularizedGaussHGFun_div_atTop a c
  apply h.tendstoLocallyUniformlyOn.iteratedDeriv _ Metric.isOpen_ball k
  filter_upwards [eventually_gt_atTop (n : ℝ)] with t ht
  intro z hz
  have ht' := (Nat.cast_nonneg n).trans_lt ht
  have hzt : ‖z / (t : ℂ)‖ < 1 := by
    rw [norm_div, norm_real, Real.norm_of_nonneg ht'.le, div_lt_one ht']
    exact (mem_ball_zero_iff.mp hz).trans ht
  exact ((analyticAt_regularizedGaussHGFun a t c hzt).differentiableAt.comp z
    (differentiableAt_id.div_const _)).differentiableWithinAt

end Complex

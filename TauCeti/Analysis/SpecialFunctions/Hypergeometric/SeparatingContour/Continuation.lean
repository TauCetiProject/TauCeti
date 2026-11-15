/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.SeparatingContour.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# Mellin–Barnes continuation of Euler's integral and the Gauss hypergeometric function

This module identifies the separating-contour Mellin–Barnes functional `Complex.mellinBarnesContour`
(and hence `Complex.mellinBarnesSeparating` at every admissible abscissa `σ < 0`) with Euler's
normalized integral `Complex.eulerIntegral`, the regularized Gauss hypergeometric function
`Complex.regularizedGaussHGFun`, and the ordinary Gauss hypergeometric function
`Complex.ordinaryHypergeometric` (`₂F₁`), establishing DLMF 15.6.6 across all non-exceptional
parameters `a, b ∉ -ℕ`, including negative real parts and integer differences `a - b ∈ ℤ`.

On the negative real half-line `z = -x` (`x > 0`) in the classical convergence region
`0 < Re a`, `0 < Re b < Re c`, an abscissa `-min (Re a) (Re b) < σ < 0` has empty residue sum, and
Fubini's theorem interchanges the vertical Mellin–Barnes integral of `(1 + x t)^{-a}`
(`Complex.integral_cpow_neg_mul_Gamma_mul_Gamma_sub`) with the Beta integral on `(0, 1)`. Combining
joint holomorphy of `mellinBarnesContour` (`Complex.analyticOnNhd_mellinBarnesContour`),
`eulerIntegral` (`Complex.analyticOnNhd_eulerIntegral`), and `regularizedGaussHGFun`
(`Complex.analyticOnNhd_regularizedGaussHGFun`) with the identity theorem along preconnected
cut-plane and punctured-parameter domains extends the representation to general parameters.

## Main results

* `Complex.eulerIntegral_eq_mellinBarnesContour`,
  `Complex.eulerIntegral_eq_mellinBarnesSeparating`: Mellin–Barnes continuation of Euler's integral
  for `0 < Re b < Re c`, `a ∉ -ℕ`, and `-z ∈ Complex.slitPlane`.
* `Complex.regularizedGaussHGFun_eq_mellinBarnesContour`,
  `Complex.regularizedGaussHGFun_eq_mellinBarnesSeparating`: DLMF 15.6.6 for
  `regularizedGaussHGFun` across `a, b ∉ -ℕ`, arbitrary `c : ℂ`, `‖z‖ < 1`, and `-z ∈ slitPlane`.
* `Complex.ordinaryHypergeometric_eq_mellinBarnesContour`,
  `Complex.ordinaryHypergeometric_eq_mellinBarnesSeparating`: DLMF 15.6.6 for
  `ordinaryHypergeometric` (`₂F₁`) across `a, b, c ∉ -ℕ`, `‖z‖ < 1`, and `-z ∈ slitPlane`.

## References

* NIST Digital Library of Mathematical Functions, §15.6(ii), equation 15.6.6.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §14.5.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 5.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Nat Real Topology

namespace Complex

private def mellinBarnesFubiniKernel (a b c : ℂ) (x σ : ℝ) (t y : ℝ) : ℂ :=
  (t : ℂ) ^ (b + (σ + y * I) - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
    ((x : ℂ) ^ (σ + y * I) * (Gamma (-(σ + y * I)) * Gamma (a + (σ + y * I))))

private theorem continuousOn_mellinBarnesFubiniKernel {a b c : ℂ} {x σ : ℝ}
    (hx : 0 < x) (hσ : σ < 0) (haσ : 0 < a.re + σ) :
    ContinuousOn (Function.uncurry (mellinBarnesFubiniKernel a b c x σ))
      (Ioo (0 : ℝ) 1 ×ˢ univ) := by
  refine continuousOn_of_forall_continuousAt fun ⟨t, y⟩ ⟨ht, _⟩ => ?_
  have hs : ContinuousAt (fun p : ℝ × ℝ => (σ : ℂ) + (p.2 : ℂ) * I) (t, y) := by fun_prop
  have ht_slit : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 ht.1
  have h1t_slit : 1 - (t : ℂ) ∈ slitPlane := by
    rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; ring]
    exact ofReal_mem_slitPlane.2 (sub_pos.2 ht.2)
  have hx_slit : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 hx
  have hG1 : ContinuousAt (fun p : ℝ × ℝ => Gamma (-((σ : ℂ) + p.2 * I))) (t, y) := by
    refine (differentiableAt_Gamma _ fun m hm => ?_).continuousAt.comp hs.neg
    have hre := congrArg re hm
    simp only [neg_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, natCast_re] at hre
    linarith [m.cast_nonneg (α := ℝ)]
  have hG2 : ContinuousAt (fun p : ℝ × ℝ => Gamma (a + ((σ : ℂ) + p.2 * I))) (t, y) := by
    refine (differentiableAt_Gamma _ fun m hm => ?_).continuousAt.comp (continuousAt_const.add hs)
    have hre := congrArg re hm
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, neg_re, natCast_re] at hre
    linarith [m.cast_nonneg (α := ℝ)]
  have hc1 : ContinuousAt (fun p : ℝ × ℝ => (p.1 : ℂ) ^ (b + (σ + p.2 * I) - 1)) (t, y) :=
    ContinuousAt.cpow (by fun_prop) ((continuousAt_const.add hs).sub continuousAt_const) ht_slit
  have hc2 : ContinuousAt (fun p : ℝ × ℝ => (1 - (p.1 : ℂ)) ^ (c - b - 1)) (t, y) :=
    ContinuousAt.cpow (by fun_prop) continuousAt_const h1t_slit
  have hc3 : ContinuousAt (fun p : ℝ × ℝ => (x : ℂ) ^ ((σ : ℂ) + p.2 * I)) (t, y) :=
    ContinuousAt.cpow continuousAt_const hs hx_slit
  exact (hc1.mul hc2).mul (hc3.mul (hG1.mul hG2))

private theorem integrable_mellinBarnesFubiniKernel {a b c : ℂ} {x σ : ℝ}
    (hx : 0 < x) (hσ : σ < 0) (haσ : 0 < a.re + σ) (hbσ : 0 < b.re + σ) (hbc : b.re < c.re) :
    Integrable (Function.uncurry (mellinBarnesFubiniKernel a b c x σ))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod volume) := by
  let g₁ : ℝ → ℝ := fun t => ‖(t : ℂ) ^ ((b + σ : ℂ) - 1) * (1 - (t : ℂ)) ^ (c - b - 1)‖
  let g₂ : ℝ → ℝ := fun y => x ^ σ * ‖Gamma (-(σ + y * I)) * Gamma (a + (σ + y * I))‖
  have hg₁ : Integrable g₁ (volume.restrict (Ioo (0 : ℝ) 1)) := by
    have hbeta := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (betaIntegral_convergent (u := b + σ) (v := c - b) (by simpa using hbσ)
        (by simpa using sub_pos.2 hbc))
    rw [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hbeta
    exact hbeta.norm
  have hg₂ : Integrable g₂ volume := by
    have hv : Integrable (fun y : ℝ =>
        Gamma ((-σ : ℝ) + y * I) * Gamma (a - ((-σ : ℝ) + y * I))) volume :=
      verticalIntegrable_Gamma_mul_Gamma_sub
        (fun n hn => by linarith [n.cast_nonneg (α := ℝ)])
        (fun n hn => by linarith [n.cast_nonneg (α := ℝ)])
    have hv' : Integrable (fun y : ℝ => Gamma (-(σ + y * I)) * Gamma (a + (σ + y * I))) volume := by
      refine hv.comp_neg.congr (Eventually.of_forall fun y => ?_)
      dsimp only
      have h1 : ((-σ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I = -((σ : ℂ) + y * I) := by push_cast; ring
      rw [h1, sub_neg_eq_add]
    exact hv'.norm.const_mul (x ^ σ)
  have hmeas_prod : (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume : Measure ℝ) =
      ((volume : Measure ℝ).prod volume).restrict (Ioo (0 : ℝ) 1 ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  refine (hg₁.mul_prod hg₂).mono' ?_ ?_
  · rw [hmeas_prod]
    exact (continuousOn_mellinBarnesFubiniKernel hx hσ haσ).aestronglyMeasurable
      (measurableSet_Ioo.prod MeasurableSet.univ)
  · rw [hmeas_prod]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)] with ⟨t, y⟩ ⟨ht, _⟩
    have ht_pos : 0 < t := ht.1
    dsimp [Function.uncurry, mellinBarnesFubiniKernel, g₁, g₂]
    rw [norm_mul, norm_mul, norm_mul, norm_mul ((t : ℂ) ^ ((b + σ : ℂ) - 1)),
      norm_cpow_eq_rpow_re_of_pos ht_pos, norm_cpow_eq_rpow_re_of_pos ht_pos,
      norm_cpow_eq_rpow_re_of_pos hx]
    have hre1 : (b + (σ + y * I) - 1).re = ((b + σ : ℂ) - 1).re := by simp
    have hre2 : ((σ : ℂ) + y * I).re = σ := by simp
    rw [hre1, hre2, mul_assoc]

private theorem integral_mellinBarnesFubiniKernel_y {a b c : ℂ} {x σ t : ℝ}
    (hx : 0 < x) (ht : t ∈ Ioo (0 : ℝ) 1) (hσ : σ < 0) (haσ : 0 < a.re + σ) :
    ∫ y : ℝ, mellinBarnesFubiniKernel a b c x σ t y =
      2 * π * Gamma a * ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
        (1 - (-(x : ℂ)) * (t : ℂ)) ^ (-a)) := by
  have hpoint (y : ℝ) : mellinBarnesFubiniKernel a b c x σ t y =
      ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
        (((x * t : ℝ) : ℂ) ^ ((σ : ℂ) + y * I) *
          (Gamma (-((σ : ℂ) + y * I)) * Gamma (a + ((σ : ℂ) + y * I)))) := by
    dsimp [mellinBarnesFubiniKernel]
    have hexp : b + ((σ : ℂ) + y * I) - 1 = (b - 1) + ((σ : ℂ) + y * I) := by ring
    rw [hexp, cpow_add _ _ (ofReal_ne_zero.2 ht.1.ne'), ofReal_mul,
      mul_cpow_ofReal_nonneg hx.le ht.1.le]
    ring
  simp_rw [hpoint, integral_const_mul]
  rw [← integral_neg_eq_self]
  have hneg (y : ℝ) : ((x * t : ℝ) : ℂ) ^ ((σ : ℂ) + (-y : ℝ) * I) *
      (Gamma (-((σ : ℂ) + (-y : ℝ) * I)) * Gamma (a + ((σ : ℂ) + (-y : ℝ) * I))) =
      ((x * t : ℝ) : ℂ) ^ (-((-σ : ℝ) + (y : ℂ) * I)) *
        (Gamma ((-σ : ℝ) + (y : ℂ) * I) * Gamma (a - ((-σ : ℝ) + (y : ℂ) * I))) := by
    have h1 : (σ : ℂ) + (-y : ℝ) * I = -((-σ : ℝ) + (y : ℂ) * I) := by push_cast; ring
    have h2 : -((σ : ℂ) + (-y : ℝ) * I) = (-σ : ℝ) + (y : ℂ) * I := by push_cast; ring
    have h3 : a + ((σ : ℂ) + (-y : ℝ) * I) = a - ((-σ : ℝ) + (y : ℂ) * I) := by push_cast; ring
    rw [h2, h3, h1]
  simp_rw [hneg]
  rw [integral_cpow_neg_mul_Gamma_mul_Gamma_sub (by linarith) (by linarith) (mul_pos hx ht.1)]
  have h1 : (1 : ℂ) + ((x * t : ℝ) : ℂ) = 1 - (-(x : ℂ)) * (t : ℂ) := by push_cast; ring
  rw [h1]
  ring

private theorem integral_mellinBarnesFubiniKernel_t {a b c : ℂ} {x σ : ℝ} (y : ℝ)
    (hbσ : 0 < b.re + σ) (hbc : b.re < c.re) :
    ∫ t in Ioo (0 : ℝ) 1, mellinBarnesFubiniKernel a b c x σ t y =
      Gamma (c - b) * mellinBarnesIntegrand a b c (-(x : ℂ)) (σ + y * I) := by
  dsimp only [mellinBarnesFubiniKernel]
  rw [integral_mul_const, setIntegral_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one, ← betaIntegral,
    betaIntegral_eq_Gamma_mul_div (b + (σ + y * I)) (c - b) (by simpa using hbσ)
      (by simpa using sub_pos.2 hbc)]
  have hadd : b + ((σ : ℂ) + y * I) + (c - b) = c + ((σ : ℂ) + y * I) := by ring
  rw [hadd, mellinBarnesIntegrand_def, neg_neg, div_eq_mul_inv]
  ring

private theorem eulerIntegral_neg_ofReal_eq_mellinBarnesContour {a b c : ℂ} {x : ℝ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hbc : b.re < c.re) (hx : 0 < x) :
    Gamma a * Gamma b * eulerIntegral a b c (-(x : ℂ)) =
      mellinBarnesContour a b c (-(x : ℂ)) := by
  let σ : ℝ := -min (min a.re b.re) 1 / 2
  have hmin : 0 < min (min a.re b.re) 1 := lt_min (lt_min ha hb) zero_lt_one
  have hσ : σ < 0 := by dsimp [σ]; linarith
  have haσ : 0 < a.re + σ := by
    have : min (min a.re b.re) 1 ≤ a.re := (min_le_left _ _).trans (min_le_left _ _)
    dsimp [σ]; linarith
  have hbσ : 0 < b.re + σ := by
    have : min (min a.re b.re) 1 ≤ b.re := (min_le_left _ _).trans (min_le_right _ _)
    dsimp [σ]; linarith
  have hswap := integral_integral_swap
    (integrable_mellinBarnesFubiniKernel hx hσ haσ hbσ hbc (c := c))
  have hlhs : (∫ t in Ioo (0 : ℝ) 1, ∫ y : ℝ, mellinBarnesFubiniKernel a b c x σ t y) =
      2 * π * Gamma (c - b) * (Gamma a * Gamma b * eulerIntegral a b c (-(x : ℂ))) := by
    rw [setIntegral_congr_fun measurableSet_Ioo fun t ht =>
        integral_mellinBarnesFubiniKernel_y hx ht hσ haσ,
      integral_const_mul, setIntegral_congr_set Ioo_ae_eq_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one]
    have hGb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
    have hGcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using sub_pos.2 hbc)
    rw [eulerIntegral_def]
    set J := ∫ t : ℝ in 0..1,
      (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - (-(x : ℂ)) * (t : ℂ)) ^ (-a)
    field_simp [hGb, hGcb]
  have hrhs : (∫ y : ℝ, ∫ t in Ioo (0 : ℝ) 1, mellinBarnesFubiniKernel a b c x σ t y) =
      Gamma (c - b) * ∫ y : ℝ, mellinBarnesIntegrand a b c (-(x : ℂ)) (σ + y * I) := by
    simp_rw [integral_mellinBarnesFubiniKernel_t _ hbσ hbc, integral_const_mul]
  rw [hlhs, hrhs] at hswap
  have hGcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using sub_pos.2 hbc)
  have h2pi : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)
  have h2pi_inv : (2 * (π : ℂ)) * ((2 * π : ℂ)⁻¹) = 1 := mul_inv_cancel₀ h2pi
  have hm := mellinBarnesContour_eq_mellinBarnesSeparating (a := a) (b := b) c hσ
    (fun k hk => by linarith [k.cast_nonneg (α := ℝ)])
    (fun k hk => by linarith [k.cast_nonneg (α := ℝ)])
    (by simpa using ofReal_mem_slitPlane.2 hx : -(-(x : ℂ)) ∈ slitPlane)
  rw [hm, mellinBarnesSeparating_of_neg_re_le _ _ (by linarith) (by linarith)]
  apply mul_left_cancel₀ h2pi
  apply mul_left_cancel₀ hGcb
  calc Gamma (c - b) * (2 * π * (Gamma a * Gamma b * eulerIntegral a b c (-(x : ℂ))))
      = 2 * π * Gamma (c - b) * (Gamma a * Gamma b * eulerIntegral a b c (-(x : ℂ))) := by ring
    _ = Gamma (c - b) * ∫ y : ℝ, mellinBarnesIntegrand a b c (-(x : ℂ)) (σ + y * I) := hswap
    _ = Gamma (c - b) * (2 * π * ((2 * π : ℂ)⁻¹ *
          ∫ y : ℝ, mellinBarnesIntegrand a b c (-(x : ℂ)) (σ + y * I))) := by
        rw [← mul_assoc (2 * (π : ℂ)), h2pi_inv, one_mul]

private theorem isPreconnected_neg_mem_slitPlane :
    IsPreconnected {z : ℂ | -z ∈ slitPlane} := by
  have h := (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
  convert h.image (fun z : ℂ => -z) continuous_neg.continuousOn using 1
  ext z
  exact ⟨fun hz => ⟨-z, hz, neg_neg z⟩, fun ⟨w, hw, hwz⟩ => by simpa [← hwz] using hw⟩

private theorem isPreconnected_ball_inter_neg_mem_slitPlane :
    IsPreconnected {z : ℂ | ‖z‖ < 1 ∧ -z ∈ slitPlane} := by
  let z₀ : ℂ := -((1 / 2 : ℝ) : ℂ)
  have hhalf : ((1 / 2 : ℝ) : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 (by norm_num)
  have hz₀ : z₀ ∈ {z : ℂ | ‖z‖ < 1 ∧ -z ∈ slitPlane} :=
    ⟨by simp [z₀]; norm_num, by simpa only [z₀, neg_neg] using hhalf⟩
  have hstar : StarConvex ℝ z₀ {z : ℂ | ‖z‖ < 1 ∧ -z ∈ slitPlane} := by
    intro z ⟨hzn, hzs⟩ u v hu hv huv
    refine ⟨?_, ?_⟩
    · have hb := (convex_ball (0 : ℂ) 1) (by simpa using hz₀.1) (by simpa using hzn) hu hv huv
      simpa using hb
    · have hneg : -(u • z₀ + v • z) = u • ((1 / 2 : ℝ) : ℂ) + v • (-z) := by
        simp only [z₀, neg_add, smul_neg, neg_neg]
      rw [hneg]
      exact starConvex_ofReal_slitPlane (by norm_num) hzs hu hv huv
  exact (hstar.isPathConnected hz₀).isConnected.isPreconnected

private theorem isPreconnected_ne_neg_nat :
    IsPreconnected {w : ℂ | ∀ k : ℕ, w ≠ -k} := by
  have hset : {w : ℂ | ∀ k : ℕ, w ≠ -k} = (Set.range fun k : ℕ => -(k : ℂ))ᶜ := by
    ext w
    simp [eq_comm]
  rw [hset]
  exact ((Set.countable_range _).isConnected_compl_of_one_lt_rank
    (Complex.rank_real_complex ▸ Nat.one_lt_ofNat)).isPreconnected

private theorem frequently_nhdsWithin_neg_quarter {P : ℂ → Prop}
    (hP : ∀ x ∈ Ioo (0 : ℝ) (1 / 2), P (-(x : ℂ))) :
    ∃ᶠ z in 𝓝[≠] (-((1 / 4 : ℝ) : ℂ)), P z := by
  let xseq : ℕ → ℝ := fun n => 1 / 4 + (n + 5 : ℝ)⁻¹
  have hx_mem (n : ℕ) : xseq n ∈ Ioo (0 : ℝ) (1 / 2) := by
    have hn : (5 : ℝ) ≤ n + 5 := by linarith [n.cast_nonneg (α := ℝ)]
    have hinv : (n + 5 : ℝ)⁻¹ ≤ 1 / 5 := by
      simpa [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 5) hn
    exact ⟨by dsimp [xseq]; positivity, by dsimp [xseq]; linarith⟩
  have hx_ne (n : ℕ) : -((xseq n : ℝ) : ℂ) ≠ -((1 / 4 : ℝ) : ℂ) := by
    intro h
    have hre : xseq n = 1 / 4 := by simpa using congrArg re (neg_inj.1 h)
    have hpos : 0 < (n + 5 : ℝ)⁻¹ := by positivity
    dsimp [xseq] at hre
    linarith
  have htend_real : Tendsto xseq atTop (𝓝 (1 / 4 : ℝ)) := by
    simpa [xseq] using (tendsto_const_nhds (x := (1 / 4 : ℝ))).add
      (tendsto_inv_atTop_zero.comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (5 : ℝ)))))
  have htend : Tendsto (fun n : ℕ => -((xseq n : ℝ) : ℂ)) atTop
      (𝓝[≠] (-((1 / 4 : ℝ) : ℂ))) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_neg.comp continuous_ofReal).continuousAt.tendsto.comp
      htend_real, Eventually.of_forall hx_ne⟩
  exact (Frequently.of_forall fun n => hP (xseq n) (hx_mem n)).mp
    (Eventually.of_forall fun _ h => h) |> htend.frequently

private theorem analyticAt_prod2 {f : ℂ → ℂ × ℂ} (hf : Differentiable ℂ f) (w : ℂ) :
    AnalyticAt ℂ f w :=
  hf.differentiableOn.analyticAt_of_finiteDimensional univ_mem

private theorem analyticAt_prod4 {f : ℂ → ℂ × ℂ × ℂ × ℂ} (hf : Differentiable ℂ f) (w : ℂ) :
    AnalyticAt ℂ f w :=
  hf.differentiableOn.analyticAt_of_finiteDimensional univ_mem

private theorem eulerIntegral_mul_Gamma_eq_mellinBarnesContour {a b c z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : 0 < b.re) (hbc : b.re < c.re) (hz : -z ∈ slitPlane) :
    Gamma a * Gamma b * eulerIntegral a b c z = mellinBarnesContour a b c z := by
  have hb_ne : ∀ k : ℕ, b ≠ -k := fun k hk => by
    have := congrArg re hk; simp only [neg_re, natCast_re] at this
    linarith [k.cast_nonneg (α := ℝ)]
  have hquarter : -(-((1 / 4 : ℝ) : ℂ)) ∈ slitPlane := by
    rw [neg_neg]
    exact ofReal_mem_slitPlane.2 (by norm_num)
  have hstep1 : ∀ {a' z' : ℂ}, 0 < a'.re → -z' ∈ slitPlane →
      Gamma a' * Gamma b * eulerIntegral a' b c z' = mellinBarnesContour a' b c z' := by
    intro a' z' ha' hz'
    have ha'_ne : ∀ k : ℕ, a' ≠ -k := fun k hk => by
      have := congrArg re hk; simp only [neg_re, natCast_re] at this
      linarith [k.cast_nonneg (α := ℝ)]
    have hf : AnalyticOnNhd ℂ (fun w => Gamma a' * Gamma b * eulerIntegral a' b c w)
        {w | -w ∈ slitPlane} := fun w hw =>
      analyticAt_const.mul ((analyticOnNhd_eulerIntegral hb hbc (a', w)
        (by simpa [sub_eq_add_neg] using
          TauCeti.ofReal_add_mem_slitPlane hw zero_le_one)).comp_of_eq
        (analyticAt_prod2 (f := fun x : ℂ => (a', x)) (by fun_prop) w) rfl)
    have hg : AnalyticOnNhd ℂ (fun w => mellinBarnesContour a' b c w)
        {w | -w ∈ slitPlane} := fun w hw =>
      (analyticOnNhd_mellinBarnesContour (a', b, c, w) ⟨ha'_ne, hb_ne, hw⟩).comp_of_eq
        (analyticAt_prod4 (f := fun x : ℂ => (a', b, c, x)) (by fun_prop) w) rfl
    exact hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_neg_mem_slitPlane
      (z₀ := -((1 / 4 : ℝ) : ℂ)) hquarter
      (frequently_nhdsWithin_neg_quarter fun x hx =>
        eulerIntegral_neg_ofReal_eq_mellinBarnesContour ha' hb hbc hx.1) hz'
  have hf2 : AnalyticOnNhd ℂ (fun w => Gamma w * Gamma b * eulerIntegral w b c z)
      {w | ∀ k : ℕ, w ≠ -k} := fun w hw =>
    ((analyticAt_Gamma hw).mul analyticAt_const).mul
      ((analyticOnNhd_eulerIntegral hb hbc (w, z)
        (by simpa [sub_eq_add_neg] using
          TauCeti.ofReal_add_mem_slitPlane hz zero_le_one)).comp_of_eq
        (analyticAt_prod2 (f := fun x : ℂ => (x, z)) (by fun_prop) w) rfl)
  have hg2 : AnalyticOnNhd ℂ (fun w => mellinBarnesContour w b c z)
      {w | ∀ k : ℕ, w ≠ -k} := fun w hw =>
    (analyticOnNhd_mellinBarnesContour (w, b, c, z) ⟨hw, hb_ne, hz⟩).comp_of_eq
      (analyticAt_prod4 (f := fun x : ℂ => (x, b, c, z)) (by fun_prop) w) rfl
  have h1_mem : (1 : ℂ) ∈ {w : ℂ | ∀ k : ℕ, w ≠ -k} := fun k hk => by
    have := congrArg re hk; simp only [one_re, neg_re, natCast_re] at this
    linarith [k.cast_nonneg (α := ℝ)]
  have hev : (fun w => Gamma w * Gamma b * eulerIntegral w b c z) =ᶠ[𝓝 (1 : ℂ)]
      (fun w => mellinBarnesContour w b c z) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by simp : (0 : ℝ) < (1 : ℂ).re)] with w hw
    exact hstep1 hw hz
  exact hf2.eqOn_of_preconnected_of_eventuallyEq hg2 isPreconnected_ne_neg_nat h1_mem hev ha

/-- **Mellin–Barnes continuation of Euler's integral.** For `0 < Re b < Re c`, `a ∉ -ℕ`, and
`-z ∈ slitPlane`, Euler's normalized integral equals `(Γ(a) Γ(b))⁻¹` times the canonical
separating-contour Mellin–Barnes continuation `mellinBarnesContour a b c z`. -/
theorem eulerIntegral_eq_mellinBarnesContour {a b c z : ℂ} (ha : ∀ k : ℕ, a ≠ -k)
    (hb : 0 < b.re) (hbc : b.re < c.re) (hz : -z ∈ slitPlane) :
    eulerIntegral a b c z = (Gamma a * Gamma b)⁻¹ * mellinBarnesContour a b c z := by
  rw [← eulerIntegral_mul_Gamma_eq_mellinBarnesContour ha hb hbc hz,
    inv_mul_cancel_left₀ (mul_ne_zero (Gamma_ne_zero ha) (Gamma_ne_zero_of_re_pos hb))]

/-- **Separating-contour Mellin–Barnes representation of Euler's integral.** For `0 < Re b < Re c`,
`a ∉ -ℕ`, `-z ∈ slitPlane`, and any admissible abscissa `σ < 0` avoiding `-Re a - ℕ` and
`-Re b - ℕ`, Euler's normalized integral equals `(Γ(a) Γ(b))⁻¹` times
`mellinBarnesSeparating a b c z σ`. -/
theorem eulerIntegral_eq_mellinBarnesSeparating {a b c z : ℂ} {σ : ℝ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : 0 < b.re) (hbc : b.re < c.re) (hσ : σ < 0)
    (haσ : ∀ k : ℕ, a.re + σ ≠ -k) (hbσ : ∀ k : ℕ, b.re + σ ≠ -k) (hz : -z ∈ slitPlane) :
    eulerIntegral a b c z = (Gamma a * Gamma b)⁻¹ * mellinBarnesSeparating a b c z σ := by
  rw [eulerIntegral_eq_mellinBarnesContour ha hb hbc hz,
    mellinBarnesContour_eq_mellinBarnesSeparating c hσ haσ hbσ hz]

private theorem multichoose_eq_ascPochhammer_div_factorial (a : ℂ) (n : ℕ) :
    Ring.multichoose a n = (ascPochhammer ℂ n).eval a / (n ! : ℂ) := by
  rw [eq_div_iff (Nat.cast_ne_zero.2 n.factorial_ne_zero), mul_comm, ← nsmul_eq_mul,
    Ring.factorial_nsmul_multichoose_eq_ascPochhammer, Polynomial.ascPochhammer_smeval_eq_eval]

private theorem summable_norm_multichoose_mul_pow (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ‖Ring.multichoose a n‖ * ‖z‖ ^ n := by
  refine (summable_norm_regularizedGaussHGFun a 1 1 hz).congr fun n => ?_
  rw [ascPochhammer_eval_one, add_comm (1 : ℂ) n, Gamma_nat_eq_factorial,
    mul_div_mul_right _ _ (Nat.cast_ne_zero.2 n.factorial_ne_zero),
    ← multichoose_eq_ascPochhammer_div_factorial, norm_mul, norm_pow]

private theorem integral_beta_mul_multichoose_term (a : ℂ) {b c : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) (z : ℂ) (n : ℕ) :
    (Gamma b * Gamma (c - b))⁻¹ *
        (∫ t : ℝ in 0..1, ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
          (Ring.multichoose a n * (z * (t : ℂ)) ^ n)) =
      ((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b /
        (n ! * Gamma (c + n))) * z ^ n := by
  have hint : (∫ t : ℝ in 0..1, ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
        (Ring.multichoose a n * (z * (t : ℂ)) ^ n)) =
      Ring.multichoose a n * z ^ n * (Gamma (b + n) * Gamma (c - b) / Gamma (c + n)) := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← setIntegral_congr_set Ioo_ae_eq_Ioc]
    have hcongr : EqOn (fun t : ℝ => ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
          (Ring.multichoose a n * (z * (t : ℂ)) ^ n))
        (fun t : ℝ => (Ring.multichoose a n * z ^ n) *
          ((t : ℂ) ^ (b + n - 1) * (1 - (t : ℂ)) ^ (c - b - 1))) (Ioo 0 1) := by
      intro t ht
      dsimp only
      rw [mul_pow, ← cpow_natCast (t : ℂ) n]
      have hexp : b + (n : ℂ) - 1 = (b - 1) + (n : ℂ) := by ring
      rw [hexp, cpow_add _ _ (ofReal_ne_zero.2 ht.1.ne')]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioo hcongr, integral_const_mul,
      setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      ← betaIntegral, betaIntegral_eq_Gamma_mul_div (b + n) (c - b)
        (by simp; linarith [n.cast_nonneg (α := ℝ)]) (by simpa using sub_pos.2 hbc)]
    have hc_add : b + (n : ℂ) + (c - b) = c + n := by ring
    rw [hc_add]
  rw [hint, multichoose_eq_ascPochhammer_div_factorial]
  have hb_ne : ∀ k : ℕ, b ≠ -k := fun k hk => by
    have := congrArg re hk; simp only [neg_re, natCast_re] at this
    linarith [k.cast_nonneg (α := ℝ)]
  have hGb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hGcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using sub_pos.2 hbc)
  have hpoch := Gamma_add_nat_div_Gamma_eq (n := n) b hb_ne
  rw [div_eq_iff hGb] at hpoch
  rw [hpoch]
  field_simp [hGb, hGcb, Nat.cast_ne_zero.2 n.factorial_ne_zero]

private theorem eulerIntegral_neg_ofReal_eq_regularizedGaussHGFun {a b c : ℂ} {x : ℝ}
    (hb : 0 < b.re) (hbc : b.re < c.re) (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    eulerIntegral a b c (-(x : ℂ)) = regularizedGaussHGFun a b c (-(x : ℂ)) := by
  let z : ℂ := -(x : ℂ)
  have hz_norm : ‖z‖ < 1 := by
    simp only [z, norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos hx.1]
    linarith [hx.2]
  have hcb' : 0 < (c - b).re := by simpa using sub_pos.2 hbc
  let F : ℕ → ℝ → ℂ := fun n t =>
    ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) * (Ring.multichoose a n * (z * (t : ℂ)) ^ n)
  let bound : ℕ → ℝ → ℝ := fun n t =>
    ‖(t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)‖ * (‖Ring.multichoose a n‖ * ‖z‖ ^ n)
  have hF_meas (n : ℕ) : AEStronglyMeasurable (F n) (volume.restrict (uIoc (0 : ℝ) 1)) :=
    (intervalIntegrable_iff.1 ((betaIntegral_convergent hb hcb').mul_continuousOn
      (g := fun t : ℝ => Ring.multichoose a n * (z * (t : ℂ)) ^ n)
      (by fun_prop))).aestronglyMeasurable
  have h_bound (n : ℕ) : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) 1 → ‖F n t‖ ≤ bound n t := by
    refine Eventually.of_forall fun t ht => ?_
    rw [uIoc_of_le zero_le_one] at ht
    have ht_norm : ‖(t : ℂ)‖ ≤ 1 := by
      simpa [Real.norm_eq_abs, abs_of_pos ht.1] using ht.2
    dsimp [F, bound]
    rw [norm_mul ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)),
      norm_mul (Ring.multichoose a n), norm_pow, norm_mul z]
    gcongr
    exact mul_le_of_le_one_right (norm_nonneg z) ht_norm
  have hsum_mc : Summable fun n : ℕ => ‖Ring.multichoose a n‖ * ‖z‖ ^ n :=
    summable_norm_multichoose_mul_pow a hz_norm
  have h_lim : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) 1 → HasSum (fun n => F n t)
      ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * (t : ℂ)) ^ (-a)) := by
    refine Eventually.of_forall fun t ht => ?_
    rw [uIoc_of_le zero_le_one] at ht
    have hzt : ‖z * (t : ℂ)‖ < 1 := by
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      exact (mul_le_of_le_one_right (norm_nonneg z) ht.2).trans_lt hz_norm
    simpa [F, one_div, ← cpow_neg] using
      (TauCeti.hasSum_multichoose_mul_geometric_complex_of_norm_lt_one (r := a) hzt).mul_left _
  have hint_sum := intervalIntegral.hasSum_integral_of_dominated_convergence bound hF_meas h_bound
    (Eventually.of_forall fun _ _ => hsum_mc.mul_left _)
    (by simpa only [bound, tsum_mul_left] using (betaIntegral_convergent hb hcb').norm.mul_const _)
    h_lim
  have hnorm_sum := (hint_sum.mul_left (Gamma b * Gamma (c - b))⁻¹).congr_fun
    fun n => (integral_beta_mul_multichoose_term a hb hbc z n).symm
  rw [eulerIntegral_def]
  exact hnorm_sum.unique (hasSum_regularizedGaussHGFun a b c hz_norm)

private theorem regularizedGaussHGFun_mul_Gamma_eq_of_re_pos {a b c z : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hz_norm : ‖z‖ < 1) (hz_slit : -z ∈ slitPlane) :
    Gamma a * Gamma b * regularizedGaussHGFun a b c z = mellinBarnesContour a b c z := by
  have ha_ne : ∀ k : ℕ, a ≠ -k := fun k hk => by
    have := congrArg re hk; simp only [neg_re, natCast_re] at this
    linarith [k.cast_nonneg (α := ℝ)]
  have hb_ne : ∀ k : ℕ, b ≠ -k := fun k hk => by
    have := congrArg re hk; simp only [neg_re, natCast_re] at this
    linarith [k.cast_nonneg (α := ℝ)]
  have hquarter : -((1 / 4 : ℝ) : ℂ) ∈ {w : ℂ | ‖w‖ < 1 ∧ -w ∈ slitPlane} := by
    refine ⟨by simp; norm_num, ?_⟩
    rw [neg_neg]
    exact ofReal_mem_slitPlane.2 (by norm_num)
  have hstep_z : ∀ {c' : ℂ}, b.re < c'.re →
      Gamma a * Gamma b * regularizedGaussHGFun a b c' z = mellinBarnesContour a b c' z := by
    intro c' hbc'
    let V : Set ℂ := {w | ‖w‖ < 1 ∧ -w ∈ slitPlane}
    have hf : AnalyticOnNhd ℂ (fun w => Gamma a * Gamma b * regularizedGaussHGFun a b c' w) V :=
      fun w hw => analyticAt_const.mul
        ((analyticOnNhd_regularizedGaussHGFun (a, b, c', w) hw.1).comp_of_eq
          (analyticAt_prod4 (f := fun x : ℂ => (a, b, c', x)) (by fun_prop) w) rfl)
    have hg : AnalyticOnNhd ℂ (fun w => mellinBarnesContour a b c' w) V := fun w hw =>
      (analyticOnNhd_mellinBarnesContour (a, b, c', w) ⟨ha_ne, hb_ne, hw.2⟩).comp_of_eq
        (analyticAt_prod4 (f := fun x : ℂ => (a, b, c', x)) (by fun_prop) w) rfl
    exact hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_ball_inter_neg_mem_slitPlane
      (z₀ := -((1 / 4 : ℝ) : ℂ)) hquarter
      (frequently_nhdsWithin_neg_quarter fun x hx => by
        rw [← eulerIntegral_neg_ofReal_eq_regularizedGaussHGFun hb hbc' hx,
          eulerIntegral_neg_ofReal_eq_mellinBarnesContour ha hb hbc' hx.1])
      ⟨hz_norm, hz_slit⟩
  have hfc : AnalyticOnNhd ℂ (fun w => Gamma a * Gamma b * regularizedGaussHGFun a b w z) univ :=
    fun w _ => analyticAt_const.mul
      ((analyticOnNhd_regularizedGaussHGFun (a, b, w, z) hz_norm).comp_of_eq
        (analyticAt_prod4 (f := fun x : ℂ => (a, b, x, z)) (by fun_prop) w) rfl)
  have hgc : AnalyticOnNhd ℂ (fun w => mellinBarnesContour a b w z) univ := fun w _ =>
    (analyticOnNhd_mellinBarnesContour (a, b, w, z) ⟨ha_ne, hb_ne, hz_slit⟩).comp_of_eq
      (analyticAt_prod4 (f := fun x : ℂ => (a, b, x, z)) (by fun_prop) w) rfl
  have hevc : (fun w => Gamma a * Gamma b * regularizedGaussHGFun a b w z) =ᶠ[𝓝 (b + 1)]
      (fun w => mellinBarnesContour a b w z) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by simp : b.re < (b + 1).re)] with w hw
    exact hstep_z hw
  exact congrFun (hfc.eq_of_eventuallyEq hgc hevc) c

private theorem regularizedGaussHGFun_mul_Gamma_eq_mellinBarnesContour {a b : ℂ} (c : ℂ) {z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) (hz_norm : ‖z‖ < 1)
    (hz_slit : -z ∈ slitPlane) :
    Gamma a * Gamma b * regularizedGaussHGFun a b c z = mellinBarnesContour a b c z := by
  have h1_mem : (1 : ℂ) ∈ {w : ℂ | ∀ k : ℕ, w ≠ -k} := fun k hk => by
    have := congrArg re hk; simp only [one_re, neg_re, natCast_re] at this
    linarith [k.cast_nonneg (α := ℝ)]
  have hstep_a : ∀ {b' : ℂ}, 0 < b'.re →
      Gamma a * Gamma b' * regularizedGaussHGFun a b' c z = mellinBarnesContour a b' c z := by
    intro b' hb'
    have hb'_ne : ∀ k : ℕ, b' ≠ -k := fun k hk => by
      have := congrArg re hk; simp only [neg_re, natCast_re] at this
      linarith [k.cast_nonneg (α := ℝ)]
    have hfa : AnalyticOnNhd ℂ (fun w => Gamma w * Gamma b' * regularizedGaussHGFun w b' c z)
        {w | ∀ k : ℕ, w ≠ -k} := fun w hw =>
      ((analyticAt_Gamma hw).mul analyticAt_const).mul
        ((analyticOnNhd_regularizedGaussHGFun (w, b', c, z) hz_norm).comp_of_eq
          (analyticAt_prod4 (f := fun x : ℂ => (x, b', c, z)) (by fun_prop) w) rfl)
    have hga : AnalyticOnNhd ℂ (fun w => mellinBarnesContour w b' c z)
        {w | ∀ k : ℕ, w ≠ -k} := fun w hw =>
      (analyticOnNhd_mellinBarnesContour (w, b', c, z) ⟨hw, hb'_ne, hz_slit⟩).comp_of_eq
        (analyticAt_prod4 (f := fun x : ℂ => (x, b', c, z)) (by fun_prop) w) rfl
    have heva : (fun w => Gamma w * Gamma b' * regularizedGaussHGFun w b' c z) =ᶠ[𝓝 (1 : ℂ)]
        (fun w => mellinBarnesContour w b' c z) := by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
        (by simp : (0 : ℝ) < (1 : ℂ).re)] with w hw
      exact regularizedGaussHGFun_mul_Gamma_eq_of_re_pos hw hb' hz_norm hz_slit
    exact hfa.eqOn_of_preconnected_of_eventuallyEq hga isPreconnected_ne_neg_nat h1_mem heva ha
  have hfb : AnalyticOnNhd ℂ (fun w => Gamma a * Gamma w * regularizedGaussHGFun a w c z)
      {w | ∀ k : ℕ, w ≠ -k} := fun w hw =>
    (analyticAt_const.mul (analyticAt_Gamma hw)).mul
      ((analyticOnNhd_regularizedGaussHGFun (a, w, c, z) hz_norm).comp_of_eq
        (analyticAt_prod4 (f := fun x : ℂ => (a, x, c, z)) (by fun_prop) w) rfl)
  have hgb : AnalyticOnNhd ℂ (fun w => mellinBarnesContour a w c z)
      {w | ∀ k : ℕ, w ≠ -k} := fun w hw =>
    (analyticOnNhd_mellinBarnesContour (a, w, c, z) ⟨ha, hw, hz_slit⟩).comp_of_eq
      (analyticAt_prod4 (f := fun x : ℂ => (a, x, c, z)) (by fun_prop) w) rfl
  have hevb : (fun w => Gamma a * Gamma w * regularizedGaussHGFun a w c z) =ᶠ[𝓝 (1 : ℂ)]
      (fun w => mellinBarnesContour a w c z) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by simp : (0 : ℝ) < (1 : ℂ).re)] with w hw
    exact hstep_a hw
  exact hfb.eqOn_of_preconnected_of_eventuallyEq hgb isPreconnected_ne_neg_nat h1_mem hevb hb

/-- **Mellin–Barnes representation of the regularized Gauss hypergeometric function (DLMF 15.6.6)**
via the canonical separating-contour continuation, valid for all `a, b ∉ -ℕ`, arbitrary `c : ℂ`,
`‖z‖ < 1`, and `-z ∈ slitPlane`. -/
theorem regularizedGaussHGFun_eq_mellinBarnesContour {a b : ℂ} (c : ℂ) {z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) (hz_norm : ‖z‖ < 1)
    (hz_slit : -z ∈ slitPlane) :
    regularizedGaussHGFun a b c z = (Gamma a * Gamma b)⁻¹ * mellinBarnesContour a b c z := by
  rw [← regularizedGaussHGFun_mul_Gamma_eq_mellinBarnesContour c ha hb hz_norm hz_slit,
    inv_mul_cancel_left₀ (mul_ne_zero (Gamma_ne_zero ha) (Gamma_ne_zero hb))]

/-- **Separating-contour Mellin–Barnes representation of `regularizedGaussHGFun` (DLMF 15.6.6)**
at any admissible abscissa `σ < 0` avoiding `-Re a - ℕ` and `-Re b - ℕ`, valid for all `a, b ∉ -ℕ`,
arbitrary `c : ℂ`, `‖z‖ < 1`, and `-z ∈ slitPlane`. -/
theorem regularizedGaussHGFun_eq_mellinBarnesSeparating {a b : ℂ} (c : ℂ) {z : ℂ} {σ : ℝ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) (hσ : σ < 0)
    (haσ : ∀ k : ℕ, a.re + σ ≠ -k) (hbσ : ∀ k : ℕ, b.re + σ ≠ -k)
    (hz_norm : ‖z‖ < 1) (hz_slit : -z ∈ slitPlane) :
    regularizedGaussHGFun a b c z = (Gamma a * Gamma b)⁻¹ * mellinBarnesSeparating a b c z σ := by
  rw [regularizedGaussHGFun_eq_mellinBarnesContour c ha hb hz_norm hz_slit,
    mellinBarnesContour_eq_mellinBarnesSeparating c hσ haσ hbσ hz_slit]

/-- **Mellin–Barnes representation of the ordinary Gauss hypergeometric function `₂F₁`**
(DLMF 15.6.6) via the canonical separating-contour continuation, valid for all `a, b, c ∉ -ℕ`,
`‖z‖ < 1`, and `-z ∈ slitPlane`. -/
theorem ordinaryHypergeometric_eq_mellinBarnesContour {a b c z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) (hc : ∀ k : ℕ, c ≠ -k)
    (hz_norm : ‖z‖ < 1) (hz_slit : -z ∈ slitPlane) :
    ordinaryHypergeometric a b c z =
      Gamma c / (Gamma a * Gamma b) * mellinBarnesContour a b c z := by
  have h := ordinaryHypergeometric_div_Gamma_eq (a := a) (b := b) (z := z) hc
  rw [div_eq_iff (Gamma_ne_zero hc),
    regularizedGaussHGFun_eq_mellinBarnesContour c ha hb hz_norm hz_slit] at h
  rw [h, div_eq_mul_inv]
  ring

/-- **Separating-contour Mellin–Barnes representation of `ordinaryHypergeometric` (`₂F₁`)**
(DLMF 15.6.6) at any admissible abscissa `σ < 0` avoiding `-Re a - ℕ` and `-Re b - ℕ`, valid for
all `a, b, c ∉ -ℕ`, `‖z‖ < 1`, and `-z ∈ slitPlane`. -/
theorem ordinaryHypergeometric_eq_mellinBarnesSeparating {a b c z : ℂ} {σ : ℝ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) (hc : ∀ k : ℕ, c ≠ -k) (hσ : σ < 0)
    (haσ : ∀ k : ℕ, a.re + σ ≠ -k) (hbσ : ∀ k : ℕ, b.re + σ ≠ -k)
    (hz_norm : ‖z‖ < 1) (hz_slit : -z ∈ slitPlane) :
    ordinaryHypergeometric a b c z =
      Gamma c / (Gamma a * Gamma b) * mellinBarnesSeparating a b c z σ := by
  rw [ordinaryHypergeometric_eq_mellinBarnesContour ha hb hc hz_norm hz_slit,
    mellinBarnesContour_eq_mellinBarnesSeparating c hσ haσ hbσ hz_slit]

end Complex

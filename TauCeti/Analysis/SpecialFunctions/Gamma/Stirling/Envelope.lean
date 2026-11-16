/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Basic
public import TauCeti.Analysis.SpecialFunctions.Gamma.Real
public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Series

import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import TauCeti.Analysis.Complex.SectorBounds
import TauCeti.NumberTheory.ZetaValues

/-!
# Alzer's complete monotonicity, polygamma brackets, and Stieltjes' sector bound

This file derives the real-axis enveloping properties of Stirling's series and Stieltjes' sharp
slit-plane sector bound from the periodic Bernoulli remainder representation in
`TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Series`.

On the positive real axis `(0, ∞)`, the periodic Bernoulli factor
`(-1)^{n+1} (B_{2n} - B_{2n}({u}))` is nonnegative everywhere and strictly positive on `(0, 1)`.
Consequently every signed real Stirling remainder `(-1)^{n+1} r_n(x)` has strictly alternating
derivatives of all orders, establishing Alzer's complete monotonicity theorem: the functions
`F_m = r_{2m+1}` and `G_m = -r_{2m+2}` are strictly completely monotone on `(0, ∞)`. Specializing
to orders `k = 0`, `k = 1`, and `k ≥ 2` yields:

* the two-sided enveloping brackets for `log Γ(x)` and the strict bound `|r_n(x)| < |T_n(x)|`;
* the arbitrary-order and leading digamma brackets
  `log x - 1/(2x) - 1/(12x²) < ψ(x) < log x - 1/(2x)`;
* Alzer's polygamma brackets `S_k(2n; x) < (-1)^{k+1} ψ^{(k)}(x) < S_k(2n + 1; x)` for all `k ≥ 1`.

Combining the constant-sign remainder integral with the half-angle inequality
`cos (arg z / 2) * (‖z‖ + u) ≤ ‖u + z‖` compares the slit-plane remainder directly to its real-axis
value at `‖z‖`, giving Stieltjes' sharp sector bound
`‖r_n(z)‖ < ‖T_n(z)‖ / cos (arg z / 2) ^ (2 * n)`, its `n = 1` specialization in Ramaré's sector
form `‖r₁(z)‖ < 1 / (12 * sin (δ / 2) ^ 2 * ‖z‖)`, and the sharp `1 / 12` derivative bound for
`r₁^{(k)}(z)`.

## Main declarations

* `TauCeti.contDiffOn_realStirlingRemainder`, `TauCeti.iteratedDeriv_realStirlingRemainder`,
  `TauCeti.realStirlingRemainder_eq_integral`: smoothness and real integral representation of
  `realStirlingRemainder n` and its derivatives on `(0, ∞)`.
* `TauCeti.differentiableOn_digamma_slitPlane`, `TauCeti.contDiffOn_digamma_Ioi`,
  `TauCeti.iteratedDeriv_digamma_ofReal`: holomorphy and real-axis derivative agreement for digamma.
* `TauCeti.isCompletelyMonotoneOnIoi_realStirlingRemainder_odd`,
  `TauCeti.isCompletelyMonotoneOnIoi_neg_realStirlingRemainder_even`: Alzer's complete monotonicity
  of `F_m = r_{2m+1}` and `G_m = -r_{2m+2}` on `(0, ∞)`.
* `TauCeti.sum_stirlingTerm_lt_log_Gamma_sub`, `TauCeti.log_Gamma_sub_lt_sum_stirlingTerm`,
  `TauCeti.stirling_lt_log_Gamma`, `TauCeti.abs_realStirlingRemainder_lt_abs_stirlingTerm`:
  enveloping inequalities for `Real.log (Real.Gamma x)`.
* `TauCeti.digamma_lt_log_sub_inv_two_mul`, `TauCeti.log_sub_inv_two_mul_sub_lt_digamma`,
  `TauCeti.digamma_lt_log_sub_inv_two_mul_sub_sum`,
  `TauCeti.log_sub_inv_two_mul_sub_sum_lt_digamma`: digamma brackets on `(0, ∞)`.
* `TauCeti.polygammaStirlingSum`,
  `TauCeti.polygammaStirlingSum_lt_neg_one_pow_mul_iteratedDeriv_digamma`,
  `TauCeti.neg_one_pow_mul_iteratedDeriv_digamma_lt_polygammaStirlingSum`: Alzer's polygamma
  brackets on `(0, ∞)`.
* `TauCeti.norm_stirlingRemainder_lt`, `TauCeti.norm_stirlingRemainder_one_lt`,
  `TauCeti.norm_iteratedDeriv_stirlingRemainder_one_lt`,
  `TauCeti.norm_stirlingRemainder_lt_of_abs_arg_le`,
  `TauCeti.norm_stirlingRemainder_one_lt_of_abs_arg_le`,
  `TauCeti.Gamma_eq_sqrt_two_pi_mul_exp`: Stieltjes' sector bound and Ramaré's exponential form.

## References

* H. Alzer, *On some inequalities for the gamma and psi functions*, Math. Comp. 66 (1997),
  373–389, Theorems 8 and 9.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §4, eq. (8.4.06).
* O. Ramaré, *Excursions in Multiplicative Number Theory*, §20.2.
* T. J. Stieltjes, *Sur le développement de `log Γ(a)`*, J. Math. Pures Appl. (4) 5 (1889),
  425–444.
-/

public section

open Complex Real Filter Set Topology MeasureTheory
open scoped ContDiff Nat

namespace TauCeti

/-! ### Real-axis derivatives of slit-plane holomorphic functions -/

/-- A function holomorphic on the slit plane that is real-valued on `(0, ∞)` restricts to a `C^∞`
real function on `(0, ∞)`. -/
private theorem contDiffOn_ofReal_of_differentiableOn_slitPlane {f : ℂ → ℂ} {g : ℝ → ℝ}
    (hf : DifferentiableOn ℂ f slitPlane) (hfg : ∀ x : ℝ, 0 < x → f (x : ℂ) = (g x : ℂ)) :
    ContDiffOn ℝ ∞ g (Ioi 0) := by
  have hf_cd : ContDiffOn ℝ ∞ f slitPlane :=
    (hf.contDiffOn (n := ∞) isOpen_slitPlane).restrict_scalars ℝ
  have hcomp : ContDiffOn ℝ ∞ (fun x : ℝ ↦ Complex.reCLM (f (Complex.ofRealCLM x))) (Ioi 0) :=
    Complex.reCLM.contDiff.contDiffOn.comp
      (hf_cd.comp Complex.ofRealCLM.contDiff.contDiffOn
        fun x hx ↦ Complex.ofReal_mem_slitPlane.mpr hx)
      (mapsTo_univ _ _)
  exact hcomp.congr fun x hx ↦ by
    simp only [Complex.reCLM_apply, Complex.ofRealCLM_apply, hfg x hx, Complex.ofReal_re]

/-- If `f : ℂ → ℂ` is holomorphic on the slit plane and agrees with `(g · : ℂ)` on `(0, ∞)`, then
every complex iterated derivative of `f` on `(0, ∞)` is the coercion of the real iterated
derivative of `g`. -/
private theorem iteratedDeriv_ofReal_of_differentiableOn_slitPlane {f : ℂ → ℂ} {g : ℝ → ℝ}
    (hf : DifferentiableOn ℂ f slitPlane) (hfg : ∀ x : ℝ, 0 < x → f (x : ℂ) = (g x : ℂ))
    (k : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k f (x : ℂ) = ((iteratedDeriv k g x : ℝ) : ℂ) := by
  have hdiff : ∀ m : ℕ, DifferentiableOn ℂ (iteratedDeriv m f) slitPlane := by
    intro m
    induction m with
    | zero => simpa only [iteratedDeriv_zero] using hf
    | succ m ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv isOpen_slitPlane
  induction k generalizing x with
  | zero => simpa only [iteratedDeriv_zero] using hfg x hx
  | succ k ih =>
    have hfk : HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f (x : ℂ)) (x : ℂ) := by
      rw [iteratedDeriv_succ]
      exact ((hdiff k).differentiableAt
        (isOpen_slitPlane.mem_nhds (Complex.ofReal_mem_slitPlane.mpr hx))).hasDerivAt
    have hcomp : HasDerivAt (fun t : ℝ ↦ ((iteratedDeriv k g t : ℝ) : ℂ))
        (iteratedDeriv (k + 1) f (x : ℂ)) x := by
      refine hfk.comp_ofReal.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
      exact (ih ht).symm
    have hre : HasDerivAt (iteratedDeriv k g) (iteratedDeriv (k + 1) f (x : ℂ)).re x := by
      simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hcomp
    have him : HasDerivAt (fun _ : ℝ ↦ (0 : ℝ)) (iteratedDeriv (k + 1) f (x : ℂ)).im x := by
      simpa only [Function.comp_def, Complex.imCLM_apply, Complex.ofReal_im] using
        Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hcomp
    have hre_eq : iteratedDeriv (k + 1) g x = (iteratedDeriv (k + 1) f (x : ℂ)).re := by
      rw [iteratedDeriv_succ, hre.deriv]
    have him_eq : (iteratedDeriv (k + 1) f (x : ℂ)).im = 0 :=
      him.unique (hasDerivAt_const x (0 : ℝ))
    exact Complex.ext (by simp [hre_eq]) (by simp [him_eq])

/-- Every real Stirling remainder `realStirlingRemainder n` is `C^∞` on `(0, ∞)`. -/
theorem contDiffOn_realStirlingRemainder (n : ℕ) :
    ContDiffOn ℝ ∞ (realStirlingRemainder n) (Ioi 0) :=
  contDiffOn_ofReal_of_differentiableOn_slitPlane (differentiableOn_stirlingRemainder n)
    (fun _ hx ↦ stirlingRemainder_ofReal n hx)

/-- On `(0, ∞)`, every complex iterated derivative of `stirlingRemainder n` is the coercion of the
corresponding real iterated derivative of `realStirlingRemainder n`. -/
@[simp]
theorem iteratedDeriv_stirlingRemainder_ofReal (n k : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k (stirlingRemainder n) (x : ℂ) =
      ((iteratedDeriv k (realStirlingRemainder n) x : ℝ) : ℂ) :=
  iteratedDeriv_ofReal_of_differentiableOn_slitPlane (differentiableOn_stirlingRemainder n)
    (fun _ ht ↦ stirlingRemainder_ofReal n ht) k hx

/-- Complex digamma is holomorphic on the slit plane. -/
theorem differentiableOn_digamma_slitPlane : DifferentiableOn ℂ Complex.digamma slitPlane :=
  (differentiableOn_logGamma.deriv isOpen_slitPlane).congr fun _ hz ↦ (deriv_logGamma hz).symm

/-- Real digamma is `C^∞` on `(0, ∞)`. -/
theorem contDiffOn_digamma_Ioi : ContDiffOn ℝ ∞ Real.digamma (Ioi 0) :=
  contDiffOn_ofReal_of_differentiableOn_slitPlane differentiableOn_digamma_slitPlane
    (fun _ _ ↦ Complex.digamma_ofReal)

/-- On `(0, ∞)`, every complex iterated derivative of `Complex.digamma` is the coercion of the
corresponding real iterated derivative of `Real.digamma`. -/
@[simp]
theorem iteratedDeriv_digamma_ofReal (k : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k Complex.digamma (x : ℂ) = ((iteratedDeriv k Real.digamma x : ℝ) : ℂ) :=
  iteratedDeriv_ofReal_of_differentiableOn_slitPlane differentiableOn_digamma_slitPlane
    (fun _ _ ↦ Complex.digamma_ofReal) k hx

/-- Exact real integral representation for every iterated derivative of `realStirlingRemainder n`
on `(0, ∞)`: for `n ≥ 1`, `k : ℕ`, and `x > 0`,
`r_n^{(k)}(x) = (-1)^k ((2n + k - 1)! / (2n)!) ∫₀^∞ (B_{2n} - B_{2n}({u})) / (u + x)^{2n + k} du`.
-/
theorem iteratedDeriv_realStirlingRemainder {n : ℕ} (hn : 1 ≤ n) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k (realStirlingRemainder n) x =
      (-1 : ℝ) ^ k * (((2 * n + k - 1)! : ℝ) / ((2 * n)! : ℝ)) *
        ∫ u in Ioi (0 : ℝ),
          ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
            (u + x) ^ (2 * n + k) := by
  apply Complex.ofReal_injective
  rw [← iteratedDeriv_stirlingRemainder_ofReal n k hx,
    iteratedDeriv_stirlingRemainder hn k (Complex.ofReal_mem_slitPlane.mpr hx)]
  have hint :
      ∫ u in Ioi (0 : ℝ),
        (((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u) : ℝ) : ℂ) /
          ((u : ℂ) + (x : ℂ)) ^ (2 * n + k) =
      ((∫ u in Ioi (0 : ℝ),
        ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
          (u + x) ^ (2 * n + k) : ℝ) : ℂ) := by
    refine Eq.trans ?_ (integral_ofReal (𝕜 := ℂ))
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
    push_cast
    rfl
  rw [hint]
  push_cast
  rfl

/-- Exact real integral representation of `realStirlingRemainder n` on `(0, ∞)` for `n ≥ 1`. -/
theorem realStirlingRemainder_eq_integral {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    realStirlingRemainder n x =
      ∫ u in Ioi (0 : ℝ),
        ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
          ((2 * n : ℝ) * (u + x) ^ (2 * n)) := by
  have h0 := iteratedDeriv_realStirlingRemainder hn 0 hx
  rw [iteratedDeriv_zero, pow_zero, one_mul, add_zero, ← integral_const_mul] at h0
  rw [h0]
  have hfac : ((2 * n)! : ℝ) = (2 * n : ℝ) * ((2 * n - 1)! : ℝ) := by
    have h1 : 2 * n = (2 * n - 1) + 1 := by omega
    have hnat : (2 * n)! = (2 * n) * (2 * n - 1)! := by
      calc (2 * n)! = ((2 * n - 1) + 1)! := by rw [← h1]
        _ = (2 * n) * (2 * n - 1)! := by rw [Nat.factorial_succ, ← h1]
    exact_mod_cast hnat
  have hne : ((2 * n - 1)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
  rw [hfac]
  field_simp

/-! ### Alzer's complete monotonicity and enveloping theorem on `(0, ∞)` -/

private theorem integrableOn_signed_bernoulli_sub_div_pow_Ioi (n : ℕ) {k : ℕ} (hk : 2 ≤ k)
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ ↦
      (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
        (u + x) ^ k) (Ioi 0) := by
  have hk' : -(k : ℝ) < -1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hpow : IntegrableOn (fun u : ℝ ↦ 1 / (u + x) ^ k) (Ioi 0) :=
    (integrableOn_add_rpow_Ioi_of_lt hk' (by linarith : -x < 0)).congr_fun
      (fun u hu ↦ by
        have hpos : 0 ≤ u + x := by linarith [mem_Ioi.mp hu]
        dsimp only
        rw [Real.rpow_neg hpos, Real.rpow_natCast, one_div])
      measurableSet_Ioi
  have hmeas : AEStronglyMeasurable (fun u : ℝ ↦
      (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)))
      (volume.restrict (Ioi 0)) :=
    (measurable_const.mul
      (measurable_const.sub ((continuous_bernoulliFun (2 * n)).measurable.comp measurable_fract)))
      |>.aestronglyMeasurable
  have hmul := hpow.bdd_mul hmeas
    (c := 2 * |(bernoulli (2 * n) : ℝ)|)
    (Eventually.of_forall fun u ↦ by
      have hle := abs_bernoulliFun_even_fract_le n u
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      calc |(bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)|
          ≤ |(bernoulli (2 * n) : ℝ)| + |bernoulliFun (2 * n) (Int.fract u)| := abs_sub _ _
        _ ≤ 2 * |(bernoulli (2 * n) : ℝ)| := by linarith)
  exact hmul.congr (Eventually.of_forall fun u ↦ by ring)

private theorem integral_signed_bernoulli_sub_div_pow_pos {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    {x : ℝ} (hx : 0 < x) :
    0 < ∫ u in Ioi (0 : ℝ),
      (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
        (u + x) ^ k := by
  let f : ℝ → ℝ := fun u ↦
    (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
      (u + x) ^ k
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := mem_Ioi.mp hu
    exact div_nonneg (neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_fract_nonneg n u)
      (by positivity)
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn
    (integrableOn_signed_bernoulli_sub_div_pow_Ioi n hk hx)]
  have hsub : Ioo (0 : ℝ) 1 ⊆ Function.support f ∩ Ioi (0 : ℝ) := by
    intro u hu
    refine ⟨?_, hu.1⟩
    have hfr : Int.fract u = u := Int.fract_eq_self.mpr ⟨hu.1.le, hu.2⟩
    have hnum : 0 < (-1 : ℝ) ^ (n + 1) *
        ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) := by
      rw [hfr]
      exact neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_pos (by omega : n ≠ 0) hu
    have hu0 : 0 < u := hu.1
    exact (div_pos hnum (by positivity)).ne'
  have hvol : (0 : ENNReal) < volume (Ioo (0 : ℝ) 1) := by
    rw [Real.volume_Ioo]
    norm_num
  exact lt_of_lt_of_le hvol (measure_mono hsub)

/-- For every `n ≥ 1`, `k : ℕ`, and `x > 0`, the signed real Stirling remainder
`t ↦ (-1)^{n+1} r_n(t)` has strictly alternating `k`-th derivative:
`0 < (-1)^k * ((-1)^{n+1} r_n)^{(k)}(x)`. -/
theorem neg_one_pow_mul_iteratedDeriv_signed_realStirlingRemainder_pos {n : ℕ} (hn : 1 ≤ n)
    (k : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < (-1 : ℝ) ^ k *
      iteratedDeriv k (fun t ↦ (-1 : ℝ) ^ (n + 1) * realStirlingRemainder n t) x := by
  have hsmul : iteratedDeriv k (fun t ↦ (-1 : ℝ) ^ (n + 1) * realStirlingRemainder n t) x =
      (-1 : ℝ) ^ (n + 1) * iteratedDeriv k (realStirlingRemainder n) x :=
    iteratedDeriv_const_mul_field ((-1 : ℝ) ^ (n + 1)) (realStirlingRemainder n)
  rw [hsmul, iteratedDeriv_realStirlingRemainder hn k hx]
  have hsq : (-1 : ℝ) ^ k * ((-1 : ℝ) ^ (n + 1) * ((-1 : ℝ) ^ k *
      (((2 * n + k - 1)! : ℝ) / ((2 * n)! : ℝ)) *
        ∫ u in Ioi (0 : ℝ),
          ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
            (u + x) ^ (2 * n + k))) =
      (((2 * n + k - 1)! : ℝ) / ((2 * n)! : ℝ)) *
        ∫ u in Ioi (0 : ℝ),
          (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
            (u + x) ^ (2 * n + k) := by
    have hk2 : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
      rw [← mul_pow, mul_neg_one, neg_neg, one_pow]
    have hint_mul :
        (-1 : ℝ) ^ (n + 1) *
          ∫ u in Ioi (0 : ℝ),
            ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
              (u + x) ^ (2 * n + k) =
        ∫ u in Ioi (0 : ℝ),
          (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
            (u + x) ^ (2 * n + k) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
      ring
    rw [← hint_mul]
    linear_combination ((((2 * n + k - 1)! : ℝ) / ((2 * n)! : ℝ)) * (-1 : ℝ) ^ (n + 1) *
      ∫ u in Ioi (0 : ℝ),
        ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
          (u + x) ^ (2 * n + k)) * hk2
  rw [hsq]
  exact mul_pos (by positivity)
    (integral_signed_bernoulli_sub_div_pow_pos hn (by omega : 2 ≤ 2 * n + k) hx)

/-- **Alzer's theorem (odd remainders)**: for every `m, k : ℕ` and `x > 0`,
`0 < (-1)^k * r_{2m+1}^{(k)}(x)`. -/
theorem neg_one_pow_mul_iteratedDeriv_realStirlingRemainder_odd_pos (m k : ℕ) {x : ℝ}
    (hx : 0 < x) :
    0 < (-1 : ℝ) ^ k * iteratedDeriv k (realStirlingRemainder (2 * m + 1)) x := by
  have h := neg_one_pow_mul_iteratedDeriv_signed_realStirlingRemainder_pos
    (n := 2 * m + 1) (by omega) k hx
  have hpow : (-1 : ℝ) ^ (2 * m + 1 + 1) = 1 := by
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, pow_mul, neg_one_sq, one_pow]
  simpa only [hpow, one_mul] using h

/-- **Alzer's theorem (negated even remainders)**: for every `m, k : ℕ` and `x > 0`,
`0 < (-1)^k * (-r_{2m+2})^{(k)}(x)`. -/
theorem neg_one_pow_mul_iteratedDeriv_neg_realStirlingRemainder_even_pos (m k : ℕ) {x : ℝ}
    (hx : 0 < x) :
    0 < (-1 : ℝ) ^ k * iteratedDeriv k (fun t ↦ -realStirlingRemainder (2 * m + 2) t) x := by
  have h := neg_one_pow_mul_iteratedDeriv_signed_realStirlingRemainder_pos
    (n := 2 * m + 2) (by omega) k hx
  have hpow : (-1 : ℝ) ^ (2 * m + 2 + 1) = -1 := by
    have : Odd (2 * m + 2 + 1) := ⟨m + 1, by omega⟩
    exact this.neg_one_pow
  simpa only [hpow, neg_one_mul] using h

/-- For every `m : ℕ`, the odd-order real Stirling remainder `F_m = realStirlingRemainder (2m + 1)`
is completely monotone on `(0, ∞)` (Alzer 1997, Theorem 8). -/
theorem isCompletelyMonotoneOnIoi_realStirlingRemainder_odd (m : ℕ) :
    IsCompletelyMonotoneOnIoi (realStirlingRemainder (2 * m + 1)) :=
  ⟨contDiffOn_realStirlingRemainder (2 * m + 1),
    fun k _ hx ↦ (neg_one_pow_mul_iteratedDeriv_realStirlingRemainder_odd_pos m k hx).le⟩

/-- For every `m : ℕ`, the negated even-order real Stirling remainder
`G_m = -realStirlingRemainder (2m + 2)` is completely monotone on `(0, ∞)`
(Alzer 1997, Theorem 8). -/
theorem isCompletelyMonotoneOnIoi_neg_realStirlingRemainder_even (m : ℕ) :
    IsCompletelyMonotoneOnIoi (fun t ↦ -realStirlingRemainder (2 * m + 2) t) :=
  ⟨(contDiffOn_realStirlingRemainder (2 * m + 2)).neg,
    fun k _ hx ↦ (neg_one_pow_mul_iteratedDeriv_neg_realStirlingRemainder_even_pos m k hx).le⟩

/-- For `n ≥ 1` and `x > 0`, `realStirlingRemainder n x` has strict sign `(-1)^{n+1}`. -/
theorem neg_one_pow_succ_mul_realStirlingRemainder_pos {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    0 < (-1 : ℝ) ^ (n + 1) * realStirlingRemainder n x := by
  simpa only [pow_zero, one_mul, iteratedDeriv_zero] using
    neg_one_pow_mul_iteratedDeriv_signed_realStirlingRemainder_pos hn 0 hx

/-- Even-length partial sums of Stirling's series strictly underestimate `log Γ(x)` minus the
leading Stirling terms for every `m : ℕ` and `x > 0`. -/
theorem sum_stirlingTerm_lt_log_Gamma_sub (m : ℕ) {x : ℝ} (hx : 0 < x) :
    ∑ i ∈ Finset.Icc 1 (2 * m), stirlingTerm i x <
      Real.log (Real.Gamma x) - ((x - 1 / 2) * Real.log x - x + Real.log (2 * π) / 2) := by
  have h := neg_one_pow_mul_iteratedDeriv_realStirlingRemainder_odd_pos m 0 hx
  simp only [pow_zero, one_mul, iteratedDeriv_zero, realStirlingRemainder,
    Finset.Ico_add_one_right_eq_Icc] at h
  linarith

/-- Odd-length partial sums of Stirling's series strictly overestimate `log Γ(x)` minus the
leading Stirling terms for every `m : ℕ` and `x > 0`. -/
theorem log_Gamma_sub_lt_sum_stirlingTerm (m : ℕ) {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) - ((x - 1 / 2) * Real.log x - x + Real.log (2 * π) / 2) <
      ∑ i ∈ Finset.Icc 1 (2 * m + 1), stirlingTerm i x := by
  have h := neg_one_pow_mul_iteratedDeriv_neg_realStirlingRemainder_even_pos m 0 hx
  simp only [pow_zero, one_mul, iteratedDeriv_zero, realStirlingRemainder,
    show 2 * m + 2 = (2 * m + 1) + 1 by omega, Finset.Ico_add_one_right_eq_Icc] at h
  linarith

/-- Leading Stirling lower bound on the positive real axis: for all `x > 0`,
`(x - 1/2) log x - x + log (2π) / 2 < log (Γ x)`. -/
theorem stirling_lt_log_Gamma {x : ℝ} (hx : 0 < x) :
    (x - 1 / 2) * Real.log x - x + Real.log (2 * π) / 2 < Real.log (Real.Gamma x) := by
  have h := sum_stirlingTerm_lt_log_Gamma_sub 0 hx
  simp only [Nat.mul_zero, Finset.Icc_eq_empty (by omega : ¬1 ≤ 0), Finset.sum_empty] at h
  linarith

/-- Enveloping bound on `(0, ∞)`: for every `n ≥ 1` and `x > 0`, the Stirling remainder is strictly
smaller in absolute value than the first omitted term: `|r_n(x)| < |T_n(x)|`. -/
theorem abs_realStirlingRemainder_lt_abs_stirlingTerm {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    |realStirlingRemainder n x| < |stirlingTerm n x| := by
  have h1 := neg_one_pow_succ_mul_realStirlingRemainder_pos hn hx
  have h2 := neg_one_pow_succ_mul_realStirlingRemainder_pos (n := n + 1) (by omega) hx
  rw [realStirlingRemainder_succ, pow_succ] at h2
  have hlt : (-1 : ℝ) ^ (n + 1) * realStirlingRemainder n x <
      (-1 : ℝ) ^ (n + 1) * stirlingTerm n x := by linarith
  have hT_pos : 0 < (-1 : ℝ) ^ (n + 1) * stirlingTerm n x := lt_trans h1 hlt
  have habs_r : |realStirlingRemainder n x| = (-1 : ℝ) ^ (n + 1) * realStirlingRemainder n x := by
    rw [← abs_of_pos h1, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have habs_T : |stirlingTerm n x| = (-1 : ℝ) ^ (n + 1) * stirlingTerm n x := by
    rw [← abs_of_pos hT_pos, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [habs_r, habs_T]
  exact hlt

/-! ### Digamma brackets on `(0, ∞)` -/

/-- First derivative of `realStirlingRemainder n` on `(0, ∞)`:
`r_n'(x) = ψ(x) - log x + 1 / (2x) + ∑_{j=1}^{n-1} B_{2j} / (2j x^{2j})`. -/
theorem deriv_realStirlingRemainder (n : ℕ) {x : ℝ} (hx : 0 < x) :
    deriv (realStirlingRemainder n) x =
      Real.digamma x - Real.log x + 1 / (2 * x) +
        ∑ j ∈ Finset.Ico 1 n, (bernoulli (2 * j) : ℝ) / ((2 * j : ℝ) * x ^ (2 * j)) := by
  have hlogG : HasDerivAt (fun t ↦ Real.log (Real.Gamma t)) (Real.digamma x) x :=
    Real.hasDerivAt_log_Gamma fun m ↦ by linarith
  have hmain : HasDerivAt
      (fun t ↦ (t - 1 / 2) * Real.log t - t + Real.log (2 * π) / 2)
      (Real.log x - 1 / (2 * x)) x := by
    have h1 : HasDerivAt (fun t : ℝ ↦ (t - 1 / 2) * Real.log t)
        (1 * Real.log x + (x - 1 / 2) * x⁻¹) x :=
      ((hasDerivAt_id x).sub_const (1 / 2 : ℝ)).mul (Real.hasDerivAt_log hx.ne')
    refine ((h1.sub (hasDerivAt_id x)).add_const (Real.log (2 * π) / 2)).congr_deriv ?_
    field_simp
    ring
  have hterm : ∀ j ∈ Finset.Ico 1 n,
      HasDerivAt (fun t : ℝ ↦ stirlingTerm j t)
        (-((bernoulli (2 * j) : ℝ) / ((2 * j : ℝ) * x ^ (2 * j)))) x := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hden_ne : (2 * (j : ℝ)) * (2 * (j : ℝ) - 1) ≠ 0 := by
      have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      have h1 : (0 : ℝ) < 2 * (j : ℝ) := by linarith
      have h2 : (0 : ℝ) < 2 * (j : ℝ) - 1 := by linarith
      exact mul_ne_zero h1.ne' h2.ne'
    have hpow : HasDerivAt (fun t : ℝ ↦ t ^ (2 * j - 1))
        (((2 * j - 1 : ℕ) : ℝ) * x ^ (2 * j - 2)) x := by
      simpa [Nat.sub_sub] using (hasDerivAt_id x).fun_pow (2 * j - 1)
    have hden : HasDerivAt (fun t : ℝ ↦ (2 * (j : ℝ)) * (2 * (j : ℝ) - 1) * t ^ (2 * j - 1))
        ((2 * (j : ℝ)) * (2 * (j : ℝ) - 1) * (((2 * j - 1 : ℕ) : ℝ) * x ^ (2 * j - 2))) x :=
      hpow.const_mul _
    have hinv := (hden.inv (mul_ne_zero hden_ne (pow_ne_zero _ hx.ne'))).const_mul
      (bernoulli (2 * j) : ℝ)
    refine (hinv.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ by
      simp only [stirlingTerm, Pi.inv_apply, div_eq_mul_inv])).congr_deriv ?_
    have hc : ((2 * j - 1 : ℕ) : ℝ) = 2 * (j : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * j)]
      push_cast
      rfl
    have hp1 : x ^ (2 * j - 1) = x ^ (2 * j - 2) * x := by
      rw [← pow_succ]
      congr 1
      omega
    have hp2 : x ^ (2 * j) = x ^ (2 * j - 2) * x ^ 2 := by
      rw [← pow_add]
      congr 1
      omega
    rw [hc, hp1, hp2]
    have hxpow : x ^ (2 * j - 2) ≠ 0 := pow_ne_zero _ hx.ne'
    have h2j1 : 2 * (j : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      linarith
    field_simp
  have hsum : HasDerivAt (fun t : ℝ ↦ ∑ j ∈ Finset.Ico 1 n, stirlingTerm j t)
      (∑ j ∈ Finset.Ico 1 n, -((bernoulli (2 * j) : ℝ) / ((2 * j : ℝ) * x ^ (2 * j)))) x :=
    HasDerivAt.fun_sum hterm
  have htot : HasDerivAt (realStirlingRemainder n)
      (Real.digamma x - (Real.log x - 1 / (2 * x)) -
        ∑ j ∈ Finset.Ico 1 n, -((bernoulli (2 * j) : ℝ) / ((2 * j : ℝ) * x ^ (2 * j)))) x :=
    ((hlogG.sub hmain).sub hsum).congr_of_eventuallyEq
      (Eventually.of_forall fun t ↦ by simp only [realStirlingRemainder, Pi.sub_apply])
  rw [htot.deriv, Finset.sum_neg_distrib]
  ring

/-- Arbitrary-order upper digamma bracket on `(0, ∞)`: for every `m : ℕ` and `x > 0`,
`ψ(x) < log x - 1 / (2x) - ∑_{j=1}^{2m} B_{2j} / (2j x^{2j})`. -/
theorem digamma_lt_log_sub_inv_two_mul_sub_sum (m : ℕ) {x : ℝ} (hx : 0 < x) :
    Real.digamma x <
      Real.log x - 1 / (2 * x) -
        ∑ j ∈ Finset.Icc 1 (2 * m), (bernoulli (2 * j) : ℝ) / ((2 * j : ℝ) * x ^ (2 * j)) := by
  have h := neg_one_pow_mul_iteratedDeriv_realStirlingRemainder_odd_pos m 1 hx
  rw [pow_one, iteratedDeriv_one, deriv_realStirlingRemainder (2 * m + 1) hx,
    Finset.Ico_add_one_right_eq_Icc] at h
  linarith

/-- Arbitrary-order lower digamma bracket on `(0, ∞)`: for every `m : ℕ` and `x > 0`,
`log x - 1 / (2x) - ∑_{j=1}^{2m+1} B_{2j} / (2j x^{2j}) < ψ(x)`. -/
theorem log_sub_inv_two_mul_sub_sum_lt_digamma (m : ℕ) {x : ℝ} (hx : 0 < x) :
    Real.log x - 1 / (2 * x) -
        ∑ j ∈ Finset.Icc 1 (2 * m + 1), (bernoulli (2 * j) : ℝ) / ((2 * j : ℝ) * x ^ (2 * j)) <
      Real.digamma x := by
  have h := neg_one_pow_mul_iteratedDeriv_neg_realStirlingRemainder_even_pos m 1 hx
  rw [pow_one, iteratedDeriv_one, deriv.fun_neg, deriv_realStirlingRemainder (2 * m + 2) hx,
    show 2 * m + 2 = (2 * m + 1) + 1 by omega, Finset.Ico_add_one_right_eq_Icc] at h
  linarith

/-- Leading upper digamma bound on `(0, ∞)`: `ψ(x) < log x - 1 / (2x)`. -/
theorem digamma_lt_log_sub_inv_two_mul {x : ℝ} (hx : 0 < x) :
    Real.digamma x < Real.log x - 1 / (2 * x) := by
  have h := digamma_lt_log_sub_inv_two_mul_sub_sum 0 hx
  simp only [Nat.mul_zero, Finset.Icc_eq_empty (by omega : ¬1 ≤ 0), Finset.sum_empty, sub_zero] at h
  exact h

/-- Leading lower digamma bound on `(0, ∞)`: `log x - 1 / (2x) - 1 / (12x²) < ψ(x)`. -/
theorem log_sub_inv_two_mul_sub_lt_digamma {x : ℝ} (hx : 0 < x) :
    Real.log x - 1 / (2 * x) - 1 / (12 * x ^ 2) < Real.digamma x := by
  have h := log_sub_inv_two_mul_sub_sum_lt_digamma 0 hx
  simp only [Nat.mul_zero, zero_add, Finset.Icc_self, Finset.sum_singleton, Nat.mul_one,
    bernoulli_two, Rat.cast_inv, Rat.cast_ofNat, Nat.cast_one] at h
  linarith [show (6 : ℝ)⁻¹ / (2 * 1 * x ^ 2) = 1 / (12 * x ^ 2) by ring]

/-! ### Alzer's polygamma brackets on `(0, ∞)` -/

/-- The order-`p` Stirling partial sum for the `k`-th polygamma function `(-1)^{k+1} ψ^{(k)}(x)`:
`S_k(p; x) = (k - 1)! / x^k + k! / (2 x^{k+1}) +`
`∑_{i=1}^p B_{2i} (∏_{j=1}^{k-1} (2i + j)) / x^{2i+k}`. -/
@[expose] noncomputable def polygammaStirlingSum (k p : ℕ) (x : ℝ) : ℝ :=
  ((k - 1)! : ℝ) / x ^ k + (k ! : ℝ) / (2 * x ^ (k + 1)) +
    ∑ i ∈ Finset.Icc 1 p,
      (bernoulli (2 * i) : ℝ) * (∏ j ∈ Finset.Ico 1 k, ((2 * i + j : ℕ) : ℝ)) / x ^ (2 * i + k)

private theorem iteratedDeriv_log_eq {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    iteratedDeriv k Real.log x = (-1 : ℝ) ^ (k - 1) * ((k - 1)! : ℝ) / x ^ k := by
  have hk_eq : k = (k - 1) + 1 := by omega
  conv_lhs => rw [hk_eq, iteratedDeriv_succ', Real.deriv_log']
  rw [iteratedDeriv_eq_iterate, iter_deriv_inv]
  have hz : (-1 - (k - 1 : ℕ) : ℤ) = -(k : ℤ) := by omega
  rw [hz, zpow_neg, zpow_natCast, div_eq_mul_inv]

private theorem iteratedDeriv_one_div_two_mul (k : ℕ) {x : ℝ} :
    iteratedDeriv k (fun t : ℝ ↦ 1 / (2 * t)) x =
      (-1 : ℝ) ^ k * ((k ! : ℝ) / (2 * x ^ (k + 1))) := by
  have heq : (fun t : ℝ ↦ 1 / (2 * t)) = fun t : ℝ ↦ (2⁻¹ : ℝ) * t⁻¹ := by
    ext t
    simp only [one_div, mul_inv]
  rw [heq, iteratedDeriv_const_mul_field (2⁻¹ : ℝ) Inv.inv, iteratedDeriv_eq_iterate,
    iter_deriv_inv]
  have hz : (-1 - (k : ℕ) : ℤ) = -((k + 1 : ℕ) : ℤ) := by omega
  rw [hz, zpow_neg, zpow_natCast]
  simp only [div_eq_mul_inv, mul_inv]
  ring

private theorem iteratedDeriv_bernoulli_div_mul_pow {i k : ℕ} (hi : 1 ≤ i) (hk : 1 ≤ k) {x : ℝ} :
    iteratedDeriv k (fun t : ℝ ↦ (bernoulli (2 * i) : ℝ) / ((2 * i : ℝ) * t ^ (2 * i))) x =
      (-1 : ℝ) ^ k * ((bernoulli (2 * i) : ℝ) *
        (∏ j ∈ Finset.Ico 1 k, ((2 * i + j : ℕ) : ℝ)) / x ^ (2 * i + k)) := by
  have heq : (fun t : ℝ ↦ (bernoulli (2 * i) : ℝ) / ((2 * i : ℝ) * t ^ (2 * i))) =
      fun t : ℝ ↦ ((bernoulli (2 * i) : ℝ) / (2 * i : ℝ)) * t ^ (-((2 * i : ℕ) : ℤ)) := by
    ext t
    rw [zpow_neg, zpow_natCast, div_eq_mul_inv, mul_inv, div_eq_mul_inv, mul_assoc]
  rw [heq, iteratedDeriv_const_mul_field ((bernoulli (2 * i) : ℝ) / (2 * i : ℝ))
    (fun t : ℝ ↦ t ^ (-((2 * i : ℕ) : ℤ))), iteratedDeriv_eq_iterate, iter_deriv_zpow]
  have hprod : ∏ j ∈ Finset.range k, (-((2 * i : ℕ) : ℝ) - (j : ℝ)) =
      (-1 : ℝ) ^ k * ((2 * i : ℝ) * ∏ j ∈ Finset.Ico 1 k, ((2 * i + j : ℕ) : ℝ)) := by
    have hneg : ∏ j ∈ Finset.range k, (-((2 * i : ℕ) : ℝ) - (j : ℝ)) =
        ∏ j ∈ Finset.range k, ((-1 : ℝ) * ((2 * i + j : ℕ) : ℝ)) := by
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      push_cast
      ring
    rw [hneg, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    congr 1
    have hsplit : Finset.range k = insert 0 (Finset.Ico 1 k) := by
      ext j
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [hsplit, Finset.prod_insert (by simp)]
    simp
  have hz : (-((2 * i : ℕ) : ℤ) - (k : ℤ)) = -((2 * i + k : ℕ) : ℤ) := by omega
  simp only [Int.cast_neg, Int.cast_natCast]
  rw [hprod, hz, zpow_neg, zpow_natCast]
  field_simp

/-- Relation between `iteratedDeriv (k + 1) (realStirlingRemainder n)` and the `k`-th polygamma
function `iteratedDeriv k Real.digamma` on `(0, ∞)` for `k ≥ 1`. -/
theorem iteratedDeriv_succ_realStirlingRemainder (n : ℕ) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx : 0 < x) :
    iteratedDeriv (k + 1) (realStirlingRemainder n) x =
      iteratedDeriv k Real.digamma x + (-1 : ℝ) ^ k * polygammaStirlingSum k (n - 1) x := by
  have hev : deriv (realStirlingRemainder n) =ᶠ[𝓝 x]
      fun t : ℝ ↦ (Real.digamma t - Real.log t + 1 / (2 * t)) +
        ∑ i ∈ Finset.Ico 1 n, (bernoulli (2 * i) : ℝ) / ((2 * i : ℝ) * t ^ (2 * i)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
    exact deriv_realStirlingRemainder n ht
  rw [iteratedDeriv_succ', hev.iteratedDeriv_eq]
  have hcd_psi : ContDiffAt ℝ k Real.digamma x :=
    (contDiffOn_digamma_Ioi.contDiffAt (isOpen_Ioi.mem_nhds hx)).of_le (by exact_mod_cast le_top)
  have hcd_log : ContDiffAt ℝ k Real.log x :=
    (contDiffAt_id.log hx.ne').of_le (by exact_mod_cast le_top)
  have hcd_half : ContDiffAt ℝ k (fun t : ℝ ↦ 1 / (2 * t)) x :=
    contDiffAt_const.div (contDiffAt_const.mul contDiffAt_id) (by positivity)
  have hcd_term : ∀ i ∈ Finset.Ico 1 n,
      ContDiffAt ℝ k (fun t : ℝ ↦ (bernoulli (2 * i) : ℝ) / ((2 * i : ℝ) * t ^ (2 * i))) x := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
    exact contDiffAt_const.div (contDiffAt_const.mul (contDiffAt_id.pow (2 * i)))
      (mul_ne_zero (by positivity) (pow_ne_zero _ hx.ne'))
  have hcd_sum : ContDiffAt ℝ k
      (fun t : ℝ ↦ ∑ i ∈ Finset.Ico 1 n, (bernoulli (2 * i) : ℝ) / ((2 * i : ℝ) * t ^ (2 * i)))
      x :=
    ContDiffAt.sum hcd_term
  rw [iteratedDeriv_fun_add ((hcd_psi.sub hcd_log).add hcd_half) hcd_sum,
    iteratedDeriv_fun_add (hcd_psi.sub hcd_log) hcd_half,
    iteratedDeriv_fun_sub hcd_psi hcd_log,
    iteratedDeriv_fun_sum hcd_term,
    iteratedDeriv_log_eq hk x,
    iteratedDeriv_one_div_two_mul k]
  have hsum_eq :
      ∑ i ∈ Finset.Ico 1 n,
        iteratedDeriv k (fun t : ℝ ↦ (bernoulli (2 * i) : ℝ) / ((2 * i : ℝ) * t ^ (2 * i))) x =
      (-1 : ℝ) ^ k * ∑ i ∈ Finset.Icc 1 (n - 1),
        (bernoulli (2 * i) : ℝ) * (∏ j ∈ Finset.Ico 1 k, ((2 * i + j : ℕ) : ℝ)) /
          x ^ (2 * i + k) := by
    rw [Finset.mul_sum, show Finset.Ico 1 n = Finset.Icc 1 (n - 1) by
      ext i; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    exact iteratedDeriv_bernoulli_div_mul_pow (Finset.mem_Icc.mp hi).1 hk
  rw [hsum_eq, polygammaStirlingSum]
  have hsign : -((-1 : ℝ) ^ (k - 1)) = (-1 : ℝ) ^ k := by
    have hk_eq : k = (k - 1) + 1 := by omega
    conv_rhs => rw [hk_eq, pow_succ]
    ring
  linear_combination (((k - 1)! : ℝ) / x ^ k) * hsign

/-- **Alzer's lower polygamma bracket** (Alzer 1997, Theorem 9): for every `k ≥ 1`, `n : ℕ`, and
`x > 0`, `S_k(2n; x) < (-1)^{k+1} ψ^{(k)}(x)`. -/
theorem polygammaStirlingSum_lt_neg_one_pow_mul_iteratedDeriv_digamma {k : ℕ} (hk : 1 ≤ k)
    (n : ℕ) {x : ℝ} (hx : 0 < x) :
    polygammaStirlingSum k (2 * n) x < (-1 : ℝ) ^ (k + 1) * iteratedDeriv k Real.digamma x := by
  have h := neg_one_pow_mul_iteratedDeriv_realStirlingRemainder_odd_pos n (k + 1) hx
  rw [iteratedDeriv_succ_realStirlingRemainder (2 * n + 1) hk hx] at h
  simp only [Nat.add_sub_cancel] at h
  have hneg : (-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ k = -1 := by
    rw [pow_succ, mul_right_comm, ← mul_pow]
    norm_num
  have hmul : (-1 : ℝ) ^ (k + 1) *
      (iteratedDeriv k Real.digamma x + (-1 : ℝ) ^ k * polygammaStirlingSum k (2 * n) x) =
      (-1 : ℝ) ^ (k + 1) * iteratedDeriv k Real.digamma x - polygammaStirlingSum k (2 * n) x := by
    linear_combination polygammaStirlingSum k (2 * n) x * hneg
  linarith

/-- **Alzer's upper polygamma bracket** (Alzer 1997, Theorem 9): for every `k ≥ 1`, `n : ℕ`, and
`x > 0`, `(-1)^{k+1} ψ^{(k)}(x) < S_k(2n + 1; x)`. -/
theorem neg_one_pow_mul_iteratedDeriv_digamma_lt_polygammaStirlingSum {k : ℕ} (hk : 1 ≤ k)
    (n : ℕ) {x : ℝ} (hx : 0 < x) :
    (-1 : ℝ) ^ (k + 1) * iteratedDeriv k Real.digamma x < polygammaStirlingSum k (2 * n + 1) x := by
  have h := neg_one_pow_mul_iteratedDeriv_neg_realStirlingRemainder_even_pos n (k + 1) hx
  rw [iteratedDeriv_fun_neg, iteratedDeriv_succ_realStirlingRemainder (2 * n + 2) hk hx] at h
  simp only [show 2 * n + 2 - 1 = 2 * n + 1 by omega] at h
  have hneg : (-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ k = -1 := by
    rw [pow_succ, mul_right_comm, ← mul_pow]
    norm_num
  have hmul : (-1 : ℝ) ^ (k + 1) *
      -(iteratedDeriv k Real.digamma x + (-1 : ℝ) ^ k * polygammaStirlingSum k (2 * n + 1) x) =
      polygammaStirlingSum k (2 * n + 1) x -
        (-1 : ℝ) ^ (k + 1) * iteratedDeriv k Real.digamma x := by
    linear_combination -(polygammaStirlingSum k (2 * n + 1) x * hneg)
  linarith

/-! ### Stieltjes' sharp sector bound on the slit plane -/

/-- Comparison of the slit-plane derivative `‖r_n^{(k)}(z)‖` to its positive real-axis value at
`‖z‖`: for `n ≥ 1`, `k : ℕ`, and `z ∈ slitPlane`,
`‖r_n^{(k)}(z)‖ ≤ ((-1)^k (-1)^{n+1} r_n^{(k)}(‖z‖)) / cos (arg z / 2) ^ (2n + k)`. -/
theorem norm_iteratedDeriv_stirlingRemainder_le_real {n : ℕ} (hn : 1 ≤ n) (k : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    ‖iteratedDeriv k (stirlingRemainder n) z‖ ≤
      ((-1 : ℝ) ^ k * (-1 : ℝ) ^ (n + 1) * iteratedDeriv k (realStirlingRemainder n) ‖z‖) /
        Real.cos (z.arg / 2) ^ (2 * n + k) := by
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr (slitPlane_ne_zero hz)
  have hcos_pos : 0 < Real.cos (z.arg / 2) := Complex.cos_arg_div_two_pos_of_mem_slitPlane hz
  rw [iteratedDeriv_stirlingRemainder hn k hz, norm_mul, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  have hint_dom : IntegrableOn (fun u : ℝ ↦
      (Real.cos (z.arg / 2) ^ (2 * n + k))⁻¹ *
        ((-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
          (u + ‖z‖) ^ (2 * n + k))) (Ioi 0) :=
    (integrableOn_signed_bernoulli_sub_div_pow_Ioi n (by omega : 2 ≤ 2 * n + k) hz_pos).const_mul _
  have hle_int : ‖∫ u in Ioi (0 : ℝ),
        (((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u) : ℝ) : ℂ) /
          ((u : ℂ) + z) ^ (2 * n + k)‖ ≤
      (Real.cos (z.arg / 2) ^ (2 * n + k))⁻¹ *
        ∫ u in Ioi (0 : ℝ),
          (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
            (u + ‖z‖) ^ (2 * n + k) := by
    rw [← integral_const_mul]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine setIntegral_mono_on
      (integrableOn_bernoulli_sub_bernoulliFun_div_pow_Ioi n (by omega : 2 ≤ 2 * n + k) hz).norm
      hint_dom measurableSet_Ioi fun u hu ↦ ?_
    have hu0 : 0 ≤ u := (mem_Ioi.mp hu).le
    have hnn := neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_fract_nonneg n u
    have habs : |(bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)| =
        (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) := by
      rw [← abs_of_nonneg hnn, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have hsec : Real.cos (z.arg / 2) * (u + ‖z‖) ≤ ‖(u : ℂ) + z‖ := by
      simpa [add_comm] using Complex.cos_arg_div_two_mul_norm_add_le_norm_add_ofReal z u
    have hpow : Real.cos (z.arg / 2) ^ (2 * n + k) * (u + ‖z‖) ^ (2 * n + k) ≤
        ‖(u : ℂ) + z‖ ^ (2 * n + k) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hsec (2 * n + k)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_pow, habs]
    calc (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
          ‖(u : ℂ) + z‖ ^ (2 * n + k)
        ≤ (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
            (Real.cos (z.arg / 2) ^ (2 * n + k) * (u + ‖z‖) ^ (2 * n + k)) :=
          div_le_div_of_nonneg_left hnn (by positivity) hpow
      _ = (Real.cos (z.arg / 2) ^ (2 * n + k))⁻¹ *
            ((-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
              (u + ‖z‖) ^ (2 * n + k)) := by
          simp only [div_eq_mul_inv, mul_inv]
          ring
  have hr_eq :
      ((-1 : ℝ) ^ k * (-1 : ℝ) ^ (n + 1) * iteratedDeriv k (realStirlingRemainder n) ‖z‖) /
        Real.cos (z.arg / 2) ^ (2 * n + k) =
      (((2 * n + k - 1)! : ℝ) / ((2 * n)! : ℝ)) *
        ((Real.cos (z.arg / 2) ^ (2 * n + k))⁻¹ *
          ∫ u in Ioi (0 : ℝ),
            (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
              (u + ‖z‖) ^ (2 * n + k)) := by
    rw [iteratedDeriv_realStirlingRemainder hn k hz_pos]
    have hk2 : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
      rw [← mul_pow, mul_neg_one, neg_neg, one_pow]
    have hint_mul :
        (-1 : ℝ) ^ (n + 1) *
          ∫ u in Ioi (0 : ℝ),
            ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
              (u + ‖z‖) ^ (2 * n + k) =
        ∫ u in Ioi (0 : ℝ),
          (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
            (u + ‖z‖) ^ (2 * n + k) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
      ring
    rw [← hint_mul, div_eq_mul_inv]
    linear_combination ((((2 * n + k - 1)! : ℝ) / ((2 * n)! : ℝ)) * (-1 : ℝ) ^ (n + 1) *
      (∫ u in Ioi (0 : ℝ),
        ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
          (u + ‖z‖) ^ (2 * n + k)) *
      (Real.cos (z.arg / 2) ^ (2 * n + k))⁻¹) * hk2
  rw [hr_eq]
  exact mul_le_mul_of_nonneg_left hle_int (by positivity)

/-- **Stieltjes' sharp sector bound** on the slit plane: for every `n ≥ 1` and `z ∈ slitPlane`,
`‖r_n(z)‖ < ‖T_n(z)‖ / cos (arg z / 2) ^ (2n)`. -/
theorem norm_stirlingRemainder_lt {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ slitPlane) :
    ‖stirlingRemainder n z‖ < ‖stirlingTerm n z‖ / Real.cos (z.arg / 2) ^ (2 * n) := by
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr (slitPlane_ne_zero hz)
  have hcos_pos : 0 < Real.cos (z.arg / 2) := Complex.cos_arg_div_two_pos_of_mem_slitPlane hz
  have hle := norm_iteratedDeriv_stirlingRemainder_le_real hn 0 hz
  simp only [iteratedDeriv_zero, pow_zero, one_mul, add_zero] at hle
  have hpos := neg_one_pow_succ_mul_realStirlingRemainder_pos hn hz_pos
  have habs_r :
      (-1 : ℝ) ^ (n + 1) * realStirlingRemainder n ‖z‖ = |realStirlingRemainder n ‖z‖| := by
    rw [← abs_of_pos hpos, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [habs_r] at hle
  have hlt := abs_realStirlingRemainder_lt_abs_stirlingTerm hn hz_pos
  rw [← norm_stirlingTerm_eq_abs_norm n z] at hlt
  exact lt_of_le_of_lt hle (div_lt_div_of_pos_right hlt (pow_pos hcos_pos _))

/-- Stieltjes' sharp `n = 1` bound on the slit plane:
`‖r₁(z)‖ < 1 / (12 * cos (arg z / 2) ^ 2 * ‖z‖)`. -/
theorem norm_stirlingRemainder_one_lt {z : ℂ} (hz : z ∈ slitPlane) :
    ‖stirlingRemainder 1 z‖ < 1 / (12 * Real.cos (z.arg / 2) ^ 2 * ‖z‖) := by
  have h := norm_stirlingRemainder_lt le_rfl hz
  rw [stirlingTerm_one, norm_div, norm_one, norm_mul, Complex.norm_ofNat] at h
  convert h using 1
  simp only [Nat.mul_one, div_eq_mul_inv, mul_inv]
  ring

/-- Sharp `1 / 12` half-angle bound for all derivatives of the leading Stirling remainder `r₁` on
the slit plane: for every `k : ℕ` and `z ∈ slitPlane`,
`‖r₁^{(k)}(z)‖ < k! / (12 * cos (arg z / 2) ^ (k + 2) * ‖z‖ ^ (k + 1))`. -/
theorem norm_iteratedDeriv_stirlingRemainder_one_lt (k : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    ‖iteratedDeriv k (stirlingRemainder 1) z‖ <
      (k ! : ℝ) / (12 * Real.cos (z.arg / 2) ^ (k + 2) * ‖z‖ ^ (k + 1)) := by
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr (slitPlane_ne_zero hz)
  have hcos_pos : 0 < Real.cos (z.arg / 2) := Complex.cos_arg_div_two_pos_of_mem_slitPlane hz
  have hle := norm_iteratedDeriv_stirlingRemainder_le_real le_rfl k hz
  have h11 : (-1 : ℝ) ^ (1 + 1) = 1 := by norm_num
  rw [h11, mul_one, show 2 * 1 + k = k + 2 by omega] at hle
  -- Since `G₀ = -r₂` is strictly completely monotone,
  -- `(-1)^k r₁^{(k)}(‖z‖) < (-1)^k T₁^{(k)}(‖z‖)`.
  have hG := neg_one_pow_mul_iteratedDeriv_neg_realStirlingRemainder_even_pos 0 k hz_pos
  have heq_r2 : (fun t : ℝ ↦ -realStirlingRemainder 2 t) =
      fun t : ℝ ↦ (12⁻¹ : ℝ) * t⁻¹ - realStirlingRemainder 1 t := by
    ext t
    rw [realStirlingRemainder_succ, stirlingTerm_one]
    simp only [one_div, mul_inv]
    ring
  have hcd_T1 : ContDiffAt ℝ k (fun t : ℝ ↦ (12⁻¹ : ℝ) * t⁻¹) ‖z‖ :=
    contDiffAt_const.mul (contDiffAt_id.inv hz_pos.ne')
  have hcd_r1 : ContDiffAt ℝ k (realStirlingRemainder 1) ‖z‖ :=
    ((contDiffOn_realStirlingRemainder 1).contDiffAt (isOpen_Ioi.mem_nhds hz_pos)).of_le
      (by exact_mod_cast le_top)
  simp only [Nat.mul_zero, zero_add] at hG
  rw [heq_r2, iteratedDeriv_fun_sub hcd_T1 hcd_r1] at hG
  have hT1_deriv : iteratedDeriv k (fun t : ℝ ↦ (12⁻¹ : ℝ) * t⁻¹) ‖z‖ =
      (-1 : ℝ) ^ k * ((k ! : ℝ) / (12 * ‖z‖ ^ (k + 1))) := by
    rw [iteratedDeriv_const_mul_field (12⁻¹ : ℝ) Inv.inv, iteratedDeriv_eq_iterate, iter_deriv_inv]
    have hz_exp : (-1 - (k : ℕ) : ℤ) = -((k + 1 : ℕ) : ℤ) := by omega
    rw [hz_exp, zpow_neg, zpow_natCast]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [hT1_deriv] at hG
  have hk2 : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← mul_pow, mul_neg_one, neg_neg, one_pow]
  have hlt_real : (-1 : ℝ) ^ k * iteratedDeriv k (realStirlingRemainder 1) ‖z‖ <
      (k ! : ℝ) / (12 * ‖z‖ ^ (k + 1)) := by
    have hmul : (-1 : ℝ) ^ k *
        ((-1 : ℝ) ^ k * ((k ! : ℝ) / (12 * ‖z‖ ^ (k + 1))) -
          iteratedDeriv k (realStirlingRemainder 1) ‖z‖) =
        (k ! : ℝ) / (12 * ‖z‖ ^ (k + 1)) -
          (-1 : ℝ) ^ k * iteratedDeriv k (realStirlingRemainder 1) ‖z‖ := by
      linear_combination ((k ! : ℝ) / (12 * ‖z‖ ^ (k + 1))) * hk2
    linarith
  calc ‖iteratedDeriv k (stirlingRemainder 1) z‖
      ≤ ((-1 : ℝ) ^ k * iteratedDeriv k (realStirlingRemainder 1) ‖z‖) /
          Real.cos (z.arg / 2) ^ (k + 2) := hle
    _ < ((k ! : ℝ) / (12 * ‖z‖ ^ (k + 1))) / Real.cos (z.arg / 2) ^ (k + 2) :=
        div_lt_div_of_pos_right hlt_real (pow_pos hcos_pos _)
    _ = (k ! : ℝ) / (12 * Real.cos (z.arg / 2) ^ (k + 2) * ‖z‖ ^ (k + 1)) := by
        simp only [div_eq_mul_inv, mul_inv]
        ring

private theorem sin_div_two_le_cos_arg_div_two {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hz : |z.arg| ≤ π - δ) : Real.sin (δ / 2) ≤ Real.cos (z.arg / 2) := by
  have hle : |z.arg / 2| ≤ π / 2 - δ / 2 := by
    rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]
    linarith
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hle
  rwa [Real.cos_pi_div_two_sub, Real.cos_abs] at hcos

/-- Uniform sector form of Stieltjes' bound: for `0 < δ`, `|arg z| ≤ π - δ`, `z ≠ 0`, and
`n ≥ 1`, `‖r_n(z)‖ < ‖T_n(z)‖ / sin (δ / 2) ^ (2n)`. -/
theorem norm_stirlingRemainder_lt_of_abs_arg_le {n : ℕ} (hn : 1 ≤ n) {z : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hz : |z.arg| ≤ π - δ) (hz0 : z ≠ 0) :
    ‖stirlingRemainder n z‖ < ‖stirlingTerm n z‖ / Real.sin (δ / 2) ^ (2 * n) := by
  have hslit : z ∈ slitPlane := Complex.mem_slitPlane_of_abs_arg_le hδ hz hz0
  have hδπ : δ ≤ π := by linarith [abs_nonneg z.arg]
  have hsin_pos : 0 < Real.sin (δ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsin_le : Real.sin (δ / 2) ≤ Real.cos (z.arg / 2) :=
    sin_div_two_le_cos_arg_div_two hδ hz
  exact lt_of_lt_of_le (norm_stirlingRemainder_lt hn hslit)
    (div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hsin_pos _)
      (pow_le_pow_left₀ hsin_pos.le hsin_le _))

/-- Ramaré's sector form of Stieltjes' `n = 1` bound: for `0 < δ`, `|arg z| ≤ π - δ`, and
`z ≠ 0`, `‖r₁(z)‖ < 1 / (12 * sin (δ / 2) ^ 2 * ‖z‖)`. -/
theorem norm_stirlingRemainder_one_lt_of_abs_arg_le {z : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hz : |z.arg| ≤ π - δ) (hz0 : z ≠ 0) :
    ‖stirlingRemainder 1 z‖ < 1 / (12 * Real.sin (δ / 2) ^ 2 * ‖z‖) := by
  have h := norm_stirlingRemainder_lt_of_abs_arg_le le_rfl hδ hz hz0
  rw [stirlingTerm_one, norm_div, norm_one, norm_mul, Complex.norm_ofNat] at h
  convert h using 1
  simp only [Nat.mul_one, div_eq_mul_inv, mul_inv]
  ring

/-- Exponential Stirling representation of `Complex.Gamma` on the slit plane:
`Γ(z) = √(2π) * exp ((z - 1/2) * log z - z + r₁(z))`. -/
theorem Gamma_eq_sqrt_two_pi_mul_exp {z : ℂ} (hz : z ∈ slitPlane) :
    Complex.Gamma z =
      (Real.sqrt (2 * π) : ℂ) *
        Complex.exp ((z - 1 / 2) * Complex.log z - z + stirlingRemainder 1 z) := by
  have hlog : logGamma z =
      ((Real.log (2 * π) / 2 : ℝ) : ℂ) +
        ((z - 1 / 2) * Complex.log z - z + stirlingRemainder 1 z) := by
    have h := logGamma_eq_stirling_add_remainder 1 z
    simp only [Finset.Ico_self, Finset.sum_empty, add_zero] at h
    linear_combination h
  have hexp_half : Real.exp (Real.log (2 * π) / 2) = Real.sqrt (2 * π) := by
    rw [← Real.sqrt_sq (Real.exp_pos _).le, sq, ← Real.exp_add, add_halves,
      Real.exp_log (by positivity)]
  rw [← exp_logGamma hz, hlog, Complex.exp_add, ← Complex.ofReal_exp, hexp_half]

end TauCeti

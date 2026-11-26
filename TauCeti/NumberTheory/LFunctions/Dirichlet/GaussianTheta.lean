/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Gaussian theta series of Dirichlet coefficients

We sum Gaussian weights over the positive integers, allowing both the even and odd weights.
The normalization by `√u` puts the Mellin transform at `s - 1/2` and gives the factor
`Gammaℝ (s + j) / 2` multiplying the Dirichlet series. In particular the Möbius-twisted
coefficients of a Dirichlet character give its reciprocal L-function in `Re s > 1`.
This is the classical theta–Mellin construction (Montgomery and Vaughan, *Multiplicative
Number Theory I*, Chapter 10), using Mathlib's `hasSum_mellin_pi_mul` to interchange sum
and integral.
-/

public section

open Complex MeasureTheory Set
open scoped ArithmeticFunction.Moebius

namespace TauCeti

/-- The Gaussian weight with monomial factor of degree `j`. The cases `j = 0` and `j = 1`
are the weights for even and odd characters. -/
noncomputable def gaussianMonomial (j : ℕ) (x : ℝ) : ℝ :=
  x ^ j * Real.exp (-(Real.pi * x ^ 2))

/-- The value of the Gaussian monomial weight. -/
theorem gaussianMonomial_def (j : ℕ) (x : ℝ) :
    gaussianMonomial j x = x ^ j * Real.exp (-(Real.pi * x ^ 2)) := (rfl)

/-- The Gaussian theta series with coefficients `c`, summed over positive integers and
normalized by `√u`. -/
noncomputable def gaussianTheta (j : ℕ) (c : ℕ → ℂ) (u : ℝ) : ℂ :=
  (Real.sqrt u : ℂ) * ∑' n : ℕ, c (n + 1) * gaussianMonomial j ((n + 1 : ℕ) * u)

/-- Expansion of the normalized theta series over the positive integers. -/
theorem gaussianTheta_def (j : ℕ) (c : ℕ → ℂ) (u : ℝ) :
    gaussianTheta j c u =
      (Real.sqrt u : ℂ) * ∑' n : ℕ, c (n + 1) * gaussianMonomial j ((n + 1 : ℕ) * u) := (rfl)

/-- The norm of a Gaussian monomial is bounded by a decaying exponential. -/
theorem norm_gaussianMonomial_le (j : ℕ) (x : ℝ) :
    ‖gaussianMonomial j x‖ ≤ 3 * j.factorial * Real.exp (-2 * |x|) := by
  have hpow : |x| ^ j ≤ (j.factorial : ℝ) * Real.exp |x| := by
    rw [mul_comm]
    exact (div_le_iff₀ (by positivity)).mp (Real.pow_div_factorial_le_exp |x| (abs_nonneg x) j)
  have hquad : |x| - Real.pi * |x| ^ 2 ≤ 1 - 2 * |x| := by
    have hπ := mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) (sq_nonneg |x|)
    nlinarith [sq_nonneg (|x| - 1 / 2)]
  rw [gaussianMonomial_def, Real.norm_eq_abs, abs_mul, abs_pow, Real.abs_exp, ← sq_abs x]
  calc
    |x| ^ j * Real.exp (-(Real.pi * |x| ^ 2)) ≤
        (j.factorial : ℝ) * Real.exp |x| * Real.exp (-(Real.pi * |x| ^ 2)) := by gcongr
    _ ≤ (j.factorial : ℝ) * Real.exp (1 - 2 * |x|) := by
      rw [mul_assoc, ← Real.exp_add, ← sub_eq_add_neg]
      gcongr
    _ ≤ 3 * j.factorial * Real.exp (-2 * |x|) := by
      rw [sub_eq_add_neg, Real.exp_add, ← mul_assoc, neg_mul, mul_comm (3 : ℝ)]
      gcongr
      exact Real.exp_one_lt_three.le

private theorem norm_gaussianTheta_term_le (j : ℕ) {c : ℕ → ℂ} {B : ℝ}
    (hc : ∀ n ≠ 0, ‖c n‖ ≤ B) (u : ℝ) (n : ℕ) :
    ‖c (n + 1) * gaussianMonomial j ((n + 1 : ℕ) * u)‖ ≤
      (3 * j.factorial * B * Real.exp (-|u|)) * Real.exp (-|u|) ^ (n + 1) := by
  have hB := (norm_nonneg _).trans (hc (n + 1) (Nat.succ_ne_zero n))
  have hweight := norm_gaussianMonomial_le j ((n + 1 : ℕ) * u)
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ))] at hweight
  rw [norm_mul, Complex.norm_real, ← Real.exp_natCast_mul]
  calc
    _ ≤ B * (3 * j.factorial * Real.exp (-2 * (↑(n + 1 : ℕ) * |u|))) :=
      mul_le_mul (hc _ (Nat.succ_ne_zero n)) hweight (norm_nonneg _) hB
    _ = (3 * j.factorial * B) * Real.exp (-2 * (↑(n + 1 : ℕ) * |u|)) := by ring
    _ ≤ _ := by
      rw [mul_assoc (3 * (j.factorial : ℝ) * B), ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg n) (abs_nonneg u), abs_nonneg u]

/-- For bounded coefficients the positive-index theta sum converges absolutely for `u ≠ 0`. -/
theorem summable_norm_gaussianTheta_term (j : ℕ) {c : ℕ → ℂ} {B : ℝ}
    (hc : ∀ n ≠ 0, ‖c n‖ ≤ B) {u : ℝ} (hu : u ≠ 0) :
    Summable fun n : ℕ ↦ ‖c (n + 1) * gaussianMonomial j ((n + 1 : ℕ) * u)‖ := by
  have hgeom := summable_geometric_of_lt_one (Real.exp_nonneg (-|u|))
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (abs_pos.mpr hu)))
  exact ((summable_nat_add_iff 1).mpr hgeom |>.mul_left _).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (norm_gaussianTheta_term_le j hc u)

/-- The theta series with coefficients bounded by `B` has norm at most
`3 j! B exp(-u) / √u` for `u > 0`. The factor `j!` is `1` for even and odd weights. -/
theorem norm_gaussianTheta_le (j : ℕ) {c : ℕ → ℂ} {B : ℝ}
    (hc : ∀ n ≠ 0, ‖c n‖ ≤ B) (u : ℝ) :
    ‖gaussianTheta j c u‖ ≤ 3 * j.factorial * B * Real.exp (-u) / Real.sqrt u := by
  rcases le_or_gt u 0 with hu | hu
  · simp [gaussianTheta_def, Real.sqrt_eq_zero_of_nonpos hu]
  have hB := (norm_nonneg _).trans (hc 1 one_ne_zero)
  have hr : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu)
  have hg := summable_geometric_of_lt_one (Real.exp_nonneg (-u)) hr
  have hsum : (∑' n : ℕ, Real.exp (-u) ^ (n + 1)) ≤ 1 / u := by
    simp_rw [pow_succ', tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_nonneg (-u)) hr]
    rw [Real.exp_neg, ← div_eq_mul_inv]
    have hexp : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have hpos : 0 < Real.exp u - 1 := by linarith
    have hden : 1 - (Real.exp u)⁻¹ = (Real.exp u - 1) / Real.exp u := by field_simp
    rw [hden]
    rw [div_div_eq_mul_div, inv_mul_cancel₀ (Real.exp_ne_zero _)]
    exact one_div_le_one_div_of_le hu (by linarith)
  have hs := summable_norm_gaussianTheta_term j hc hu.ne'
  have hterm := norm_gaussianTheta_term_le j hc u
  rw [abs_of_pos hu] at hterm
  rw [gaussianTheta_def, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt u * ∑' n : ℕ, ‖c (n + 1) * gaussianMonomial j ((n + 1 : ℕ) * u)‖ :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hs) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt u * ((3 * j.factorial * B * Real.exp (-u)) * (1 / u)) := by
      refine mul_le_mul_of_nonneg_left (?_ : _ ≤ _) (Real.sqrt_nonneg _)
      refine (hs.tsum_le_tsum hterm
        ((summable_nat_add_iff 1).mpr hg |>.mul_left _)).trans ?_
      rw [tsum_mul_left]
      gcongr
    _ = _ := by
      have hsqrt0 := (Real.sqrt_pos.2 hu).ne'
      field_simp
      rw [Real.sq_sqrt hu.le, mul_comm]

/-- The normalized theta series is measurable, including when the sum is interpreted as a
`tsum` outside the positive half-line. -/
@[fun_prop]
theorem measurable_gaussianTheta (j : ℕ) (c : ℕ → ℂ) : Measurable (gaussianTheta j c) := by
  unfold gaussianTheta gaussianMonomial
  refine Measurable.mul (by fun_prop) (Measurable.tsum fun n ↦ ?_)
  fun_prop

private theorem mellinConvergent_gaussianTheta (j : ℕ) {c : ℕ → ℂ} {B : ℝ}
    (hc : ∀ n ≠ 0, ‖c n‖ ≤ B) {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (gaussianTheta j c) (s - 1 / 2) := by
  have hG := (Complex.GammaIntegral_convergent (s := (s.re - 1 : ℝ)) (by simpa)).norm
  refine (hG.const_mul (3 * j.factorial * B)).mono'
    ((measurable_ofReal.pow_const _ |>.smul (measurable_gaussianTheta j c)).aestronglyMeasurable)
    (ae_restrict_iff' measurableSet_Ioi |>.mpr <| ae_of_all _ fun u (hu : 0 < u) ↦ ?_)
  simp only [norm_smul, norm_mul, norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_real,
    Real.norm_eq_abs, Real.abs_exp, sub_re, div_ofNat_re, one_re, ofReal_re]
  refine (mul_le_mul_of_nonneg_left (norm_gaussianTheta_le j hc u) (by positivity)).trans_eq ?_
  rw [Real.sqrt_eq_rpow]
  calc
    _ = (3 * (j.factorial : ℝ) * B) * (Real.exp (-u) *
        (u ^ (s.re - 1 / 2 - 1) / u ^ (1 / 2 : ℝ))) := by ring
    _ = _ := by
      rw [← Real.rpow_sub hu, (by ring : s.re - 1 / 2 - 1 - 1 / 2 = s.re - 1 - 1)]

private noncomputable def gaussianThetaKernel (j : ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, c (n + 1) * (n + 1 : ℕ) ^ j * Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * t)

private theorem mellin_gaussianThetaKernel (j : ℕ) {c : ℕ → ℂ} {B : ℝ}
    (hc : ∀ n ≠ 0, ‖c n‖ ≤ B) {s : ℂ} (hs : 1 < s.re) :
    mellin (gaussianThetaKernel j c) ((s + j) / 2) = Gammaℝ (s + j) * LSeries c s := by
  have hcoeff := LSeriesSummable_of_bounded_of_one_lt_re hc hs
  have hshift : Summable fun n : ℕ ↦ LSeries.term c s (n + 1) :=
    (summable_nat_add_iff 1).mpr hcoeff
  have hp (n : ℕ) : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hs' : 0 < ((s + j) / 2).re := by
    simp only [div_ofNat_re, add_re, natCast_re]
    positivity
  -- The kernel at `t` differs from the sum at `√t` by the monomial factor `(√t)^j`.
  have hsF (t : ℝ) (ht : t ∈ Ioi 0) : HasSum
      (fun n : ℕ ↦ c (n + 1) * (n + 1 : ℕ) ^ j *
        Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * t)) (gaussianThetaKernel j c t) := by
    unfold gaussianThetaKernel
    have ht' : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    refine ((summable_norm_iff.mp (summable_norm_gaussianTheta_term j hc ht'.ne')).mul_right
      ((Real.sqrt t : ℂ) ^ j)⁻¹).congr (fun n ↦ ?_) |>.hasSum
    have h : (↑(n + 1 : ℕ) * Real.sqrt t) ^ 2 = ((n + 1 : ℕ) : ℝ) ^ 2 * t := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt ht)]
    simp only [gaussianMonomial_def, h, ofReal_mul, ofReal_pow, ofReal_natCast, mul_pow]
    have hexp : -(Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2 * t)) =
        -Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * t := by ring
    rw [hexp]
    field_simp [(ofReal_ne_zero.mpr ht'.ne' : (Real.sqrt t : ℂ) ≠ 0)]
  have hAb (n : ℕ) : ‖c (n + 1) * (n + 1 : ℕ) ^ j‖ /
      (((n + 1 : ℕ) : ℝ) ^ 2) ^ ((s + j) / 2).re = ‖LSeries.term c s (n + 1)‖ := by
    rw [LSeries.norm_term_eq, ite_eq_right (Nat.succ_ne_zero n), norm_mul, norm_pow,
      Complex.norm_natCast, div_ofNat_re, add_re, natCast_re, ← Real.rpow_natCast_mul (hp n).le,
      Nat.cast_ofNat, mul_div_cancel₀ _ two_ne_zero, Real.rpow_add (hp n), Real.rpow_natCast]
    field_simp
  have hF := hasSum_mellin_pi_mul (q := fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) ^ 2))
    (fun n ↦ Or.inr (by positivity)) hs' hsF
    (by simpa only [hAb] using hshift.norm)
  have hscale (n : ℕ) : (Real.pi : ℂ) ^ (-((s + j) / 2)) * Gamma ((s + j) / 2) *
        (c (n + 1) * (n + 1 : ℕ) ^ j) / (↑(((n + 1 : ℕ) : ℝ) ^ 2) : ℂ) ^ ((s + j) / 2) =
      Gammaℝ (s + j) * LSeries.term c s (n + 1) := by
    rw [Gammaℝ_def, neg_div, LSeries.term_of_ne_zero (Nat.succ_ne_zero n), ofReal_pow,
      ofReal_natCast, ← natCast_cpow_natCast_mul, Nat.cast_ofNat, mul_div_cancel₀ _ two_ne_zero,
      cpow_add _ _ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)), cpow_natCast]
    field_simp
  rw [← hF.tsum_eq]
  simp only [hscale, tsum_mul_left]
  rw [LSeries, hcoeff.tsum_eq_zero_add, LSeries.term_zero, zero_add]

/-- The normalized Gaussian theta series has an absolutely convergent Mellin transform at
`s - 1/2` for `Re s > 1`. Its value is the Dirichlet series times `Gammaℝ (s + j) / 2`. -/
theorem hasMellin_gaussianTheta (j : ℕ) {c : ℕ → ℂ} {B : ℝ}
    (hc : ∀ n ≠ 0, ‖c n‖ ≤ B) {s : ℂ} (hs : 1 < s.re) :
    HasMellin (gaussianTheta j c) (s - 1 / 2) (Gammaℝ (s + j) / 2 * LSeries c s) := by
  refine ⟨mellinConvergent_gaussianTheta j hc hs, ?_⟩
  calc
    mellin (gaussianTheta j c) (s - 1 / 2) =
        mellin (fun u ↦ (u : ℂ) ^ ((j : ℂ) + 1 / 2) • gaussianThetaKernel j c (u ^ (2 : ℝ)))
          (s - 1 / 2) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) ↦ ?_
      congr 1
      have hsqrt : (u : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt u : ℂ) := by
        rw [Real.sqrt_eq_rpow, ofReal_cpow hu.le]
        norm_num
      dsimp only
      rw [gaussianTheta_def, smul_eq_mul, cpow_add _ _ (ofReal_ne_zero.mpr hu.ne'),
        cpow_natCast, hsqrt]
      simp only [gaussianThetaKernel, gaussianMonomial_def, Real.rpow_two, ofReal_mul,
        ofReal_pow, ofReal_natCast, mul_pow, ← tsum_mul_left]
      congr 1
      funext n
      ring_nf
    _ = (1 / 2 : ℝ) • mellin (gaussianThetaKernel j c) ((s + j) / 2) := by
      rw [mellin_cpow_smul, mellin_comp_rpow]
      congr 2 <;> push_cast <;> ring_nf
    _ = _ := by rw [mellin_gaussianThetaKernel j hc hs, Complex.real_smul]; push_cast; ring

end TauCeti

namespace DirichletCharacter

/-- The normalized Gaussian theta series of the Möbius-twisted coefficients of a Dirichlet
character represents the reciprocal L-function, times the Gaussian Mellin factor. -/
theorem hasMellin_gaussianTheta_mul_moebius {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (j : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasMellin (TauCeti.gaussianTheta j (fun n ↦ χ n * (μ n : ℂ))) (s - 1 / 2)
      (Gammaℝ (s + j) / 2 / χ.LFunction s) := by
  have hμ : ∀ (n : ℕ), n ≠ 0 → ‖χ n * (μ n : ℂ)‖ ≤ 1 := by
    intro n _
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one n)).trans ?_
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  have hval := eq_inv_of_mul_eq_one_right (LSeries.mul_mu_eq_one χ hs)
  rw [LFunction_eq_LSeries χ hs, div_eq_mul_inv (Gammaℝ (s + j) / 2), ← hval]
  exact TauCeti.hasMellin_gaussianTheta j hμ hs

end DirichletCharacter

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Tricomi
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Gamma.Real
import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Basic

/-!
# Parameter zeros of Tricomi's incomplete Gamma function for positive arguments

This file establishes DLMF §8.13(iii)(b) for Tricomi's entire incomplete Gamma function
(`Complex.tricomiIncompleteGamma`):

* `Complex.tricomiIncompleteGamma_param_zeros` — for every `n ≥ 1`, there is a threshold
  `x*_n > 0` such that on the even negative band `(−2n, 1 − 2n)`, `a ↦ γ*(a, x)` has two
  simple real zeros for `0 < x < x*_n`, one double real zero for `x = x*_n` (`γ*` and `∂_a γ*`
  vanish while `∂_a² γ* ≠ 0`), and no real zeros for `x > x*_n`.

## Implementation notes

We avoid branch cuts and power singularities by working with the smooth tail integral
`V(a, x) = ∫₀^∞ exp (a s - x exp s) ds`. It satisfies
`Γ(a) Re γ*(a, x) + V(a, x) = x^(-a) Γ(a)` for all `a ∉ −ℕ`, proved for `a > 0` by a
variable substitution and extended leftward via the shared parameter recurrence. On
`(−2n, 1 − 2n)` (`n ≥ 1`), `Γ(a) > 0`, so `Re γ*(a, x) = x^(-a) (1 - exp (-Φ_x(a)))` where
`Φ_x(a) = log Γ(a) - a log x - log V(a, x)`. One integration by parts bounds the variance
`(log V(·, x))''(a) ≤ 1 / a^2`, while the digamma recurrence and monotonicity on `(0, ∞)`
give `(log Γ)''(a) ≥ 1 / a^2 + 1 / (a + 1)^2`, yielding strict convexity
`Φ_x''(a) ≥ 1 / (a + 1)^2 > 0`. The unique minimum `M(x) = min_a Φ_x(a)` is continuous and
strictly increasing in `x > 0`, negative near `0` and positive for large `x`, producing the
unique threshold `x*_n`.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.13(iii)](https://dlmf.nist.gov/8.13#iii).
* F. G. Tricomi, *Sulla funzione gamma incompleta*, Ann. Mat. Pura Appl. (4) 31 (1950).
* K. S. Kölbig, *On the zeros of the incomplete gamma function*, Math. Comp. 26 (1972), 451–465.
-/

public section

noncomputable section

open Complex Filter Finset Set MeasureTheory
open scoped Interval Nat Topology

namespace Complex

/-! ### Even negative band helpers -/

private theorem evenBand_mem_unit {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) :
    a ∈ Ioo (-((2 * n - 1 + 1 : ℕ) : ℝ)) (-((2 * n - 1 : ℕ) : ℝ)) := by
  have h1 : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h2 : ((2 * n - 1 + 1 : ℕ) : ℝ) = 2 * (n : ℝ) := by
    rw [Nat.sub_add_cancel (by omega)]; push_cast; ring
  exact ⟨by linarith [ha.1], by linarith [ha.2]⟩

private theorem mem_Ioo_neg_two_mul_ne_neg_nat {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) : ∀ k : ℕ, a ≠ -(k : ℝ) :=
  Real.ne_neg_natCast_of_mem_Ioo (evenBand_mem_unit hn ha)

private theorem pi_div_factorial_le_Gamma_of_evenBand {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) :
    Real.pi / ((2 * n)! : ℝ) ≤ Real.Gamma a := by
  have hu := evenBand_mem_unit hn ha
  have hbd := Real.pi_div_factorial_le_neg_one_pow_mul_Gamma hu.1 hu.2
  have hsub : 2 * n - 1 + 1 = 2 * n := Nat.sub_add_cancel (by omega)
  have heven : (-1 : ℝ) ^ (2 * n) = 1 := by rw [pow_mul]; norm_num
  rwa [hsub, heven, one_mul] at hbd

private theorem Gamma_pos_of_mem_Ioo_neg_two_mul {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) : 0 < Real.Gamma a :=
  (div_pos Real.pi_pos (by positivity)).trans_le (pi_div_factorial_le_Gamma_of_evenBand hn ha)

/-! ### The smooth tail integral `V(a, x)` -/

private def tailMoment (k : ℕ) (a x : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), s ^ k * Real.exp (a * s - x * Real.exp s)

private theorem tailIntegrand_le_exp_neg (k : ℕ) (A : ℝ) {x₀ : ℝ} (hx₀ : 0 < x₀)
    {a x s : ℝ} (ha : a ≤ A) (hx : x₀ ≤ x) (hs : 0 ≤ s) :
    s ^ k * Real.exp (a * s - x * Real.exp s) ≤
      (k ! : ℝ) * Real.exp ((max A 0 + 2) ^ 2 / (2 * x₀)) * Real.exp (-s) := by
  let M : ℝ := max A 0 + 2
  have hsk : s ^ k ≤ (k ! : ℝ) * Real.exp s := by
    have := Real.pow_div_factorial_le_exp s hs k
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have hs2 : s ^ 2 / 2 ≤ Real.exp s := by
    simpa [Nat.factorial] using Real.pow_div_factorial_le_exp s hs 2
  have hquad : M * s - x₀ * (s ^ 2 / 2) ≤ M ^ 2 / (2 * x₀) := by
    have hsq : 0 ≤ x₀ / 2 * (s - M / x₀) ^ 2 := by positivity
    have hid :
        M ^ 2 / (2 * x₀) - (M * s - x₀ * (s ^ 2 / 2)) = x₀ / 2 * (s - M / x₀) ^ 2 := by
      field_simp; ring
    linarith
  have hexp : s + (a * s - x * Real.exp s) ≤ M ^ 2 / (2 * x₀) + (-s) := by
    have h2 : (a + 2) * s ≤ M * s :=
      mul_le_mul_of_nonneg_right (by dsimp only [M]; linarith [le_max_left A 0]) hs
    have h3 : x₀ * (s ^ 2 / 2) ≤ x * Real.exp s :=
      mul_le_mul hx hs2 (by positivity) (by linarith)
    linarith
  calc s ^ k * Real.exp (a * s - x * Real.exp s)
      ≤ ((k ! : ℝ) * Real.exp s) * Real.exp (a * s - x * Real.exp s) :=
          mul_le_mul_of_nonneg_right hsk (Real.exp_pos _).le
    _ = (k ! : ℝ) * Real.exp (s + (a * s - x * Real.exp s)) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ (k ! : ℝ) * Real.exp (M ^ 2 / (2 * x₀) + (-s)) := by gcongr
    _ = (k ! : ℝ) * Real.exp (M ^ 2 / (2 * x₀)) * Real.exp (-s) := by
          rw [Real.exp_add, mul_assoc]

private theorem integrableOn_tailIntegrand (k : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun s : ℝ => s ^ k * Real.exp (a * s - x * Real.exp s)) (Ioi 0) := by
  let C : ℝ := (k ! : ℝ) * Real.exp ((max a 0 + 2) ^ 2 / (2 * x))
  refine ((integrableOn_exp_neg_Ioi 0).const_mul C).mono'
    (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hs.out.le _) (Real.exp_pos _).le)]
  exact tailIntegrand_le_exp_neg k a hx le_rfl le_rfl hs.out.le

private theorem tendsto_tailIntegrand_atTop (k : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun s : ℝ => s ^ k * Real.exp (a * s - x * Real.exp s)) atTop (𝓝 0) := by
  let C : ℝ := (k ! : ℝ) * Real.exp ((max a 0 + 2) ^ 2 / (2 * x))
  refine squeeze_zero' ?_ ?_ (by simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    exact mul_nonneg (pow_nonneg hs _) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    exact tailIntegrand_le_exp_neg k a hx le_rfl le_rfl hs

private theorem tailMoment_nonneg (k : ℕ) (a x : ℝ) : 0 ≤ tailMoment k a x :=
  setIntegral_nonneg measurableSet_Ioi fun _ hs =>
    mul_nonneg (pow_nonneg hs.out.le _) (Real.exp_pos _).le

private theorem tailMoment_zero_pos (a : ℝ) {x : ℝ} (hx : 0 < x) : 0 < tailMoment 0 a x := by
  rw [tailMoment]
  simp only [pow_zero, one_mul]
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)
    (by simpa only [pow_zero, one_mul] using integrableOn_tailIntegrand 0 a hx)]
  have hsupp : Function.support (fun s : ℝ => Real.exp (a * s - x * Real.exp s)) = univ :=
    Set.eq_univ_of_forall fun _ => (Real.exp_pos _).ne'
  rw [hsupp, univ_inter, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

private theorem hasDerivAt_tailMoment (k : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun b : ℝ => tailMoment k b x) (tailMoment (k + 1) a x) a := by
  let C : ℝ := ((k + 1)! : ℝ) * Real.exp ((max (a + 1) 0 + 2) ^ 2 / (2 * x))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ)
    (F := fun b s => s ^ k * Real.exp (b * s - x * Real.exp s))
    (F' := fun b s => s ^ (k + 1) * Real.exp (b * s - x * Real.exp s))
    (bound := fun s => C * Real.exp (-s))
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (Ioo_mem_nhds (by linarith : a - 1 < a) (by linarith : a < a + 1))
    (Eventually.of_forall fun _ => Continuous.aestronglyMeasurable (by fun_prop))
    (integrableOn_tailIntegrand k a hx)
    (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    ((integrableOn_exp_neg_Ioi 0).const_mul C) ?_
  · exact h.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs b hb
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hs.out.le _) (Real.exp_pos _).le)]
    exact tailIntegrand_le_exp_neg (k + 1) (a + 1) hx hb.2.le le_rfl hs.out.le
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s _ b _
    have h1 : HasDerivAt (fun y : ℝ => y * s - x * Real.exp s) s b := by
      simpa using ((hasDerivAt_id' b).mul_const s).sub_const (x * Real.exp s)
    convert h1.exp.const_mul (s ^ k) using 1
    rw [pow_succ]; ring

private theorem continuousAt_tailMoment_zero (a₀ : ℝ) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ContinuousAt (fun p : ℝ × ℝ => tailMoment 0 p.1 p.2) (a₀, x₀) := by
  let C : ℝ := ((0 : ℕ)! : ℝ) * Real.exp ((max (a₀ + 1) 0 + 2) ^ 2 / (2 * (x₀ / 2)))
  refine continuousAt_of_dominated
    (F := fun (p : ℝ × ℝ) s => s ^ 0 * Real.exp (p.1 * s - p.2 * Real.exp s))
    (bound := fun s => C * Real.exp (-s)) (μ := volume.restrict (Ioi (0 : ℝ)))
    (Eventually.of_forall fun _ => Continuous.aestronglyMeasurable (by fun_prop)) ?_
    ((integrableOn_exp_neg_Ioi 0).const_mul C)
    (Eventually.of_forall fun _ => Continuous.continuousAt (by fun_prop))
  filter_upwards [prod_mem_nhds (Iio_mem_nhds (by linarith : a₀ < a₀ + 1))
    (Ioi_mem_nhds (by linarith : x₀ / 2 < x₀))] with p hp
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (by simp [(Real.exp_pos _).le])]
  exact tailIntegrand_le_exp_neg 0 (a₀ + 1) (half_pos hx₀) hp.1.le hp.2.le hs.out.le

private theorem rpow_mul_tailMoment_zero_eq_integral (a : ℝ) {x : ℝ} (hx : 0 < x) :
    x ^ a * tailMoment 0 a x = ∫ u in Ioi x, u ^ (a - 1) * Real.exp (-u) := by
  have h1 : tailMoment 0 a x = ∫ y in Ioi (1 : ℝ), y ^ (a - 1) * Real.exp (-(x * y)) := by
    have hcomp := integral_comp_exp_Ioi (fun y : ℝ => y ^ (a - 1) * Real.exp (-(x * y))) 0
    rw [Real.exp_zero] at hcomp
    rw [tailMoment, ← hcomp]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [pow_zero, one_mul, smul_eq_mul, Real.rpow_def_of_pos (Real.exp_pos s), Real.log_exp,
      ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
    exact congrArg Real.exp (by ring)
  rw [h1, ← integral_const_mul]
  have h2 := integral_comp_mul_left_Ioi' (fun u : ℝ => u ^ (a - 1) * Real.exp (-u)) 1 hx
  rw [mul_one, smul_eq_mul, ← integral_const_mul] at h2
  rw [← h2]
  have hmul : x ^ a = x * x ^ (a - 1) := by
    rw [Real.rpow_sub hx, Real.rpow_one, mul_div_cancel₀ _ hx.ne']
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  rw [Real.mul_rpow hx.le (lt_trans zero_lt_one hy).le, hmul]
  ring

private theorem tailMoment_zero_recurrence (a : ℝ) {x : ℝ} (hx : 0 < x) :
    a * tailMoment 0 a x - x * tailMoment 0 (a + 1) x = -Real.exp (-x) := by
  have hderiv : ∀ s ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => Real.exp (a * t - x * Real.exp t))
        (a * Real.exp (a * s - x * Real.exp s) -
          x * Real.exp ((a + 1) * s - x * Real.exp s)) s := fun s _ => by
    have h1 : HasDerivAt (fun t : ℝ => a * t - x * Real.exp t) (a - x * Real.exp s) s := by
      simpa using ((hasDerivAt_id' s).const_mul a).fun_sub ((Real.hasDerivAt_exp s).const_mul x)
    convert h1.exp using 1
    have hexp : Real.exp (a * s - x * Real.exp s) * Real.exp s =
        Real.exp ((a + 1) * s - x * Real.exp s) := by rw [← Real.exp_add]; congr 1; ring
    rw [mul_sub, mul_left_comm _ x, hexp]; ring
  have hI0 : IntegrableOn (fun s : ℝ => Real.exp (a * s - x * Real.exp s)) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using integrableOn_tailIntegrand 0 a hx
  have hI1 : IntegrableOn (fun s : ℝ => Real.exp ((a + 1) * s - x * Real.exp s)) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using integrableOn_tailIntegrand 0 (a + 1) hx
  have htend : Tendsto (fun s : ℝ => Real.exp (a * s - x * Real.exp s)) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul] using tendsto_tailIntegrand_atTop 0 a hx
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    ((hI0.const_mul a).sub (hI1.const_mul x)) htend
  rw [integral_sub (hI0.const_mul a) (hI1.const_mul x),
    integral_const_mul, integral_const_mul] at hftc
  simpa only [tailMoment, pow_zero, one_mul, mul_zero, Real.exp_zero, mul_one, zero_sub] using hftc

private theorem Gamma_mul_tricomi_re_eq_integral_of_pos {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Real.Gamma a * (tricomiIncompleteGamma a x).re =
      ∫ t in (0 : ℝ)..1, t ^ (a - 1) * Real.exp (-(x * t)) := by
  have hC := tricomiIncompleteGamma_eq_integral (a := (a : ℂ)) (by simpa using ha) (x : ℂ)
  have hΓ : Gamma (a : ℂ) ≠ 0 := by
    rw [Complex.Gamma_ofReal]; exact Complex.ofReal_ne_zero.mpr (Real.Gamma_pos_of_pos ha).ne'
  have hmul : Gamma (a : ℂ) * tricomiIncompleteGamma a x =
      ∫ t in (0 : ℝ)..1, (t : ℂ) ^ ((a : ℂ) - 1) * cexp (-((x : ℂ) * t)) := by
    rw [hC, ← mul_assoc, mul_inv_cancel₀ hΓ, one_mul]
  have hre := congrArg Complex.re hmul
  rw [Complex.Gamma_ofReal, Complex.re_ofReal_mul] at hre
  rw [hre]
  have hcongr : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      ((t : ℝ) : ℂ) ^ ((a : ℂ) - 1) * cexp (-((x : ℂ) * (t : ℝ))) =
        ((t ^ (a - 1) * Real.exp (-(x * t)) : ℝ) : ℂ) := fun t ht => by
    rw [Set.uIcc_of_le zero_le_one] at ht
    rw [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_cpow ht.1]
    push_cast; rfl
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_ofReal, Complex.ofReal_re]

private theorem Gamma_mul_tricomi_re_add_tailMoment_of_pos {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    Real.Gamma a * (tricomiIncompleteGamma a x).re + tailMoment 0 a x =
      x ^ (-a) * Real.Gamma a := by
  have hlow : x ^ a * (Real.Gamma a * (tricomiIncompleteGamma a x).re) =
      ∫ u in Ioc (0 : ℝ) x, u ^ (a - 1) * Real.exp (-u) := by
    rw [Gamma_mul_tricomi_re_eq_integral_of_pos ha x, ← intervalIntegral.integral_const_mul]
    have hcomp := congrArg (x * ·) <| intervalIntegral.integral_comp_mul_left
      (f := fun u : ℝ => u ^ (a - 1) * Real.exp (-u)) (a := 0) (b := 1) hx.ne'
    rw [mul_zero, mul_one, intervalIntegral.integral_of_le hx.le, smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul,
      ← intervalIntegral.integral_const_mul] at hcomp
    rw [← hcomp]
    have hmul : x ^ a = x * x ^ (a - 1) := by
      rw [Real.rpow_sub hx, Real.rpow_one, mul_div_cancel₀ _ hx.ne']
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    rw [Real.mul_rpow hx.le ht.1, hmul]
    ring
  have hInt : IntegrableOn (fun u : ℝ => u ^ (a - 1) * Real.exp (-u)) (Ioi 0) :=
    (Real.GammaIntegral_convergent ha).congr_fun (fun _ _ => mul_comm _ _) measurableSet_Ioi
  have hsplit : (∫ u in Ioc (0 : ℝ) x, u ^ (a - 1) * Real.exp (-u)) +
      (∫ u in Ioi x, u ^ (a - 1) * Real.exp (-u)) = Real.Gamma a := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hInt.mono_set Ioc_subset_Ioi_self) (hInt.mono_set (Ioi_subset_Ioi hx.le)),
      Ioc_union_Ioi_eq_Ioi hx.le, Real.Gamma_eq_integral ha]
    exact setIntegral_congr_fun measurableSet_Ioi fun _ _ => mul_comm _ _
  have htotal : x ^ a * (Real.Gamma a * (tricomiIncompleteGamma a x).re + tailMoment 0 a x) =
      Real.Gamma a := by
    rw [mul_add, hlow, rpow_mul_tailMoment_zero_eq_integral a hx, hsplit]
  have hxpow : x ^ (-a) * x ^ a = 1 := by
    rw [← Real.rpow_add hx, neg_add_cancel, Real.rpow_zero]
  calc Real.Gamma a * (tricomiIncompleteGamma a x).re + tailMoment 0 a x
      = (x ^ (-a) * x ^ a) *
          (Real.Gamma a * (tricomiIncompleteGamma a x).re + tailMoment 0 a x) := by
            rw [hxpow, one_mul]
    _ = x ^ (-a) * Real.Gamma a := by rw [mul_assoc, htotal]

private theorem Gamma_mul_tricomi_re_add_tailMoment {a x : ℝ}
    (ha : ∀ m : ℕ, a ≠ -(m : ℝ)) (hx : 0 < x) :
    Real.Gamma a * (tricomiIncompleteGamma a x).re + tailMoment 0 a x =
      x ^ (-a) * Real.Gamma a := by
  suffices h : ∀ k : ℕ, ∀ b : ℝ, (∀ m : ℕ, b ≠ -(m : ℝ)) → 0 < b + k →
      Real.Gamma b * (tricomiIncompleteGamma b x).re + tailMoment 0 b x =
        x ^ (-b) * Real.Gamma b by
    obtain ⟨k, hk⟩ := exists_nat_gt (-a)
    exact h k a ha (by linarith)
  intro k
  induction k with
  | zero => exact fun b _ hb => Gamma_mul_tricomi_re_add_tailMoment_of_pos (by simpa using hb) hx
  | succ k ih =>
    intro b hb hbk
    have hb0 : b ≠ 0 := by simpa using hb 0
    have hb1 : ∀ m : ℕ, b + 1 ≠ -(m : ℝ) := fun m h => hb (m + 1) (by push_cast; linarith)
    have hstep := ih (b + 1) hb1 (by push_cast at hbk; linarith)
    have htric := congrArg Complex.re
      (tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one (b : ℂ) (x : ℂ))
    have hre1 : (tricomiIncompleteGamma b x).re =
        x * (tricomiIncompleteGamma (b + 1) x).re + Real.exp (-x) / Real.Gamma (b + 1) := by
      have hcast : cexp (-(x : ℂ)) / Gamma ((b : ℂ) + 1) =
          ((Real.exp (-x) / Real.Gamma (b + 1) : ℝ) : ℂ) := by
        push_cast [Complex.ofReal_exp, ← Complex.Gamma_ofReal]; rfl
      rw [Complex.add_re, Complex.re_ofReal_mul, hcast, Complex.ofReal_re] at htric
      simpa using htric
    have hΓ1 : Real.Gamma (b + 1) = b * Real.Gamma b := Real.Gamma_add_one hb0
    have htric_mul : b * (Real.Gamma b * (tricomiIncompleteGamma b x).re) =
        x * (Real.Gamma (b + 1) * (tricomiIncompleteGamma (b + 1) x).re) + Real.exp (-x) := by
      have := congrArg (Real.Gamma (b + 1) * ·) hre1
      rw [mul_add, mul_div_cancel₀ _ (Real.Gamma_ne_zero hb1)] at this
      rw [← mul_assoc, ← hΓ1, this]; ring
    have htail := tailMoment_zero_recurrence b hx
    have hlhs : b * (Real.Gamma b * (tricomiIncompleteGamma b x).re + tailMoment 0 b x) =
        x * (Real.Gamma (b + 1) * (tricomiIncompleteGamma (b + 1) x).re +
          tailMoment 0 (b + 1) x) := by linarith
    have hrhs : x * (x ^ (-(b + 1)) * Real.Gamma (b + 1)) = b * (x ^ (-b) * Real.Gamma b) := by
      rw [hΓ1, neg_add, Real.rpow_add hx, Real.rpow_neg_one]
      have hxinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx.ne'
      calc x * (x ^ (-b) * x⁻¹ * (b * Real.Gamma b))
          = (x * x⁻¹) * (b * (x ^ (-b) * Real.Gamma b)) := by ring
        _ = b * (x ^ (-b) * Real.Gamma b) := by rw [hxinv, one_mul]
    push_cast at hstep
    exact mul_left_cancel₀ hb0 (by rw [hlhs, hstep, hrhs])

private theorem tailMoment_variance_le {a x : ℝ} (ha : a < 0) (hx : 0 < x) :
    (tailMoment 2 a x * tailMoment 0 a x - (tailMoment 1 a x) ^ 2) / (tailMoment 0 a x) ^ 2 ≤
      (a ^ 2)⁻¹ := by
  have hderiv : ∀ s ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => t ^ 2 * Real.exp (a * t - x * Real.exp t))
        (2 * (s ^ 1 * Real.exp (a * s - x * Real.exp s)) +
          a * (s ^ 2 * Real.exp (a * s - x * Real.exp s)) -
          x * (s ^ 2 * Real.exp ((a + 1) * s - x * Real.exp s))) s := fun s _ => by
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
    have h1' : HasDerivAt (fun t : ℝ => a * t - x * Real.exp t) (a - x * Real.exp s) s := by
      simpa using ((hasDerivAt_id' s).const_mul a).fun_sub ((Real.hasDerivAt_exp s).const_mul x)
    convert h1.mul h1'.exp using 1
    have hexp : Real.exp (a * s - x * Real.exp s) * Real.exp s =
        Real.exp ((a + 1) * s - x * Real.exp s) := by rw [← Real.exp_add]; congr 1; ring
    rw [pow_one, mul_sub, mul_sub, mul_left_comm _ x, hexp]
    ring
  have hI1 := (integrableOn_tailIntegrand 1 a hx).const_mul 2
  have hI2 := (integrableOn_tailIntegrand 2 a hx).const_mul a
  have hI3 := (integrableOn_tailIntegrand 2 (a + 1) hx).const_mul x
  have hI12 : IntegrableOn (fun s : ℝ =>
      2 * (s ^ 1 * Real.exp (a * s - x * Real.exp s)) +
        a * (s ^ 2 * Real.exp (a * s - x * Real.exp s))) (Ioi 0) := hI1.add hI2
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (hI12.sub hI3)
    (tendsto_tailIntegrand_atTop 2 a hx)
  rw [integral_sub hI12 hI3, integral_add hI1 hI2,
    integral_const_mul, integral_const_mul, integral_const_mul] at hftc
  have h0 : 2 * tailMoment 1 a x + a * tailMoment 2 a x - x * tailMoment 2 (a + 1) x = 0 := by
    simpa only [tailMoment, zero_pow two_ne_zero, zero_mul, sub_zero] using hftc
  have hle : (-a) * tailMoment 2 a x ≤ 2 * tailMoment 1 a x := by
    linarith [mul_nonneg hx.le (tailMoment_nonneg 2 (a + 1) x)]
  have hI0 : 0 < tailMoment 0 a x := tailMoment_zero_pos a hx
  have hstep : a ^ 2 * (tailMoment 2 a x * tailMoment 0 a x) ≤
      2 * (-a) * tailMoment 1 a x * tailMoment 0 a x := by
    have := mul_le_mul_of_nonneg_left hle (mul_pos (neg_pos.mpr ha) hI0).le
    linarith
  have hsq : a ^ 2 * (tailMoment 2 a x * tailMoment 0 a x - (tailMoment 1 a x) ^ 2) ≤
      (tailMoment 0 a x) ^ 2 := by
    nlinarith [sq_nonneg (tailMoment 0 a x + a * tailMoment 1 a x)]
  rw [div_le_iff₀ (sq_pos_of_pos hI0), inv_mul_eq_div, le_div_iff₀ (sq_pos_of_ne_zero ha.ne)]
  linarith

/-! ### The strictly convex auxiliary function `Φ` on `(−2n, 1 − 2n)` -/

private def paramPhi (x a : ℝ) : ℝ :=
  Real.log (Real.Gamma a) - a * Real.log x - Real.log (tailMoment 0 a x)

private def paramPhiDeriv (x a : ℝ) : ℝ :=
  Real.digamma a - Real.log x - tailMoment 1 a x / tailMoment 0 a x

private def paramPhiDeriv₂ (x a : ℝ) : ℝ :=
  deriv Real.digamma a -
    (tailMoment 2 a x * tailMoment 0 a x - (tailMoment 1 a x) ^ 2) / (tailMoment 0 a x) ^ 2

private theorem hasDerivAt_paramPhi {x a : ℝ} (hx : 0 < x) (ha : ∀ m : ℕ, a ≠ -(m : ℝ)) :
    HasDerivAt (paramPhi x) (paramPhiDeriv x a) a := by
  have h1 : HasDerivAt (fun b : ℝ => Real.log (Real.Gamma b)) (Real.digamma a) a :=
    Real.hasDerivAt_log_Gamma ha
  have h2 : HasDerivAt (fun b : ℝ => b * Real.log x) (Real.log x) a := by
    simpa using (hasDerivAt_id' a).mul_const (Real.log x)
  have h3 : HasDerivAt (fun b : ℝ => Real.log (tailMoment 0 b x))
      (tailMoment 1 a x / tailMoment 0 a x) a :=
    (hasDerivAt_tailMoment 0 a hx).log (tailMoment_zero_pos a hx).ne'
  exact (h1.fun_sub h2).fun_sub h3

private theorem hasDerivAt_paramPhiDeriv {x a : ℝ} (hx : 0 < x)
    (ha : ∀ m : ℕ, a ≠ -(m : ℝ)) :
    HasDerivAt (paramPhiDeriv x) (paramPhiDeriv₂ x a) a := by
  have h1 : HasDerivAt Real.digamma (deriv Real.digamma a) a :=
    (Real.differentiableAt_digamma ha).hasDerivAt
  have h2 : HasDerivAt (fun b : ℝ => tailMoment 1 b x / tailMoment 0 b x)
      ((tailMoment 2 a x * tailMoment 0 a x - (tailMoment 1 a x) ^ 2) /
        (tailMoment 0 a x) ^ 2) a := by
    convert (hasDerivAt_tailMoment 1 a hx).div (hasDerivAt_tailMoment 0 a hx)
      (tailMoment_zero_pos a hx).ne' using 1
    ring
  exact (h1.sub_const (Real.log x)).fun_sub h2

private theorem paramPhiDeriv₂_pos {n : ℕ} (hn : 1 ≤ n) {x a : ℝ} (hx : 0 < x)
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) : 0 < paramPhiDeriv₂ x a := by
  have ha' := mem_Ioo_neg_two_mul_ne_neg_nat hn ha
  have hdig := Real.deriv_digamma_apply_add_nat ha' (2 * n)
  have hnn : 0 ≤ deriv Real.digamma (a + (2 * n : ℕ)) :=
    Real.deriv_digamma_nonneg (by push_cast; linarith [ha.1])
  have h01 : ({0, 1} : Finset ℕ) ⊆ range (2 * n) := fun k hk => by
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_range] at hk ⊢; omega
  have hsum :
      (a ^ 2)⁻¹ + ((a + 1) ^ 2)⁻¹ ≤ ∑ k ∈ range (2 * n), ((a + k) ^ 2)⁻¹ := by
    have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k : ℕ => ((a + k) ^ 2)⁻¹)
      h01 fun _ _ _ => by positivity
    simpa [Finset.sum_pair Nat.zero_ne_one] using hle
  have hneg : a < 0 := by linarith [ha.2, (Nat.one_le_cast.mpr hn : (1 : ℝ) ≤ n)]
  have hvar := tailMoment_variance_le hneg hx
  have ha1 : a + 1 ≠ 0 := fun h => ha' 1 (by push_cast; linarith)
  have hpos1 : 0 < ((a + 1) ^ 2)⁻¹ := by positivity
  rw [paramPhiDeriv₂]
  linarith

private theorem tricomi_re_eq_rpow_mul_one_sub_exp_neg_paramPhi {n : ℕ} (hn : 1 ≤ n)
    {x a : ℝ} (hx : 0 < x) (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) :
    (tricomiIncompleteGamma a x).re = x ^ (-a) * (1 - Real.exp (-paramPhi x a)) := by
  have hΓ : 0 < Real.Gamma a := Gamma_pos_of_mem_Ioo_neg_two_mul hn ha
  have hV : 0 < tailMoment 0 a x := tailMoment_zero_pos a hx
  have hid := Gamma_mul_tricomi_re_add_tailMoment (mem_Ioo_neg_two_mul_ne_neg_nat hn ha) hx
  have hexp : Real.exp (-paramPhi x a) = x ^ a * tailMoment 0 a x / Real.Gamma a := by
    have hrew : -paramPhi x a = a * Real.log x + Real.log (tailMoment 0 a x) -
        Real.log (Real.Gamma a) := by rw [paramPhi]; ring
    rw [hrew, Real.exp_sub, Real.exp_add, Real.exp_log hV, Real.exp_log hΓ,
      Real.rpow_def_of_pos hx, mul_comm a]
  have hxpow : x ^ (-a) * x ^ a = 1 := by
    rw [← Real.rpow_add hx, neg_add_cancel, Real.rpow_zero]
  rw [hexp, mul_sub, mul_one, mul_div_assoc', ← mul_assoc, hxpow, one_mul]
  exact mul_left_cancel₀ hΓ.ne' (by rw [mul_sub, mul_div_cancel₀ _ hΓ.ne']; linarith)

private theorem tricomi_eq_zero_iff_paramPhi_eq_zero {n : ℕ} (hn : 1 ≤ n)
    {x a : ℝ} (hx : 0 < x) (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) :
    tricomiIncompleteGamma a x = 0 ↔ paramPhi x a = 0 := by
  rw [tricomiIncompleteGamma_ofReal_eq_zero_iff,
    tricomi_re_eq_rpow_mul_one_sub_exp_neg_paramPhi hn hx ha,
    mul_eq_zero, or_iff_right (Real.rpow_pos_of_pos hx _).ne', sub_eq_zero, eq_comm,
    Real.exp_eq_one_iff, neg_eq_zero]

private theorem hasDerivAt_tricomi_re_eq {n : ℕ} (hn : 1 ≤ n) {x a : ℝ} (hx : 0 < x)
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) :
    HasDerivAt (fun b : ℝ => (tricomiIncompleteGamma b x).re)
      ((-Real.log x * x ^ (-a)) * (1 - Real.exp (-paramPhi x a)) +
        x ^ (-a) * (Real.exp (-paramPhi x a) * paramPhiDeriv x a)) a := by
  have hEq : (fun b : ℝ => (tricomiIncompleteGamma b x).re) =ᶠ[𝓝 a]
      fun b : ℝ => x ^ (-b) * (1 - Real.exp (-paramPhi x b)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
    exact tricomi_re_eq_rpow_mul_one_sub_exp_neg_paramPhi hn hx hb
  have hpow : HasDerivAt (fun b : ℝ => x ^ (-b)) (-Real.log x * x ^ (-a)) a := by
    simpa only [mul_neg_one, neg_mul] using (hasDerivAt_neg a).const_rpow hx
  have hphi := hasDerivAt_paramPhi hx (mem_Ioo_neg_two_mul_ne_neg_nat hn ha)
  have hexp : HasDerivAt (fun b : ℝ => 1 - Real.exp (-paramPhi x b))
      (Real.exp (-paramPhi x a) * paramPhiDeriv x a) a := by
    convert (hphi.fun_neg.exp).const_sub 1 using 1; ring
  exact (hpow.mul hexp).congr_of_eventuallyEq hEq

private theorem deriv_tricomi_re_at_zero {n : ℕ} (hn : 1 ≤ n) {x a : ℝ} (hx : 0 < x)
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) (hphi : paramPhi x a = 0) :
    deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a = x ^ (-a) * paramPhiDeriv x a := by
  rw [(hasDerivAt_tricomi_re_eq hn hx ha).deriv, hphi, neg_zero, Real.exp_zero, sub_self,
    mul_zero, zero_add, one_mul]

private theorem deriv₂_tricomi_re_at_double_zero {n : ℕ} (hn : 1 ≤ n) {x a : ℝ} (hx : 0 < x)
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)))
    (hphi : paramPhi x a = 0) (hphi' : paramPhiDeriv x a = 0) :
    deriv (deriv fun b : ℝ => (tricomiIncompleteGamma b x).re) a =
      x ^ (-a) * paramPhiDeriv₂ x a := by
  have hEq : deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) =ᶠ[𝓝 a]
      fun b : ℝ => (-Real.log x * x ^ (-b)) * (1 - Real.exp (-paramPhi x b)) +
        x ^ (-b) * (Real.exp (-paramPhi x b) * paramPhiDeriv x b) := by
    filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
    exact (hasDerivAt_tricomi_re_eq hn hx hb).deriv
  have ha' := mem_Ioo_neg_two_mul_ne_neg_nat hn ha
  have hpow : HasDerivAt (fun b : ℝ => x ^ (-b)) (-Real.log x * x ^ (-a)) a := by
    simpa only [mul_neg_one, neg_mul] using (hasDerivAt_neg a).const_rpow hx
  have hphi_d := hasDerivAt_paramPhi hx ha'
  have hphi'_d := hasDerivAt_paramPhiDeriv hx ha'
  have hterm1 :
      HasDerivAt (fun b : ℝ => (-Real.log x * x ^ (-b)) * (1 - Real.exp (-paramPhi x b)))
        0 a := by
    convert (hpow.const_mul (-Real.log x)).mul ((hphi_d.fun_neg.exp).const_sub 1) using 1
    simp [hphi, hphi']
  have hterm2 : HasDerivAt
      (fun b : ℝ => x ^ (-b) * (Real.exp (-paramPhi x b) * paramPhiDeriv x b))
      (x ^ (-a) * paramPhiDeriv₂ x a) a := by
    convert hpow.mul ((hphi_d.fun_neg.exp).mul hphi'_d) using 1
    simp [hphi, hphi']
  simpa only [zero_add] using ((hterm1.fun_add hterm2).congr_of_eventuallyEq hEq).deriv

private theorem tendsto_paramPhi_of_pole {x a₀ : ℝ} (hx : 0 < x) {s : Set ℝ}
    (hΓ0 : Real.Gamma a₀ = 0) (hpos : ∀ᶠ a in 𝓝[s] a₀, 0 < Real.Gamma a) :
    Tendsto (paramPhi x) (𝓝[s] a₀) atTop := by
  have hinv_cont : Tendsto (fun a : ℝ => (Real.Gamma a)⁻¹) (𝓝[s] a₀) (𝓝 0) := by
    have h0 : (Real.Gamma a₀)⁻¹ = 0 := by rw [hΓ0, inv_zero]
    rw [← h0]
    exact Real.continuous_inv_Gamma.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hinv_pos : Tendsto (fun a : ℝ => (Real.Gamma a)⁻¹) (𝓝[s] a₀) (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hinv_cont
      (hpos.mono fun _ h => inv_pos.mpr h)
  have hΓ_top : Tendsto Real.Gamma (𝓝[s] a₀) atTop :=
    (tendsto_inv_nhdsGT_zero.comp hinv_pos).congr fun a => inv_inv (Real.Gamma a)
  have hcont : ContinuousAt (fun a : ℝ => a * Real.log x + Real.log (tailMoment 0 a x)) a₀ :=
    (continuous_id.mul continuous_const).continuousAt.add
      ((hasDerivAt_tailMoment 0 a₀ hx).continuousAt.log (tailMoment_zero_pos a₀ hx).ne')
  exact ((Real.tendsto_log_atTop.comp hΓ_top).atTop_add
    (hcont.neg.tendsto.mono_left nhdsWithin_le_nhds)).congr fun a => by
      simp [paramPhi]; ring

private theorem tendsto_paramPhi_left {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    Tendsto (paramPhi x) (𝓝[>] (-2 * (n : ℝ))) atTop :=
  tendsto_paramPhi_of_pole hx
    (by
      have hcast : -2 * (n : ℝ) = -((2 * n : ℕ) : ℝ) := by push_cast; ring
      rw [hcast, Real.Gamma_neg_nat_eq_zero])
    (by
      filter_upwards [Ioo_mem_nhdsGT (by linarith : -2 * (n : ℝ) < 1 - 2 * (n : ℝ))] with a ha
      exact Gamma_pos_of_mem_Ioo_neg_two_mul hn ha)

private theorem tendsto_paramPhi_right {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    Tendsto (paramPhi x) (𝓝[<] (1 - 2 * (n : ℝ))) atTop :=
  tendsto_paramPhi_of_pole hx
    (by
      have hcast : 1 - 2 * (n : ℝ) = -((2 * n - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hcast, Real.Gamma_neg_nat_eq_zero])
    (by
      filter_upwards [Ioo_mem_nhdsLT (by linarith : -2 * (n : ℝ) < 1 - 2 * (n : ℝ))] with a ha
      exact Gamma_pos_of_mem_Ioo_neg_two_mul hn ha)

/-! ### Minimizer, monotonicity, continuity, and threshold `x*_n` -/

private theorem exists_compact_trap {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) (B : ℝ) :
    ∃ p q : ℝ, -2 * (n : ℝ) < p ∧ p < q ∧ q < 1 - 2 * (n : ℝ) ∧
      ∀ a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)), a ∉ Icc p q → B < paramPhi x a := by
  let L : ℝ := -2 * (n : ℝ)
  let R : ℝ := 1 - 2 * (n : ℝ)
  have hL := tendsto_atTop.mp (tendsto_paramPhi_left hn hx) (B + 1)
  have hR := tendsto_atTop.mp (tendsto_paramPhi_right hn hx) (B + 1)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hL hR
  obtain ⟨δ₁, hδ₁, hL⟩ := hL
  obtain ⟨δ₂, hδ₂, hR⟩ := hR
  let p : ℝ := L + min (δ₁ / 2) (1 / 4)
  let q : ℝ := R - min (δ₂ / 2) (1 / 4)
  have hp_gt : L < p := by linarith [lt_min (half_pos hδ₁) (by norm_num : (0 : ℝ) < 1 / 4)]
  have hq_lt : q < R := by linarith [lt_min (half_pos hδ₂) (by norm_num : (0 : ℝ) < 1 / 4)]
  have hpq : p < q := by
    linarith [min_le_right (δ₁ / 2) (1 / 4), min_le_right (δ₂ / 2) (1 / 4)]
  refine ⟨p, q, hp_gt, hpq, hq_lt, fun a ha hnot => ?_⟩
  rcases (by by_contra h; push Not at h; exact hnot ⟨h.1, h.2⟩ : a < p ∨ q < a) with hlt | hgt
  · have hdist : dist a L < δ₁ := by
      rw [Real.dist_eq, abs_of_pos (by linarith [ha.1])]
      linarith [min_le_left (δ₁ / 2) (1 / 4)]
    linarith [hL hdist ha.1]
  · have hdist : dist a R < δ₂ := by
      rw [Real.dist_eq, abs_of_neg (by linarith [ha.2])]
      linarith [min_le_left (δ₂ / 2) (1 / 4)]
    linarith [hR hdist ha.2]

private theorem exists_isMinOn_paramPhi {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    ∃ a₀ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)),
      IsMinOn (paramPhi x) (Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) a₀ := by
  let I := Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))
  let c : ℝ := 1 / 2 - 2 * (n : ℝ)
  have hcI : c ∈ I := by dsimp only [c, I]; exact ⟨by linarith, by linarith⟩
  obtain ⟨p, q, hp, hpq, hq, htrap⟩ := exists_compact_trap hn hx (paramPhi x c)
  have hsub : Icc p q ⊆ I := fun _ ha => ⟨lt_of_lt_of_le hp ha.1, lt_of_le_of_lt ha.2 hq⟩
  have hcont : ContinuousOn (paramPhi x) (Icc p q) := fun _ ha =>
    (hasDerivAt_paramPhi hx (mem_Ioo_neg_two_mul_ne_neg_nat hn (hsub ha)))
      |>.continuousAt.continuousWithinAt
  obtain ⟨a₀, ha₀_icc, ha₀_min⟩ :=
    isCompact_Icc.exists_isMinOn ⟨p, left_mem_Icc.mpr hpq.le⟩ hcont
  refine ⟨a₀, hsub ha₀_icc, fun a ha => ?_⟩
  by_cases ha_icc : a ∈ Icc p q
  · exact ha₀_min ha_icc
  · have hc_le : paramPhi x a₀ ≤ paramPhi x c := by
      by_cases hc_icc : c ∈ Icc p q
      · exact ha₀_min hc_icc
      · linarith [htrap c hcI hc_icc]
    exact hc_le.trans (htrap a ha ha_icc).le

private theorem strictMonoOn_paramPhiDeriv {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    StrictMonoOn (paramPhiDeriv x) (Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) :=
  strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    (fun _ ha => (hasDerivAt_paramPhiDeriv hx (mem_Ioo_neg_two_mul_ne_neg_nat hn ha))
      |>.continuousAt.continuousWithinAt)
    fun _ ha => by
      have haI := interior_subset ha
      rw [(hasDerivAt_paramPhiDeriv hx (mem_Ioo_neg_two_mul_ne_neg_nat hn haI)).deriv]
      exact paramPhiDeriv₂_pos hn hx haI

private theorem paramPhi_strictAntiOn_left {n : ℕ} (hn : 1 ≤ n) {x a₀ : ℝ} (hx : 0 < x)
    (ha₀ : a₀ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) (hd0 : paramPhiDeriv x a₀ = 0) :
    StrictAntiOn (paramPhi x) (Ioc (-2 * (n : ℝ)) a₀) := by
  have hmono := strictMonoOn_paramPhiDeriv hn hx
  refine strictAntiOn_of_deriv_neg (convex_Ioc _ _)
    (fun _ ha => (hasDerivAt_paramPhi hx (mem_Ioo_neg_two_mul_ne_neg_nat hn
      ⟨ha.1, lt_of_le_of_lt ha.2 ha₀.2⟩)).continuousAt.continuousWithinAt) fun a ha => ?_
  rw [interior_Ioc] at ha
  have haI : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) := ⟨ha.1, lt_trans ha.2 ha₀.2⟩
  rw [(hasDerivAt_paramPhi hx (mem_Ioo_neg_two_mul_ne_neg_nat hn haI)).deriv]
  linarith [hmono haI ha₀ ha.2]

private theorem paramPhi_strictMonoOn_right {n : ℕ} (hn : 1 ≤ n) {x a₀ : ℝ} (hx : 0 < x)
    (ha₀ : a₀ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) (hd0 : paramPhiDeriv x a₀ = 0) :
    StrictMonoOn (paramPhi x) (Ico a₀ (1 - 2 * (n : ℝ))) := by
  have hmono := strictMonoOn_paramPhiDeriv hn hx
  refine strictMonoOn_of_deriv_pos (convex_Ico _ _)
    (fun _ ha => (hasDerivAt_paramPhi hx (mem_Ioo_neg_two_mul_ne_neg_nat hn
      ⟨lt_of_lt_of_le ha₀.1 ha.1, ha.2⟩)).continuousAt.continuousWithinAt) fun a ha => ?_
  rw [interior_Ico] at ha
  have haI : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) := ⟨lt_trans ha₀.1 ha.1, ha.2⟩
  rw [(hasDerivAt_paramPhi hx (mem_Ioo_neg_two_mul_ne_neg_nat hn haI)).deriv]
  linarith [hmono ha₀ haI ha.1]

private theorem paramPhi_strictMono_right (a : ℝ) :
    StrictMonoOn (fun x : ℝ => paramPhi x a) (Ioi 0) := by
  intro x₁ hx₁ x₂ hx₂ hlt
  have h2 : 0 < x₂ ^ a * tailMoment 0 a x₂ :=
    mul_pos (Real.rpow_pos_of_pos hx₂ a) (tailMoment_zero_pos a hx₂)
  have hgap : 0 < ∫ u in Ioc x₁ x₂, u ^ (a - 1) * Real.exp (-u) := by
    have hcont : ContinuousOn (fun u : ℝ => u ^ (a - 1) * Real.exp (-u)) (Icc x₁ x₂) :=
      ContinuousOn.mul (fun u hu => (Real.continuousAt_rpow_const u (a - 1)
        (Or.inl (lt_of_lt_of_le hx₁ hu.1).ne')).continuousWithinAt)
        (Continuous.continuousOn (by fun_prop))
    rw [setIntegral_pos_iff_support_of_nonneg_ae ?_
      (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
    · have hsub : Ioc x₁ x₂ ⊆
          Function.support (fun u : ℝ => u ^ (a - 1) * Real.exp (-u)) ∩ Ioc x₁ x₂ :=
        fun _ hu => ⟨mul_ne_zero (Real.rpow_pos_of_pos (lt_trans hx₁ hu.1) _).ne'
          (Real.exp_pos _).ne', hu⟩
      calc 0 < volume (Ioc x₁ x₂) := by
            rw [Real.volume_Ioc]; exact ENNReal.ofReal_pos.mpr (by linarith)
        _ ≤ volume (Function.support (fun u : ℝ => u ^ (a - 1) * Real.exp (-u)) ∩
              Ioc x₁ x₂) := measure_mono hsub
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with _ hu
      exact mul_nonneg (Real.rpow_nonneg (lt_trans hx₁ hu.1).le _) (Real.exp_pos _).le
  have hsplit : x₁ ^ a * tailMoment 0 a x₁ =
      (∫ u in Ioc x₁ x₂, u ^ (a - 1) * Real.exp (-u)) + x₂ ^ a * tailMoment 0 a x₂ := by
    rw [rpow_mul_tailMoment_zero_eq_integral a hx₁, rpow_mul_tailMoment_zero_eq_integral a hx₂]
    have hInt := TauCeti.integrableOn_rpow_mul_exp_neg_Ioi (a - 1) hx₁
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hInt.mono_set Ioc_subset_Ioi_self) (hInt.mono_set (Ioi_subset_Ioi hlt.le)),
      Ioc_union_Ioi_eq_Ioi hlt.le]
  have hlog := Real.log_lt_log h2
    (by linarith : x₂ ^ a * tailMoment 0 a x₂ < x₁ ^ a * tailMoment 0 a x₁)
  have hrew : ∀ x > 0, a * Real.log x + Real.log (tailMoment 0 a x) =
      Real.log (x ^ a * tailMoment 0 a x) := fun x hx => by
    rw [Real.log_mul (Real.rpow_pos_of_pos hx a).ne' (tailMoment_zero_pos a hx).ne',
      Real.log_rpow hx]
  have h1' := hrew x₁ hx₁
  have h2' := hrew x₂ hx₂
  unfold paramPhi
  linarith

private def minParamPhi (n : ℕ) (x : ℝ) : ℝ :=
  if h : 1 ≤ n ∧ 0 < x then paramPhi x (exists_isMinOn_paramPhi h.1 h.2).choose else 0

private theorem minParamPhi_spec {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    ∃ a₀ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)),
      paramPhi x a₀ = minParamPhi n x ∧
      IsMinOn (paramPhi x) (Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) a₀ ∧
      paramPhiDeriv x a₀ = 0 := by
  let h := exists_isMinOn_paramPhi hn hx
  refine ⟨h.choose, h.choose_spec.1, by simp [minParamPhi, hn, hx], h.choose_spec.2, ?_⟩
  exact (h.choose_spec.2.isLocalMin (isOpen_Ioo.mem_nhds h.choose_spec.1)).hasDerivAt_eq_zero
    (hasDerivAt_paramPhi hx (mem_Ioo_neg_two_mul_ne_neg_nat hn h.choose_spec.1))

private theorem strictMonoOn_minParamPhi {n : ℕ} (hn : 1 ≤ n) :
    StrictMonoOn (minParamPhi n) (Ioi 0) := by
  intro x₁ hx₁ x₂ hx₂ hlt
  obtain ⟨a₁, _, hval₁, hmin₁, _⟩ := minParamPhi_spec hn hx₁
  obtain ⟨a₂, ha₂I, hval₂, _, _⟩ := minParamPhi_spec hn hx₂
  calc minParamPhi n x₁
      = paramPhi x₁ a₁ := hval₁.symm
    _ ≤ paramPhi x₁ a₂ := hmin₁ ha₂I
    _ < paramPhi x₂ a₂ := paramPhi_strictMono_right a₂ hx₁ hx₂ hlt
    _ = minParamPhi n x₂ := hval₂

private theorem continuousOn_paramPhi_prod {n : ℕ} (hn : 1 ≤ n) {p q x₀ : ℝ}
    (hx₀ : 0 < x₀) (hsub : Icc p q ⊆ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) :
    ContinuousOn (fun z : ℝ × ℝ => paramPhi z.2 z.1)
      (Icc p q ×ˢ Icc (x₀ / 2) (2 * x₀)) := by
  intro ⟨a, x⟩ ⟨ha, hx⟩
  have haI := hsub ha
  have hxpos : 0 < x := lt_of_lt_of_le (half_pos hx₀) hx.1
  have hΓ : ContinuousAt (fun z : ℝ × ℝ => Real.log (Real.Gamma z.1)) (a, x) :=
    ((Real.differentiableAt_Gamma (mem_Ioo_neg_two_mul_ne_neg_nat hn haI)).continuousAt.log
      (Gamma_pos_of_mem_Ioo_neg_two_mul hn haI).ne').comp continuous_fst.continuousAt
  have hlogx : ContinuousAt (fun z : ℝ × ℝ => z.1 * Real.log z.2) (a, x) :=
    continuous_fst.continuousAt.mul (continuous_snd.continuousAt.log hxpos.ne')
  have hV : ContinuousAt (fun z : ℝ × ℝ => Real.log (tailMoment 0 z.1 z.2)) (a, x) :=
    (continuousAt_tailMoment_zero a hxpos).log (tailMoment_zero_pos a hxpos).ne'
  exact ((hΓ.sub hlogx).sub hV).continuousWithinAt

private theorem continuousOn_minParamPhi {n : ℕ} (hn : 1 ≤ n) :
    ContinuousOn (minParamPhi n) (Ioi 0) := by
  intro x₀ hx₀
  have hx₀_pos : 0 < x₀ := hx₀
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨p, q, hp, _, hq, htrap⟩ :=
    exists_compact_trap hn (half_pos hx₀_pos) (minParamPhi n (2 * x₀))
  have hsub : Icc p q ⊆ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) :=
    fun _ ha => ⟨lt_of_lt_of_le hp ha.1, lt_of_le_of_lt ha.2 hq⟩
  have huc := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
    (continuousOn_paramPhi_prod hn hx₀_pos hsub)
  obtain ⟨δ, hδ, hδ_unif⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  refine ⟨min δ (x₀ / 2), lt_min hδ (half_pos hx₀_pos), fun x hx hdist => ?_⟩
  have hx_mem : x ∈ Icc (x₀ / 2) (2 * x₀) := by
    have h1 := abs_lt.mp (by rw [← Real.dist_eq]; exact lt_of_lt_of_le hdist (min_le_right _ _))
    exact ⟨by linarith, by linarith⟩
  have hx₀_mem : x₀ ∈ Icc (x₀ / 2) (2 * x₀) := ⟨by linarith, by linarith⟩
  have htrap_min : ∀ y ∈ Icc (x₀ / 2) (2 * x₀),
      ∀ a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)),
        paramPhi y a = minParamPhi n y → a ∈ Icc p q := fun y hy a ha hval => by
    by_contra hnot
    have h1 := htrap a ha hnot
    have hypos : 0 < y := lt_of_lt_of_le (half_pos hx₀_pos) hy.1
    have h2 := (paramPhi_strictMono_right a).monotoneOn (half_pos hx₀_pos) hypos hy.1
    have h3 := (strictMonoOn_minParamPhi hn).monotoneOn hypos (mul_pos two_pos hx₀_pos) hy.2
    linarith
  obtain ⟨a₀, ha₀I, hval₀, hmin₀, _⟩ := minParamPhi_spec hn hx₀_pos
  obtain ⟨a, haI, hval, hmin, _⟩ := minParamPhi_spec hn hx
  have hclose : ∀ b ∈ Icc p q, |paramPhi x b - paramPhi x₀ b| < ε := fun b hb => by
    have := hδ_unif (b, x) ⟨hb, hx_mem⟩ (b, x₀) ⟨hb, hx₀_mem⟩ (by
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
      exact lt_of_lt_of_le hdist (min_le_left _ _))
    rwa [Real.dist_eq] at this
  have hU := (abs_lt.mp (hclose a₀ (htrap_min x₀ hx₀_mem a₀ ha₀I hval₀))).2
  have hL := (abs_lt.mp (hclose a (htrap_min x hx_mem a haI hval))).1
  have hle1 : minParamPhi n x ≤ paramPhi x a₀ := hval ▸ hmin ha₀I
  have hle2 : minParamPhi n x₀ ≤ paramPhi x₀ a := hval₀ ▸ hmin₀ haI
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩

private theorem rpow_mul_tailMoment_ge {a x : ℝ} (ha : a < 0) (hx : x ∈ Ioo (0 : ℝ) 1) :
    Real.exp (-1) * ((x ^ a - 1) / (-a)) ≤ x ^ a * tailMoment 0 a x := by
  rw [rpow_mul_tailMoment_zero_eq_integral a hx.1]
  have hInt := TauCeti.integrableOn_rpow_mul_exp_neg_Ioi (a - 1) hx.1
  have h1 : ∫ u in Ioc x 1, u ^ (a - 1) * Real.exp (-u) ≤
      ∫ u in Ioi x, u ^ (a - 1) * Real.exp (-u) :=
    setIntegral_mono_set hInt
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with _ hu
          exact mul_nonneg (Real.rpow_nonneg (lt_trans hx.1 hu.out).le _) (Real.exp_pos _).le)
      (Eventually.of_forall Ioc_subset_Ioi_self)
  have hint_rpow : IntegrableOn (fun u : ℝ => u ^ (a - 1)) (Ioc x 1) :=
    (ContinuousOn.integrableOn_Icc fun u hu => (Real.continuousAt_rpow_const u (a - 1)
      (Or.inl (lt_of_lt_of_le hx.1 hu.1).ne')).continuousWithinAt).mono_set Ioc_subset_Icc_self
  have h2 : ∫ u in Ioc x 1, Real.exp (-1) * u ^ (a - 1) ≤
      ∫ u in Ioc x 1, u ^ (a - 1) * Real.exp (-u) :=
    setIntegral_mono_on (hint_rpow.const_mul _) (hInt.mono_set Ioc_subset_Ioi_self)
      measurableSet_Ioc fun _ hu => by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hu.2]))
          (Real.rpow_nonneg (lt_trans hx.1 hu.1).le _)
  have h3 : ∫ u in Ioc x 1, Real.exp (-1) * u ^ (a - 1) =
      Real.exp (-1) * ((x ^ a - 1) / (-a)) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hx.2.le,
      integral_rpow (Or.inr ⟨by linarith, fun h0 => by
        rw [uIcc_of_le hx.2.le] at h0; linarith [h0.1, hx.1]⟩)]
    rw [sub_add_cancel, Real.one_rpow]
    congr 1; field_simp [ha.ne]; ring
  linarith

private theorem exists_minParamPhi_neg {n : ℕ} (hn : 1 ≤ n) :
    ∃ x : ℝ, 0 < x ∧ minParamPhi n x < 0 := by
  let a₀ : ℝ := 1 / 2 - 2 * (n : ℝ)
  have ha₀I : a₀ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) := by
    dsimp only [a₀]; exact ⟨by linarith, by linarith⟩
  have ha₀_neg : a₀ < 0 := by
    dsimp only [a₀]; linarith [(Nat.one_le_cast.mpr hn : (1 : ℝ) ≤ n)]
  have htend :
      Tendsto (fun x : ℝ => Real.exp (-1) * ((x ^ a₀ - 1) / (-a₀))) (𝓝[>] 0) atTop :=
    (((tendsto_rpow_neg_nhdsGT_zero ha₀_neg).atTop_add
      (tendsto_const_nhds (x := (-1 : ℝ)))).atTop_mul_const
      (inv_pos.mpr (neg_pos.mpr ha₀_neg))).const_mul_atTop (Real.exp_pos _) |>.congr fun _ => by
        ring
  obtain ⟨x, hbig, hx⟩ :=
    ((tendsto_atTop.mp htend (Real.Gamma a₀ + 1)).and (Ioo_mem_nhdsGT zero_lt_one)).exists
  refine ⟨x, hx.1, ?_⟩
  obtain ⟨_, _, hval, hmin, _⟩ := minParamPhi_spec hn hx.1
  have hlt_tail : Real.Gamma a₀ < x ^ a₀ * tailMoment 0 a₀ x := by
    linarith [rpow_mul_tailMoment_ge ha₀_neg hx]
  have hlog := Real.log_lt_log (Gamma_pos_of_mem_Ioo_neg_two_mul hn ha₀I) hlt_tail
  rw [Real.log_mul (Real.rpow_pos_of_pos hx.1 a₀).ne' (tailMoment_zero_pos a₀ hx.1).ne',
    Real.log_rpow hx.1] at hlog
  have hmin_le : minParamPhi n x ≤ paramPhi x a₀ := hval ▸ hmin ha₀I
  rw [paramPhi] at hmin_le
  linarith

private theorem exists_minParamPhi_pos {n : ℕ} (hn : 1 ≤ n) :
    ∃ x : ℝ, 0 < x ∧ 0 < minParamPhi n x := by
  let x : ℝ := max 1 (1 - Real.log (Real.pi / ((2 * n)! : ℝ)))
  have hx1 : 1 ≤ x := le_max_left _ _
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  refine ⟨x, hx, ?_⟩
  obtain ⟨a₀, ha₀I, hval₀, _, _⟩ := minParamPhi_spec hn hx
  have htail_le : x ^ a₀ * tailMoment 0 a₀ x ≤ Real.exp (-x) := by
    rw [rpow_mul_tailMoment_zero_eq_integral a₀ hx, ← integral_exp_neg_Ioi x]
    refine setIntegral_mono_on (TauCeti.integrableOn_rpow_mul_exp_neg_Ioi (a₀ - 1) hx)
      (integrableOn_exp_neg_Ioi x) measurableSet_Ioi fun u hu => ?_
    have ha1 : a₀ - 1 ≤ 0 := by linarith [ha₀I.2, (Nat.one_le_cast.mpr hn : (1 : ℝ) ≤ n)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (Real.rpow_le_one_of_one_le_of_nonpos (le_trans hx1 hu.out.le) ha1) (Real.exp_pos _).le
  have hlog_tail : a₀ * Real.log x + Real.log (tailMoment 0 a₀ x) ≤ -x := by
    have hlog := Real.log_le_log
      (mul_pos (Real.rpow_pos_of_pos hx a₀) (tailMoment_zero_pos a₀ hx)) htail_le
    rwa [Real.log_mul (Real.rpow_pos_of_pos hx a₀).ne' (tailMoment_zero_pos a₀ hx).ne',
      Real.log_rpow hx, Real.log_exp] at hlog
  have hlog_Γ : Real.log (Real.pi / ((2 * n)! : ℝ)) ≤ Real.log (Real.Gamma a₀) :=
    Real.log_le_log (by positivity) (pi_div_factorial_le_Gamma_of_evenBand hn ha₀I)
  have hbig : 1 - Real.log (Real.pi / ((2 * n)! : ℝ)) ≤ x := le_max_right _ _
  rw [← hval₀, paramPhi]
  linarith

private theorem paramPhi_zeros_of_min_neg {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x)
    (hmin_neg : minParamPhi n x < 0) :
    ∃ a₁ a₂ : ℝ, a₁ < a₂ ∧
      {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
        tricomiIncompleteGamma a x = 0} = {a₁, a₂} ∧
      deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₁ ≠ 0 ∧
      deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₂ ≠ 0 := by
  let I := Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))
  obtain ⟨a₀, ha₀I, hval₀, _, hd₀⟩ := minParamPhi_spec hn hx
  have hphi₀ : paramPhi x a₀ < 0 := hval₀.trans_lt hmin_neg
  have hcontPhi : ContinuousOn (paramPhi x) I := fun _ hb =>
    (hasDerivAt_paramPhi hx (mem_Ioo_neg_two_mul_ne_neg_nat hn hb)).continuousAt.continuousWithinAt
  obtain ⟨c₁, hc₁_ge, hc₁⟩ :=
    ((tendsto_atTop.mp (tendsto_paramPhi_left hn hx) 1).and (Ioo_mem_nhdsGT ha₀I.1)).exists
  obtain ⟨a₁, ha₁_icc, ha₁_phi⟩ := intermediate_value_Icc' hc₁.2.le
    (hcontPhi.mono fun _ hb => ⟨lt_of_lt_of_le hc₁.1 hb.1, lt_of_le_of_lt hb.2 ha₀I.2⟩)
    ⟨hphi₀.le, by linarith⟩
  have ha₁_lt : a₁ < a₀ := lt_of_le_of_ne ha₁_icc.2 fun h => by rw [h] at ha₁_phi; linarith
  have ha₁I : a₁ ∈ I := ⟨lt_of_lt_of_le hc₁.1 ha₁_icc.1, lt_trans ha₁_lt ha₀I.2⟩
  obtain ⟨c₂, hc₂_ge, hc₂⟩ :=
    ((tendsto_atTop.mp (tendsto_paramPhi_right hn hx) 1).and (Ioo_mem_nhdsLT ha₀I.2)).exists
  obtain ⟨a₂, ha₂_icc, ha₂_phi⟩ := intermediate_value_Icc hc₂.1.le
    (hcontPhi.mono fun _ hb => ⟨lt_of_lt_of_le ha₀I.1 hb.1, lt_of_le_of_lt hb.2 hc₂.2⟩)
    ⟨hphi₀.le, by linarith⟩
  have ha₂_gt : a₀ < a₂ := lt_of_le_of_ne ha₂_icc.1 fun h => by rw [← h] at ha₂_phi; linarith
  have ha₂I : a₂ ∈ I := ⟨lt_trans ha₀I.1 ha₂_gt, lt_of_le_of_lt ha₂_icc.2 hc₂.2⟩
  refine ⟨a₁, a₂, lt_trans ha₁_lt ha₂_gt, ?_, ?_, ?_⟩
  · ext a
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨haI, ha0⟩
      have hphi := (tricomi_eq_zero_iff_paramPhi_eq_zero hn hx haI).mp ha0
      rcases lt_trichotomy a a₀ with hlt | rfl | hgt
      · exact Or.inl ((paramPhi_strictAntiOn_left hn hx ha₀I hd₀).injOn
          ⟨haI.1, hlt.le⟩ ⟨ha₁I.1, ha₁_lt.le⟩ (hphi.trans ha₁_phi.symm))
      · linarith
      · exact Or.inr ((paramPhi_strictMonoOn_right hn hx ha₀I hd₀).injOn
          ⟨hgt.le, haI.2⟩ ⟨ha₂_gt.le, ha₂I.2⟩ (hphi.trans ha₂_phi.symm))
    · rintro (rfl | rfl)
      · exact ⟨ha₁I, (tricomi_eq_zero_iff_paramPhi_eq_zero hn hx ha₁I).mpr ha₁_phi⟩
      · exact ⟨ha₂I, (tricomi_eq_zero_iff_paramPhi_eq_zero hn hx ha₂I).mpr ha₂_phi⟩
  · rw [deriv_tricomi_re_at_zero hn hx ha₁I ha₁_phi]
    exact mul_ne_zero (Real.rpow_pos_of_pos hx _).ne'
      (ne_of_lt (by linarith [strictMonoOn_paramPhiDeriv hn hx ha₁I ha₀I ha₁_lt]))
  · rw [deriv_tricomi_re_at_zero hn hx ha₂I ha₂_phi]
    exact mul_ne_zero (Real.rpow_pos_of_pos hx _).ne'
      (ne_of_gt (by linarith [strictMonoOn_paramPhiDeriv hn hx ha₀I ha₂I ha₂_gt]))

private theorem paramPhi_zeros_of_min_zero {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x)
    (hmin_zero : minParamPhi n x = 0) :
    ∃ a₀ : ℝ,
      {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
        tricomiIncompleteGamma a x = 0} = {a₀} ∧
      deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₀ = 0 ∧
      deriv (deriv fun b : ℝ => (tricomiIncompleteGamma b x).re) a₀ ≠ 0 := by
  obtain ⟨a₀, ha₀I, hval₀, _, hd₀⟩ := minParamPhi_spec hn hx
  have hphi₀ : paramPhi x a₀ = 0 := hval₀.trans hmin_zero
  have hanti := paramPhi_strictAntiOn_left hn hx ha₀I hd₀
  have hmono := paramPhi_strictMonoOn_right hn hx ha₀I hd₀
  refine ⟨a₀, ?_, ?_, ?_⟩
  · ext a
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨haI, ha0⟩
      have hphi := (tricomi_eq_zero_iff_paramPhi_eq_zero hn hx haI).mp ha0
      rcases lt_trichotomy a a₀ with hlt | rfl | hgt
      · linarith [hanti ⟨haI.1, hlt.le⟩ ⟨ha₀I.1, le_rfl⟩ hlt]
      · rfl
      · linarith [hmono ⟨le_rfl, ha₀I.2⟩ ⟨hgt.le, haI.2⟩ hgt]
    · rintro rfl
      exact ⟨ha₀I, (tricomi_eq_zero_iff_paramPhi_eq_zero hn hx ha₀I).mpr hphi₀⟩
  · rw [deriv_tricomi_re_at_zero hn hx ha₀I hphi₀, hd₀, mul_zero]
  · rw [deriv₂_tricomi_re_at_double_zero hn hx ha₀I hphi₀ hd₀]
    exact mul_ne_zero (Real.rpow_pos_of_pos hx _).ne' (paramPhiDeriv₂_pos hn hx ha₀I).ne'

/-- DLMF §8.13(iii)(b): for `n ≥ 1`, there is `x*_n > 0` such that on `(−2n, 1 − 2n)`,
Tricomi's function `γ*(·, x)` has two simple real zeros for `0 < x < x*_n`, one double real zero
for `x = x*_n`, and no real zeros for `x > x*_n`. The derivatives are those of the real function
`b ↦ Re γ*(b, x)`. -/
theorem tricomiIncompleteGamma_param_zeros {n : ℕ} (hn : 1 ≤ n) :
    ∃ xs : ℝ, 0 < xs ∧ ∀ x : ℝ, 0 < x →
      (x < xs → ∃ a₁ a₂ : ℝ, a₁ < a₂ ∧
        {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
          tricomiIncompleteGamma a x = 0} = {a₁, a₂} ∧
        deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₁ ≠ 0 ∧
        deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₂ ≠ 0) ∧
      (x = xs → ∃ a₀ : ℝ,
        {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
          tricomiIncompleteGamma a x = 0} = {a₀} ∧
        deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₀ = 0 ∧
        deriv (deriv fun b : ℝ => (tricomiIncompleteGamma b x).re) a₀ ≠ 0) ∧
      (xs < x →
        {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
          tricomiIncompleteGamma a x = 0} = ∅) := by
  obtain ⟨x₁, hx₁, hneg⟩ := exists_minParamPhi_neg hn
  obtain ⟨x₂, hx₂, hpos⟩ := exists_minParamPhi_pos hn
  have hmonoM := strictMonoOn_minParamPhi hn
  have hlt12 : x₁ < x₂ := by
    by_contra hle
    rcases eq_or_lt_of_le (not_lt.mp hle) with rfl | hgt
    · linarith
    · linarith [hmonoM hx₂ hx₁ hgt]
  have hcontM : ContinuousOn (minParamPhi n) (Icc x₁ x₂) :=
    (continuousOn_minParamPhi hn).mono fun _ hy => lt_of_lt_of_le hx₁ hy.1
  obtain ⟨xs, hxs_icc, hxs_zero⟩ :=
    intermediate_value_Icc hlt12.le hcontM ⟨hneg.le, hpos.le⟩
  have hxs : 0 < xs := lt_of_lt_of_le hx₁ hxs_icc.1
  refine ⟨xs, hxs, fun x hx => ⟨?_, ?_, ?_⟩⟩
  · exact fun hlt => paramPhi_zeros_of_min_neg hn hx (hxs_zero ▸ hmonoM hx hxs hlt)
  · rintro rfl
    exact paramPhi_zeros_of_min_zero hn hxs hxs_zero
  · intro hgt
    have hpos_m : 0 < minParamPhi n x := hxs_zero ▸ hmonoM hxs hx hgt
    obtain ⟨_, _, hval₀, hmin₀, _⟩ := minParamPhi_spec hn hx
    ext a
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro haI ha0
    have hphi := (tricomi_eq_zero_iff_paramPhi_eq_zero hn hx haI).mp ha0
    have hle : minParamPhi n x ≤ paramPhi x a := hval₀ ▸ hmin₀ haI
    linarith

end Complex

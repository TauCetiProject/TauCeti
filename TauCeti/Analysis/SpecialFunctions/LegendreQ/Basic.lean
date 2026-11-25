/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Function.JacobianOneDim
import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral.Basic

/-!
# The Legendre function of the second kind

For `t > 1` and `-1 < re ν`, the Legendre function of the second kind of degree `ν` is given by
Heine's integral
`Q_ν(t) = ∫₀^∞ (t + √(t² - 1) cosh u) ^ (-(ν + 1)) du`,
where the base is a real number `> 1` and the power is the principal complex power. In the
normalization of Gross–Zagier, the Green function of the hyperbolic Laplacian is
`g_s(z, z') = -2 Q_{s-1}(1 + |z - z'|² / (2 y y'))`, so `Q_{s - 1}` with `1 < re s` is the case
used for automorphic Green kernels.

## Main declarations

* `Complex.legendreQ ν t` — Heine's integral `Q_ν(t)`, the Legendre function of the second kind,
  with `Complex.legendreQ_def` unfolding it.
* `Complex.integrableOn_legendreQ_integrand` — the defining integral converges for `-1 < re ν`
  and `1 < t`.
* `Complex.hasDerivAt_legendreQ`, `Complex.analyticOnNhd_legendreQ` — `ν ↦ Q_ν(t)` is
  holomorphic on `-1 < re ν`, with derivative `-∫₀^∞ log(base) · base ^ (-(ν + 1)) du`.
* `Complex.legendreQ_zero` — `Q₀(t) = ½ log((t + 1) / (t - 1))`.
* `Complex.legendreQ_one` — `Q₁(t) = t Q₀(t) - 1`.
* `Complex.add_one_mul_legendreQ_add_one` — the three-term recurrence
  `(ν + 1) Q_{ν+1}(t) = (2ν + 1) t Q_ν(t) - ν Q_{ν-1}(t)` for `0 < re ν`.
* `Complex.legendreQ_eq_regularizedGaussHGFun` — the hypergeometric form
  `Q_ν(t) = Γ(ν + 1)² / (2 Γ(2ν + 2)) · z ^ (ν + 1) · ₂F₁(ν + 1, ν + 1; 2ν + 2; z)` with
  `z = 2 / (1 + t)`, stated with the regularized Gauss function.

Together, `legendreQ_zero`, `legendreQ_one` and the recurrence at natural `ν` determine `Q_n(t)`
for every natural number `n` in terms of `Q₀(t) = ½ log((t + 1) / (t - 1))`.

## Implementation notes

The definition is intended for `1 < t` and `-1 < re ν`, where the integral converges absolutely,
and every theorem assumes these conditions (the degree is fixed in `legendreQ_zero` and
`legendreQ_one`). Outside this range `legendreQ` is either the junk value `0` of a non-integrable
Bochner integral or an integral without the classical meaning.

The hypergeometric form follows from Euler's integral `Complex.eulerIntegral` for
`₂F₁(s, s; 2s; z)` under the substitution `x = eᵘ / (eᵘ + (t - 1) / √(t² - 1))`, which carries
`ℝ` onto `(0, 1)` and turns Euler's integrand into `z ^ (-s)` times Heine's integrand; Heine's
integrand is even, so the integral over `ℝ` is twice `Q_ν(t)`.

The recurrence and the value `Q₁` come from integrating the derivative of
`sinh u · (t + √(t² - 1) cosh u) ^ (-s)`; at `s = 1` the boundary term at infinity is
`1 / √(t² - 1)` rather than `0`, which is why `Q₁` is not the case `ν = 0` of the recurrence.

## References

* B. Gross and D. Zagier, *Heegner points and derivatives of L-series*, Invent. Math. 84 (1986),
  Chapter II, §2, (2.5)–(2.6).
* *NIST Digital Library of Mathematical Functions*, §14.5 (special values), §14.10 (recurrence
  relations) and §14.12 (integral representations).
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace Complex

/-- The Legendre function of the second kind `Q_ν(t)`, given by Heine's integral
`∫₀^∞ (t + √(t² - 1) cosh u) ^ (-(ν + 1)) du` with the principal power of the positive base.
It is meaningful for `1 < t` and `-1 < re ν`, where the integral converges absolutely; outside
this range the value carries no meaning. The Gross–Zagier function `Q_{s-1}(t)` is
`legendreQ (s - 1) t`. -/
def legendreQ (ν : ℂ) (t : ℝ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-(ν + 1))

/-- Unfolds `Complex.legendreQ` to Heine's integral. -/
theorem legendreQ_def (ν : ℂ) (t : ℝ) :
    legendreQ ν t =
      ∫ u in Ioi (0 : ℝ), ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-(ν + 1)) :=
  (rfl)

variable {t : ℝ}

private lemma sqrt_sq_sub_one_pos (ht : 1 < t) : 0 < √(t ^ 2 - 1) :=
  Real.sqrt_pos.2 (by nlinarith)

private lemma sq_sqrt_sq_sub_one (ht : 1 < t) : √(t ^ 2 - 1) ^ 2 = t ^ 2 - 1 :=
  Real.sq_sqrt (by nlinarith)

private lemma one_lt_base (ht : 1 < t) (u : ℝ) : 1 < t + √(t ^ 2 - 1) * Real.cosh u := by
  have := mul_nonneg (Real.sqrt_nonneg (t ^ 2 - 1)) (Real.cosh_pos u).le
  linarith

private lemma base_pos (ht : 1 < t) (u : ℝ) : 0 < t + √(t ^ 2 - 1) * Real.cosh u :=
  zero_lt_one.trans (one_lt_base ht u)

/-- The base grows like `e ^ u`: it is at least `√(t² - 1) / 2 · e ^ u`. -/
private lemma mul_exp_le_base (ht : 1 < t) (u : ℝ) :
    √(t ^ 2 - 1) / 2 * Real.exp u ≤ t + √(t ^ 2 - 1) * Real.cosh u := by
  have hb := Real.sqrt_nonneg (t ^ 2 - 1)
  nlinarith [Real.exp_le_two_mul_cosh u]

private lemma base_rpow_neg_le (ht : 1 < t) {σ : ℝ} (hσ : 0 ≤ σ) (u : ℝ) :
    (t + √(t ^ 2 - 1) * Real.cosh u) ^ (-σ) ≤
      (√(t ^ 2 - 1) / 2) ^ (-σ) * Real.exp (-σ * u) := by
  have hb := sqrt_sq_sub_one_pos ht
  calc (t + √(t ^ 2 - 1) * Real.cosh u) ^ (-σ)
      ≤ (√(t ^ 2 - 1) / 2 * Real.exp u) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (mul_exp_le_base ht u) (by linarith)
    _ = (√(t ^ 2 - 1) / 2) ^ (-σ) * Real.exp (-σ * u) := by
        rw [Real.mul_rpow (by positivity) (Real.exp_pos u).le, ← Real.exp_mul, mul_comm u]

private lemma integrableOn_base_rpow_neg (ht : 1 < t) {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun u => (t + √(t ^ 2 - 1) * Real.cosh u) ^ (-σ)) (Ioi 0) := by
  refine Integrable.mono'
    ((exp_neg_integrableOn_Ioi 0 hσ).const_mul ((√(t ^ 2 - 1) / 2) ^ (-σ))) ?_ ?_
  · exact ((by fun_prop : Continuous fun u => t + √(t ^ 2 - 1) * Real.cosh u).rpow_const
      fun u => Or.inl (base_pos ht u).ne').aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (base_pos ht u).le _)]
    exact base_rpow_neg_le ht hσ.le u

private lemma continuous_cpow_base (ht : 1 < t) (s : ℂ) :
    Continuous fun u : ℝ => ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ s :=
  (continuous_ofReal.comp (by fun_prop)).cpow continuous_const fun u =>
    ofReal_mem_slitPlane.2 (base_pos ht u)

private lemma norm_cpow_base (ht : 1 < t) (s : ℂ) (u : ℝ) :
    ‖((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ s‖ =
      (t + √(t ^ 2 - 1) * Real.cosh u) ^ s.re :=
  norm_cpow_eq_rpow_re_of_pos (base_pos ht u) s

private lemma integrableOn_cpow_neg (ht : 1 < t) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun u : ℝ => ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-s)) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_base_rpow_neg ht hs)
    (continuous_cpow_base ht _).aestronglyMeasurable (ae_of_all _ fun u => ?_)
  rw [norm_cpow_base ht, neg_re]

/-- Heine's integral for `Q_ν(t)` converges absolutely when `-1 < re ν` and `1 < t`. -/
theorem integrableOn_legendreQ_integrand {ν : ℂ} (hν : -1 < ν.re) (ht : 1 < t) :
    IntegrableOn (fun u : ℝ => ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-(ν + 1)))
      (Ioi 0) :=
  integrableOn_cpow_neg ht (by simp; linarith)

/-- The domination of the degree derivative of Heine's integrand used for `hasDerivAt_legendreQ`:
`‖log c · c ^ (-(w + 1))‖ ≤ (2 / δ) c ^ (-(δ / 2))` for the base `c ≥ 1` and `δ ≤ re (w + 1)`. -/
private lemma norm_log_mul_cpow_base_le (ht : 1 < t) {w : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hw : δ ≤ (w + 1).re) (u : ℝ) :
    ‖-((Real.log (t + √(t ^ 2 - 1) * Real.cosh u) : ℂ) *
      ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-(w + 1)))‖ ≤
      2 / δ * (t + √(t ^ 2 - 1) * Real.cosh u) ^ (-(δ / 2)) := by
  have hc := one_lt_base ht u
  rw [norm_neg, norm_mul, norm_cpow_base ht, norm_real,
    Real.norm_of_nonneg (Real.log_nonneg hc.le), neg_re]
  calc Real.log (t + √(t ^ 2 - 1) * Real.cosh u) *
        (t + √(t ^ 2 - 1) * Real.cosh u) ^ (-(w + 1).re)
      ≤ (t + √(t ^ 2 - 1) * Real.cosh u) ^ (δ / 2) / (δ / 2) *
        (t + √(t ^ 2 - 1) * Real.cosh u) ^ (-δ) :=
        mul_le_mul (Real.log_le_rpow_div (by linarith) (by linarith))
          (Real.rpow_le_rpow_of_exponent_le hc.le (by linarith))
          (Real.rpow_nonneg (by linarith) _) (by positivity)
    _ = 2 / δ * ((t + √(t ^ 2 - 1) * Real.cosh u) ^ (δ / 2) *
        (t + √(t ^ 2 - 1) * Real.cosh u) ^ (-δ)) := by field_simp
    _ = 2 / δ * (t + √(t ^ 2 - 1) * Real.cosh u) ^ (-(δ / 2)) := by
        rw [← Real.rpow_add (by linarith)]
        ring_nf

/-- The degree derivative of Heine's integral:
`∂_ν Q_ν(t) = -∫₀^∞ log(t + √(t² - 1) cosh u) (t + √(t² - 1) cosh u) ^ (-(ν + 1)) du`
for `-1 < re ν` and `1 < t`. -/
theorem hasDerivAt_legendreQ {ν : ℂ} (hν : -1 < ν.re) (ht : 1 < t) :
    HasDerivAt (legendreQ · t)
      (-∫ u in Ioi (0 : ℝ), (Real.log (t + √(t ^ 2 - 1) * Real.cosh u) : ℂ) *
        ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-(ν + 1))) ν := by
  set δ := (ν.re + 1) / 2 with hδ
  have hδ0 : 0 < δ := by linarith
  have hlog (u : ℝ) : Complex.log (t + √(t ^ 2 - 1) * Real.cosh u : ℝ) =
      (Real.log (t + √(t ^ 2 - 1) * Real.cosh u) : ℂ) :=
    (ofReal_log (base_pos ht u).le).symm
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun (w : ℂ) (u : ℝ) => ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-(w + 1)))
    (F' := fun (w : ℂ) (u : ℝ) => -((Real.log (t + √(t ^ 2 - 1) * Real.cosh u) : ℂ) *
      ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-(w + 1))))
    (x₀ := ν) (bound := fun u => 2 / δ * (t + √(t ^ 2 - 1) * Real.cosh u) ^ (-(δ / 2)))
    (Metric.ball_mem_nhds ν hδ0)
    (Eventually.of_forall fun w => (continuous_cpow_base ht _).aestronglyMeasurable)
    (integrableOn_legendreQ_integrand hν ht)
    (((continuous_ofReal.comp ((by fun_prop : Continuous fun u =>
      t + √(t ^ 2 - 1) * Real.cosh u).log fun u => (base_pos ht u).ne')).mul
      (continuous_cpow_base ht _)).neg.aestronglyMeasurable) ?_
    ((integrableOn_base_rpow_neg ht (by linarith)).const_mul _) ?_
  · rw [integral_neg] at key
    exact key.2
  · refine ae_of_all _ fun u w hw => norm_log_mul_cpow_base_le ht hδ0 ?_ u
    have hw' : |w.re - ν.re| < δ :=
      calc |w.re - ν.re| = |(w - ν).re| := by rw [sub_re]
        _ ≤ ‖w - ν‖ := abs_re_le_norm _
        _ < δ := by rwa [Metric.mem_ball, dist_eq] at hw
    rw [add_re, one_re]
    linarith [(abs_lt.1 hw').1]
  · refine ae_of_all _ fun u w _ => ?_
    have hf : HasDerivAt (fun w : ℂ => -(w + 1)) (-1) w := ((hasDerivAt_id' w).add_const 1).neg
    refine (hf.const_cpow (c := ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ))
      (Or.inl (ofReal_ne_zero.2 (base_pos ht u).ne'))).congr_deriv ?_
    rw [hlog]
    ring

/-- For `1 < t`, the degree map `ν ↦ Q_ν(t)` is complex differentiable at every `ν` with
`-1 < re ν`. -/
theorem differentiableAt_legendreQ {ν : ℂ} (hν : -1 < ν.re) (ht : 1 < t) :
    DifferentiableAt ℂ (legendreQ · t) ν :=
  (hasDerivAt_legendreQ hν ht).differentiableAt

/-- For `1 < t`, the degree map `ν ↦ Q_ν(t)` is holomorphic on the half-plane `-1 < re ν`. -/
theorem analyticOnNhd_legendreQ (ht : 1 < t) :
    AnalyticOnNhd ℂ (legendreQ · t) {ν | -1 < ν.re} :=
  DifferentiableOn.analyticOnNhd
    (fun _ hν => (differentiableAt_legendreQ hν ht).differentiableWithinAt)
    (isOpen_lt continuous_const continuous_re)

/-- An antiderivative of `1 / (t + √(t² - 1) cosh u)`. -/
private lemma hasDerivAt_log_sub_log (ht : 1 < t) (u : ℝ) :
    HasDerivAt (fun u => Real.log (√(t ^ 2 - 1) * Real.exp u + (t - 1)) -
        Real.log (√(t ^ 2 - 1) * Real.exp u + (t + 1)))
      ((t + √(t ^ 2 - 1) * Real.cosh u)⁻¹) u := by
  have hb := sqrt_sq_sub_one_pos ht
  have hb2 := sq_sqrt_sq_sub_one ht
  have h1 : 0 < √(t ^ 2 - 1) * Real.exp u + (t - 1) := by positivity
  have h2 : 0 < √(t ^ 2 - 1) * Real.exp u + (t + 1) := by positivity
  have hd (a : ℝ) : HasDerivAt (fun u => √(t ^ 2 - 1) * Real.exp u + a)
      (√(t ^ 2 - 1) * Real.exp u) u :=
    ((Real.hasDerivAt_exp u).const_mul _).add_const a
  refine ((hd _).log h1.ne').sub ((hd _).log h2.ne') |>.congr_deriv ?_
  have hc := base_pos ht u
  rw [Real.cosh_eq, Real.exp_neg] at hc ⊢
  field_simp
  linear_combination 2 * hb2

/-- `Q₀(t) = ½ log((t + 1) / (t - 1))` for `1 < t`. -/
theorem legendreQ_zero (ht : 1 < t) :
    legendreQ 0 t = (Real.log ((t + 1) / (t - 1)) / 2 : ℝ) := by
  have hb := sqrt_sq_sub_one_pos ht
  have hb2 := sq_sqrt_sq_sub_one ht
  have hint : IntegrableOn (fun u => (t + √(t ^ 2 - 1) * Real.cosh u)⁻¹) (Ioi 0) := by
    simpa [Real.rpow_neg_one] using integrableOn_base_rpow_neg ht one_pos
  have htop : Tendsto (fun u => √(t ^ 2 - 1) * Real.exp u + (t + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (Real.tendsto_exp_atTop.const_mul_atTop hb)
  have hlim : Tendsto (fun u => Real.log (√(t ^ 2 - 1) * Real.exp u + (t - 1)) -
      Real.log (√(t ^ 2 - 1) * Real.exp u + (t + 1))) atTop (𝓝 0) := by
    have h := (Real.continuousAt_log one_ne_zero).tendsto.comp
      (by simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (htop.const_div_atTop 2))
    rw [Real.log_one] at h
    refine h.congr' (Eventually.of_forall fun u => ?_)
    have h2 : 0 < √(t ^ 2 - 1) * Real.exp u + (t + 1) := by positivity
    have h1 : 0 < √(t ^ 2 - 1) * Real.exp u + (t - 1) := by
      nlinarith [Real.exp_pos u]
    simp only [Function.comp_apply]
    rw [← Real.log_div h1.ne' h2.ne']
    congr 1
    field_simp
    ring
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u _ => hasDerivAt_log_sub_log ht u) hint hlim
  have hsq : (t + 1) / (t - 1) =
      ((√(t ^ 2 - 1) + (t + 1)) / (√(t ^ 2 - 1) + (t - 1))) ^ 2 := by
    have : 0 < √(t ^ 2 - 1) + (t - 1) := by linarith
    field_simp
    linear_combination 2 * hb2
  have hp : 0 < √(t ^ 2 - 1) + (t - 1) := by linarith
  rw [legendreQ, zero_add]
  simp_rw [cpow_neg_one, ← ofReal_inv]
  rw [integral_complex_ofReal, hval, Real.exp_zero, mul_one, hsq, Real.log_pow,
    Real.log_div (by positivity) hp.ne']
  push_cast
  ring

/-- The derivative of `sinh u · (t + √(t² - 1) cosh u) ^ (-s)`, written in the three powers
`-(s - 1)`, `-s` and `-(s + 1)` of the base. -/
private lemma hasDerivAt_sinh_mul_cpow (ht : 1 < t) (s : ℂ) (u : ℝ) :
    HasDerivAt
      (fun u : ℝ => (Real.sinh u : ℂ) * ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-s))
      ((√(t ^ 2 - 1) : ℂ)⁻¹ *
        ((1 - s) * ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-(s - 1)) +
          (2 * s - 1) * t * ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-s) -
          s * ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-(s + 1)))) u := by
  have hb0 : (√(t ^ 2 - 1) : ℂ) ≠ 0 := ofReal_ne_zero.2 (sqrt_sq_sub_one_pos ht).ne'
  have hb2 : (√(t ^ 2 - 1) : ℂ) ^ 2 = (t : ℂ) ^ 2 - 1 := by
    exact_mod_cast sq_sqrt_sq_sub_one ht
  have hcs : (Real.cosh u : ℂ) ^ 2 - (Real.sinh u : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cosh_sq_sub_sinh_sq u
  have hC0 : ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (base_pos ht u).ne'
  have hc : HasDerivAt (fun u : ℝ => ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ))
      ((√(t ^ 2 - 1) * Real.sinh u : ℝ) : ℂ) u :=
    (((Real.hasDerivAt_cosh u).const_mul _).const_add t).ofReal_comp
  have hcp := (hasStrictDerivAt_cpow_const (c := -s)
    (ofReal_mem_slitPlane.2 (base_pos ht u))).hasDerivAt.comp u hc
  refine ((Real.hasDerivAt_sinh u).ofReal_comp.mul hcp).congr_deriv ?_
  simp only [Function.comp_apply]
  set C := ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) with hC
  have e1 : C ^ (-s) = C * C ^ (-(s + 1)) := by
    conv_lhs => rw [show -s = 1 + -(s + 1) by ring]
    rw [cpow_add _ _ hC0, cpow_one]
  have e2 : C ^ (-(s - 1)) = C ^ 2 * C ^ (-(s + 1)) := by
    conv_lhs => rw [show -(s - 1) = 2 + -(s + 1) by ring]
    rw [cpow_add _ _ hC0, cpow_two]
  have e3 : C ^ (-s - 1) = C ^ (-(s + 1)) := by
    rw [show -s - 1 = -(s + 1) by ring]
  rw [e1, e2, e3, eq_inv_mul_iff_mul_eq₀ hb0]
  set P := C ^ (-(s + 1))
  simp only [hC, ofReal_add, ofReal_mul]
  linear_combination (P * s * (√(t ^ 2 - 1) : ℂ) ^ 2) * hcs + (P * s) * hb2

/-- Integrating the derivative of `sinh u · (t + √(t² - 1) cosh u) ^ (-s)` over `(0, ∞)`, when
the product tends to `L` at infinity. -/
private lemma integral_sinh_mul_cpow_deriv (ht : 1 < t) {s L : ℂ} (hs : 0 < s.re)
    (h1 : IntegrableOn (fun u : ℝ =>
      (1 - s) * ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-(s - 1))) (Ioi 0))
    (hL : Tendsto (fun u : ℝ =>
      (Real.sinh u : ℂ) * ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-s)) atTop (𝓝 L)) :
    (1 - s) * (∫ u in Ioi (0 : ℝ), ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-(s - 1))) +
        (2 * s - 1) * t *
          (∫ u in Ioi (0 : ℝ), ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-s)) -
        s * (∫ u in Ioi (0 : ℝ), ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-(s + 1))) =
      √(t ^ 2 - 1) * L := by
  have hb0 : (√(t ^ 2 - 1) : ℂ) ≠ 0 := ofReal_ne_zero.2 (sqrt_sq_sub_one_pos ht).ne'
  have h2 := (integrableOn_cpow_neg ht hs).const_mul ((2 * s - 1) * t)
  have h3 := (integrableOn_cpow_neg ht (s := s + 1) (by simp; linarith)).const_mul s
  have h12 : IntegrableOn (fun u : ℝ =>
      (1 - s) * ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-(s - 1)) +
        (2 * s - 1) * t * ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-s)) (Ioi 0) :=
    h1.add h2
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u _ => hasDerivAt_sinh_mul_cpow ht s u) ((h12.sub h3).const_mul _) hL
  rw [integral_const_mul, integral_sub h12 h3, integral_add h1 h2] at hval
  simp only [integral_const_mul, Real.sinh_zero, ofReal_zero, zero_mul, sub_zero] at hval
  rw [← hval]
  field_simp

/-- `Q₁(t) = t Q₀(t) - 1` for `1 < t`. -/
theorem legendreQ_one (ht : 1 < t) : legendreQ 1 t = t * legendreQ 0 t - 1 := by
  have hb := sqrt_sq_sub_one_pos ht
  have hg : ContinuousAt
      (fun y : ℝ => (1 - y ^ 2) / (2 * t * y + √(t ^ 2 - 1) * (1 + y ^ 2))) 0 :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (by simpa using hb.ne')
  have hreal : Tendsto (fun u => Real.sinh u / (t + √(t ^ 2 - 1) * Real.cosh u)) atTop
      (𝓝 (√(t ^ 2 - 1))⁻¹) := by
    have h := hg.tendsto.comp Real.tendsto_exp_neg_atTop_nhds_zero
    have h0 : (1 - (0 : ℝ) ^ 2) / (2 * t * 0 + √(t ^ 2 - 1) * (1 + 0 ^ 2)) =
        (√(t ^ 2 - 1))⁻¹ := by simp
    rw [h0] at h
    refine h.congr' (Eventually.of_forall fun u => ?_)
    have hc := base_pos ht u
    simp only [Function.comp_apply]
    rw [Real.sinh_eq, Real.exp_neg]
    rw [Real.cosh_eq, Real.exp_neg] at hc ⊢
    field_simp
  have hL : Tendsto (fun u : ℝ =>
      (Real.sinh u : ℂ) * ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-(1 : ℂ))) atTop
      (𝓝 ((√(t ^ 2 - 1))⁻¹ : ℝ)) := by
    refine ((continuous_ofReal.tendsto _).comp hreal).congr fun u => ?_
    rw [Function.comp_apply, cpow_neg_one]
    push_cast
    ring
  have h := integral_sinh_mul_cpow_deriv ht (s := 1) (by simp) (by simp) hL
  have hb' : (√(t ^ 2 - 1) : ℂ) * (((√(t ^ 2 - 1))⁻¹ : ℝ) : ℂ) = 1 := by
    rw [ofReal_inv]
    exact mul_inv_cancel₀ (ofReal_ne_zero.2 hb.ne')
  rw [legendreQ, legendreQ, zero_add]
  linear_combination -h - hb'

/-- The three-term recurrence `(ν + 1) Q_{ν+1}(t) = (2ν + 1) t Q_ν(t) - ν Q_{ν-1}(t)` for
`0 < re ν` and `1 < t`. -/
theorem add_one_mul_legendreQ_add_one {ν : ℂ} (hν : 0 < ν.re) (ht : 1 < t) :
    (ν + 1) * legendreQ (ν + 1) t =
      (2 * ν + 1) * t * legendreQ ν t - ν * legendreQ (ν - 1) t := by
  have hσ : 1 < (ν + 1).re := by simp; linarith
  have hlim : Tendsto (fun u => (√(t ^ 2 - 1) / 2) ^ (-(ν + 1).re) *
      Real.exp (-(((ν + 1).re - 1) * u))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by linarith : 0 < (ν + 1).re - 1))).const_mul
        ((√(t ^ 2 - 1) / 2) ^ (-(ν + 1).re))
  have hL : Tendsto (fun u : ℝ =>
      (Real.sinh u : ℂ) * ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-(ν + 1))) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 0] with u hu
    rw [norm_mul, norm_real, norm_cpow_base ht, neg_re,
      Real.norm_of_nonneg (Real.sinh_nonneg_iff.2 hu)]
    calc Real.sinh u * (t + √(t ^ 2 - 1) * Real.cosh u) ^ (-(ν + 1).re)
        ≤ Real.exp u * ((√(t ^ 2 - 1) / 2) ^ (-(ν + 1).re) *
          Real.exp (-(ν + 1).re * u)) :=
          mul_le_mul (by rw [Real.sinh_eq]; linarith [Real.exp_pos u, Real.exp_pos (-u)])
            (base_rpow_neg_le ht (by linarith) u)
            (Real.rpow_nonneg (base_pos ht u).le _) (Real.exp_pos u).le
      _ = (√(t ^ 2 - 1) / 2) ^ (-(ν + 1).re) * Real.exp (-(((ν + 1).re - 1) * u)) := by
          rw [mul_left_comm, ← Real.exp_add]
          ring_nf
  have h1 := (integrableOn_cpow_neg ht (s := ν + 1 - 1) (by simpa using hν)).const_mul
    (1 - (ν + 1))
  have h := integral_sinh_mul_cpow_deriv ht (s := ν + 1) (by linarith) h1 hL
  rw [legendreQ, legendreQ, legendreQ, show -(ν - 1 + 1) = -(ν + 1 - 1) by ring]
  linear_combination -h

/-! ### The hypergeometric form -/

/-- The substitution `x = eᵘ / (eᵘ + K)` with `K = (t - 1) / √(t² - 1)`, which carries `ℝ` onto
`(0, 1)` and Heine's integrand to Euler's integrand for `₂F₁(s, s; 2s; 2 / (1 + t))`. -/
private def eulerSubst (t u : ℝ) : ℝ :=
  Real.exp u / (Real.exp u + (t - 1) / √(t ^ 2 - 1))

private lemma eulerSubst_const_pos (ht : 1 < t) : 0 < (t - 1) / √(t ^ 2 - 1) :=
  div_pos (by linarith) (sqrt_sq_sub_one_pos ht)

private lemma hasDerivAt_eulerSubst (ht : 1 < t) (u : ℝ) :
    HasDerivAt (eulerSubst t) (eulerSubst t u * (1 - eulerSubst t u)) u := by
  have hK := eulerSubst_const_pos ht
  refine ((Real.hasDerivAt_exp u).div ((Real.hasDerivAt_exp u).add_const _)
    (by positivity)).congr_deriv ?_
  simp only [eulerSubst]
  field_simp

private lemma image_eulerSubst (ht : 1 < t) : eulerSubst t '' univ = Ioo 0 1 := by
  have hb := sqrt_sq_sub_one_pos ht
  have hK := eulerSubst_const_pos ht
  ext x
  simp only [image_univ, mem_range, mem_Ioo, eulerSubst]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨by positivity, (div_lt_one (by positivity)).2 (by linarith)⟩
  · rintro ⟨hx0, hx1⟩
    refine ⟨Real.log ((t - 1) / √(t ^ 2 - 1) * x / (1 - x)), ?_⟩
    rw [Real.exp_log (by positivity)]
    field_simp
    ring

private lemma eulerSubst_mem_Ioo (ht : 1 < t) (u : ℝ) : eulerSubst t u ∈ Ioo 0 1 :=
  image_eulerSubst ht ▸ mem_image_of_mem _ (mem_univ u)

private lemma injective_eulerSubst (ht : 1 < t) : Function.Injective (eulerSubst t) := by
  have hK := eulerSubst_const_pos ht
  intro u v h
  simp only [eulerSubst] at h
  rw [div_eq_div_iff (by positivity) (by positivity)] at h
  exact Real.exp_injective (mul_left_cancel₀ hK.ne' (by linarith))

/-- The real identity behind the substitution: with `x = eulerSubst t u` and `z = 2 / (1 + t)`,
`z x (1 - x) = (t + √(t² - 1) cosh u)⁻¹ (1 - z x)`. -/
private lemma eulerSubst_mul_one_sub_eulerSubst (ht : 1 < t) (u : ℝ) :
    2 / (1 + t) * eulerSubst t u * (1 - eulerSubst t u) =
      (t + √(t ^ 2 - 1) * Real.cosh u)⁻¹ * (1 - 2 / (1 + t) * eulerSubst t u) := by
  have hb := sqrt_sq_sub_one_pos ht
  have hb2 := sq_sqrt_sq_sub_one ht
  have hC := base_pos ht u
  rw [Real.cosh_eq, Real.exp_neg] at hC
  rw [eulerSubst, Real.cosh_eq, Real.exp_neg]
  field_simp
  linear_combination (t - 1) * hb2

/-- Under `x = eulerSubst t u`, the Jacobian `x (1 - x)` times Euler's integrand for
`₂F₁(s, s; 2s; z)`, `z = 2 / (1 + t)`, is `z ^ (-s)` times Heine's integrand. -/
private lemma eulerIntegrand_eulerSubst (ht : 1 < t) (s : ℂ) (u : ℝ) :
    ((eulerSubst t u * (1 - eulerSubst t u) : ℝ) : ℂ) *
      ((eulerSubst t u : ℂ) ^ (s - 1) * (1 - (eulerSubst t u : ℂ)) ^ (2 * s - s - 1) *
        (1 - ((2 / (1 + t) : ℝ) : ℂ) * eulerSubst t u) ^ (-s)) =
      (((2 / (1 + t) : ℝ) : ℂ) ^ s)⁻¹ *
        ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-s) := by
  have hC := base_pos ht u
  have key := eulerSubst_mul_one_sub_eulerSubst ht u
  set x := eulerSubst t u
  set z : ℝ := 2 / (1 + t) with hz_def
  have hx0 : 0 < x := (eulerSubst_mem_Ioo ht u).1
  have hx1 : 0 < 1 - x := sub_pos.2 (eulerSubst_mem_Ioo ht u).2
  have hz0 : 0 < z := by rw [hz_def]; positivity
  have hw : 0 < 1 - z * x := by
    have : z < 1 := by rw [hz_def, div_lt_one (by linarith)]; linarith
    have : x < 1 := by linarith
    nlinarith
  have keyC : (z : ℂ) ^ s * (x : ℂ) ^ s * ((1 - x : ℝ) : ℂ) ^ s =
      (((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ s)⁻¹ * ((1 - z * x : ℝ) : ℂ) ^ s := by
    have := congrArg (fun r : ℝ => (r : ℂ) ^ s) key
    rwa [ofReal_mul (z * x), ofReal_mul_cpow (by positivity), ofReal_mul z,
      ofReal_mul_cpow hz0.le, ofReal_mul _ (1 - z * x),
      ofReal_mul_cpow (by positivity), ofReal_inv,
      inv_cpow_ofReal_nonneg hC.le] at this
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx0.ne'
  have hyC : ((1 - x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hx1.ne'
  have hzs : (z : ℂ) ^ s ≠ 0 :=
    cpow_ne_zero_iff.2 (Or.inl (ofReal_ne_zero.2 hz0.ne'))
  have hws : ((1 - z * x : ℝ) : ℂ) ^ s ≠ 0 :=
    cpow_ne_zero_iff.2 (Or.inl (ofReal_ne_zero.2 hw.ne'))
  have hCs : ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ s ≠ 0 :=
    cpow_ne_zero_iff.2 (Or.inl (ofReal_ne_zero.2 hC.ne'))
  rw [show 2 * s - s - 1 = s - 1 by ring,
    show (1 : ℂ) - x = ((1 - x : ℝ) : ℂ) by push_cast; ring,
    show (1 : ℂ) - z * x = ((1 - z * x : ℝ) : ℂ) by push_cast; ring,
    cpow_sub _ _ hxC, cpow_sub _ _ hyC, cpow_one, cpow_one, cpow_neg, cpow_neg]
  rw [ofReal_mul]
  -- Replace the powers and casts by atoms, so that `field_simp` does not rewrite inside the casts
  -- and the goal becomes a rational identity in `keyC`.
  generalize (x : ℂ) ^ s = X at keyC ⊢
  generalize ((1 - x : ℝ) : ℂ) ^ s = Y at keyC ⊢
  generalize ((1 - z * x : ℝ) : ℂ) ^ s = W at keyC hws ⊢
  generalize (z : ℂ) ^ s = Z at keyC hzs ⊢
  generalize ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ s = D at keyC hCs ⊢
  generalize (x : ℂ) = X₀ at hxC ⊢
  generalize ((1 - x : ℝ) : ℂ) = Y₀ at hyC ⊢
  have keyD : Z * X * Y * D = W := by rw [keyC]; field_simp
  field_simp
  linear_combination keyD

/-- Heine's integrand is even in `u`, so its integral over `ℝ` is twice that over `(0, ∞)`. -/
private lemma integral_cpow_neg_eq_two_mul {s : ℂ}
    (hint : Integrable fun u : ℝ => ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-s)) :
    ∫ u, ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-s) =
      2 * ∫ u in Ioi (0 : ℝ), ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-s) := by
  have h := integral_comp_neg_Ioi 0
    fun u : ℝ => ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-s)
  simp only [Real.cosh_neg, neg_zero] at h
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn, ← h, two_mul]

/-- The hypergeometric form of Heine's integral: for `-1 < re ν` and `1 < t`, with
`z = 2 / (1 + t)`,
`Q_ν(t) = Γ(ν + 1)² / 2 · z ^ (ν + 1) · regularizedGaussHGFun (ν + 1) (ν + 1) (2ν + 2) z`,
where `regularizedGaussHGFun a b c z = ₂F₁(a, b; c; z) / Γ(c)` is the regularized Gauss
function. Equivalently,
`Q_ν(t) = Γ(ν + 1)² / (2 Γ(2ν + 2)) · z ^ (ν + 1) · ₂F₁(ν + 1, ν + 1; 2ν + 2; z)`. -/
theorem legendreQ_eq_regularizedGaussHGFun {ν : ℂ} (hν : -1 < ν.re) (ht : 1 < t) :
    legendreQ ν t = Gamma (ν + 1) ^ 2 / 2 * ((2 / (1 + t) : ℝ) : ℂ) ^ (ν + 1) *
      regularizedGaussHGFun (ν + 1) (ν + 1) (2 * (ν + 1)) ((2 / (1 + t) : ℝ) : ℂ) := by
  have hs : 0 < (ν + 1).re := by simp; linarith
  have hsc : (ν + 1).re < (2 * (ν + 1)).re := by simp; linarith
  have hz0 : 0 < 2 / (1 + t) := div_pos two_pos (by linarith)
  have hz1 : 2 / (1 + t) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hzs : ((2 / (1 + t) : ℝ) : ℂ) ^ (ν + 1) ≠ 0 :=
    cpow_ne_zero_iff.2 (Or.inl (ofReal_ne_zero.2 hz0.ne'))
  have hG := Gamma_ne_zero_of_re_pos hs
  rw [regularizedGaussHGFun_eq_eulerIntegral _ hs hsc
    (by rw [norm_real, Real.norm_of_nonneg hz0.le]; exact hz1), eulerIntegral_def]
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ (ν + 1 - 1) *
    (1 - (x : ℂ)) ^ (2 * (ν + 1) - (ν + 1) - 1) *
      (1 - ((2 / (1 + t) : ℝ) : ℂ) * x) ^ (-(ν + 1))
  have hgi : IntegrableOn g (Ioo 0 1) :=
    (intervalIntegrable_eulerIntegrand (ν + 1) hs hsc (by
      rw [← ofReal_one, ← ofReal_sub, ofReal_mem_slitPlane]
      linarith)).1.mono_set Ioo_subset_Ioc_self
  have hderiv (u : ℝ) (_ : u ∈ univ) :=
    (hasDerivAt_eulerSubst ht u).hasDerivWithinAt (s := univ)
  have hpt (u : ℝ) : |eulerSubst t u * (1 - eulerSubst t u)| • g (eulerSubst t u) =
      (((2 / (1 + t) : ℝ) : ℂ) ^ (ν + 1))⁻¹ *
        ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-(ν + 1)) := by
    have hx := eulerSubst_mem_Ioo ht u
    rw [abs_of_pos (mul_pos hx.1 (sub_pos.2 hx.2)), real_smul]
    exact eulerIntegrand_eulerSubst ht (ν + 1) u
  have hint : Integrable fun u : ℝ =>
      ((t + √(t ^ 2 - 1) * Real.cosh u : ℝ) : ℂ) ^ (-(ν + 1)) := by
    have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hderiv
      (injective_eulerSubst ht).injOn g).1 (by rwa [image_eulerSubst ht])
    rw [integrableOn_univ] at h
    simpa only [hpt, ← mul_assoc, mul_inv_cancel₀ hzs, one_mul] using
      h.const_mul (((2 / (1 + t) : ℝ) : ℂ) ^ (ν + 1))
  have hJ : ∫ x in (0 : ℝ)..1, g x =
      (((2 / (1 + t) : ℝ) : ℂ) ^ (ν + 1))⁻¹ * (2 * legendreQ ν t) := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
      ← image_eulerSubst ht, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
        hderiv (injective_eulerSubst ht).injOn, Measure.restrict_univ]
    simp_rw [hpt]
    rw [integral_const_mul, integral_cpow_neg_eq_two_mul hint, legendreQ]
  rw [hJ, show 2 * (ν + 1) - (ν + 1) = ν + 1 by ring]
  field_simp

end Complex

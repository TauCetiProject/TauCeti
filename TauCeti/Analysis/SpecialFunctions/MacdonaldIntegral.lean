/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import TauCeti.Analysis.MellinTransform
import TauCeti.Analysis.MellinTransform.Basic
import TauCeti.Analysis.MellinTransform.Convolution
import TauCeti.Analysis.SpecialFunctions.Exp.Decay
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical.Basic
import TauCeti.Analysis.SpecialFunctions.Hyperbolic

/-!
# The Macdonald integral and its Mellin transform

For `c > 0` and every complex `a`, the integral

`Q_a(c) = ∫₀^∞ s^{a - 1} e^{-s - c/s} ds`

converges absolutely, since `e^{-c/s}` vanishes to infinite order at `s = 0`. Classically
`Q_a(c) = 2 c^{a/2} K_a(2 √c)` with the modified Bessel function `K_a` of the second kind
(Macdonald's function; DLMF 10.32.10), which neither Mathlib nor Tau Ceti defines; this file
works with the integral itself. As the multiplicative convolution of `s ↦ s^a e^{-s}` with
`s ↦ e^{-s}`, its Mellin transform in `c` is a product of two Gamma functions (the integral form
of DLMF 10.43.19):

`∫₀^∞ c^{t - 1} Q_a(c) dc = Γ(t) Γ(t + a)`   for `Re t > 0`, `Re (t + a) > 0`.

The product `Γ(t) Γ(t + a)` is integrable on every vertical line avoiding the poles of both
factors (`Complex.verticalIntegrable_Gamma_mul_Gamma_add`), and `Q_a` is continuous, so Mellin
inversion recovers `Q_a` as the Mellin–Barnes integral

`Q_a(c) = (1 / 2π) ∫ c^{-(σ + i y)} Γ(σ + i y) Γ(σ + a + i y) dy`   for `σ > 0`, `σ + Re a > 0`.

This is the starting point of the residue expansion of `Q_a(c)`, obtained by shifting the line
to the left across the poles of `Γ(t) Γ(t + a)` at `t = -k` and `t = -a - k`. For `a` not an
integer these poles are simple and the expansion is in the powers `c^k` and `c^{a + k}`; for
integer `a` the two families overlap in double poles, which contribute terms `c^m log c`. That
expansion is not proved here.

The substitution `s = (ζ / 2) e^u` turns Schläfli's integral for `K_p` (DLMF 10.32.9) into the
Macdonald integral: for real `ζ > 0` and complex `p`,

`∫₀^∞ e^{-ζ cosh u} cosh (p u) du = ½ (ζ / 2)^{-p} Q_p(ζ² / 4)`.

The left side converges absolutely for `Re ζ > 0` and is holomorphic in `ζ` there, so identities
proved on the positive axis extend to the right half-plane by the identity theorem. By
DLMF 9.13.4 and 10.32.9, for `n ≥ 1` and `z ≠ 0` with `|arg z| < p π`, the generalized Airy
function `A_n` of Swanson and Headley is `(2p / π) sin (p π) z^{1/2}` times Schläfli's integral
at `p = 1 / (n + 2)` and `ζ = 2p z^{(n + 2)/2}`. That representation is not proved here.

## Main results

* `Complex.integrableOn_cpow_mul_exp_neg_add_div_Ioi` and
  `Complex.continuousOn_integral_cpow_mul_exp_neg_add_div_Ioi`: `Q_a(c)` converges for `c > 0`
  and is continuous there.
* `Complex.hasMellin_integral_cpow_mul_exp_neg_add_div_Ioi`: the Mellin transform of `Q_a` is
  `Γ(t) Γ(t + a)`.
* `Complex.mellinInv_Gamma_mul_Gamma_add`: the Mellin–Barnes integral of `Q_a`.
* `Complex.integral_exp_neg_mul_cosh_mul_cosh_Ioi`: Schläfli's integral as a Macdonald integral.
* `Complex.integrable_exp_mul_mul_exp_neg_mul_cosh`: `e^{p u} e^{-ζ cosh u}` is integrable on the
  line for `Re ζ > 0`.
* `Complex.integrable_exp_neg_mul_cosh_mul_cosh` and
  `Complex.differentiableOn_integral_exp_neg_mul_cosh_mul_cosh_Ioi`: Schläfli's integrand is
  integrable on the line, and Schläfli's integral is holomorphic in `ζ` on the right half-plane.

## References

* NIST Digital Library of Mathematical Functions, equations 9.13.4, 10.32.9, 10.32.10 and
  10.43.19.
* G. N. Watson, *A Treatise on the Theory of Bessel Functions*, 2nd ed., §6.22.

The Mellin-inversion proof of `Complex.mellinInv_Gamma_mul_Gamma_add` follows that of
`Complex.mellinInv_Gamma_mul_Gamma_sub` in
`TauCeti/Analysis/SpecialFunctions/Gamma/MellinBarnes.lean`, and the holomorphy proof of
`Complex.differentiableOn_integral_exp_neg_mul_cosh_mul_cosh_Ioi` follows that of
`Complex.differentiableOn_integral_cpow_mul_exp_neg_mul_Ioi` in
`TauCeti/Analysis/SpecialFunctions/Gamma/IntegralComplexRate.lean`.
-/

public section

open Real Set MeasureTheory Filter Topology
open Complex hiding exp continuous_exp

namespace Complex

/-- For `c > 0` and every complex `a`, the Macdonald integrand `s^{a - 1} e^{-s - c/s}` is
integrable on `(0, ∞)`. -/
theorem integrableOn_cpow_mul_exp_neg_add_div_Ioi (a : ℂ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun s : ℝ ↦ (s : ℂ) ^ (a - 1) * Real.exp (-(s + c / s))) (Ioi 0) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < a.re + n :=
    ⟨⌈-a.re⌉₊ + 1, by push_cast; linarith [Nat.le_ceil (-a.re)]⟩
  refine ((Real.GammaIntegral_convergent hn).const_mul (n.factorial / c ^ n)).mono'
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
  have hexp : Real.exp (-(c / s)) ≤ n.factorial / c ^ n * s ^ n :=
    (TauCeti.exp_neg_le_factorial_div_pow (div_pos hc hs) n).trans_eq (by rw [div_pow]; field_simp)
  calc ‖(s : ℂ) ^ (a - 1) * Real.exp (-(s + c / s))‖
      = s ^ (a.re - 1) * (Real.exp (-s) * Real.exp (-(c / s))) := by
        simp [norm_cpow_eq_rpow_re_of_pos hs, norm_exp, Real.exp_add, mul_comm]
    _ ≤ s ^ (a.re - 1) * (Real.exp (-s) * (n.factorial / c ^ n * s ^ n)) := by gcongr
    _ = _ := by
        rw [add_sub_right_comm, Real.rpow_add hs, Real.rpow_natCast]
        ring

/-- The Macdonald integral `c ↦ ∫₀^∞ s^{a - 1} e^{-s - c/s} ds` is continuous on `(0, ∞)`. -/
theorem continuousOn_integral_cpow_mul_exp_neg_add_div_Ioi (a : ℂ) :
    ContinuousOn (fun c : ℝ ↦ ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (a - 1) * Real.exp (-(s + c / s)))
      (Ioi 0) := by
  intro c₀ (hc₀ : 0 < c₀)
  -- for `c > c₀ / 2` the integrand is dominated by the integrand at `c₀ / 2`
  have hnhds : Ioi (c₀ / 2) ∈ 𝓝 c₀ := Ioi_mem_nhds (half_lt_self hc₀)
  refine (continuousAt_of_dominated (bound := fun s : ℝ ↦
    ‖(s : ℂ) ^ (a - 1) * Real.exp (-(s + c₀ / 2 / s))‖) ?_ ?_
    (integrableOn_cpow_mul_exp_neg_add_div_Ioi a (half_pos hc₀)).norm ?_).continuousWithinAt
  · filter_upwards [hnhds] with c (hc : c₀ / 2 < c)
    exact (integrableOn_cpow_mul_exp_neg_add_div_Ioi a
      ((half_pos hc₀).trans hc)).aestronglyMeasurable
  · filter_upwards [hnhds] with c (hc : c₀ / 2 < c)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
    rw [norm_mul, norm_mul, norm_real, norm_real, Real.norm_of_nonneg (exp_pos _).le,
      Real.norm_of_nonneg (exp_pos _).le]
    gcongr
  · exact Eventually.of_forall fun s ↦ by fun_prop

/-- **The Mellin transform of the Macdonald integral** (the integral form of DLMF 10.43.19). For
`Re t > 0` and `Re (t + a) > 0`, the Mellin transform of `c ↦ ∫₀^∞ s^{a - 1} e^{-s - c/s} ds`
converges at `t` and equals `Γ(t) Γ(t + a)`. -/
theorem hasMellin_integral_cpow_mul_exp_neg_add_div_Ioi {a t : ℂ} (ht : 0 < t.re)
    (hta : 0 < (t + a).re) :
    HasMellin (fun c : ℝ ↦ ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (a - 1) * Real.exp (-(s + c / s))) t
      (Gamma t * Gamma (t + a)) := by
  -- the Macdonald integral is the multiplicative convolution of `s^a e^{-s}` with `e^{-s}`
  have hf : MellinConvergent (fun s : ℝ ↦ (s : ℂ) ^ a • (Real.exp (-s) : ℂ)) t :=
    MellinConvergent.cpow_smul.mpr <|
      (GammaIntegral_convergent hta).congr_fun (fun _ _ ↦ mul_comm _ _) measurableSet_Ioi
  have h := TauCeti.hasMellin_mellinConv hf (TauCeti.hasMellin_exp_neg ht).1
  rw [mellin_cpow_smul, (TauCeti.hasMellin_exp_neg hta).2, (TauCeti.hasMellin_exp_neg ht).2,
    mul_comm] at h
  refine (TauCeti.hasMellin_congr fun c _ ↦ (TauCeti.mellinConv_def _ _ c).trans <|
    setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) ↦ ?_).mp h
  rw [smul_eq_mul, cpow_sub _ _ (ofReal_ne_zero.mpr hs.ne'), cpow_one, neg_add, Real.exp_add]
  push_cast
  ring

/-- **The Mellin–Barnes integral of the Macdonald integral.** On every vertical line
`Re t = σ` with `σ > 0` and `σ + Re a > 0`, Mellin inversion of `Γ(t) Γ(t + a)` gives
`∫₀^∞ s^{a - 1} e^{-s - c/s} ds` for `c > 0`. -/
theorem mellinInv_Gamma_mul_Gamma_add {a : ℂ} {σ : ℝ} (hσ : 0 < σ) (hσa : 0 < σ + a.re) {c : ℝ}
    (hc : 0 < c) :
    mellinInv σ (fun t ↦ Gamma t * Gamma (t + a)) c =
      ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (a - 1) * Real.exp (-(s + c / s)) := by
  set f : ℝ → ℂ := fun c ↦ ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (a - 1) * Real.exp (-(s + c / s))
  have hline (y : ℝ) : Gamma (σ + y * I) * Gamma (σ + y * I + a) = mellin f (σ + y * I) :=
    ((hasMellin_integral_cpow_mul_exp_neg_add_div_Ioi (by simpa using hσ)
      (by simpa using hσa)).2).symm
  have hint : VerticalIntegrable (mellin f) σ :=
    (verticalIntegrable_Gamma_mul_Gamma_add (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])
      (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])).congr (Eventually.of_forall hline)
  have hconv : MellinConvergent f σ :=
    (hasMellin_integral_cpow_mul_exp_neg_add_div_Ioi (t := σ) (a := a) (by simpa using hσ)
      (by simpa using hσa)).1
  rw [mellinInv]
  simp_rw [hline]
  rw [← mellinInv, mellinInv_mellin_eq σ f hc hconv hint
    ((continuousOn_integral_cpow_mul_exp_neg_add_div_Ioi a).continuousAt (Ioi_mem_nhds hc))]

/-- For `ζ > 0` and `s > 0`, `s + (ζ² / 4) / s = (ζ / 2) (x + x⁻¹)` at `x = (2 / ζ) s`. -/
private lemma integrand_eq_comp_mul_left {ζ : ℝ} (hζ : 0 < ζ) (p : ℂ) :
    EqOn (fun s : ℝ ↦ (s : ℂ) ^ (p - 1) * Real.exp (-(s + ζ ^ 2 / 4 / s)))
      (fun s : ℝ ↦ (s : ℂ) ^ (p - 1) •
        ((Real.exp (-(ζ / 2 * (2 / ζ * s + (2 / ζ * s)⁻¹))) : ℝ) : ℂ)) (Ioi 0) := by
  intro s (hs : 0 < s)
  simp only [smul_eq_mul]
  congr 4
  field_simp
  ring

/-- The Mellin transform of `x ↦ e^{-(ζ / 2)(x + x⁻¹)}` converges at every `p` for `ζ > 0`. -/
private lemma mellinConvergent_exp_neg_mul_add_inv {ζ : ℝ} (hζ : 0 < ζ) (p : ℂ) :
    MellinConvergent (fun x : ℝ ↦ ((Real.exp (-(ζ / 2 * (x + x⁻¹))) : ℝ) : ℂ)) p :=
  (MellinConvergent.comp_mul_left (div_pos two_pos hζ)).mp
    ((integrableOn_cpow_mul_exp_neg_add_div_Ioi p (c := ζ ^ 2 / 4) (by positivity)).congr_fun
      (integrand_eq_comp_mul_left hζ p) measurableSet_Ioi)

/-- In logarithmic coordinates `x = e^{-u}`, `(ζ / 2) (x + x⁻¹) = ζ cosh u`. -/
private lemma exp_neg_mul_add_inv_exp_neg (ζ u : ℝ) :
    ((Real.exp (-(ζ / 2 * (Real.exp (-u) + (Real.exp (-u))⁻¹))) : ℝ) : ℂ) =
      cexp (-((ζ : ℂ) * Real.cosh u)) := by
  rw [Real.cosh_eq, ← Real.exp_neg, neg_neg, ofReal_exp]
  push_cast
  ring_nf

/-- The real-`ζ` case of `integrable_exp_mul_mul_exp_neg_mul_cosh`, from the convergence of the
Mellin transform of `x ↦ e^{-(ζ / 2)(x + x⁻¹)}` in logarithmic coordinates. -/
private lemma integrable_exp_mul_mul_exp_neg_mul_cosh_of_real {ζ : ℝ} (hζ : 0 < ζ) (p : ℂ) :
    Integrable (fun u : ℝ ↦ cexp (p * u) * cexp (-((ζ : ℂ) * Real.cosh u))) := by
  have h := (TauCeti.mellinConvergent_iff_integrable_exp_smul _ (-p)).mp
    (mellinConvergent_exp_neg_mul_add_inv hζ (-p))
  simpa only [neg_neg, exp_neg_mul_add_inv_exp_neg, smul_eq_mul] using h

/-- For `Re ζ > 0` and every complex `p`, `u ↦ e^{p u} e^{-ζ cosh u}` is integrable on the real
line. -/
theorem integrable_exp_mul_mul_exp_neg_mul_cosh {ζ : ℂ} (hζ : 0 < ζ.re) (p : ℂ) :
    Integrable (fun u : ℝ ↦ cexp (p * u) * cexp (-(ζ * Real.cosh u))) := by
  refine (integrable_exp_mul_mul_exp_neg_mul_cosh_of_real hζ p).norm.mono'
    (Measurable.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun u ↦ le_of_eq ?_)
  simp only [norm_mul, norm_exp_neg_mul_ofReal, ofReal_re]

/-- **Schläfli's integral as a Macdonald integral.** For `ζ > 0` and every complex `p`, the
substitution `s = (ζ / 2) e^u` gives
`∫₀^∞ e^{-ζ cosh u} cosh (p u) du = ½ (ζ / 2)^{-p} ∫₀^∞ s^{p - 1} e^{-s - (ζ² / 4) / s} ds`.
Both sides are classically `K_p(ζ)` (DLMF 10.32.9–10.32.10). -/
theorem integral_exp_neg_mul_cosh_mul_cosh_Ioi {ζ : ℝ} (hζ : 0 < ζ) (p : ℂ) :
    ∫ u in Ioi (0 : ℝ), cexp (-((ζ : ℂ) * Real.cosh u)) * Complex.cosh (p * u) =
      (ζ / 2 : ℂ) ^ (-p) / 2 *
        ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (p - 1) * Real.exp (-(s + ζ ^ 2 / 4 / s)) := by
  set F : ℝ → ℂ := fun u ↦ cexp (-p * u) * cexp (-((ζ : ℂ) * Real.cosh u)) with hF
  have hk : 0 < 2 / ζ := div_pos two_pos hζ
  have hFint : Integrable F := integrable_exp_mul_mul_exp_neg_mul_cosh_of_real hζ (-p)
  -- the Mellin transform of `x ↦ e^{-(ζ / 2)(x + x⁻¹)}` at `p` is `∫_ℝ F`
  have hmellin : mellin (fun x : ℝ ↦ ((Real.exp (-(ζ / 2 * (x + x⁻¹))) : ℝ) : ℂ)) p =
      ∫ u, F u := by
    simp only [TauCeti.mellin_eq_integral_exp_smul, exp_neg_mul_add_inv_exp_neg, smul_eq_mul, hF]
  -- folding `∫_ℝ F` onto the half-line gives `2 ∫₀^∞ e^{-ζ cosh u} cosh (p u) du`
  have hsplit : ∫ u, F u =
      2 * ∫ u in Ioi (0 : ℝ), cexp (-((ζ : ℂ) * Real.cosh u)) * Complex.cosh (p * u) := by
    rw [← intervalIntegral.integral_Iic_add_Ioi hFint.integrableOn hFint.integrableOn,
      ← neg_zero, ← integral_comp_neg_Ioi, neg_zero,
      ← integral_add hFint.comp_neg.integrableOn hFint.integrableOn, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
    simp only [hF, ofReal_neg, Real.cosh_neg, mul_neg, neg_mul, neg_neg]
    rw [mul_left_comm, two_cosh]
    ring
  -- the two scale factors cancel; the first factor is a nonnegative real, so that
  -- `ofReal_mul_cpow` merges the two powers
  have hcancel : (ζ / 2 : ℂ) * (2 / ζ) = 1 := by
    field_simp [ofReal_ne_zero.mpr hζ.ne']
  have hunit : (ζ / 2 : ℂ) ^ (-p) * ((2 / ζ : ℝ) : ℂ) ^ (-p) = 1 := by
    have h := ofReal_mul_cpow (half_pos hζ).le ((2 / ζ : ℝ) : ℂ) (-p)
    push_cast at h ⊢
    rw [← h, hcancel, one_cpow]
  rw [setIntegral_congr_fun measurableSet_Ioi (integrand_eq_comp_mul_left hζ p), ← mellin,
    mellin_comp_mul_left (fun x : ℝ ↦ ((Real.exp (-(ζ / 2 * (x + x⁻¹))) : ℝ) : ℂ)) p hk,
    hmellin, hsplit, smul_eq_mul]
  linear_combination
    -(∫ u in Ioi (0 : ℝ), cexp (-((ζ : ℂ) * Real.cosh u)) * Complex.cosh (p * u)) * hunit

/-- For `Re ζ > 0` and every complex `p`, Schläfli's integrand `e^{-ζ cosh u} cosh (p u)` is
integrable on the real line. -/
theorem integrable_exp_neg_mul_cosh_mul_cosh {ζ : ℂ} (hζ : 0 < ζ.re) (p : ℂ) :
    Integrable (fun u : ℝ ↦ cexp (-(ζ * Real.cosh u)) * Complex.cosh (p * u)) := by
  refine (((integrable_exp_mul_mul_exp_neg_mul_cosh hζ p).norm.add
    (integrable_exp_mul_mul_exp_neg_mul_cosh hζ (-p)).norm).div_const 2).mono'
    (Measurable.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun u ↦ ?_)
  rw [Pi.add_apply, mul_comm, neg_mul]
  exact norm_cosh_mul_le _ _

/-- **Schläfli's integral is holomorphic** in `ζ` on the right half-plane: for every complex `p`,
`ζ ↦ ∫₀^∞ e^{-ζ cosh u} cosh (p u) du` is complex differentiable on `Re ζ > 0`. -/
theorem differentiableOn_integral_exp_neg_mul_cosh_mul_cosh_Ioi (p : ℂ) :
    DifferentiableOn ℂ
      (fun ζ : ℂ ↦ ∫ u in Ioi (0 : ℝ), cexp (-(ζ * Real.cosh u)) * Complex.cosh (p * u))
      {ζ | 0 < ζ.re} := by
  intro ζ₀ (hζ₀ : 0 < ζ₀.re)
  -- on the ball of radius `δ = Re ζ₀ / 2` about `ζ₀` we have `Re ζ > δ`
  set δ := ζ₀.re / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hball : Metric.ball ζ₀ δ ∈ 𝓝 ζ₀ := Metric.ball_mem_nhds _ hδ0
  have hre (ζ : ℂ) (hζ : ζ ∈ Metric.ball ζ₀ δ) : δ < ζ.re := by
    rw [Metric.mem_ball, dist_eq_norm] at hζ
    have h := (abs_lt.mp ((abs_re_le_norm (ζ - ζ₀)).trans_lt hζ)).1
    rw [sub_re] at h
    linarith
  set w : ℝ → ℂ := fun u ↦ cexp (-(((δ / 2 : ℝ) : ℂ) * Real.cosh u)) with hw
  have hwδ : (0 : ℝ) < ((δ / 2 : ℝ) : ℂ).re := by simpa using half_pos hδ0
  set bound : ℝ → ℝ := fun u ↦ 2 / δ * (‖cexp (p * u) * w u‖ + ‖cexp (-p * u) * w u‖)
  have hbound : Integrable bound (volume.restrict (Ioi 0)) :=
    (((integrable_exp_mul_mul_exp_neg_mul_cosh hwδ p).norm.add
      (integrable_exp_mul_mul_exp_neg_mul_cosh hwδ (-p)).norm).const_mul (2 / δ)).integrableOn
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0))
    (F := fun ζ (u : ℝ) ↦ cexp (-(ζ * Real.cosh u)) * Complex.cosh (p * u))
    (F' := fun ζ (u : ℝ) ↦ cexp (-(ζ * Real.cosh u)) * Complex.cosh (p * u) * -(Real.cosh u))
    hball (Eventually.of_forall fun _ ↦ Measurable.aestronglyMeasurable (by fun_prop))
    (integrable_exp_neg_mul_cosh_mul_cosh hζ₀ p).integrableOn
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_ hbound ?_
  · exact h.2.differentiableAt.differentiableWithinAt
  · refine Eventually.of_forall fun u ζ hζ ↦ ?_
    have hc : 0 < Real.cosh u := Real.cosh_pos u
    calc ‖cexp (-(ζ * Real.cosh u)) * Complex.cosh (p * u) * -(Real.cosh u : ℂ)‖
        = ‖Complex.cosh (p * u)‖ * (Real.exp (-(ζ.re * Real.cosh u)) * Real.cosh u) := by
          rw [norm_mul, norm_mul, norm_neg, norm_real, Real.norm_of_nonneg hc.le,
            norm_exp_neg_mul_ofReal]
          ring
      _ ≤ ‖Complex.cosh (p * u)‖ * (2 / δ * Real.exp (-(δ / 2 * Real.cosh u))) :=
          mul_le_mul_of_nonneg_left (TauCeti.exp_neg_mul_mul_le hδ0 (hre ζ hζ).le _)
            (norm_nonneg _)
      _ = 2 / δ * (‖Complex.cosh (p * u)‖ * ‖w u‖) := by
          simp only [hw, norm_exp_neg_mul_ofReal, ofReal_re]
          ring
      _ ≤ bound u := by
          simp only [bound, ← norm_mul, neg_mul]
          gcongr
          linarith [norm_cosh_mul_le (p * u) (w u), norm_nonneg (cexp (p * u) * w u),
            norm_nonneg (cexp (-(p * u)) * w u)]
  · refine Eventually.of_forall fun u ζ _ ↦ ?_
    exact (((hasDerivAt_id' ζ).mul_const (Real.cosh u : ℂ)).neg.cexp.mul_const
      (Complex.cosh (p * u))).congr_deriv (by simp only [Pi.neg_apply]; ring)

end Complex

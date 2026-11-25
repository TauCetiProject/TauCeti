/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Divisor.JointSmooth
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.FieldTopology
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Polynomial
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.FDeriv.OfReal
import TauCeti.Analysis.Calculus.IteratedFDeriv.Reciprocal
import TauCeti.Analysis.PDE.Vortex.Reduced.HigherSmoothness
import TauCeti.Analysis.Polynomial.Monic.OfCoeff
import TauCeti.Analysis.Polynomial.Sobolev
import TauCeti.Analysis.Sobolev.BesselPotential.CompactFamily
import TauCeti.Analysis.Sobolev.BesselPotential.Exp
import TauCeti.Analysis.Sobolev.BesselPotential.SmoothFamily
import TauCeti.Analysis.Sobolev.BesselPotential.SmoothMultiplier
import TauCeti.Analysis.Sobolev.BesselPotential.ZeroAtInfty
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic

/-!
# The normalized family of plane vortices over the divisor space

For `c ∈ ℂᵐ`, `m ≥ 1`, let `P_c = TauCeti.Polynomial.monicOfCoeff c`, the monic polynomial whose
lower coefficients `c` are the symmetric coordinates of its zero divisor in `Sym^m ℂ`, collisions
of zeros included. Taubes's plane vortex with this divisor is `x_c = polynomialVortex P_c`, with
section `exp (u₀ + w_c) P_c`, where `u₀ = -log (1 + ‖P_c‖²) / 2` and `w_c` is the reduced
solution. Its phase tends to the winding phase `(z / |z|)ᵐ` only like `1 / |z|`, so `x_c` itself
need not lie in the affine Sobolev space `A_m^s = x_m + H^s(ℂ)⁴`. The **normalized vortex**

`y_c = g_c · x_c`    (`TauCeti.Vortex.normalizedVortex`)

applies the end-normalizing polynomial gauge `g_c = TauCeti.Vortex.polynomialGauge c`; it lies in
every `A_m^s` (`TauCeti.Vortex.normalizedVortex_mem_framedFieldSpace`), and its gauge orbit is the
vortex orbit with divisor `P_c`. This file proves that these representatives form a smooth family:
the coordinates `y_c - x_m ∈ H^s(ℂ)⁴` depend smoothly on `c` for every `s ≥ 0`
(`TauCeti.Vortex.SobolevFieldSpace.contDiff_subRef_normalizedVortex`). Through the elementary
symmetric chart `Sym.coeffHomeomorph` this is a smooth family of representatives over every compact
window of divisors, collisions included, with exterior phase the fixed winding phase, smooth in
the Sobolev topology of `A_m^s`, which is the topology of the Coulomb slice charts of the vortex
moduli space.

**The proof.** Fix `c₀`. The difference `y_c - y_{c₀}` is the sum of three kinds of terms.

* *The reduced solution.* The connection of `y_c` contains the derivatives of `w_c`, and its
  section the factor `exp w_c`. By `TauCeti.Vortex.contDiff_ofRealSobolevFunction_reducedSolution`,
  `w_c` is smooth in every `H^s(ℂ)`, and the derivatives and `u ↦ exp u - 1` act smoothly on
  `H^s(ℂ)`, `s > 1`.
* *The core of the background.* The rest of `y_c` is the normalized background field, built from
  `u₀`, `P_c` and `g_c`, jointly smooth in `(c, z)`. Cut off by `1 - χ`, for a cutoff `χ` equal to
  `1` outside a large disc, it is compactly supported in a fixed disc, so it is smooth in every
  `H^s(ℂ)` (`BesselPotentialSpace.exists_contDiff_inclusionLp_ae_eq_of_forall_le_norm`).
* *The exterior of the background.* Outside that disc the polynomial gauge has turned the phase of
  `P_c` into the winding phase, and the background field of `c` is obtained from that of `c₀` by
  the complex gauge `exp (V_c / 2)`: its section is multiplied by `exp (V_c / 2)` and its connection
  changes by `(-∂_I V_c / 2, ∂_1 V_c / 2)`, where `V_c = log ((1 - φ_c) / (1 - φ_{c₀}))` and
  `φ_c = (1 + ‖P_c‖²)⁻¹`. With a weight `μ` equal to `(1 - φ_{c₀})⁻¹` outside a disc,
  `U_c = μ (φ_{c₀} - φ_c)` is smooth in `H^(k+1)(ℂ)` and vanishes at `c₀`, and
  `V_c = log (1 + U_c)` is its image under the smooth local inverse of `u ↦ exp u - 1` near `0`
  (`BesselPotentialSpace.exists_contDiffAt_expSubOne_eq`). Multiplied by `χ`, these terms are
  smooth in `H^k(ℂ)`.

## Main definitions

* `TauCeti.Vortex.SobolevFieldSpace.normalizedVortex`: the normalized vortex
  `TauCeti.Vortex.normalizedVortex c = g_c · x_c` (defined, with its joint smoothness in `(c, z)`,
  in `Divisor/JointSmooth.lean`) as a point of `A_m^s`.

## Main results

* `TauCeti.Vortex.normalizedVortex_mem_framedFieldSpace`: `y_c` lies in every `A_m^s`.
* `TauCeti.Vortex.SobolevFieldSpace.contDiff_subRef_normalizedVortex`: the coordinates of `y_c` in
  `H^s(ℂ)⁴` are smooth in `c`, for every `s ≥ 0`.
* `TauCeti.Vortex.SobolevFieldSpace.continuous_normalizedVortex`: `c ↦ y_c` is continuous into
  `A_m^s`.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

open Complex Filter Metric MeasureTheory Module Set Topology TemperedDistribution
  BesselPotentialSpace
open scoped ContDiff BesselPotentialSpace InnerProductSpace

namespace TauCeti.Vortex

open TauCeti.Polynomial

variable {m : ℕ}

/-- **The normalized vortex lies in every `A_m^s`.** -/
theorem normalizedVortex_mem_framedFieldSpace (hm : 0 < m) (f : ContDiffBump (0 : ℝ))
    (c : Fin m → ℂ) (s : ℝ) : normalizedVortex c ∈ framedFieldSpace f m s := by
  have hP := monic_monicOfCoeff c
  have hd : 0 < (monicOfCoeff c).natDegree := by rwa [natDegree_monicOfCoeff]
  have hframe := tendsto_sectionValue_polynomialVortex hP hd
  rw [natDegree_monicOfCoeff] at hframe
  rw [normalizedVortex_def]
  exact (gaugeTransform_polynomialGauge_mem_framedFieldSpace f (contDiff_polynomialVortex _)
    (equation_polynomialVortex hP hd) hframe (ρ := fun z ↦
      Real.exp (backgroundAmplitude (monicOfCoeff c).eval z + reducedSolution (monicOfCoeff c) z))
    fun z ↦ sectionValue_polynomialVortex _ z).1 s

/-! ### The background and reduced parts of the normalized vortex -/

/-- The background amplitude `u₀ = -log (1 + ‖P_c‖²) / 2` of `P_c`. -/
private abbrev bgAmp (c : Fin m → ℂ) : ℂ → ℝ :=
  backgroundAmplitude (monicOfCoeff c).eval

/-- The reduced solution `w_c` of `P_c`. -/
private abbrev redSol (c : Fin m → ℂ) : ℂ → ℝ :=
  reducedSolution (monicOfCoeff c)

/-- The connection coordinate `∂_v u₀ - Im (conj g_c ∂_{I v} g_c)` of the normalized background
field along the direction `v`: its two connection coordinates are `-bgConn c I` and
`bgConn c 1`. -/
private def bgConn (c : Fin m → ℂ) (v z : ℂ) : ℝ :=
  fderiv ℝ (bgAmp c) z v - gaugeForm (polynomialGauge c) z (I * v)

/-- The section `p + i q` of the normalized background field, `g_c exp (u₀) P_c / 2`. -/
private def bgSection (c : Fin m → ℂ) (z : ℂ) : ℂ :=
  (polynomialGauge c z : ℂ) * ((Real.exp (bgAmp c z) : ℂ) * (monicOfCoeff c).eval z) / 2

private theorem contDiff_bgAmp (c : Fin m → ℂ) : ContDiff ℝ ∞ (bgAmp c) :=
  contDiff_backgroundAmplitude ((monicOfCoeff c).differentiable.contDiff.restrict_scalars ℝ)

private theorem normalizedVortex_apply_zero (c : Fin m → ℂ) (z : ℂ) :
    normalizedVortex c z 0 = -(bgConn c I z + fderiv ℝ (redSol c) z I) := by
  have hu := ((contDiff_bgAmp c).differentiable (by simp)) z
  have hw := ((contDiff_reducedSolution (monicOfCoeff c)).differentiable (by simp)) z
  simp only [normalizedVortex_def, gaugeTransform_apply, polynomialVortex_def, bgConn,
    Matrix.cons_val_zero, amplitudeField_apply_zero, fderiv_fun_add hu hw, add_apply, I_mul_I,
    map_neg]
  ring

private theorem normalizedVortex_apply_one (c : Fin m → ℂ) (z : ℂ) :
    normalizedVortex c z 1 = bgConn c 1 z + fderiv ℝ (redSol c) z 1 := by
  have hu := ((contDiff_bgAmp c).differentiable (by simp)) z
  have hw := ((contDiff_reducedSolution (monicOfCoeff c)).differentiable (by simp)) z
  simp only [normalizedVortex_def, polynomialVortex_def, gaugeTransform_apply,
    amplitudeField_apply_one, fderiv_fun_add hu hw, add_apply, gaugeForm_apply, Matrix.cons_val_one,
    Matrix.cons_val_zero, bgConn, mul_one]
  ring

private theorem normalizedVortex_apply_two_add_three (c : Fin m → ℂ) (z : ℂ) :
    (normalizedVortex c z 2 : ℂ) + normalizedVortex c z 3 * I =
      bgSection c z * Real.exp (redSol c z) := by
  -- The section of `y_c`, twice the left side, is `g_c exp (u₀ + w_c) P_c`.
  have h := sectionValue_gaugeTransform (polynomialGauge c) (polynomialVortex (monicOfCoeff c)) z
  rw [sectionValue_polynomialVortex, ← normalizedVortex_def, sectionValue_apply, Real.exp_add,
    ofReal_mul] at h
  rw [bgSection]
  linear_combination h / 2

/-! ### The background field outside a disc -/

/-- The defect `φ_c = (1 + ‖P_c‖²)⁻¹`. -/
private abbrev defect (c : Fin m → ℂ) (z : ℂ) : ℝ :=
  (1 + ‖(monicOfCoeff c).eval z‖ ^ 2)⁻¹

/-- The logarithm `Λ_c = log (1 - φ_c) / 2` of the modulus `‖P_c‖ / √(1 + ‖P_c‖²)` of the
background section. -/
private abbrev logMod (c : Fin m → ℂ) (z : ℂ) : ℝ :=
  Real.log (1 - defect c z) / 2

/-- Where `P_c` does not vanish, `Λ_c = u₀ + log ‖P_c‖`. -/
private theorem logMod_eq (c : Fin m → ℂ) {z : ℂ} (hz : (monicOfCoeff c).eval z ≠ 0) :
    logMod c z = bgAmp c z + Real.log ‖(monicOfCoeff c).eval z‖ := by
  have h1 : (0 : ℝ) < 1 + ‖(monicOfCoeff c).eval z‖ ^ 2 := by positivity
  have hsub : 1 - (1 + ‖(monicOfCoeff c).eval z‖ ^ 2)⁻¹ =
      ‖(monicOfCoeff c).eval z‖ ^ 2 / (1 + ‖(monicOfCoeff c).eval z‖ ^ 2) := by
    field_simp
    ring
  rw [logMod, defect, hsub, Real.log_div (by positivity) h1.ne', Real.log_pow, bgAmp,
    backgroundAmplitude_apply]
  push_cast
  ring

/-- The derivative of `log ‖P_c‖` where `P_c` does not vanish:
`D log ‖P_c‖ (v) = ⟪P_c, P_c' v⟫ / ‖P_c‖²`. -/
private theorem hasFDerivAt_log_norm_eval (c : Fin m → ℂ) {z : ℂ}
    (hz : (monicOfCoeff c).eval z ≠ 0) :
    ∃ L : ℂ →L[ℝ] ℝ, HasFDerivAt (fun w ↦ Real.log ‖(monicOfCoeff c).eval w‖) L z ∧
      ∀ v, L v = ⟪(monicOfCoeff c).eval z, (monicOfCoeff c).derivative.eval z * v⟫_ℝ /
        ‖(monicOfCoeff c).eval z‖ ^ 2 := by
  have hP : HasFDerivAt (fun w ↦ (monicOfCoeff c).eval w)
      (ContinuousLinearMap.smulRight (1 : ℂ →L[ℝ] ℂ) ((monicOfCoeff c).derivative.eval z)) z :=
    ((monicOfCoeff c).hasDerivAt z).hasFDerivAt.restrictScalars ℝ |>.congr_fderiv (by ext; simp)
  refine ⟨_, ((hasFDerivAt_log_norm_of_ne hz).comp z hP :), fun v ↦ ?_⟩
  simp [div_eq_inv_mul, mul_comm]

/-- Near a point where `P_c` does not vanish, `Λ_c = u₀ + log ‖P_c‖`. -/
private theorem logMod_eventuallyEq (c : Fin m → ℂ) {z : ℂ} (hz : (monicOfCoeff c).eval z ≠ 0) :
    logMod c =ᶠ[𝓝 z] fun w ↦ bgAmp c w + Real.log ‖(monicOfCoeff c).eval w‖ := by
  filter_upwards [((monicOfCoeff c).continuous.continuousAt.eventually_ne hz)] with w hw
  exact logMod_eq c hw

/-- Where `P_c` does not vanish, `Λ_c` is differentiable. -/
private theorem differentiableAt_logMod (c : Fin m → ℂ) {z : ℂ}
    (hz : (monicOfCoeff c).eval z ≠ 0) : DifferentiableAt ℝ (logMod c) z := by
  obtain ⟨L, hL, -⟩ := hasFDerivAt_log_norm_eval c hz
  exact ((((contDiff_bgAmp c).differentiable (by simp) z).hasFDerivAt.fun_add
    hL).differentiableAt).congr_of_eventuallyEq (logMod_eventuallyEq c hz)

/-- Near a point where `P_c` does not vanish, `Λ_c = u₀ + log ‖P_c‖`, so the derivative of `Λ_c`
is that of `u₀` plus `⟪P_c, P_c' v⟫ / ‖P_c‖²`. -/
private theorem fderiv_logMod_apply (c : Fin m → ℂ) {z : ℂ} (hz : (monicOfCoeff c).eval z ≠ 0)
    (v : ℂ) :
    fderiv ℝ (logMod c) z v = fderiv ℝ (bgAmp c) z v +
      ⟪(monicOfCoeff c).eval z, (monicOfCoeff c).derivative.eval z * v⟫_ℝ /
        ‖(monicOfCoeff c).eval z‖ ^ 2 := by
  obtain ⟨L, hL, hLv⟩ := hasFDerivAt_log_norm_eval c hz
  rw [(logMod_eventuallyEq c hz).fderiv_eq,
    (((contDiff_bgAmp c).differentiable (by simp) z).hasFDerivAt.fun_add hL).fderiv, add_apply,
    hLv]

/-- Outside the disc where the polynomial gauge normalizes, the background connection coordinate
along `v` is `∂_v Λ_c - m Im (I v / z)`: the term `Im (P_c' (I v) / P_c)` of the gauge form is
`⟪P_c, P_c' v⟫ / ‖P_c‖²`, the derivative of `log ‖P_c‖`. -/
private theorem bgConn_eq (c : Fin m → ℂ) {z : ℂ} (hP : (monicOfCoeff c).eval z ≠ 0)
    (hz : m * ∑ i, ‖c i‖ ^ 2 + 2 < ‖z‖ ^ 2) (v : ℂ) :
    bgConn c v z = fderiv ℝ (logMod c) z v - m * (I * v / z).im := by
  rw [bgConn, gaugeForm_polynomialGauge_apply hz, fderiv_logMod_apply c hP]
  set P := (monicOfCoeff c).eval z
  set P' := (monicOfCoeff c).derivative.eval z
  have hn : ‖P‖ ^ 2 = P.re * P.re + P.im * P.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have key : (P' * (I * v) / P).im = ⟪P, P' * v⟫_ℝ / ‖P‖ ^ 2 := by
    rw [hn, Complex.inner, div_im, Complex.normSq_apply]
    simp only [mul_re, mul_im, I_re, I_im, conj_re, conj_im]
    field_simp
    ring
  rw [key]
  ring

/-- Outside the disc where the polynomial gauge normalizes, the background section is
`exp (Λ_c) (z / |z|)ᵐ / 2`. -/
private theorem bgSection_eq (c : Fin m → ℂ) {z : ℂ} (hP : (monicOfCoeff c).eval z ≠ 0)
    (hz : m * ∑ i, ‖c i‖ ^ 2 + 2 < ‖z‖ ^ 2) :
    bgSection c z = Real.exp (logMod c z) * windingPhase m z / 2 := by
  rw [bgSection, logMod_eq c hP, Real.exp_add, Real.exp_log (norm_pos_iff.2 hP),
    mul_left_comm, polynomialGauge_mul_eval hz.le]
  push_cast
  ring

/-! ### A common exterior over a neighbourhood of a divisor -/

/-- The squared radius `R₀` serves the coefficients near `c₀`: beyond it every `P_c`,
`c ∈ ball c₀ 1`, is nonzero and the polynomial gauge of `c` normalizes. -/
private def IsGoodRadius (c₀ : Fin m → ℂ) (R₀ : ℝ) : Prop :=
  ∀ c ∈ ball c₀ 1, ∀ z : ℂ, R₀ < ‖z‖ ^ 2 →
    (monicOfCoeff c).eval z ≠ 0 ∧ m * ∑ i, ‖c i‖ ^ 2 + 2 < ‖z‖ ^ 2

/-- Over the coefficients near `c₀`, one radius `R₀` serves: beyond it every `P_c` is nonzero and
the polynomial gauge of `c` normalizes, and slightly inside it `‖P_{c₀}‖ ≥ 1`. -/
private theorem exists_radius (hm : 0 < m) (c₀ : Fin m → ℂ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ IsGoodRadius c₀ R₀ ∧
      ∀ z : ℂ, R₀ - 1 < ‖z‖ ^ 2 → 1 ≤ ‖(monicOfCoeff c₀).eval z‖ := by
  obtain ⟨r, hr⟩ := _root_.Polynomial.exists_forall_le_norm_eval
    (P := monicOfCoeff c₀) (by rwa [natDegree_monicOfCoeff]) 1
  set A := ‖c₀‖ + 2
  have hA : 0 ≤ A ^ 2 + m * (m * A ^ 2) := by positivity
  refine ⟨A ^ 2 + m * (m * A ^ 2) + 2 + (max r 0 ^ 2 + 1), by nlinarith [sq_nonneg (max r 0)],
    fun c hc z hz ↦ ?_,
    fun z hz ↦ hr z ?_⟩
  · have hcA : ‖c‖ < ‖c₀‖ + 1 := by
      have := norm_le_norm_add_norm_sub' c c₀
      rw [← dist_eq_norm] at this
      linarith [mem_ball.1 hc]
    refine ⟨fun h0 ↦ ?_, ?_⟩
    · have hlt := norm_lt_of_isRoot_monicOfCoeff c h0
      have hzA : A ^ 2 < ‖z‖ ^ 2 := by nlinarith [sq_nonneg (max r 0), sq_nonneg (m * A)]
      have : A < ‖z‖ := lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hzA
      linarith
    · have hci (i : Fin m) : ‖c i‖ ^ 2 ≤ A ^ 2 := by
        have := norm_le_pi_norm c i
        have : 0 ≤ ‖c i‖ := norm_nonneg _
        nlinarith
      have hsum : ∑ i, ‖c i‖ ^ 2 ≤ m * A ^ 2 := by
        simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hci i
      have : (m : ℝ) * ∑ i, ‖c i‖ ^ 2 ≤ m * (m * A ^ 2) := by gcongr
      nlinarith [sq_nonneg A, sq_nonneg (max r 0)]
  · rw [Metric.mem_closedBall, dist_zero_right, not_le]
    have : max r 0 ^ 2 < ‖z‖ ^ 2 := by nlinarith [sq_nonneg A, sq_nonneg (m * A)]
    exact (le_max_left r 0).trans_lt (lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this)

/-- The cutoff equal to `1` beyond the squared radius `R₀` and to `0` inside `R₀ - 1`. -/
private abbrev innerCut (R₀ : ℝ) (z : ℂ) : ℝ :=
  Real.smoothTransition (‖z‖ ^ 2 - (R₀ - 1))

/-- The cutoff equal to `1` beyond the squared radius `R₀ + 2` and to `0` inside `R₀ + 1`. -/
private abbrev outerCut (R₀ : ℝ) : ℂ → ℝ :=
  innerCut (R₀ + 2)

private theorem contDiff_innerCut (R₀ : ℝ) : ContDiff ℝ ∞ (innerCut R₀) :=
  Real.smoothTransition.contDiff.comp ((contDiff_norm_sq ℝ).sub contDiff_const)

/-- The cutoff `innerCut R₀` is `1` outside the disc of radius `|R₀| + 1`. -/
private theorem innerCut_eq_one {R₀ : ℝ} {z : ℂ} (hz : |R₀| + 1 ≤ ‖z‖) : innerCut R₀ z = 1 :=
  Real.smoothTransition.one_of_one_le
    (by nlinarith [le_abs_self R₀, abs_nonneg R₀, mul_le_mul hz hz (by positivity) (norm_nonneg z)])

/-- The cutoff `innerCut R₀` has bounded derivatives: it is bounded by `1`, and it agrees with the
constant `1` outside a disc. -/
private theorem exists_bound_iteratedFDeriv_innerCut (R₀ : ℝ) (n : ℕ) :
    ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (innerCut R₀) z‖ ≤ C := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact ⟨1, fun z ↦ by simpa [abs_of_nonneg (Real.smoothTransition.nonneg _)] using
      Real.smoothTransition.le_one (‖z‖ ^ 2 - (R₀ - 1))⟩
  · refine ContDiff.exists_bound_iteratedFDeriv_of_eqOn_compl
      ((contDiff_innerCut R₀).of_le (by exact_mod_cast le_top)) (Nat.one_le_iff_ne_zero.2 hn)
      (isCompact_closedBall (0 : ℂ) (|R₀| + 1)) (b := (1 : ℝ)) (L := 0) fun z hz ↦ ?_
    simp only [zero_apply, add_zero]
    exact innerCut_eq_one (le_of_lt (by simpa using hz))

/-- The weight `(1 - χ₀ φ_{c₀})⁻¹`, equal to `(1 - φ_{c₀})⁻¹` beyond `R₀`. -/
private abbrev weight (c₀ : Fin m → ℂ) (R₀ : ℝ) (z : ℂ) : ℝ :=
  (1 - innerCut R₀ z * defect c₀ z)⁻¹

/-- `U_c = (φ_{c₀} - φ_c) / (1 - χ₀ φ_{c₀})`, so that `1 + U_c = (1 - φ_c) / (1 - φ_{c₀})` beyond
`R₀`. -/
private abbrev ratioSubOne (c₀ : Fin m → ℂ) (R₀ : ℝ) (c : Fin m → ℂ) (z : ℂ) : ℝ :=
  weight c₀ R₀ z * (defect c₀ z - defect c z)

/-- `V_c = log (1 + U_c)`, equal to `2 (Λ_c - Λ_{c₀})` beyond `R₀`. -/
private abbrev logRatio (c₀ : Fin m → ℂ) (R₀ : ℝ) (c : Fin m → ℂ) (z : ℂ) : ℝ :=
  Real.log (1 + ratioSubOne c₀ R₀ c z)

private theorem defect_lt_one (c : Fin m → ℂ) {z : ℂ} (hz : (monicOfCoeff c).eval z ≠ 0) :
    defect c z < 1 := by
  have : 1 < 1 + ‖(monicOfCoeff c).eval z‖ ^ 2 := by
    have := norm_pos_iff.2 hz
    nlinarith
  exact inv_lt_one_of_one_lt₀ this

private theorem innerCut_mul_defect_le {c₀ : Fin m → ℂ} {R₀ : ℝ}
    (hR : ∀ z : ℂ, R₀ - 1 < ‖z‖ ^ 2 → 1 ≤ ‖(monicOfCoeff c₀).eval z‖) (z : ℂ) :
    0 ≤ innerCut R₀ z * defect c₀ z ∧ innerCut R₀ z * defect c₀ z ≤ 1 / 2 := by
  refine ⟨mul_nonneg (Real.smoothTransition.nonneg _) (by positivity), ?_⟩
  rcases le_or_gt (‖z‖ ^ 2) (R₀ - 1) with hz | hz
  · have h0 : innerCut R₀ z = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    rw [h0, zero_mul]
    norm_num
  · have h1 := hR z hz
    have hd : defect c₀ z ≤ 1 / 2 := by
      rw [defect, inv_le_comm₀ (by positivity) (by norm_num)]
      nlinarith
    calc innerCut R₀ z * defect c₀ z ≤ 1 * defect c₀ z :=
          mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _) (by positivity)
      _ ≤ 1 / 2 := by rw [one_mul]; exact hd

/-- Beyond `R₀`, `V_c = 2 (Λ_c - Λ_{c₀})` near every point. -/
private theorem logRatio_eventuallyEq {c₀ : Fin m → ℂ} {R₀ : ℝ}
    (hR : IsGoodRadius c₀ R₀)
    {c : Fin m → ℂ} (hc : c ∈ ball c₀ 1) {z : ℂ} (hz : R₀ < ‖z‖ ^ 2) :
    logRatio c₀ R₀ c =ᶠ[𝓝 z] fun w ↦ 2 * logMod c w - 2 * logMod c₀ w := by
  have hopen : IsOpen {w : ℂ | R₀ < ‖w‖ ^ 2} :=
    isOpen_lt continuous_const (continuous_norm.pow 2)
  filter_upwards [hopen.mem_nhds hz] with w hw
  have h₀ := defect_lt_one c₀ (hR c₀ (mem_ball_self one_pos) w hw).1
  have h₁ := defect_lt_one c (hR c hc w hw).1
  have hcut : innerCut R₀ w = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith [show R₀ < ‖w‖ ^ 2 from hw])
  have hq : 1 + ratioSubOne c₀ R₀ c w = (1 - defect c w) / (1 - defect c₀ w) := by
    rw [ratioSubOne, weight, hcut, one_mul]
    generalize defect c₀ w = a at h₀ ⊢
    generalize defect c w = b at h₁ ⊢
    have : 1 - a ≠ 0 := by linarith
    field_simp
    ring
  rw [logRatio, hq, Real.log_div (by linarith) (by linarith), logMod, logMod]
  ring

/-- Beyond `R₀`, the background connection coordinates along `v` differ by `∂_v V_c / 2`. -/
private theorem bgConn_sub_eq {c₀ : Fin m → ℂ} {R₀ : ℝ} (hR : IsGoodRadius c₀ R₀)
    {c : Fin m → ℂ} (hc : c ∈ ball c₀ 1) {z : ℂ} (hz : R₀ < ‖z‖ ^ 2) (v : ℂ) :
    bgConn c v z - bgConn c₀ v z = fderiv ℝ (logRatio c₀ R₀ c) z v / 2 := by
  obtain ⟨hP, hg⟩ := hR c hc z hz
  obtain ⟨hP₀, hg₀⟩ := hR c₀ (mem_ball_self one_pos) z hz
  rw [bgConn_eq c hP hg, bgConn_eq c₀ hP₀ hg₀, (logRatio_eventuallyEq hR hc hz).fderiv_eq,
    fderiv_fun_sub ((differentiableAt_logMod c hP).const_mul 2)
      ((differentiableAt_logMod c₀ hP₀).const_mul 2), sub_apply, fderiv_const_mul
      (differentiableAt_logMod c hP), fderiv_const_mul (differentiableAt_logMod c₀ hP₀)]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- Beyond `R₀`, the background sections differ by the factor `exp (V_c / 2)`. -/
private theorem bgSection_eq_mul {c₀ : Fin m → ℂ} {R₀ : ℝ}
    (hR : IsGoodRadius c₀ R₀)
    {c : Fin m → ℂ} (hc : c ∈ ball c₀ 1) {z : ℂ} (hz : R₀ < ‖z‖ ^ 2) :
    bgSection c z = bgSection c₀ z * Real.exp (logRatio c₀ R₀ c z / 2) := by
  obtain ⟨hP, hg⟩ := hR c hc z hz
  obtain ⟨hP₀, hg₀⟩ := hR c₀ (mem_ball_self one_pos) z hz
  rw [bgSection_eq c hP hg, bgSection_eq c₀ hP₀ hg₀, (logRatio_eventuallyEq hR hc hz).self_of_nhds,
    show (2 * logMod c z - 2 * logMod c₀ z) / 2 = logMod c z - logMod c₀ z by ring,
    Real.exp_sub]
  have := Real.exp_pos (logMod c₀ z)
  push_cast
  field_simp

/-! ### The pointwise decomposition of the difference of two normalized vortices -/

/-- Multiplied by the outer cutoff, functions agreeing beyond `R₀` agree everywhere. -/
private theorem outerCut_smul_eq {M : Type*} [AddCommGroup M] [Module ℝ M] {R₀ : ℝ} {a b : ℂ → M}
    (hab : ∀ z, R₀ < ‖z‖ ^ 2 → a z = b z) (z : ℂ) :
    outerCut R₀ z • a z = outerCut R₀ z • b z := by
  rcases le_or_gt (‖z‖ ^ 2) (R₀ + 1) with hz | hz
  · have h0 : outerCut R₀ z = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    rw [h0, zero_smul, zero_smul]
  · rw [hab z (by linarith)]

section Decomposition

variable {c₀ : Fin m → ℂ} {R₀ : ℝ} {c : Fin m → ℂ}

/-- The connection part of `y_c - y_{c₀}` along `v`: the core of the background difference, the
exterior term `χ ∂_v V_c / 2` and the term `∂_v (w_c - w_{c₀})`. -/
private theorem bgConn_add_fderiv_redSol_sub_eq (hR : IsGoodRadius c₀ R₀) (hc : c ∈ ball c₀ 1)
    (v z : ℂ) :
    bgConn c v z + fderiv ℝ (redSol c) z v - (bgConn c₀ v z + fderiv ℝ (redSol c₀) z v) =
      (1 - outerCut R₀ z) * (bgConn c v z - bgConn c₀ v z) +
        outerCut R₀ z * (fderiv ℝ (logRatio c₀ R₀ c) z v / 2) +
          fderiv ℝ (fun w ↦ redSol c w - redSol c₀ w) z v := by
  have h := outerCut_smul_eq (a := fun z ↦ bgConn c v z - bgConn c₀ v z)
    (b := fun z ↦ fderiv ℝ (logRatio c₀ R₀ c) z v / 2) (fun z hz ↦ bgConn_sub_eq hR hc hz v) z
  simp only [smul_eq_mul] at h
  rw [fderiv_fun_sub (((contDiff_reducedSolution _).differentiable (by simp)) z)
    (((contDiff_reducedSolution _).differentiable (by simp)) z), sub_apply]
  linear_combination h

/-- The section of `y_c - y_{c₀}`, with `σ₀ = p + i q` the section of `y_{c₀}`, as a combination
of `bgSection c - bgSection c₀` and `σ₀` with real coefficients. -/
private theorem normalizedVortex_sub_section (hR : IsGoodRadius c₀ R₀) (hc : c ∈ ball c₀ 1)
    (z : ℂ) :
    (normalizedVortex c z 2 : ℂ) + normalizedVortex c z 3 * I -
        ((normalizedVortex c₀ z 2 : ℂ) + normalizedVortex c₀ z 3 * I) =
      ((1 - outerCut R₀ z) * Real.exp (redSol c z)) • (bgSection c z - bgSection c₀ z) +
        (outerCut R₀ z * ((Real.exp (logRatio c₀ R₀ c z / 2) - 1) *
          Real.exp (redSol c z - redSol c₀ z))) •
          ((normalizedVortex c₀ z 2 : ℂ) + normalizedVortex c₀ z 3 * I) +
        (Real.exp (redSol c z - redSol c₀ z) - 1) •
          ((normalizedVortex c₀ z 2 : ℂ) + normalizedVortex c₀ z 3 * I) := by
  have hs := outerCut_smul_eq (a := fun z ↦ bgSection c z - bgSection c₀ z)
    (b := fun z ↦ bgSection c₀ z * (Real.exp (logRatio c₀ R₀ c z / 2) - 1))
    (fun z hz ↦ by rw [bgSection_eq_mul hR hc hz]; ring) z
  simp only [Complex.real_smul] at hs ⊢
  rw [normalizedVortex_apply_two_add_three, normalizedVortex_apply_two_add_three, Real.exp_sub]
  have he : (Real.exp (redSol c₀ z) : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.exp_pos _).ne'
  simp only [ofReal_mul, ofReal_sub, ofReal_one, ofReal_div]
  field_simp
  linear_combination (Real.exp (redSol c z) : ℂ) * hs

/-- An `ℝ`-linear functional `ℓ` of the section of `y_c - y_{c₀}`; `ℓ = re` and `ℓ = im` give its
third and fourth coordinates. -/
private theorem map_normalizedVortex_sub_section (hR : IsGoodRadius c₀ R₀) (hc : c ∈ ball c₀ 1)
    (ℓ : ℂ →L[ℝ] ℝ) (z : ℂ) :
    ℓ ((normalizedVortex c z 2 : ℂ) + normalizedVortex c z 3 * I) -
        ℓ ((normalizedVortex c₀ z 2 : ℂ) + normalizedVortex c₀ z 3 * I) =
      (1 - outerCut R₀ z) * Real.exp (redSol c z) * ℓ (bgSection c z - bgSection c₀ z) +
        outerCut R₀ z * ((Real.exp (logRatio c₀ R₀ c z / 2) - 1) *
          Real.exp (redSol c z - redSol c₀ z)) *
            ℓ ((normalizedVortex c₀ z 2 : ℂ) + normalizedVortex c₀ z 3 * I) +
        (Real.exp (redSol c z - redSol c₀ z) - 1) *
          ℓ ((normalizedVortex c₀ z 2 : ℂ) + normalizedVortex c₀ z 3 * I) := by
  rw [← map_sub, normalizedVortex_sub_section hR hc z]
  simp only [map_add, map_smul, smul_eq_mul]

end Decomposition

/-! ### Bounded derivatives -/

/-- The defect `φ_c` is smooth. -/
private theorem contDiff_defect (c : Fin m → ℂ) : ContDiff ℝ ∞ (defect c) :=
  (contDiff_const.add ((((monicOfCoeff c).differentiable.contDiff (n := ∞)).restrict_scalars
    ℝ).norm_sq ℝ)).inv fun _ ↦ by positivity

/-- For `m ≥ 1` the defect `φ_c`, which lies in every Sobolev space, has bounded derivatives. -/
private theorem exists_bound_iteratedFDeriv_defect (hm : 0 < m) (c : Fin m → ℂ) (n : ℕ) :
    ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (defect c) z‖ ≤ C :=
  exists_norm_iteratedFDeriv_le_of_mem_realSobolevFunctions (s := n + 2) (k := n)
    (by rw [finrank_real_complex]; push_cast; linarith)
    (_root_.Polynomial.inv_one_add_norm_eval_sq_mem_realSobolevFunctions
      (by rwa [natDegree_monicOfCoeff]) _) (contDiff_defect c).continuous le_rfl

/-- The product `χ₀ φ_{c₀}` has bounded derivatives: outside a disc it is `φ_{c₀}`. -/
private theorem exists_bound_iteratedFDeriv_innerCut_mul_defect (hm : 0 < m) (c₀ : Fin m → ℂ)
    (R₀ : ℝ) (n : ℕ) :
    ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ innerCut R₀ z * defect c₀ z) z‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_iteratedFDeriv_defect hm c₀ n
  exact (((contDiff_innerCut R₀).mul (contDiff_defect c₀)).of_le
    (by exact_mod_cast le_top)).exists_norm_iteratedFDeriv_le_of_eq_of_lt_norm (g := defect c₀)
    (R := |R₀| + 1) (fun z hz ↦ by rw [innerCut_eq_one hz.le, one_mul]) fun z _ ↦ hC z

private theorem contDiff_weight {c₀ : Fin m → ℂ} {R₀ : ℝ}
    (hq : ∀ z, innerCut R₀ z * defect c₀ z ≤ 1 / 2) : ContDiff ℝ ∞ (weight c₀ R₀) :=
  (contDiff_const.sub ((contDiff_innerCut R₀).mul (contDiff_defect c₀))).inv
    fun z ↦ by linarith [hq z]

/-- The weight `(1 - χ₀ φ_{c₀})⁻¹` has bounded derivatives. -/
private theorem exists_bound_iteratedFDeriv_weight (hm : 0 < m) {c₀ : Fin m → ℂ} {R₀ : ℝ}
    (hq : ∀ z, 0 ≤ innerCut R₀ z * defect c₀ z ∧ innerCut R₀ z * defect c₀ z ≤ 1 / 2) (n : ℕ) :
    ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (weight c₀ R₀) z‖ ≤ C := by
  have hh : ContDiff ℝ ∞ fun z ↦ innerCut R₀ z * defect c₀ z :=
    (contDiff_innerCut R₀).mul (contDiff_defect c₀)
  choose B hB using exists_bound_iteratedFDeriv_innerCut_mul_defect hm c₀ R₀
  set C := max 1 (∑ i ∈ Finset.range (n + 1), |B i|)
  refine ⟨(n.factorial : ℝ) ^ 2 * C ^ n / (1 / 2) ^ (n + 1), fun z ↦ ?_⟩
  refine norm_iteratedFDeriv_inv_comp_le ((contDiff_const.sub hh).of_le
    (by exact_mod_cast le_top)) (by norm_num) (by norm_num) ?_ (le_max_left _ _)
    fun i hi hin ↦ ?_
  · rw [Real.norm_eq_abs, abs_of_pos (by linarith [(hq z).2])]
    linarith [(hq z).2]
  -- In positive order, the derivatives of `1 - χ₀ φ_{c₀}` are those of `-χ₀ φ_{c₀}`.
  rw [fun_iteratedFDeriv_sub_apply contDiffAt_const
    (hh.contDiffAt.of_le (by exact_mod_cast le_top)), iteratedFDeriv_const_of_ne (by omega),
    Pi.zero_apply, zero_sub, norm_neg]
  exact (hB i z).trans ((le_abs_self _).trans ((Finset.single_le_sum (f := fun i ↦ |B i|)
    (fun _ _ ↦ abs_nonneg _) (Finset.mem_range.2 (by omega))).trans (le_max_right _ _)))

/-! ### Joint smoothness of the background field -/

private theorem contDiff_gaugeForm_uncurry (v : ℂ) :
    ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ gaugeForm (polynomialGauge p.1) p.2 v := by
  simp only [gaugeForm_apply]
  exact imCLM.contDiff.comp ((conjCLE.contDiff.comp contDiff_polynomialGauge).mul
    (ContDiff.fderiv_apply (f := fun p : (Fin m → ℂ) × ℂ ↦ fun z ↦ (polynomialGauge p.1 z : ℂ))
      (contDiff_polynomialGauge.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd
      contDiff_const (by simp)))

private theorem contDiff_bgConn_uncurry (v : ℂ) :
    ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ bgConn p.1 v p.2 :=
  (ContDiff.fderiv_apply (f := fun p : (Fin m → ℂ) × ℂ ↦ bgAmp p.1)
    ((contDiff_parametric_backgroundAmplitude (n := ∞) (f := fun c ↦ (monicOfCoeff c).eval)
      ((contDiff_eval_monicOfCoeff contDiff_fst contDiff_snd).restrict_scalars ℝ)).comp
      (contDiff_fst.fst.prodMk contDiff_snd))
    contDiff_snd contDiff_const (by simp)).sub (contDiff_gaugeForm_uncurry (I * v))

private theorem contDiff_bgSection_uncurry :
    ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ bgSection p.1 p.2 := by
  have hP : ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ (monicOfCoeff p.1).eval p.2 :=
    (contDiff_eval_monicOfCoeff contDiff_fst contDiff_snd).restrict_scalars ℝ
  exact (contDiff_polynomialGauge.mul ((ofRealCLM.contDiff.comp (Real.contDiff_exp.comp
    (contDiff_parametric_backgroundAmplitude (f := fun c ↦ (monicOfCoeff c).eval) hP))).mul
    hP)).div_const 2

/-! ### The logarithmic ratio as a smooth family in `H^(k+1)` -/

/-- The complexification `z ↦ (g z : ℂ)` of a smooth real function `g` with bounded derivatives
has bounded derivatives. -/
private theorem exists_bound_iteratedFDeriv_ofReal {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hbd : ∀ n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n g z‖ ≤ C) (n : ℕ) :
    ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ (g z : ℂ)) z‖ ≤ C :=
  ofRealCLM.exists_bound_iteratedFDeriv_comp_left (hg.of_le (by exact_mod_cast le_top))
    (fun i _ ↦ hbd i) n le_rfl

/-- Multiplication by a smooth real function `g` with bounded derivatives, on `H^N(ℂ)`. -/
private theorem exists_realMulCLM {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hbd : ∀ n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n g z‖ ≤ C) (N : ℕ) :
    ∃ M : H^{(N : ℝ)}(ℂ) →L[ℂ] H^{(N : ℝ)}(ℂ), ∀ u, ⇑(inclusionLp N.cast_nonneg (M u)) =ᵐ[volume]
      fun z ↦ (g z : ℂ) * inclusionLp N.cast_nonneg u z := by
  have hbd' := exists_bound_iteratedFDeriv_ofReal hg hbd
  exact ⟨smulLeftCLMOfNormIteratedFDerivLe (by norm_num) (by norm_num) fun n _ ↦ hbd' n,
    coeFn_inclusionLp_smulLeftCLMOfNormIteratedFDerivLe_ae_eq (by norm_num) (by norm_num)
      (fun n _ ↦ hbd' n) (.of_norm_iteratedFDeriv_le (ofRealCLM.contDiff.comp hg) hbd')⟩

private theorem contDiff_ratioSubOne {c₀ : Fin m → ℂ} {R₀ : ℝ}
    (hq : ∀ z, innerCut R₀ z * defect c₀ z ≤ 1 / 2) (c : Fin m → ℂ) :
    ContDiff ℝ ∞ (ratioSubOne c₀ R₀ c) :=
  (contDiff_weight hq).mul ((contDiff_defect c₀).sub (contDiff_defect c))

/-- **The ratio `U_c` is a smooth family in `H^(k+1)`**, vanishing at `c₀`: the multiplier
`(1 - χ₀ φ_{c₀})⁻¹` applied to `φ_{c₀} - φ_c`. -/
private theorem exists_ratioSubOne_family (hm : 0 < m) (k : ℕ) (c₀ : Fin m → ℂ) {R₀ : ℝ}
    (hq : ∀ z, 0 ≤ innerCut R₀ z * defect c₀ z ∧ innerCut R₀ z * defect c₀ z ≤ 1 / 2) :
    ∃ U : (Fin m → ℂ) → H^{(k : ℝ) + 1}(ℂ), ContDiff ℝ ∞ U ∧ U c₀ = 0 ∧
      ∀ c, ⇑(inclusionLp (by positivity) (U c)) =ᵐ[volume]
        fun z ↦ (ratioSubOne c₀ R₀ c z : ℂ) := by
  have hdeg (c : Fin m → ℂ) : 0 < (monicOfCoeff c).natDegree := by rwa [natDegree_monicOfCoeff]
  set φS : (Fin m → ℂ) → H^{((k + 1 : ℕ) : ℝ)}(ℂ) := fun c ↦
    sobolevBackgroundDefect (hdeg c) (Nat.cast_nonneg _)
  -- Multiplication by the weight, which has bounded derivatives.
  obtain ⟨μ, hμ⟩ := exists_realMulCLM (contDiff_weight fun z ↦ (hq z).2)
    (exists_bound_iteratedFDeriv_weight hm hq) (k + 1)
  set ι : H^{((k + 1 : ℕ) : ℝ)}(ℂ) →L[ℂ] H^{(k : ℝ) + 1}(ℂ) :=
    BesselPotentialSpace.inclusion (Nat.cast_succ k).ge
  refine ⟨fun c ↦ ι (μ (φS c₀ - φS c)), (ι.restrictScalars ℝ).contDiff.comp
    ((μ.restrictScalars ℝ).contDiff.comp (contDiff_const.sub
      (contDiff_sobolevBackgroundDefect_monicOfCoeff hm (Nat.cast_nonneg _)))), by simp,
    fun c ↦ ?_⟩
  rw [inclusionLp_inclusion]
  filter_upwards [hμ (φS c₀ - φS c),
    coeFn_inclusionLp_sub_ae_eq _ (coeFn_inclusionLp_sobolevBackgroundDefect (hdeg c₀) _)
      (coeFn_inclusionLp_sobolevBackgroundDefect (hdeg c) _)] with z h₁ h₂
  rw [h₁, h₂, ← ofReal_sub, ← ofReal_mul]

/-- **The logarithmic ratio `V_c` is a smooth family in `H^(k+1)` near `c₀`.** There is a family of
elements of `H^(k+1)(ℂ)`, smooth at `c₀`, whose `L²` function near `c₀` is `log (1 + U_c)`, where
`1 + U_c` is positive. -/
private theorem exists_logRatio_family (hm : 0 < m) {k : ℕ} (hk : 2 ≤ k) (c₀ : Fin m → ℂ)
    {R₀ : ℝ} (hR' : ∀ z : ℂ, R₀ - 1 < ‖z‖ ^ 2 → 1 ≤ ‖(monicOfCoeff c₀).eval z‖) :
    ∃ V : (Fin m → ℂ) → H^{(k : ℝ) + 1}(ℂ), ContDiffAt ℝ ∞ V c₀ ∧
      ∀ᶠ c in 𝓝 c₀, (∀ z, 0 < 1 + ratioSubOne c₀ R₀ c z) ∧
        ⇑(inclusionLp (by positivity) (V c)) =ᵐ[volume]
          fun z ↦ (logRatio c₀ R₀ c z : ℂ) := by
  have hk1 : (finrank ℝ ℂ : ℝ) < 2 * ((k : ℝ) + 1) :=
    finrank_real_complex_lt_two_mul (by linarith [show (2 : ℝ) ≤ k from mod_cast hk])
  have hq := innerCut_mul_defect_le hR'
  obtain ⟨U, hU, hU0, hUae⟩ := exists_ratioSubOne_family hm k c₀ hq
  obtain ⟨L, hL, hL0, hLinv⟩ := exists_contDiffAt_expSubOne_eq hk1
  have hV : ContDiffAt ℝ ∞ (fun c ↦ L (U c)) c₀ :=
    (hU0 ▸ hL.restrict_scalars ℝ).comp c₀ hU.contDiffAt
  set T := toZeroAtInfty (E := ℂ) (F := ℂ) hk1
  have hUt : Tendsto (fun c ↦ ‖T (U c)‖) (𝓝 c₀) (𝓝 0) := by
    simpa [hU0, Function.comp_def] using
      ((T.continuous.tendsto _).comp (hU.continuous.tendsto c₀)).norm
  have hVt : Tendsto (fun c ↦ ‖T (L (U c))‖) (𝓝 c₀) (𝓝 0) := by
    simpa [hU0, hL0, Function.comp_def] using
      ((T.continuous.tendsto _).comp hV.continuousAt.tendsto).norm
  refine ⟨fun c ↦ L (U c), hV, ?_⟩
  filter_upwards [(hU0 ▸ hU.continuous.tendsto c₀).eventually hLinv,
    hUt.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hVt.eventually (gt_mem_nhds one_pos)] with c h₁ h₂ h₃
  have hpos (z : ℂ) : 0 < 1 + ratioSubOne c₀ R₀ c z := by
    have := norm_le_norm_toZeroAtInfty_of_ae_eq (hs := hk1) (by positivity)
      (g := fun z ↦ (ratioSubOne c₀ R₀ c z : ℂ))
      (ofRealCLM.continuous.comp (contDiff_ratioSubOne (fun z ↦ (hq z).2) c).continuous)
      (hUae c) z
    rw [norm_real, Real.norm_eq_abs] at this
    linarith [neg_abs_le (ratioSubOne c₀ R₀ c z)]
  refine ⟨hpos, ?_⟩
  have hexp := coeFn_toLp_inclusion_expSubOne hk1 (by positivity) (L (U c))
  rw [h₁, toLp_inclusion, toLp_inclusion] at hexp
  filter_upwards [coeFn_inclusionLp_ae_eq_toZeroAtInfty (hs := hk1) (by positivity) (L (U c)),
    hexp, hUae c] with z hz₁ hz₂ hz₃
  -- `exp V_c = 1 + U_c` with `|Im V_c| ≤ ‖V_c‖ < 1 < π`, so `V_c` is the real `log (1 + U_c)`.
  rw [hz₁]
  set v := T (L (U c)) z
  have he : Complex.exp v = ((1 + ratioSubOne c₀ R₀ c z : ℝ) : ℂ) := by
    have h : Complex.exp v - 1 = ratioSubOne c₀ R₀ c z := by rw [← hz₁, ← hz₂, hz₃]
    rw [ofReal_add, ofReal_one]
    linear_combination h
  have him : |v.im| < Real.pi := (abs_im_le_norm v).trans_lt
    (((ZeroAtInftyContinuousMap.norm_coe_le_norm _ z).trans_lt h₃).trans
      (by linarith [Real.two_le_pi]))
  rw [logRatio, ofReal_log (hpos z).le, ← he,
    log_exp (by linarith [neg_abs_le v.im]) (by linarith [le_abs_self v.im])]

/-! ### Families of real functions that are smooth in `H^s` at a point -/

/-- The family of real functions `F c` is smooth in `H^s(ℂ)` at `c₀`
(`BesselPotentialSpace.IsSmoothFamilyAt`). -/
private abbrev IsSmoothAt (s : ℝ) (hs : 0 ≤ s) (c₀ : Fin m → ℂ) (F : (Fin m → ℂ) → ℂ → ℝ) :
    Prop :=
  IsSmoothFamilyAt s 2 hs c₀ fun c z ↦ (F c z : ℂ)

section IsSmoothAt

variable {s : ℝ} {hs : 0 ≤ s} {c₀ : Fin m → ℂ} {F G : (Fin m → ℂ) → ℂ → ℝ}

private theorem IsSmoothAt.congr (hF : IsSmoothAt s hs c₀ F) (h : ∀ᶠ c in 𝓝 c₀, F c = G c) :
    IsSmoothAt s hs c₀ G :=
  IsSmoothFamilyAt.congr hF (h.mono fun c hc ↦ by rw [hc])

private theorem IsSmoothAt.add (hF : IsSmoothAt s hs c₀ F) (hG : IsSmoothAt s hs c₀ G) :
    IsSmoothAt s hs c₀ fun c z ↦ F c z + G c z :=
  (IsSmoothFamilyAt.add hF hG).congr (.of_forall fun _ ↦ funext fun _ ↦ (ofReal_add _ _).symm)

private theorem IsSmoothAt.sub (hF : IsSmoothAt s hs c₀ F) (hG : IsSmoothAt s hs c₀ G) :
    IsSmoothAt s hs c₀ fun c z ↦ F c z - G c z :=
  (IsSmoothFamilyAt.sub hF hG).congr (.of_forall fun _ ↦ funext fun _ ↦ (ofReal_sub _ _).symm)

private theorem IsSmoothAt.const_mul (a : ℝ) (hF : IsSmoothAt s hs c₀ F) :
    IsSmoothAt s hs c₀ fun c z ↦ a * F c z :=
  (IsSmoothFamilyAt.smul (γ := fun _ ↦ (a : ℂ)) contDiffAt_const hF).congr
    (.of_forall fun _ ↦ funext fun _ ↦ (ofReal_mul _ _).symm)

/-- Products, in the algebra `H^s(ℂ)`, `s > 1`. -/
private theorem IsSmoothAt.mul (hs' : (finrank ℝ ℂ : ℝ) < 2 * s) (hF : IsSmoothAt s hs c₀ F)
    (hG : IsSmoothAt s hs c₀ G) : IsSmoothAt s hs c₀ fun c z ↦ F c z * G c z :=
  (IsSmoothFamilyAt.mul hs' hF hG).congr (.of_forall fun _ ↦ funext fun _ ↦ (ofReal_mul _ _).symm)

/-- Exponentials, in the algebra `H^s(ℂ)`, `s > 1`. -/
private theorem IsSmoothAt.exp_sub_one (hs' : (finrank ℝ ℂ : ℝ) < 2 * s)
    (hF : IsSmoothAt s hs c₀ F) : IsSmoothAt s hs c₀ fun c z ↦ Real.exp (F c z) - 1 :=
  (IsSmoothFamilyAt.cexp_sub_one hs' hF).congr (.of_forall fun _ ↦ funext fun _ ↦ by
    rw [ofReal_sub, ofReal_exp, ofReal_one])

/-- Multiplication by a fixed real function with bounded derivatives, at an integer order. -/
private theorem IsSmoothAt.realMul {N : ℕ} {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hbd : ∀ n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n g z‖ ≤ C)
    (hF : IsSmoothAt N N.cast_nonneg c₀ F) :
    IsSmoothAt N N.cast_nonneg c₀ fun c z ↦ g z * F c z := by
  have hbd' := exists_bound_iteratedFDeriv_ofReal hg hbd
  exact (IsSmoothFamilyAt.smulLeft (by norm_num) (by norm_num) (fun n _ ↦ hbd' n)
    (.of_norm_iteratedFDeriv_le (ofRealCLM.contDiff.comp hg) hbd') hF).congr
    (.of_forall fun _ ↦ funext fun _ ↦ by rw [smul_eq_mul, ofReal_mul])

/-- Directional derivatives, from `H^(s+1)` to `H^s`. -/
private theorem IsSmoothAt.fderiv_apply (hF : IsSmoothAt (s + 1) (by linarith) c₀ F)
    (hF1 : ∀ᶠ c in 𝓝 c₀, ContDiff ℝ 1 (F c)) (v : ℂ) :
    IsSmoothAt s hs c₀ fun c z ↦ fderiv ℝ (F c) z v := by
  refine (IsSmoothFamilyAt.lineDeriv (hs := hs) ENNReal.one_lt_two ENNReal.ofNat_ne_top hF
    (hF1.mono fun c h ↦ ofRealCLM.contDiff.comp h) v).congr
    (.of_forall fun c ↦ funext fun z ↦ TauCeti.fderiv_ofReal_comp_apply (F c) z v)

end IsSmoothAt

/-! ### The pieces of the difference of two normalized vortices -/

/-- The core `(1 - χ) F_c` of a jointly smooth family is smooth in every `H^k`. -/
private theorem isSmoothAt_core {F : (Fin m → ℂ) → ℂ → ℝ}
    (hF : ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ F p.1 p.2) (R₀ : ℝ) (k : ℕ)
    (c₀ : Fin m → ℂ) :
    IsSmoothAt k k.cast_nonneg c₀ fun c z ↦ (1 - outerCut R₀ z) * F c z := by
  have hj : ContDiff ℝ ∞ (Function.uncurry fun c z ↦ (((1 - outerCut R₀ z) * F c z : ℝ) : ℂ)) :=
    ofRealCLM.contDiff.comp ((contDiff_const.sub
      ((contDiff_innerCut (R₀ + 2)).comp contDiff_snd)).mul hF)
  obtain ⟨D, hD, hDF⟩ := exists_contDiff_inclusionLp_ae_eq_of_forall_le_norm hj
    (R := |R₀ + 2| + 1) (fun c z hz ↦ by simp [innerCut_eq_one hz]) k.cast_nonneg
  exact IsSmoothFamilyAt.of_contDiff hD hDF

/-- The reduced solution `w_c` is smooth in every `H^s`. -/
private theorem isSmoothAt_redSol {s : ℝ} (hs : 0 ≤ s) (c₀ : Fin m → ℂ) :
    IsSmoothAt s hs c₀ fun c z ↦ redSol c z :=
  IsSmoothFamilyAt.of_contDiff (contDiff_ofRealSobolevFunction_reducedSolution hs)
    fun _ ↦ coeFn_inclusionLp_ofRealSobolevFunction hs _

/-- The difference `w_c - w_{c₀}` is smooth in every `H^s`. -/
private theorem isSmoothAt_redSol_sub {s : ℝ} (hs : 0 ≤ s) (c₀ : Fin m → ℂ) :
    IsSmoothAt s hs c₀ fun c z ↦ redSol c z - redSol c₀ z :=
  (isSmoothAt_redSol hs c₀).sub (.of_contDiff (D := fun _ ↦ ofRealSobolevFunction hs
    (reducedSolution_mem_realSobolevFunctions (monicOfCoeff c₀) s)) contDiff_const
    fun _ ↦ coeFn_inclusionLp_ofRealSobolevFunction hs _)

private theorem contDiff_redSol_sub (c c₀ : Fin m → ℂ) :
    ContDiff ℝ 1 fun z ↦ redSol c z - redSol c₀ z :=
  ((contDiff_reducedSolution _).sub (contDiff_reducedSolution _)).of_le (by simp)

/-- The coordinates of the normalized vortex have bounded derivatives. -/
private theorem exists_bound_iteratedFDeriv_normalizedVortex (hm : 0 < m) (c₀ : Fin m → ℂ)
    (j : Fin 4) (n : ℕ) :
    ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ normalizedVortex c₀ z j) z‖ ≤ C :=
  exists_norm_iteratedFDeriv_le_of_forall_mem_framedFieldSpace (f := ContDiffBump.mk 1 2
    one_pos one_lt_two) (contDiff_normalizedVortex c₀).continuous
    (fun k ↦ normalizedVortex_mem_framedFieldSpace hm _ c₀ k) j n

private theorem contDiff_normalizedVortex_apply (c₀ : Fin m → ℂ) (j : Fin 4) :
    ContDiff ℝ ∞ fun z ↦ normalizedVortex c₀ z j :=
  (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ).contDiff.comp
    (contDiff_normalizedVortex c₀)

/-- The common setting of the four coordinates: a radius `R₀` for the coefficients near `c₀`, and
the logarithmic ratio `V_c`, smooth in `H^(k+1)` and of class `C¹`. -/
private theorem exists_radius_isSmoothAt_logRatio (hm : 0 < m) {k : ℕ} (hk : 2 ≤ k)
    (c₀ : Fin m → ℂ) :
    ∃ R₀ : ℝ, IsGoodRadius c₀ R₀ ∧
      IsSmoothAt ((k : ℝ) + 1) (by positivity) c₀ (logRatio c₀ R₀) ∧
      ∀ᶠ c in 𝓝 c₀, ContDiff ℝ 1 (logRatio c₀ R₀ c) := by
  obtain ⟨R₀, -, hR, hR'⟩ := exists_radius hm c₀
  obtain ⟨V, hV, hVev⟩ := exists_logRatio_family hm hk c₀ hR'
  have hq := innerCut_mul_defect_le hR'
  refine ⟨R₀, hR, isSmoothFamilyAt_iff.2 ⟨V, hV, hVev.mono fun c h ↦ h.2⟩,
    hVev.mono fun c h ↦ ?_⟩
  exact (((contDiff_const.add (contDiff_ratioSubOne (fun z ↦ (hq z).2) c)).log
    fun z ↦ (h.1 z).ne').of_le (by simp))

/-- **The connection part of `y_c - y_{c₀}` along `v` is smooth in `H^k` at `c₀`.** The
connection coordinates of `y_c` are `-(bgConn c I + ∂_I w_c)` and `bgConn c 1 + ∂_1 w_c`. -/
private theorem isSmoothAt_bgConn_add_fderiv_redSol_sub (hm : 0 < m) {k : ℕ} (hk : 2 ≤ k)
    (c₀ : Fin m → ℂ) (v : ℂ) :
    IsSmoothAt k k.cast_nonneg c₀ fun c z ↦
      bgConn c v z + fderiv ℝ (redSol c) z v - (bgConn c₀ v z + fderiv ℝ (redSol c₀) z v) := by
  obtain ⟨R₀, hR, hV, hV1⟩ := exists_radius_isSmoothAt_logRatio hm hk c₀
  have hK := isSmoothAt_core (F := fun c z ↦ bgConn c v z - bgConn c₀ v z)
    ((contDiff_bgConn_uncurry v).sub ((contDiff_bgConn_uncurry v).comp
      (contDiff_const.prodMk contDiff_snd))) R₀ k c₀
  have hdV := ((hV.fderiv_apply (hs := k.cast_nonneg) hV1 v).const_mul (1 / 2)).realMul
    (g := outerCut R₀) (contDiff_innerCut (R₀ + 2)) (exists_bound_iteratedFDeriv_innerCut (R₀ + 2))
  have hdW := (isSmoothAt_redSol_sub (by positivity : (0 : ℝ) ≤ k + 1) c₀).fderiv_apply
    (hs := k.cast_nonneg) (.of_forall fun c ↦ contDiff_redSol_sub c c₀) v
  refine ((hK.add hdV).add hdW).congr ?_
  filter_upwards [ball_mem_nhds c₀ one_pos] with c hc
  funext z
  rw [bgConn_add_fderiv_redSol_sub_eq hR hc v z]
  ring

/-- **The section coordinates of `y_c - y_{c₀}` are smooth in `H^k` at `c₀`.** Here `ℓ` is `re` or
`im`, and the coordinate `j` is `ℓ` of the section. -/
private theorem isSmoothAt_normalizedVortex_sub_section (hm : 0 < m) {k : ℕ} (hk : 2 ≤ k)
    (c₀ : Fin m → ℂ) (ℓ : ℂ →L[ℝ] ℝ) (j : Fin 4)
    (hℓ : ∀ (c : Fin m → ℂ) z, ℓ ((normalizedVortex c z 2 : ℂ) + normalizedVortex c z 3 * I) =
      normalizedVortex c z j) :
    IsSmoothAt k k.cast_nonneg c₀ fun c z ↦ normalizedVortex c z j - normalizedVortex c₀ z j := by
  obtain ⟨R₀, hR, hV, -⟩ := exists_radius_isSmoothAt_logRatio hm hk c₀
  have hk0 : (finrank ℝ ℂ : ℝ) < 2 * k := finrank_real_complex_lt_two_mul (by exact_mod_cast hk)
  have hk1 : (finrank ℝ ℂ : ℝ) < 2 * ((k : ℝ) + 1) := by linarith
  have hS := contDiff_bgSection_uncurry (m := m)
  have hK := isSmoothAt_core (F := fun c z ↦ ℓ (bgSection c z - bgSection c₀ z))
    (ℓ.contDiff.comp (hS.sub (hS.comp (contDiff_const.prodMk contDiff_snd)))) R₀ k c₀
  have hw := (isSmoothAt_redSol k.cast_nonneg c₀).exp_sub_one hk0
  have hEW := (isSmoothAt_redSol_sub k.cast_nonneg c₀).exp_sub_one hk0
  have hEV : IsSmoothAt k k.cast_nonneg c₀ fun c z ↦ Real.exp (1 / 2 * logRatio c₀ R₀ c z) - 1 :=
    IsSmoothFamilyAt.mono ((hV.const_mul (1 / 2)).exp_sub_one hk1) (by linarith)
  have hy := contDiff_normalizedVortex_apply c₀ j
  have hyb := exists_bound_iteratedFDeriv_normalizedVortex hm c₀ j
  have h₁ := hK.add (hK.mul hk0 hw)
  have h₂ := ((hEV.add (hEV.mul hk0 hEW)).realMul hy hyb).realMul (g := outerCut R₀)
    (contDiff_innerCut (R₀ + 2)) (exists_bound_iteratedFDeriv_innerCut (R₀ + 2))
  refine ((h₁.add h₂).add (hEW.realMul hy hyb)).congr ?_
  filter_upwards [ball_mem_nhds c₀ one_pos] with c hc
  funext z
  have h := map_normalizedVortex_sub_section hR hc ℓ z
  rw [hℓ, hℓ] at h
  rw [h, show logRatio c₀ R₀ c z / 2 = 1 / 2 * logRatio c₀ R₀ c z by ring]
  ring

/-- **The coordinates of `y_c - y_{c₀}` are smooth in `H^k` at `c₀`.** -/
private theorem isSmoothAt_normalizedVortex_sub (hm : 0 < m) {k : ℕ} (hk : 2 ≤ k)
    (c₀ : Fin m → ℂ) (j : Fin 4) :
    IsSmoothAt k k.cast_nonneg c₀ fun c z ↦ normalizedVortex c z j - normalizedVortex c₀ z j := by
  fin_cases j
  · refine ((isSmoothAt_bgConn_add_fderiv_redSol_sub hm hk c₀ I).const_mul (-1)).congr
      (.of_forall fun c ↦ funext fun z ↦ ?_)
    simp only [Fin.zero_eta, normalizedVortex_apply_zero]
    ring
  · refine (isSmoothAt_bgConn_add_fderiv_redSol_sub hm hk c₀ 1).congr
      (.of_forall fun c ↦ funext fun z ↦ ?_)
    simp only [Fin.mk_one, normalizedVortex_apply_one]
  · exact isSmoothAt_normalizedVortex_sub_section hm hk c₀ reCLM 2 fun c z ↦ by simp
  · exact isSmoothAt_normalizedVortex_sub_section hm hk c₀ imCLM 3 fun c z ↦ by simp

/-! ### The normalized vortices as a smooth family in `A_m^s` -/

namespace SobolevFieldSpace

/-- **The normalized vortex** with divisor coefficients `c ∈ ℂᵐ`, `m ≥ 1`, as a field of the affine
Sobolev space `A_m^s` (`TauCeti.Vortex.normalizedVortex_mem_framedFieldSpace`). -/
def normalizedVortex (hm : 0 < m) (f : ContDiffBump (0 : ℝ)) (s : ℝ) (c : Fin m → ℂ) :
    SobolevFieldSpace f m s :=
  ⟨Vortex.normalizedVortex c, normalizedVortex_mem_framedFieldSpace hm f c s,
    (contDiff_normalizedVortex c).continuous⟩

@[simp]
theorem coe_normalizedVortex (hm : 0 < m) (f : ContDiffBump (0 : ℝ)) (s : ℝ) (c : Fin m → ℂ) :
    ⇑(normalizedVortex hm f s c) = Vortex.normalizedVortex c :=
  (rfl)

/-- **The normalized plane vortices form a smooth family in every Sobolev space.** For `m ≥ 1` and
`s ≥ 0`, the coordinates `y_c - x_m` in `H^s(ℂ)⁴` of the normalized vortex `y_c` with divisor
coefficients `c ∈ ℂᵐ` depend smoothly on `c`, collisions of zeros included. -/
theorem contDiff_subRef_normalizedVortex (hm : 0 < m) (f : ContDiffBump (0 : ℝ)) {s : ℝ}
    (hs : 0 ≤ s) : ContDiff ℝ ∞ fun c ↦ (normalizedVortex hm f s c).subRef := by
  refine contDiff_pi.2 fun j ↦ contDiff_iff_contDiffAt.2 fun c₀ ↦ ?_
  set k := max 2 ⌈s⌉₊
  have hsk : s ≤ k := (Nat.le_ceil s).trans (by exact_mod_cast le_max_right _ _)
  obtain ⟨D, hD, hDF⟩ :=
    isSmoothFamilyAt_iff.1 (isSmoothAt_normalizedVortex_sub hm (le_max_left 2 ⌈s⌉₊) c₀ j)
  set ι : H^{(k : ℝ)}(ℂ) →L[ℂ] H^{s}(ℂ) := BesselPotentialSpace.inclusion hsk
  refine (contDiffAt_const (c := (normalizedVortex hm f s c₀).subRef j).add
    ((ι.restrictScalars ℝ).contDiff.contDiffAt.comp c₀ hD)).congr_of_eventuallyEq ?_
  filter_upwards [hDF] with c hc
  -- `y_c - x_m = (y_{c₀} - x_m) + (y_c - y_{c₀})`.
  dsimp only [Function.comp_apply]
  refine (subRef_eq_iff hs _ j _).2 ?_
  have h₀ := (subRef_eq_iff hs (normalizedVortex hm f s c₀) j _).1 rfl
  rw [toLp_inclusion] at h₀ ⊢
  have h₁ : ⇑(inclusionLp hs (ι (D c))) =ᵐ[volume] fun z ↦
      ((Vortex.normalizedVortex c z j - Vortex.normalizedVortex c₀ z j : ℝ) : ℂ) := by
    rw [inclusionLp_inclusion]
    exact hc
  refine (coeFn_inclusionLp_add_ae_eq hs h₀ h₁).trans (.of_forall fun z ↦ ?_)
  simp only [coe_normalizedVortex]
  push_cast
  ring

/-- The normalized vortices depend continuously on their divisor coefficients in `A_m^s`. -/
theorem continuous_normalizedVortex (hm : 0 < m) (f : ContDiffBump (0 : ℝ)) {s : ℝ}
    (hs : 0 ≤ s) : Continuous (normalizedVortex hm f s) :=
  continuous_induced_rng.2 (contDiff_subRef_normalizedVortex hm f hs).continuous

end SobolevFieldSpace

end TauCeti.Vortex

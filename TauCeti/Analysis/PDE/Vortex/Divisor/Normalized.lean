/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Divisor.Family
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.FieldTopology
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Polynomial
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.Calculus.IteratedFDeriv.Reciprocal
import TauCeti.Analysis.PDE.Vortex.Reduced.HigherSmoothness
import TauCeti.Analysis.Polynomial.Monic.OfCoeff
import TauCeti.Analysis.Polynomial.Sobolev
import TauCeti.Analysis.Sobolev.BesselPotential.CompactFamily
import TauCeti.Analysis.Sobolev.BesselPotential.Exp
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
window of divisors, collisions included, with exterior phase the fixed winding phase. It is the
family through which the Coulomb slice charts of the vortex moduli space are compared with the
coordinates `c`.

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

* `TauCeti.Vortex.normalizedVortex c`: the normalized vortex `g_c · x_c` with divisor
  coefficients `c`.
* `TauCeti.Vortex.SobolevFieldSpace.normalizedVortex`: the same field as a point of `A_m^s`.

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

/-- **The normalized plane vortex** with divisor coefficients `c ∈ ℂᵐ`: Taubes's vortex
`TauCeti.Vortex.polynomialVortex` of the monic polynomial `P_c = monicOfCoeff c`, followed by its
end-normalizing gauge `TauCeti.Vortex.polynomialGauge c`, so that outside a disc its section is a
positive multiple of the winding phase `(z / |z|)ᵐ`. -/
def normalizedVortex (c : Fin m → ℂ) : ℂ → EuclideanSpace ℝ (Fin 4) :=
  gaugeTransform (polynomialGauge c) (polynomialVortex (monicOfCoeff c))

theorem normalizedVortex_def (c : Fin m → ℂ) :
    normalizedVortex c = gaugeTransform (polynomialGauge c) (polynomialVortex (monicOfCoeff c)) :=
  (rfl)

/-- The gauge `polynomialGauge c`, as a complex-valued function, is smooth. -/
private theorem contDiff_polynomialGauge_right (c : Fin m → ℂ) :
    ContDiff ℝ ∞ fun z ↦ (polynomialGauge c z : ℂ) :=
  contDiff_polynomialGauge.comp (contDiff_const.prodMk contDiff_id)

/-- The normalized vortex is smooth. -/
theorem contDiff_normalizedVortex (c : Fin m → ℂ) : ContDiff ℝ ∞ (normalizedVortex c) :=
  contDiff_gaugeTransform (by simpa using contDiff_polynomialGauge_right c)
    (contDiff_polynomialVortex _)

/-- **The normalized vortex lies in every `A_m^s`.** -/
theorem normalizedVortex_mem_framedFieldSpace (hm : 0 < m) (f : ContDiffBump (0 : ℝ))
    (c : Fin m → ℂ) (s : ℝ) : normalizedVortex c ∈ framedFieldSpace f m s := by
  have hP := monic_monicOfCoeff c
  have hd : 0 < (monicOfCoeff c).natDegree := by rwa [natDegree_monicOfCoeff]
  have hframe := tendsto_sectionValue_polynomialVortex hP hd
  rw [natDegree_monicOfCoeff] at hframe
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

/-- The first connection coordinate of the normalized background field. -/
private def bgConn0 (c : Fin m → ℂ) (z : ℂ) : ℝ :=
  -fderiv ℝ (bgAmp c) z I - gaugeForm (polynomialGauge c) z 1

/-- The second connection coordinate of the normalized background field. -/
private def bgConn1 (c : Fin m → ℂ) (z : ℂ) : ℝ :=
  fderiv ℝ (bgAmp c) z 1 - gaugeForm (polynomialGauge c) z I

/-- The section `p + i q` of the normalized background field, `g_c exp (u₀) P_c / 2`. -/
private def bgSection (c : Fin m → ℂ) (z : ℂ) : ℂ :=
  (polynomialGauge c z : ℂ) * ((Real.exp (bgAmp c z) : ℂ) * (monicOfCoeff c).eval z) / 2

private theorem contDiff_bgAmp (c : Fin m → ℂ) : ContDiff ℝ ∞ (bgAmp c) :=
  contDiff_backgroundAmplitude ((monicOfCoeff c).differentiable.contDiff.restrict_scalars ℝ)

private theorem normalizedVortex_apply_zero (c : Fin m → ℂ) (z : ℂ) :
    normalizedVortex c z 0 = bgConn0 c z - fderiv ℝ (redSol c) z I := by
  have hu := ((contDiff_bgAmp c).differentiable (by simp)) z
  have hw := ((contDiff_reducedSolution (monicOfCoeff c)).differentiable (by simp)) z
  simp only [normalizedVortex, gaugeTransform_apply, polynomialVortex_def, bgConn0,
    Matrix.cons_val_zero, amplitudeField_apply_zero, fderiv_fun_add hu hw, add_apply]
  ring

private theorem normalizedVortex_apply_one (c : Fin m → ℂ) (z : ℂ) :
    normalizedVortex c z 1 = bgConn1 c z + fderiv ℝ (redSol c) z 1 := by
  have hu := ((contDiff_bgAmp c).differentiable (by simp)) z
  have hw := ((contDiff_reducedSolution (monicOfCoeff c)).differentiable (by simp)) z
  simp only [normalizedVortex, gaugeTransform_apply, polynomialVortex_def, bgConn1,
    Matrix.cons_val_one, amplitudeField_apply_one, fderiv_fun_add hu hw,
    add_apply]
  simp
  ring

private theorem normalizedVortex_apply_two_add_three (c : Fin m → ℂ) (z : ℂ) :
    (normalizedVortex c z 2 : ℂ) + normalizedVortex c z 3 * I =
      bgSection c z * Real.exp (redSol c z) := by
  rw [normalizedVortex, gaugeTransform_apply, polynomialVortex_def, bgSection]
  simp only [amplitudeField_apply_two, amplitudeField_apply_three]
  simp only [Matrix.cons_val, Real.exp_add]
  apply Complex.ext <;> simp <;> ring

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

/-- Outside the disc where the polynomial gauge normalizes, the first connection coordinate of the
background field is `-∂_I Λ_c - m Im (1 / z)`. -/
private theorem bgConn0_eq (c : Fin m → ℂ) {z : ℂ} (hP : (monicOfCoeff c).eval z ≠ 0)
    (hz : m * ∑ i, ‖c i‖ ^ 2 + 2 < ‖z‖ ^ 2) :
    bgConn0 c z = -fderiv ℝ (logMod c) z I - m * (1 / z).im := by
  rw [bgConn0, gaugeForm_polynomialGauge_apply hz, fderiv_logMod_apply c hP]
  set P := (monicOfCoeff c).eval z
  set P' := (monicOfCoeff c).derivative.eval z
  have hn : ‖P‖ ^ 2 = P.re * P.re + P.im * P.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.inner, mul_re, mul_im, I_re, I_im, div_im, one_re, one_im,
    Complex.normSq_apply, hn, mul_one, mul_zero, conj_re, conj_im]
  field_simp
  ring

/-- Outside the disc where the polynomial gauge normalizes, the second connection coordinate of the
background field is `∂_1 Λ_c - m Im (I / z)`. -/
private theorem bgConn1_eq (c : Fin m → ℂ) {z : ℂ} (hP : (monicOfCoeff c).eval z ≠ 0)
    (hz : m * ∑ i, ‖c i‖ ^ 2 + 2 < ‖z‖ ^ 2) :
    bgConn1 c z = fderiv ℝ (logMod c) z 1 - m * (I / z).im := by
  rw [bgConn1, gaugeForm_polynomialGauge_apply hz, fderiv_logMod_apply c hP]
  set P := (monicOfCoeff c).eval z
  set P' := (monicOfCoeff c).derivative.eval z
  have hn : ‖P‖ ^ 2 = P.re * P.re + P.im * P.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.inner, mul_re, mul_im, I_re, I_im, div_im,
    Complex.normSq_apply, hn, mul_one, mul_zero, conj_re, conj_im]
  field_simp
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

/-- Over the coefficients near `c₀`, one radius `R₀` serves: beyond it every `P_c` is nonzero and
the polynomial gauge of `c` normalizes, and slightly inside it `‖P_{c₀}‖ ≥ 1`. -/
private theorem exists_radius (hm : 0 < m) (c₀ : Fin m → ℂ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧
      (∀ c ∈ ball c₀ 1, ∀ z : ℂ, R₀ < ‖z‖ ^ 2 →
        (monicOfCoeff c).eval z ≠ 0 ∧ m * ∑ i, ‖c i‖ ^ 2 + 2 < ‖z‖ ^ 2) ∧
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
private abbrev outerCut (R₀ : ℝ) (z : ℂ) : ℝ :=
  Real.smoothTransition (‖z‖ ^ 2 - (R₀ + 1))

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
    (hR : ∀ c ∈ ball c₀ 1, ∀ z : ℂ, R₀ < ‖z‖ ^ 2 →
      (monicOfCoeff c).eval z ≠ 0 ∧ m * ∑ i, ‖c i‖ ^ 2 + 2 < ‖z‖ ^ 2)
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

/-- Beyond `R₀`, the first background connection coordinates differ by `-∂_I V_c / 2`. -/
private theorem bgConn0_sub_eq {c₀ : Fin m → ℂ} {R₀ : ℝ}
    (hR : ∀ c ∈ ball c₀ 1, ∀ z : ℂ, R₀ < ‖z‖ ^ 2 →
      (monicOfCoeff c).eval z ≠ 0 ∧ m * ∑ i, ‖c i‖ ^ 2 + 2 < ‖z‖ ^ 2)
    {c : Fin m → ℂ} (hc : c ∈ ball c₀ 1) {z : ℂ} (hz : R₀ < ‖z‖ ^ 2) :
    bgConn0 c z - bgConn0 c₀ z = -(fderiv ℝ (logRatio c₀ R₀ c) z I / 2) := by
  obtain ⟨hP, hg⟩ := hR c hc z hz
  obtain ⟨hP₀, hg₀⟩ := hR c₀ (mem_ball_self one_pos) z hz
  rw [bgConn0_eq c hP hg, bgConn0_eq c₀ hP₀ hg₀, (logRatio_eventuallyEq hR hc hz).fderiv_eq,
    fderiv_fun_sub ((differentiableAt_logMod c hP).const_mul 2)
      ((differentiableAt_logMod c₀ hP₀).const_mul 2), sub_apply, fderiv_const_mul
      (differentiableAt_logMod c hP), fderiv_const_mul (differentiableAt_logMod c₀ hP₀)]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- Beyond `R₀`, the second background connection coordinates differ by `∂_1 V_c / 2`. -/
private theorem bgConn1_sub_eq {c₀ : Fin m → ℂ} {R₀ : ℝ}
    (hR : ∀ c ∈ ball c₀ 1, ∀ z : ℂ, R₀ < ‖z‖ ^ 2 →
      (monicOfCoeff c).eval z ≠ 0 ∧ m * ∑ i, ‖c i‖ ^ 2 + 2 < ‖z‖ ^ 2)
    {c : Fin m → ℂ} (hc : c ∈ ball c₀ 1) {z : ℂ} (hz : R₀ < ‖z‖ ^ 2) :
    bgConn1 c z - bgConn1 c₀ z = fderiv ℝ (logRatio c₀ R₀ c) z 1 / 2 := by
  obtain ⟨hP, hg⟩ := hR c hc z hz
  obtain ⟨hP₀, hg₀⟩ := hR c₀ (mem_ball_self one_pos) z hz
  rw [bgConn1_eq c hP hg, bgConn1_eq c₀ hP₀ hg₀, (logRatio_eventuallyEq hR hc hz).fderiv_eq,
    fderiv_fun_sub ((differentiableAt_logMod c hP).const_mul 2)
      ((differentiableAt_logMod c₀ hP₀).const_mul 2), sub_apply, fderiv_const_mul
      (differentiableAt_logMod c hP), fderiv_const_mul (differentiableAt_logMod c₀ hP₀)]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- Beyond `R₀`, the background sections differ by the factor `exp (V_c / 2)`. -/
private theorem bgSection_eq_mul {c₀ : Fin m → ℂ} {R₀ : ℝ}
    (hR : ∀ c ∈ ball c₀ 1, ∀ z : ℂ, R₀ < ‖z‖ ^ 2 →
      (monicOfCoeff c).eval z ≠ 0 ∧ m * ∑ i, ‖c i‖ ^ 2 + 2 < ‖z‖ ^ 2)
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

variable {c₀ : Fin m → ℂ} {R₀ : ℝ}
  (hR : ∀ c ∈ ball c₀ 1, ∀ z : ℂ, R₀ < ‖z‖ ^ 2 →
    (monicOfCoeff c).eval z ≠ 0 ∧ m * ∑ i, ‖c i‖ ^ 2 + 2 < ‖z‖ ^ 2)
  {c : Fin m → ℂ} (hc : c ∈ ball c₀ 1)
include hR hc

/-- The first coordinate of `y_c - y_{c₀}`: the core of the background difference, the exterior
term `-χ ∂_I V_c / 2` and the term `-∂_I (w_c - w_{c₀})`. -/
private theorem normalizedVortex_sub_apply_zero (z : ℂ) :
    normalizedVortex c z 0 - normalizedVortex c₀ z 0 =
      (1 - outerCut R₀ z) * (bgConn0 c z - bgConn0 c₀ z) -
        outerCut R₀ z * (fderiv ℝ (logRatio c₀ R₀ c) z I / 2) -
          fderiv ℝ (fun w ↦ redSol c w - redSol c₀ w) z I := by
  have h := outerCut_smul_eq (a := fun z ↦ bgConn0 c z - bgConn0 c₀ z)
    (b := fun z ↦ -(fderiv ℝ (logRatio c₀ R₀ c) z I / 2)) (fun z hz ↦ bgConn0_sub_eq hR hc hz) z
  simp only [smul_eq_mul] at h
  rw [normalizedVortex_apply_zero, normalizedVortex_apply_zero,
    fderiv_fun_sub (((contDiff_reducedSolution _).differentiable (by simp)) z)
      (((contDiff_reducedSolution _).differentiable (by simp)) z), sub_apply]
  linear_combination h

/-- The second coordinate of `y_c - y_{c₀}`. -/
private theorem normalizedVortex_sub_apply_one (z : ℂ) :
    normalizedVortex c z 1 - normalizedVortex c₀ z 1 =
      (1 - outerCut R₀ z) * (bgConn1 c z - bgConn1 c₀ z) +
        outerCut R₀ z * (fderiv ℝ (logRatio c₀ R₀ c) z 1 / 2) +
          fderiv ℝ (fun w ↦ redSol c w - redSol c₀ w) z 1 := by
  have h := outerCut_smul_eq (a := fun z ↦ bgConn1 c z - bgConn1 c₀ z)
    (b := fun z ↦ fderiv ℝ (logRatio c₀ R₀ c) z 1 / 2) (fun z hz ↦ bgConn1_sub_eq hR hc hz) z
  simp only [smul_eq_mul] at h
  rw [normalizedVortex_apply_one, normalizedVortex_apply_one,
    fderiv_fun_sub (((contDiff_reducedSolution _).differentiable (by simp)) z)
      (((contDiff_reducedSolution _).differentiable (by simp)) z), sub_apply]
  linear_combination h

/-- The section of `y_c - y_{c₀}`, with `σ₀ = p + i q` the section of `y_{c₀}`. -/
private theorem normalizedVortex_sub_section (z : ℂ) :
    ((normalizedVortex c z 2 - normalizedVortex c₀ z 2 : ℝ) : ℂ) +
        (normalizedVortex c z 3 - normalizedVortex c₀ z 3 : ℝ) * I =
      (1 - outerCut R₀ z) * ((bgSection c z - bgSection c₀ z) * Real.exp (redSol c z)) +
        outerCut R₀ z * (((normalizedVortex c₀ z 2 : ℂ) + normalizedVortex c₀ z 3 * I) *
          ((Real.exp (logRatio c₀ R₀ c z / 2) - 1) * Real.exp (redSol c z - redSol c₀ z))) +
        ((normalizedVortex c₀ z 2 : ℂ) + normalizedVortex c₀ z 3 * I) *
          (Real.exp (redSol c z - redSol c₀ z) - 1) := by
  have hs := outerCut_smul_eq (a := fun z ↦ bgSection c z - bgSection c₀ z)
    (b := fun z ↦ bgSection c₀ z * (Real.exp (logRatio c₀ R₀ c z / 2) - 1))
    (fun z hz ↦ by rw [bgSection_eq_mul hR hc hz]; ring) z
  simp only [Complex.real_smul] at hs
  have hL : ((normalizedVortex c z 2 - normalizedVortex c₀ z 2 : ℝ) : ℂ) +
      (normalizedVortex c z 3 - normalizedVortex c₀ z 3 : ℝ) * I =
      ((normalizedVortex c z 2 : ℂ) + normalizedVortex c z 3 * I) -
        ((normalizedVortex c₀ z 2 : ℂ) + normalizedVortex c₀ z 3 * I) := by
    push_cast
    ring
  rw [hL, normalizedVortex_apply_two_add_three, normalizedVortex_apply_two_add_three, Real.exp_sub,
    ofReal_div]
  have he : (Real.exp (redSol c₀ z) : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.exp_pos _).ne'
  field_simp
  linear_combination (Real.exp (redSol c z) : ℂ) * hs

/-- The third coordinate of `y_c - y_{c₀}`, the real part of the section. -/
private theorem normalizedVortex_sub_apply_two (z : ℂ) :
    normalizedVortex c z 2 - normalizedVortex c₀ z 2 =
      (1 - outerCut R₀ z) * (bgSection c z - bgSection c₀ z).re * Real.exp (redSol c z) +
        outerCut R₀ z * (normalizedVortex c₀ z 2 *
          ((Real.exp (logRatio c₀ R₀ c z / 2) - 1) * Real.exp (redSol c z - redSol c₀ z))) +
        normalizedVortex c₀ z 2 * (Real.exp (redSol c z - redSol c₀ z) - 1) := by
  have h := congrArg Complex.re (normalizedVortex_sub_section hR hc z)
  simp only [add_re, mul_re, sub_re, one_re, ofReal_re, ofReal_im, I_re, I_im, sub_im, one_im,
    mul_im, add_im, mul_zero, mul_one, sub_zero, zero_mul, add_zero] at h
  rw [sub_re]
  linear_combination h

/-- The fourth coordinate of `y_c - y_{c₀}`, the imaginary part of the section. -/
private theorem normalizedVortex_sub_apply_three (z : ℂ) :
    normalizedVortex c z 3 - normalizedVortex c₀ z 3 =
      (1 - outerCut R₀ z) * (bgSection c z - bgSection c₀ z).im * Real.exp (redSol c z) +
        outerCut R₀ z * (normalizedVortex c₀ z 3 *
          ((Real.exp (logRatio c₀ R₀ c z / 2) - 1) * Real.exp (redSol c z - redSol c₀ z))) +
        normalizedVortex c₀ z 3 * (Real.exp (redSol c z - redSol c₀ z) - 1) := by
  have h := congrArg Complex.im (normalizedVortex_sub_section hR hc z)
  simp only [add_re, mul_re, sub_re, one_re, ofReal_re, ofReal_im, I_re, I_im, sub_im, one_im,
    mul_im, add_im, mul_zero, mul_one, sub_zero, zero_mul, add_zero, zero_add] at h
  rw [sub_im]
  linear_combination h

end Decomposition

/-! ### Multipliers and bounded derivatives -/

/-- A real function with bounded derivatives of every order, complexified, has bounded
derivatives of every order. -/
private theorem exists_bound_iteratedFDeriv_ofReal {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hbd : ∀ n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n g z‖ ≤ C) (n : ℕ) :
    ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ (g z : ℂ)) z‖ ≤ C := by
  obtain ⟨C, hC⟩ := hbd n
  refine ⟨C, fun z ↦ ?_⟩
  have h := ofRealLI.norm_iteratedFDeriv_comp_left (hg.contDiffAt (x := z))
    (i := n) (by exact_mod_cast le_top)
  rw [Function.comp_def] at h
  exact (h.trans_le (hC z) :)

/-- Multiplication by a real function with bounded derivatives, as a bounded operator on
`H^N(ℂ)`. -/
private def realMulCLM (N : ℕ) {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hbd : ∀ n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n g z‖ ≤ C) :
    H^{(N : ℝ)}(ℂ) →L[ℂ] H^{(N : ℝ)}(ℂ) :=
  mapCLM (TemperedDistribution.smulLeftCLM ℂ fun z ↦ (g z : ℂ)) fun u ↦
    u.memSobolev_toDistr.smulLeftCLM_of_norm_iteratedFDeriv_le (by norm_num) (by norm_num)
      fun n _ ↦ exists_bound_iteratedFDeriv_ofReal hg hbd n

private theorem coeFn_inclusionLp_realMulCLM (N : ℕ) {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hbd : ∀ n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n g z‖ ≤ C) (u : H^{(N : ℝ)}(ℂ)) :
    ⇑(inclusionLp N.cast_nonneg (realMulCLM N hg hbd u)) =ᵐ[volume]
      fun z ↦ (g z : ℂ) * inclusionLp N.cast_nonneg u z := by
  have hgc : ContDiff ℝ ∞ fun z ↦ (g z : ℂ) := ofRealCLM.contDiff.comp hg
  have htemp : (fun z ↦ (g z : ℂ)).HasTemperateGrowth :=
    ⟨hgc, fun n ↦ by
      obtain ⟨C, hC⟩ := exists_bound_iteratedFDeriv_ofReal hg hbd n
      exact ⟨0, C, fun z ↦ by simpa using hC z⟩⟩
  obtain ⟨C, hC⟩ := exists_bound_iteratedFDeriv_ofReal hg hbd 0
  have h := coeFn_inclusionLp_ae_eq_smul_of_toDistr_eq_smulLeftCLM N.cast_nonneg N.cast_nonneg
    htemp (C := C) (fun z ↦ by simpa using hC z) (w := realMulCLM N hg hbd u)
    (toDistr_mapCLM _ _ u)
  simpa only [smul_eq_mul] using h

/-- A difference of smooth functions with bounded derivatives has bounded derivatives. -/
private theorem exists_bound_iteratedFDeriv_sub {f g : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hfb : ∀ n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n f z‖ ≤ C)
    (hgb : ∀ n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n g z‖ ≤ C) (n : ℕ) :
    ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ f z - g z) z‖ ≤ C := by
  obtain ⟨A, hA⟩ := hfb n
  obtain ⟨B, hB⟩ := hgb n
  refine ⟨A + B, fun z ↦ ?_⟩
  rw [show (fun z ↦ f z - g z) = f - g from rfl, iteratedFDeriv_sub_apply
    (hf.contDiffAt.of_le (by exact_mod_cast le_top))
    (hg.contDiffAt.of_le (by exact_mod_cast le_top))]
  exact (norm_sub_le _ _).trans (add_le_add (hA z) (hB z))

/-- Constants have bounded derivatives. -/
private theorem exists_bound_iteratedFDeriv_const (a : ℝ) (n : ℕ) :
    ∃ C, ∀ z : ℂ, ‖iteratedFDeriv ℝ n (fun _ : ℂ ↦ a) z‖ ≤ C := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact ⟨‖a‖, fun z ↦ by simp⟩
  · exact ⟨0, fun z ↦ by simp [iteratedFDeriv_const_of_ne hn]⟩

/-- A smooth function equal to `1` outside a compact set has bounded derivatives. -/
private theorem exists_bound_iteratedFDeriv_of_hasCompactSupport_one_sub {g : ℂ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport fun z ↦ 1 - g z) (n : ℕ) :
    ∃ C, ∀ z, ‖iteratedFDeriv ℝ n g z‖ ≤ C := by
  have h := exists_bound_iteratedFDeriv_sub contDiff_const (contDiff_const.sub hg)
    (exists_bound_iteratedFDeriv_const 1) (fun k ↦ by
      obtain ⟨C, -, hC⟩ := hc.exists_bound_iteratedFDeriv (contDiff_const.sub hg) k
      exact ⟨C, hC k le_rfl⟩) n
  simpa using h

private theorem contDiff_smoothTransition_normSq_sub (a : ℝ) :
    ContDiff ℝ ∞ fun z : ℂ ↦ Real.smoothTransition (‖z‖ ^ 2 - a) :=
  Real.smoothTransition.contDiff.comp ((contDiff_norm_sq ℝ).sub contDiff_const)

/-- `1 - smoothTransition (‖z‖² - a)` vanishes outside a ball. -/
private theorem hasCompactSupport_one_sub_smoothTransition (a : ℝ) :
    HasCompactSupport fun z : ℂ ↦ 1 - Real.smoothTransition (‖z‖ ^ 2 - a) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (|a| + 1)) fun z hz ↦ ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
  have h1 : |a| + 1 ≤ ‖z‖ ^ 2 := by nlinarith [abs_nonneg a]
  rw [Real.smoothTransition.one_of_one_le (by linarith [le_abs_self a]), sub_self]

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

/-- The product `χ₀ φ_{c₀}` has bounded derivatives. -/
private theorem exists_bound_iteratedFDeriv_innerCut_mul_defect (hm : 0 < m) (c₀ : Fin m → ℂ)
    (R₀ : ℝ) (n : ℕ) :
    ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ innerCut R₀ z * defect c₀ z) z‖ ≤ C := by
  have hcut := contDiff_smoothTransition_normSq_sub (R₀ - 1)
  have hcs : HasCompactSupport fun z ↦ (1 - innerCut R₀ z) * defect c₀ z :=
    (hasCompactSupport_one_sub_smoothTransition (R₀ - 1)).mul_right
  have h := exists_bound_iteratedFDeriv_sub (contDiff_defect c₀)
    ((contDiff_const.sub hcut).mul (contDiff_defect c₀))
    (exists_bound_iteratedFDeriv_defect hm c₀) (fun k ↦ by
      obtain ⟨C, -, hC⟩ := hcs.exists_bound_iteratedFDeriv
        ((contDiff_const.sub hcut).mul (contDiff_defect c₀)) k
      exact ⟨C, hC k le_rfl⟩) n
  have hfun : (fun z ↦ defect c₀ z - (1 - innerCut R₀ z) * defect c₀ z) =
      fun z ↦ innerCut R₀ z * defect c₀ z := by
    ext z
    ring
  rwa [hfun] at h

private theorem contDiff_weight {c₀ : Fin m → ℂ} {R₀ : ℝ}
    (hq : ∀ z, innerCut R₀ z * defect c₀ z ≤ 1 / 2) : ContDiff ℝ ∞ (weight c₀ R₀) :=
  (contDiff_const.sub ((contDiff_smoothTransition_normSq_sub _).mul (contDiff_defect c₀))).inv
    fun z ↦ by linarith [hq z]

/-- The weight `(1 - χ₀ φ_{c₀})⁻¹` has bounded derivatives. -/
private theorem exists_bound_iteratedFDeriv_weight (hm : 0 < m) {c₀ : Fin m → ℂ} {R₀ : ℝ}
    (hq : ∀ z, 0 ≤ innerCut R₀ z * defect c₀ z ∧ innerCut R₀ z * defect c₀ z ≤ 1 / 2) (n : ℕ) :
    ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (weight c₀ R₀) z‖ ≤ C := by
  have hp : ContDiff ℝ ∞ fun z ↦ 1 - innerCut R₀ z * defect c₀ z :=
    contDiff_const.sub ((contDiff_smoothTransition_normSq_sub _).mul (contDiff_defect c₀))
  have hpb := exists_bound_iteratedFDeriv_sub contDiff_const
    ((contDiff_smoothTransition_normSq_sub _).mul (contDiff_defect c₀))
    (exists_bound_iteratedFDeriv_const 1) (exists_bound_iteratedFDeriv_innerCut_mul_defect hm c₀ R₀)
  choose B hB using hpb
  set C := max 1 (∑ i ∈ Finset.range (n + 1), |B i|)
  refine ⟨(n.factorial : ℝ) ^ 2 * C ^ n / (1 / 2) ^ (n + 1), fun z ↦ ?_⟩
  refine norm_iteratedFDeriv_inv_comp_le (hp.of_le (by exact_mod_cast le_top)) (by norm_num)
    (by norm_num) ?_ (le_max_left _ _) fun i _ hi ↦ ?_
  · rw [Real.norm_eq_abs, abs_of_pos (by linarith [(hq z).2])]
    linarith [(hq z).2]
  · refine (hB i z).trans ((le_abs_self _).trans ((Finset.single_le_sum (f := fun i ↦ |B i|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_range.2 (by omega))).trans (le_max_right _ _)))

/-! ### Joint smoothness of the background field -/

private theorem contDiff_eval_monicOfCoeff :
    ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ (monicOfCoeff p.1).eval p.2 := by
  simp only [eval_monicOfCoeff]
  have h : ContDiff ℂ ∞ fun p : (Fin m → ℂ) × ℂ ↦ p.2 ^ m + ∑ i : Fin m, p.1 i * p.2 ^ (i : ℕ) :=
    (contDiff_snd.pow m).add (ContDiff.sum fun i _ ↦
      (contDiff_pi.1 contDiff_fst i).mul (contDiff_snd.pow _))
  exact h.restrict_scalars ℝ

private theorem contDiff_bgAmp_uncurry :
    ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ bgAmp p.1 p.2 := by
  have h : ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ 1 + ‖(monicOfCoeff p.1).eval p.2‖ ^ 2 :=
    contDiff_const.add (contDiff_eval_monicOfCoeff.norm_sq ℝ)
  simpa only [bgAmp, backgroundAmplitude_apply] using
    (h.log fun p ↦ by positivity).neg.div_const 2

/-- The derivative in the point of a jointly smooth family, along a fixed vector. -/
private theorem contDiff_fderiv_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : (Fin m → ℂ) → ℂ → G} (hF : ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ F p.1 p.2) (v : ℂ) :
    ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ fderiv ℝ (F p.1) p.2 v :=
  (ContDiff.fderiv (f := fun p : (Fin m → ℂ) × ℂ ↦ F p.1)
    (hF.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by simp)).clm_apply
    contDiff_const

private theorem contDiff_gaugeForm_uncurry (v : ℂ) :
    ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ gaugeForm (polynomialGauge p.1) p.2 v := by
  simp only [gaugeForm_apply]
  exact imCLM.contDiff.comp ((conjCLE.contDiff.comp contDiff_polynomialGauge).mul
    (contDiff_fderiv_apply (F := fun c z ↦ (polynomialGauge c z : ℂ)) contDiff_polynomialGauge v))

private theorem contDiff_bgConn0_uncurry :
    ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ bgConn0 p.1 p.2 :=
  (contDiff_fderiv_apply (F := bgAmp) contDiff_bgAmp_uncurry I).neg.sub
    (contDiff_gaugeForm_uncurry 1)

private theorem contDiff_bgConn1_uncurry :
    ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ bgConn1 p.1 p.2 :=
  (contDiff_fderiv_apply (F := bgAmp) contDiff_bgAmp_uncurry 1).sub
    (contDiff_gaugeForm_uncurry I)

private theorem contDiff_bgSection_uncurry :
    ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ bgSection p.1 p.2 :=
  (contDiff_polynomialGauge.mul ((ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp contDiff_bgAmp_uncurry)).mul contDiff_eval_monicOfCoeff)).div_const 2

/-! ### The logarithmic ratio as a smooth family in `H^(k+1)` -/

/-- A complex number of modulus less than `1` whose exponential is the positive real `1 + u` is
the real logarithm `log (1 + u)`. -/
private theorem eq_ofReal_log_of_exp_sub_one_eq {v : ℂ} {u : ℝ} (hv : ‖v‖ < 1) (hu : 0 < 1 + u)
    (h : Complex.exp v - 1 = u) : v = (Real.log (1 + u) : ℂ) := by
  have hexp : Complex.exp v = ((1 + u : ℝ) : ℂ) := by
    push_cast
    linear_combination h
  have him : |v.im| < Real.pi :=
    (abs_im_le_norm v).trans_lt (hv.trans (by linarith [Real.two_le_pi]))
  calc v = Complex.log (Complex.exp v) :=
        (Complex.log_exp (by linarith [neg_abs_le v.im]) (by linarith [le_abs_self v.im])).symm
    _ = (Real.log (1 + u) : ℂ) := by rw [hexp, Complex.ofReal_log hu.le]

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
  set μ := realMulCLM (k + 1) (contDiff_weight fun z ↦ (hq z).2)
    (exists_bound_iteratedFDeriv_weight hm hq)
  set ι : H^{((k + 1 : ℕ) : ℝ)}(ℂ) →L[ℂ] H^{(k : ℝ) + 1}(ℂ) :=
    BesselPotentialSpace.inclusion (by push_cast; rfl)
  refine ⟨fun c ↦ ι (μ (φS c₀ - φS c)), (ι.restrictScalars ℝ).contDiff.comp
    ((μ.restrictScalars ℝ).contDiff.comp (contDiff_const.sub
      (contDiff_sobolevBackgroundDefect_monicOfCoeff hm (Nat.cast_nonneg _)))), by simp,
    fun c ↦ ?_⟩
  rw [inclusionLp_inclusion]
  filter_upwards [coeFn_inclusionLp_realMulCLM (k + 1) (contDiff_weight fun z ↦ (hq z).2)
    (exists_bound_iteratedFDeriv_weight hm hq) (φS c₀ - φS c),
    coeFn_inclusionLp_sub_ae_eq _ (coeFn_inclusionLp_sobolevBackgroundDefect (hdeg c₀) _)
      (coeFn_inclusionLp_sobolevBackgroundDefect (hdeg c) _)] with z h₁ h₂
  rw [h₁, h₂]
  push_cast
  rfl

/-- If the `L²` function of `u ∈ H^s` is a continuous real function `g`, then `g` is bounded by
the sup norm of the continuous representative of `u`. -/
private theorem abs_le_norm_toZeroAtInfty {s : ℝ} (hs : (finrank ℝ ℂ : ℝ) < 2 * s) (h0 : 0 ≤ s)
    {u : H^{s}(ℂ)} {g : ℂ → ℝ} (hg : Continuous g)
    (hu : ⇑(inclusionLp h0 u) =ᵐ[volume] fun z ↦ (g z : ℂ)) (z : ℂ) :
    |g z| ≤ ‖toZeroAtInfty (E := ℂ) (F := ℂ) hs u‖ := by
  have h : toZeroAtInfty hs u z = (g z : ℂ) := congrFun ((Continuous.ae_eq_iff_eq volume
    (toZeroAtInfty hs u).continuous (ofRealCLM.continuous.comp hg)).1
    ((coeFn_inclusionLp_ae_eq_toZeroAtInfty _ u).symm.trans hu)) z
  have := ZeroAtInftyContinuousMap.norm_coe_le_norm (toZeroAtInfty hs u) z
  rwa [h, norm_real, Real.norm_eq_abs] at this

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
    finrank_real_complex_lt_two_mul (by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith)
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
    have := abs_le_norm_toZeroAtInfty hk1 (by positivity)
      (contDiff_ratioSubOne (fun z ↦ (hq z).2) c).continuous (hUae c) z
    linarith [neg_abs_le (ratioSubOne c₀ R₀ c z)]
  refine ⟨hpos, ?_⟩
  -- `exp V_c - 1 = U_c`, and `V_c` is small, so `V_c = log (1 + U_c)`.
  have hexp := coeFn_toLp_inclusion_expSubOne hk1 (by positivity) (L (U c))
  rw [h₁, toLp_inclusion, toLp_inclusion] at hexp
  filter_upwards [coeFn_inclusionLp_ae_eq_toZeroAtInfty (hs := hk1) (by positivity) (L (U c)),
    hexp, hUae c] with z hz₁ hz₂ hz₃
  rw [hz₁]
  refine eq_ofReal_log_of_exp_sub_one_eq ?_ (hpos z) ?_
  · exact (ZeroAtInftyContinuousMap.norm_coe_le_norm _ z).trans_lt h₃
  · rw [← hz₁, ← hz₂, hz₃]

/-! ### Families of real functions that are smooth in `H^s` at a point -/

/-- The family of real functions `F c` is smooth in `H^s(ℂ)` at `c₀`: some family of elements of
`H^s(ℂ)`, smooth at `c₀`, has `L²` function `F c` for `c` near `c₀`. -/
private def IsSmoothAt (s : ℝ) (hs : 0 ≤ s) (c₀ : Fin m → ℂ) (F : (Fin m → ℂ) → ℂ → ℝ) : Prop :=
  ∃ D : (Fin m → ℂ) → H^{s}(ℂ), ContDiffAt ℝ ∞ D c₀ ∧
    ∀ᶠ c in 𝓝 c₀, ⇑(inclusionLp hs (D c)) =ᵐ[volume] fun z ↦ (F c z : ℂ)

section IsSmoothAt

variable {s : ℝ} {hs : 0 ≤ s} {c₀ : Fin m → ℂ} {F G : (Fin m → ℂ) → ℂ → ℝ}

private theorem IsSmoothAt.congr (hF : IsSmoothAt s hs c₀ F) (h : ∀ᶠ c in 𝓝 c₀, F c = G c) :
    IsSmoothAt s hs c₀ G := by
  obtain ⟨D, hD, hDF⟩ := hF
  refine ⟨D, hD, ?_⟩
  filter_upwards [hDF, h] with c h₁ h₂
  simpa [h₂] using h₁

private theorem IsSmoothAt.add (hF : IsSmoothAt s hs c₀ F) (hG : IsSmoothAt s hs c₀ G) :
    IsSmoothAt s hs c₀ fun c z ↦ F c z + G c z := by
  obtain ⟨D, hD, hDF⟩ := hF
  obtain ⟨E, hE, hEG⟩ := hG
  refine ⟨D + E, hD.add hE, ?_⟩
  filter_upwards [hDF, hEG] with c h₁ h₂
  simpa using coeFn_inclusionLp_add_ae_eq hs h₁ h₂

private theorem IsSmoothAt.sub (hF : IsSmoothAt s hs c₀ F) (hG : IsSmoothAt s hs c₀ G) :
    IsSmoothAt s hs c₀ fun c z ↦ F c z - G c z := by
  obtain ⟨D, hD, hDF⟩ := hF
  obtain ⟨E, hE, hEG⟩ := hG
  refine ⟨D - E, hD.sub hE, ?_⟩
  filter_upwards [hDF, hEG] with c h₁ h₂
  simpa using coeFn_inclusionLp_sub_ae_eq hs h₁ h₂

private theorem IsSmoothAt.const_mul (a : ℝ) (hF : IsSmoothAt s hs c₀ F) :
    IsSmoothAt s hs c₀ fun c z ↦ a * F c z := by
  obtain ⟨D, hD, hDF⟩ := hF
  refine ⟨fun c ↦ (a : ℂ) • D c, hD.const_smul _, ?_⟩
  filter_upwards [hDF] with c h
  simpa using coeFn_inclusionLp_smul_ae_eq hs (a : ℂ) h

/-- Products, in the algebra `H^s(ℂ)`, `s > 1`. -/
private theorem IsSmoothAt.mul (hs' : (finrank ℝ ℂ : ℝ) < 2 * s) (hF : IsSmoothAt s hs c₀ F)
    (hG : IsSmoothAt s hs c₀ G) : IsSmoothAt s hs c₀ fun c z ↦ F c z * G c z := by
  obtain ⟨D, hD, hDF⟩ := hF
  obtain ⟨E, hE, hEG⟩ := hG
  refine ⟨fun c ↦ mulCLM hs' (D c) (E c),
    ((mulCLM hs').isBoundedBilinearMap.contDiff.restrict_scalars ℝ).contDiffAt.comp c₀
      (hD.prodMk hE), ?_⟩
  filter_upwards [hDF, hEG] with c h₁ h₂
  filter_upwards [coeFn_inclusionLp_mulCLM hs' hs (D c) (E c), h₁, h₂] with z hz h₁ h₂
  rw [hz, h₁, h₂]
  push_cast
  rfl

/-- Exponentials, in the algebra `H^s(ℂ)`, `s > 1`. -/
private theorem IsSmoothAt.exp_sub_one (hs' : (finrank ℝ ℂ : ℝ) < 2 * s)
    (hF : IsSmoothAt s hs c₀ F) : IsSmoothAt s hs c₀ fun c z ↦ Real.exp (F c z) - 1 := by
  obtain ⟨D, hD, hDF⟩ := hF
  refine ⟨fun c ↦ expSubOne hs' (D c),
    ((contDiff_expSubOne hs').restrict_scalars ℝ).contDiffAt.comp c₀ hD, ?_⟩
  filter_upwards [hDF] with c h
  have he := coeFn_toLp_inclusion_expSubOne hs' hs (D c)
  rw [toLp_inclusion, toLp_inclusion] at he
  filter_upwards [he, h] with z h₁ h₂
  rw [h₁, h₂]
  push_cast
  rfl

/-- Lowering the order. -/
private theorem IsSmoothAt.mono {t : ℝ} {ht : 0 ≤ t} (hF : IsSmoothAt t ht c₀ F) (hst : s ≤ t) :
    IsSmoothAt s hs c₀ F := by
  obtain ⟨D, hD, hDF⟩ := hF
  refine ⟨fun c ↦ BesselPotentialSpace.inclusion hst (D c),
    ((BesselPotentialSpace.inclusion hst).restrictScalars ℝ).contDiff.contDiffAt.comp c₀ hD, ?_⟩
  filter_upwards [hDF] with c h
  rwa [inclusionLp_inclusion]

/-- Multiplication by a fixed real function with bounded derivatives, at an integer order. -/
private theorem IsSmoothAt.realMul {N : ℕ} {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hbd : ∀ n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n g z‖ ≤ C)
    (hF : IsSmoothAt N N.cast_nonneg c₀ F) :
    IsSmoothAt N N.cast_nonneg c₀ fun c z ↦ g z * F c z := by
  obtain ⟨D, hD, hDF⟩ := hF
  refine ⟨fun c ↦ realMulCLM N hg hbd (D c),
    ((realMulCLM N hg hbd).restrictScalars ℝ).contDiff.contDiffAt.comp c₀ hD, ?_⟩
  filter_upwards [hDF] with c h
  filter_upwards [coeFn_inclusionLp_realMulCLM N hg hbd (D c), h] with z h₁ h₂
  rw [h₁, h₂]
  push_cast
  rfl

/-- Directional derivatives, from `H^(s+1)` to `H^s`. -/
private theorem IsSmoothAt.fderiv_apply (hF : IsSmoothAt (s + 1) (by linarith) c₀ F)
    (hF1 : ∀ᶠ c in 𝓝 c₀, ContDiff ℝ 1 (F c)) (v : ℂ) :
    IsSmoothAt s hs c₀ fun c z ↦ fderiv ℝ (F c) z v := by
  obtain ⟨D, hD, hDF⟩ := hF
  set Dv := lineDerivCLM (E := ℂ) (F := ℂ) (s := s) ENNReal.one_lt_two ENNReal.ofNat_ne_top v
  refine ⟨fun c ↦ Dv (D c), (Dv.restrictScalars ℝ).contDiff.contDiffAt.comp c₀ hD, ?_⟩
  filter_upwards [hDF, hF1] with c h₁ h₂
  exact coeFn_inclusionLp_lineDerivCLM_ae_eq ENNReal.one_lt_two ENNReal.ofNat_ne_top hs h₂ h₁ v

/-- A smooth family of elements of `H^s(ℂ)`. -/
private theorem isSmoothAt_of_contDiff {D : (Fin m → ℂ) → H^{s}(ℂ)} (hD : ContDiff ℝ ∞ D)
    (hDF : ∀ c, ⇑(inclusionLp hs (D c)) =ᵐ[volume] fun z ↦ (F c z : ℂ)) :
    IsSmoothAt s hs c₀ F :=
  ⟨D, hD.contDiffAt, .of_forall hDF⟩

end IsSmoothAt

/-! ### The pieces of the difference of two normalized vortices -/

/-- `1 - smoothTransition (‖z‖² - a)` vanishes for `‖z‖ ≥ |a| + 1`. -/
private theorem one_sub_smoothTransition_eq_zero {a : ℝ} {z : ℂ} (hz : |a| + 1 ≤ ‖z‖) :
    1 - Real.smoothTransition (‖z‖ ^ 2 - a) = 0 := by
  have h1 : |a| + 1 ≤ ‖z‖ ^ 2 := by nlinarith [abs_nonneg a]
  rw [Real.smoothTransition.one_of_one_le (by linarith [le_abs_self a]), sub_self]

/-- The core `(1 - χ) F_c` of a jointly smooth family is smooth in every `H^k`. -/
private theorem isSmoothAt_core {F : (Fin m → ℂ) → ℂ → ℝ}
    (hF : ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ F p.1 p.2) (R₀ : ℝ) (k : ℕ)
    (c₀ : Fin m → ℂ) :
    IsSmoothAt k k.cast_nonneg c₀ fun c z ↦ (1 - outerCut R₀ z) * F c z := by
  have hj : ContDiff ℝ ∞ (Function.uncurry fun c z ↦ (((1 - outerCut R₀ z) * F c z : ℝ) : ℂ)) :=
    ofRealCLM.contDiff.comp ((contDiff_const.sub
      ((contDiff_smoothTransition_normSq_sub (R₀ + 1)).comp contDiff_snd)).mul hF)
  obtain ⟨D, hD, hDF⟩ := exists_contDiff_inclusionLp_ae_eq_of_forall_le_norm hj
    (R := |R₀ + 1| + 1) (fun c z hz ↦ by simp [one_sub_smoothTransition_eq_zero hz])
    k.cast_nonneg
  exact isSmoothAt_of_contDiff hD hDF

/-- The reduced solution `w_c` is smooth in every `H^s`. -/
private theorem isSmoothAt_redSol {s : ℝ} (hs : 0 ≤ s) (c₀ : Fin m → ℂ) :
    IsSmoothAt s hs c₀ fun c z ↦ redSol c z :=
  isSmoothAt_of_contDiff (contDiff_ofRealSobolevFunction_reducedSolution hs)
    fun _ ↦ coeFn_inclusionLp_ofRealSobolevFunction hs _

/-- The difference `w_c - w_{c₀}` is smooth in every `H^s`. -/
private theorem isSmoothAt_redSol_sub {s : ℝ} (hs : 0 ≤ s) (c₀ : Fin m → ℂ) :
    IsSmoothAt s hs c₀ fun c z ↦ redSol c z - redSol c₀ z :=
  (isSmoothAt_redSol hs c₀).sub (isSmoothAt_of_contDiff (D := fun _ ↦ ofRealSobolevFunction hs
    (reducedSolution_mem_realSobolevFunctions (monicOfCoeff c₀) s)) contDiff_const
    fun _ ↦ coeFn_inclusionLp_ofRealSobolevFunction hs _)

private theorem contDiff_redSol_sub (c c₀ : Fin m → ℂ) :
    ContDiff ℝ 1 fun z ↦ redSol c z - redSol c₀ z :=
  ((contDiff_reducedSolution _).sub (contDiff_reducedSolution _)).of_le (by simp)

/-- The cutoff `χ` has bounded derivatives. -/
private theorem exists_bound_iteratedFDeriv_outerCut (R₀ : ℝ) (n : ℕ) :
    ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (outerCut R₀) z‖ ≤ C :=
  exists_bound_iteratedFDeriv_of_hasCompactSupport_one_sub
    (contDiff_smoothTransition_normSq_sub _) (hasCompactSupport_one_sub_smoothTransition _) n

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
    ∃ R₀ : ℝ, (∀ c ∈ ball c₀ 1, ∀ z : ℂ, R₀ < ‖z‖ ^ 2 →
        (monicOfCoeff c).eval z ≠ 0 ∧ m * ∑ i, ‖c i‖ ^ 2 + 2 < ‖z‖ ^ 2) ∧
      IsSmoothAt ((k : ℝ) + 1) (by positivity) c₀ (logRatio c₀ R₀) ∧
      ∀ᶠ c in 𝓝 c₀, ContDiff ℝ 1 (logRatio c₀ R₀ c) := by
  obtain ⟨R₀, -, hR, hR'⟩ := exists_radius hm c₀
  obtain ⟨V, hV, hVev⟩ := exists_logRatio_family hm hk c₀ hR'
  have hq := innerCut_mul_defect_le hR'
  refine ⟨R₀, hR, ⟨V, hV, hVev.mono fun c h ↦ h.2⟩, hVev.mono fun c h ↦ ?_⟩
  exact (((contDiff_const.add (contDiff_ratioSubOne (fun z ↦ (hq z).2) c)).log
    fun z ↦ (h.1 z).ne').of_le (by simp))

/-- **The first coordinate of `y_c - y_{c₀}` is smooth in `H^k` at `c₀`.** -/
private theorem isSmoothAt_normalizedVortex_sub_apply_zero (hm : 0 < m) {k : ℕ} (hk : 2 ≤ k)
    (c₀ : Fin m → ℂ) :
    IsSmoothAt k k.cast_nonneg c₀ fun c z ↦ normalizedVortex c z 0 - normalizedVortex c₀ z 0 := by
  obtain ⟨R₀, hR, hV, hV1⟩ := exists_radius_isSmoothAt_logRatio hm hk c₀
  have hK := isSmoothAt_core (F := fun c z ↦ bgConn0 c z - bgConn0 c₀ z)
    (contDiff_bgConn0_uncurry.sub (contDiff_bgConn0_uncurry.comp
      (contDiff_const.prodMk contDiff_snd))) R₀ k c₀
  have hdV := ((hV.fderiv_apply (hs := k.cast_nonneg) hV1 I).const_mul (1 / 2)).realMul
    (contDiff_smoothTransition_normSq_sub _) (exists_bound_iteratedFDeriv_outerCut R₀)
  have hdW := (isSmoothAt_redSol_sub (by positivity : (0 : ℝ) ≤ k + 1) c₀).fderiv_apply
    (hs := k.cast_nonneg) (.of_forall fun c ↦ contDiff_redSol_sub c c₀) I
  refine ((hK.sub hdV).sub hdW).congr ?_
  filter_upwards [ball_mem_nhds c₀ one_pos] with c hc
  funext z
  rw [normalizedVortex_sub_apply_zero hR hc z]
  ring

/-- **The second coordinate of `y_c - y_{c₀}` is smooth in `H^k` at `c₀`.** -/
private theorem isSmoothAt_normalizedVortex_sub_apply_one (hm : 0 < m) {k : ℕ} (hk : 2 ≤ k)
    (c₀ : Fin m → ℂ) :
    IsSmoothAt k k.cast_nonneg c₀ fun c z ↦ normalizedVortex c z 1 - normalizedVortex c₀ z 1 := by
  obtain ⟨R₀, hR, hV, hV1⟩ := exists_radius_isSmoothAt_logRatio hm hk c₀
  have hK := isSmoothAt_core (F := fun c z ↦ bgConn1 c z - bgConn1 c₀ z)
    (contDiff_bgConn1_uncurry.sub (contDiff_bgConn1_uncurry.comp
      (contDiff_const.prodMk contDiff_snd))) R₀ k c₀
  have hdV := ((hV.fderiv_apply (hs := k.cast_nonneg) hV1 1).const_mul (1 / 2)).realMul
    (contDiff_smoothTransition_normSq_sub _) (exists_bound_iteratedFDeriv_outerCut R₀)
  have hdW := (isSmoothAt_redSol_sub (by positivity : (0 : ℝ) ≤ k + 1) c₀).fderiv_apply
    (hs := k.cast_nonneg) (.of_forall fun c ↦ contDiff_redSol_sub c c₀) 1
  refine ((hK.add hdV).add hdW).congr ?_
  filter_upwards [ball_mem_nhds c₀ one_pos] with c hc
  funext z
  rw [normalizedVortex_sub_apply_one hR hc z]
  ring

/-- The section coordinates `j = 2, 3` of `y_c - y_{c₀}` are smooth in `H^k` at `c₀`, given the
pointwise decomposition of their background part `B_c` (the real or imaginary part of
`bgSection c - bgSection c₀`). -/
private theorem isSmoothAt_normalizedVortex_sub_section (hm : 0 < m) {k : ℕ} (hk : 2 ≤ k)
    (c₀ : Fin m → ℂ) (j : Fin 4) {B : (Fin m → ℂ) → ℂ → ℝ}
    (hB : ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ B p.1 p.2)
    (hdec : ∀ R₀ : ℝ, (∀ c ∈ ball c₀ 1, ∀ z : ℂ, R₀ < ‖z‖ ^ 2 →
        (monicOfCoeff c).eval z ≠ 0 ∧ m * ∑ i, ‖c i‖ ^ 2 + 2 < ‖z‖ ^ 2) →
      ∀ c ∈ ball c₀ 1, ∀ z, normalizedVortex c z j - normalizedVortex c₀ z j =
        (1 - outerCut R₀ z) * B c z * Real.exp (redSol c z) +
          outerCut R₀ z * (normalizedVortex c₀ z j *
            ((Real.exp (logRatio c₀ R₀ c z / 2) - 1) * Real.exp (redSol c z - redSol c₀ z))) +
          normalizedVortex c₀ z j * (Real.exp (redSol c z - redSol c₀ z) - 1)) :
    IsSmoothAt k k.cast_nonneg c₀ fun c z ↦ normalizedVortex c z j - normalizedVortex c₀ z j := by
  obtain ⟨R₀, hR, hV, -⟩ := exists_radius_isSmoothAt_logRatio hm hk c₀
  have hk0 : (finrank ℝ ℂ : ℝ) < 2 * k := finrank_real_complex_lt_two_mul (by exact_mod_cast hk)
  have hk1 : (finrank ℝ ℂ : ℝ) < 2 * ((k : ℝ) + 1) := by linarith
  have hK := isSmoothAt_core hB R₀ k c₀
  have hw := (isSmoothAt_redSol k.cast_nonneg c₀).exp_sub_one hk0
  have hEW := (isSmoothAt_redSol_sub k.cast_nonneg c₀).exp_sub_one hk0
  have hEV : IsSmoothAt k k.cast_nonneg c₀ fun c z ↦ Real.exp (1 / 2 * logRatio c₀ R₀ c z) - 1 :=
    ((hV.const_mul (1 / 2)).exp_sub_one hk1).mono (by linarith)
  have hy := contDiff_normalizedVortex_apply c₀ j
  have hyb := exists_bound_iteratedFDeriv_normalizedVortex hm c₀ j
  have h₁ := hK.add (hK.mul hk0 hw)
  have h₂ := ((hEV.add (hEV.mul hk0 hEW)).realMul hy hyb).realMul
    (contDiff_smoothTransition_normSq_sub _) (exists_bound_iteratedFDeriv_outerCut R₀)
  refine ((h₁.add h₂).add (hEW.realMul hy hyb)).congr ?_
  filter_upwards [ball_mem_nhds c₀ one_pos] with c hc
  funext z
  rw [hdec R₀ hR c hc z, show logRatio c₀ R₀ c z / 2 = 1 / 2 * logRatio c₀ R₀ c z by ring]
  ring

/-- **The coordinates of `y_c - y_{c₀}` are smooth in `H^k` at `c₀`.** -/
private theorem isSmoothAt_normalizedVortex_sub (hm : 0 < m) {k : ℕ} (hk : 2 ≤ k)
    (c₀ : Fin m → ℂ) (j : Fin 4) :
    IsSmoothAt k k.cast_nonneg c₀ fun c z ↦ normalizedVortex c z j - normalizedVortex c₀ z j := by
  have hS := contDiff_bgSection_uncurry (m := m)
  have hS₀ : ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ bgSection p.1 p.2 - bgSection c₀ p.2 :=
    hS.sub (hS.comp (contDiff_const.prodMk contDiff_snd))
  fin_cases j
  · exact isSmoothAt_normalizedVortex_sub_apply_zero hm hk c₀
  · exact isSmoothAt_normalizedVortex_sub_apply_one hm hk c₀
  · exact isSmoothAt_normalizedVortex_sub_section hm hk c₀ 2 (reCLM.contDiff.comp hS₀)
      fun R₀ hR c hc z ↦ normalizedVortex_sub_apply_two hR hc z
  · exact isSmoothAt_normalizedVortex_sub_section hm hk c₀ 3 (imCLM.contDiff.comp hS₀)
      fun R₀ hR c hc z ↦ normalizedVortex_sub_apply_three hR hc z

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
  obtain ⟨D, hD, hDF⟩ := isSmoothAt_normalizedVortex_sub hm (le_max_left 2 ⌈s⌉₊) c₀ j
  set ι : H^{(k : ℝ)}(ℂ) →L[ℂ] H^{s}(ℂ) := BesselPotentialSpace.inclusion hsk
  refine (contDiffAt_const (c := (normalizedVortex hm f s c₀).subRef j).add
    ((ι.restrictScalars ℝ).contDiff.contDiffAt.comp c₀ hD)).congr_of_eventuallyEq ?_
  filter_upwards [hDF] with c hc
  -- `y_c - x_m = (y_{c₀} - x_m) + (y_c - y_{c₀})`.
  refine (subRef_eq_iff hs _ j _).2 ?_
  have h₀ := (subRef_eq_iff hs (normalizedVortex hm f s c₀) j _).1 rfl
  rw [toLp_inclusion] at h₀ ⊢
  have h₁ : ⇑(inclusionLp hs (ι (D c))) =ᵐ[volume] fun z ↦
      ((Vortex.normalizedVortex c z j - Vortex.normalizedVortex c₀ z j : ℝ) : ℂ) := by
    rw [inclusionLp_inclusion]
    exact hc
  have e (c : Fin m → ℂ) : (normalizedVortex hm f s c).toFun = Vortex.normalizedVortex c := (rfl)
  filter_upwards [coeFn_inclusionLp_add_ae_eq hs h₀ h₁] with z hz
  simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', e] at hz ⊢
  rw [hz]
  push_cast
  ring

/-- The normalized vortices depend continuously on their divisor coefficients in `A_m^s`. -/
theorem continuous_normalizedVortex (hm : 0 < m) (f : ContDiffBump (0 : ℝ)) {s : ℝ}
    (hs : 0 ≤ s) : Continuous (normalizedVortex hm f s) :=
  continuous_induced_rng.2 (contDiff_subRef_normalizedVortex hm f hs).continuous

end SobolevFieldSpace

end TauCeti.Vortex

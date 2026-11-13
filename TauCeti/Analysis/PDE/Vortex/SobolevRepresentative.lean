/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.WindingPhase
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Sobolev.BesselPotential.Laplacian
import TauCeti.Analysis.Sobolev.BesselPotential.Multiplier
import TauCeti.Analysis.Sobolev.BesselPotential.PowerSeries
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# Smooth framed vortices have representatives in every affine Sobolev space

The plane vortex moduli are modelled on the affine Sobolev spaces
`A_m^s = x_ref + H^s(ℂ; iT*ℂ ⊕ ℂ)` (`TauCeti.Vortex.framedFieldSpace`), centred at a reference field
equal to `(-i m dθ, (z / |z|)^m)` outside a disc. A smooth solution of the vortex equations with
the degree-`m` end framing `α (z / |z|)^(-m) → 1` need not lie in any `A_m^s`: a smooth framed gauge
can change its phase by a factor tending to one with a `1 / |z|` tail, which is not square
integrable. This file shows that, after a suitable smooth framed gauge, it lies in every `A_m^s`
at once (`TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace`). Together with
`TauCeti.Vortex.mem_sobolevGaugeGroup_of_mem_framedFieldSpace`, by which two representatives in
`A_m^k`, `k ≥ 2`, of one smooth framed gauge orbit differ by an element of `G_(k+1)`, every
smooth framed vortex orbit meets the Sobolev model, in a single `G_(k+1)` orbit.

The gauge is the one normalizing the end phase
(`TauCeti.Vortex.exists_framedGaugeGroup_sectionValue_smul_eq`): outside a compact set the
section is `α = |α| (z / |z|)^m`. There the whole field is determined by `ψ = log |α|`. The
holomorphicity rows `∂bar_a α = 0` give the connection coordinates `(-∂₂ ψ, ∂₁ ψ)` relative to the
reference field, and the section is `exp ψ` times the reference section. So the field differs
from the reference field by a smooth compactly supported field plus the model field
`(-∂₂ g, ∂₁ g, (exp g - 1) x_ref)`, where `g = (1 - b) ψ` is `ψ` cut off by a bump function `b`
equal to one on a disc containing the zeros of `α`.

It remains to show that `g` lies in every `H^s`. Off the zeros, the curvature row gives
`Δψ = (exp (2ψ) - 1) / 8`, so

`-Δg + g / 4 = -(exp (2g) - 1 - 2g) / 8 + k`

with `k` smooth and compactly supported. The function `g` is bounded and square integrable, since
`g² ≤ 1 - |α|²` and the modulus defect is integrable
(`TauCeti.Vortex.integrable_one_sub_normSq`). The elliptic regularity of `-Δ + 1 / 4` for classical
functions (`TemperedDistribution.mem_realSobolevFunctions_add_two_of_neg_laplacian_add_smul`)
then raises the order of `g` by two at each step: the nonlinearity is square integrable because
`g` is bounded, and lies in `H^s` together with `g` once `s > 1`, by the power series of the
exponential on the Sobolev algebra
(`TemperedDistribution.exp_mul_sub_one_mem_realSobolevFunctions`).
No pointwise decay of the derivatives of the field is used.

## Main results

* `TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace`: every smooth framed vortex
  has a smooth framed gauge transform lying in `A_m^s` for every `s`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric MeasureTheory TemperedDistribution Topology
open scoped ComplexConjugate ContDiff Laplacian

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {m : ℕ}

/-! ### The field in the end region -/

/-- The logarithmic modulus `log |α| = log (4 (p² + q²)) / 2` of the section of a field. -/
private def logModulus (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) : ℝ :=
  Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) / 2

private theorem exp_logModulus {z : ℂ} (hz : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0) :
    Real.exp (logModulus x z) = ‖sectionValue x z‖ := by
  have h0 : 0 < ‖sectionValue x z‖ := by
    refine norm_pos_iff.2 fun h ↦ hz ?_
    have := sq_norm_sectionValue x z
    rw [h, norm_zero] at this
    linarith
  rw [logModulus, ← sq_norm_sectionValue, Real.log_pow, Nat.cast_ofNat,
    mul_div_cancel_left₀ _ two_ne_zero, Real.exp_log h0]

/-- The field `(-∂₂ g, ∂₁ g, (exp g - 1) x_ref)` determined by a real function `g`, the
logarithmic modulus of the section in the end region. -/
private def modelField (f : ContDiffBump (0 : ℝ)) (m : ℕ) (g : ℂ → ℝ) (z : ℂ) :
    EuclideanSpace ℝ (Fin 4) :=
  !₂[-fderiv ℝ g z I, fderiv ℝ g z 1, (Real.exp (g z) - 1) * referenceField f m z 2,
    (Real.exp (g z) - 1) * referenceField f m z 3]

/-- **Connection coordinates of a solution with a positive real section.** If near `z` the section
of a solution `y` of the vortex equations is the positive real function `exp ψ`, with coordinates
`(exp ψ / 2, 0)`, then the holomorphicity rows force its connection coordinates at `z` to be
`(-∂₂ ψ, ∂₁ ψ)`. -/
private theorem connection_eq_of_section_eq_exp {y : ℂ → EuclideanSpace ℝ (Fin 4)} {ψ : ℂ → ℝ}
    {z : ℂ} (hψ : DifferentiableAt ℝ ψ z) (hsol : equation y z = 0)
    (hsec : ∀ᶠ w in 𝓝 z, y w 2 = Real.exp (ψ w) / 2 ∧ y w 3 = 0) :
    y z 0 = -fderiv ℝ ψ z I ∧ y z 1 = fderiv ℝ ψ z 1 := by
  obtain ⟨hy2, hy3⟩ := hsec.self_of_nhds
  have hd2 : fderiv ℝ (fun w ↦ y w 2) z = (Real.exp (ψ z) / 2) • fderiv ℝ ψ z := by
    have h : (fun w ↦ y w 2) =ᶠ[𝓝 z] fun w ↦ Real.exp (ψ w) * 2⁻¹ :=
      hsec.mono fun w hw ↦ hw.1.trans (div_eq_mul_inv _ _)
    rw [h.fderiv_eq, (hψ.hasFDerivAt.exp.mul_const _).fderiv, smul_smul, div_eq_mul_inv,
      mul_comm]
  have hd3 : fderiv ℝ (fun w ↦ y w 3) z = 0 := by
    have h : (fun w ↦ y w 3) =ᶠ[𝓝 z] fun _ ↦ (0 : ℝ) := hsec.mono fun w hw ↦ hw.2
    rw [h.fderiv_eq]
    exact fderiv_const_apply 0
  have hr1 := equation_apply_one y z
  have hr2 := equation_apply_two y z
  rw [hsol] at hr1 hr2
  simp only [PiLp.zero_apply, hd2, hd3, hy2, hy3, FunLike.coe_smul, Pi.smul_apply,
    zero_apply, smul_eq_mul] at hr1 hr2
  constructor
  · have h : Real.exp (ψ z) / 2 * (y z 0 + fderiv ℝ ψ z I) = 0 := by
      linear_combination -hr2
    linarith [(mul_eq_zero.1 h).resolve_left (by positivity)]
  · have h : Real.exp (ψ z) / 2 * (y z 1 - fderiv ℝ ψ z 1) = 0 := by
      linear_combination hr1
    linarith [(mul_eq_zero.1 h).resolve_left (by positivity)]

/-- **The field in the end region.** At a point `z` outside the cutoff disc near which the
section of a smooth vortex `x` is `|α|` times the winding phase and does not vanish, the
difference from the reference field is the model field of `ψ = log |α|`: its connection
coordinates are `(-∂₂ ψ, ∂₁ ψ)`, and its section is `exp ψ - 1` times the reference section. -/
private theorem sub_referenceField_eq (f : ContDiffBump (0 : ℝ)) {z : ℂ}
    (hrOut : f.rOut ≤ ‖z‖ ^ 2) (hx : ContDiff ℝ ∞ x) (hsol : equation x z = 0)
    (hphase : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w)
    (hpos : ∀ᶠ w in 𝓝 z, x w 2 ^ 2 + x w 3 ^ 2 ≠ 0) :
    x z - referenceField f m z = modelField f m (logModulus x) z := by
  have hz₀ := ne_zero_of_rOut_le_norm_sq f hrOut
  have hxd (i : Fin 4) : ContDiff ℝ ∞ (fun w ↦ x w i) := contDiff_euclidean.1 hx i
  set y := gaugeTransform (windingPhase m)⁻¹ x
  have hinv : ContDiffAt ℝ 2 (fun w ↦ ((windingPhase m)⁻¹ w : ℂ)) z := by
    have h : (fun w ↦ ((windingPhase m)⁻¹ w : ℂ)) = fun w ↦ conj (windingPhase m w : ℂ) := by
      funext w
      rw [Pi.inv_apply, Circle.coe_inv_eq_conj]
    rw [h]
    exact conjCLE.contDiff.contDiffAt.comp z (contDiffAt_windingPhase m hz₀)
  have hysol : equation y z = 0 :=
    (equation_gaugeTransform_eq_zero_iff hinv fun i ↦ (hxd i).differentiable (by simp) z).2 hsol
  -- In the end trivialization the section is the real function `|α| = exp ψ`.
  have hsec : ∀ᶠ w in 𝓝 z, y w 2 = Real.exp (logModulus x w) / 2 ∧ y w 3 = 0 := by
    filter_upwards [hphase, hpos] with w hw hw'
    have h1 : ((windingPhase m w)⁻¹ : Circle) * (windingPhase m w : ℂ) = 1 := by
      rw [← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
    have hs : sectionValue y w = ‖sectionValue x w‖ := by
      rw [sectionValue_gaugeTransform, Pi.inv_apply]
      nth_rw 1 [hw]
      rw [mul_left_comm, h1, mul_one]
    rw [sectionValue_apply, ← exp_logModulus hw'] at hs
    constructor
    · have := congrArg Complex.re hs
      simp only [mul_re, add_re, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat] at this
      linarith
    · have := congrArg Complex.im hs
      simp only [mul_im, add_im, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat] at this
      linarith
  have hψ : DifferentiableAt ℝ (logModulus x) z := by
    have hs : DifferentiableAt ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z :=
      ((((hxd 2).differentiable (by simp) z).pow 2).add
        (((hxd 3).differentiable (by simp) z).pow 2)).const_mul 4
    have hfun : logModulus x = fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) * 2⁻¹ := by
      funext w
      rw [logModulus, div_eq_mul_inv]
    rw [hfun]
    exact (hs.log (by simpa using hpos.self_of_nhds)).mul_const _
  obtain ⟨hy0, hy1⟩ := connection_eq_of_section_eq_exp hψ hysol hsec
  -- The end trivialization fixes the connection coordinates of `x - x_ref`.
  have hiso : y z - vacuumField z =
      gaugeLinearAction (windingPhase m)⁻¹ (x - referenceField f m) z := by
    rw [← gaugeTransform_inv_windingPhase_referenceField f m hrOut, ← Pi.sub_apply y,
      gaugeTransform_sub_gaugeTransform]
  have h0 : y z 0 = x z 0 - referenceField f m z 0 := by
    simpa [gaugeLinearAction_apply, vacuumField_apply] using congrArg (· 0) hiso
  have h1 : y z 1 = x z 1 - referenceField f m z 1 := by
    simpa [gaugeLinearAction_apply, vacuumField_apply] using congrArg (· 1) hiso
  -- The section of `x` is `|α|` times the reference section.
  have hsx : sectionValue x z = ‖sectionValue x z‖ * sectionValue (referenceField f m) z := by
    rw [sectionValue_referenceField, referenceSection_eq_phase f m hrOut, ← coe_windingPhase m hz₀]
    exact hphase.self_of_nhds
  rw [← exp_logModulus hpos.self_of_nhds, sectionValue_apply, sectionValue_apply] at hsx
  have hs2 := congrArg Complex.re hsx
  have hs3 := congrArg Complex.im hsx
  simp only [mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im, re_ofNat,
    im_ofNat] at hs2 hs3
  rw [modelField]
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, PiLp.sub_apply, Matrix.cons_val_zero]
    linarith
  · simp only [Fin.mk_one, Fin.isValue, PiLp.sub_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    linarith
  · simp only [Fin.reduceFinMk, Fin.isValue, PiLp.sub_apply, Matrix.cons_val]
    linear_combination hs2 / 2
  · simp only [Fin.reduceFinMk, Fin.isValue, PiLp.sub_apply, Matrix.cons_val]
    linear_combination hs3 / 2

/-! ### The cut-off logarithmic modulus -/

/-- The logarithmic modulus `log |α|`, cut off by a bump function `b` that equals one on a disc
containing the zeros of `α`. -/
private def cutoffLogModulus (b : ContDiffBump (0 : ℂ)) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (z : ℂ) : ℝ :=
  (1 - b z) * logModulus x z

private theorem contDiff_cutoffLogModulus (b : ContDiffBump (0 : ℂ)) (hx : ContDiff ℝ ∞ x)
    (hb : ∀ z, b.rIn - 1 ≤ ‖z‖ → 1 / 2 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) :
    ContDiff ℝ ∞ (cutoffLogModulus b x) := by
  have h2 := contDiff_euclidean.1 hx 2
  have h3 := contDiff_euclidean.1 hx 3
  have hs : ContDiff ℝ ∞ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) := by fun_prop
  refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
  rcases lt_or_ge ‖z‖ b.rIn with hz | hz
  · -- The cutoff factor vanishes near `z`.
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz)] with w hw
    rw [cutoffLogModulus, b.one_of_mem_closedBall (ball_subset_closedBall hw), sub_self,
      zero_mul]
  · have hz' : 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≠ 0 := (hb z (by linarith)).trans_lt' one_half_pos |>.ne'
    have hlog : ContDiffAt ℝ ∞ (logModulus x) z :=
      (hs.contDiffAt.log hz').div_const 2
    exact (contDiffAt_const.sub b.contDiff.contDiffAt).mul hlog

private theorem cutoffLogModulus_eventuallyEq (b : ContDiffBump (0 : ℂ)) {z : ℂ}
    (hz : b.rOut < ‖z‖) : cutoffLogModulus b x =ᶠ[𝓝 z] logModulus x := by
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
  have hb : b w = 0 := by
    rw [← Function.notMem_support, b.support_eq, mem_ball_zero_iff, not_lt]
    exact hw.le
  rw [cutoffLogModulus, hb, sub_zero, one_mul]

private theorem abs_cutoffLogModulus_le (b : ContDiffBump (0 : ℂ))
    (hle : ∀ z, 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ 1)
    (hb : ∀ z, b.rIn - 1 ≤ ‖z‖ → 1 / 2 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (z : ℂ) :
    |cutoffLogModulus b x z| ≤ 1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2) ∧
      |cutoffLogModulus b x z| ≤ 1 / 2 := by
  rcases lt_or_ge ‖z‖ b.rIn with hz | hz
  · rw [cutoffLogModulus, b.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hz.le), sub_self,
      zero_mul, abs_zero]
    exact ⟨by linarith [hle z], by norm_num⟩
  set t := 4 * (x z 2 ^ 2 + x z 3 ^ 2)
  have ht : 1 / 2 ≤ t := hb z (by linarith)
  have ht1 : t ≤ 1 := hle z
  have ht0 : 0 < t := by linarith
  -- `|log t| / 2 ≤ (1 / t - 1) / 2 ≤ 1 - t` for `1 / 2 ≤ t ≤ 1`.
  have hlog : |logModulus x z| ≤ 1 - t := by
    have hneg : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht1
    have hinv : Real.log t⁻¹ ≤ t⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.2 ht0)
    rw [Real.log_inv] at hinv
    have h2 : t⁻¹ ≤ 2 := by rw [inv_le_comm₀ ht0 two_pos]; linarith
    have key : t⁻¹ - 1 ≤ 2 * (1 - t) := by
      have : t⁻¹ - 1 = t⁻¹ * (1 - t) := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right h2 (by linarith)
    rw [logModulus, abs_div, abs_two, abs_of_nonpos hneg]
    linarith
  have hχ : |1 - b z| ≤ 1 :=
    abs_le.2 ⟨by linarith [b.le_one (x := z)], by linarith [b.nonneg (x := z)]⟩
  have hg : |cutoffLogModulus b x z| ≤ 1 - t := by
    rw [cutoffLogModulus, abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hχ).trans hlog
  exact ⟨hg, by linarith⟩

/-- **The cut-off logarithmic modulus solves a semilinear equation up to a compact error.** Off
the zeros of `α`, `ψ = log |α|` solves `Δψ = (exp (2ψ) - 1) / 8`, so the cut-off modulus `g`
satisfies `-Δg + g / 4 = -(exp (2g) - 1 - 2g) / 8 + k` with `k` smooth and compactly supported. -/
private theorem hasCompactSupport_cutoffLogModulus_remainder (b : ContDiffBump (0 : ℂ))
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hb : ∀ z, b.rIn - 1 ≤ ‖z‖ → 1 / 2 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) :
    HasCompactSupport fun z ↦ -Δ (cutoffLogModulus b x) z + cutoffLogModulus b x z / 4 +
      (Real.exp (2 * cutoffLogModulus b x z) - 1 - 2 * cutoffLogModulus b x z) / 8 := by
  have hxd (i : Fin 4) : ContDiff ℝ ∞ (fun w ↦ x w i) := contDiff_euclidean.1 hx i
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) b.rOut) fun z hz ↦ ?_
  rw [mem_closedBall_zero_iff, not_le] at hz
  have hrIn : b.rIn - 1 < ‖z‖ := by linarith [b.rIn_lt_rOut]
  set t := 4 * (x z 2 ^ 2 + x z 3 ^ 2)
  have ht : 0 < t := by linarith [hb z hrIn.le]
  have hα : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0 := by
    intro h
    simp only [t, h, mul_zero, lt_self_iff_false] at ht
  have heq := cutoffLogModulus_eventuallyEq (x := x) b hz
  have hs : ContDiff ℝ ∞ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) := by
    have h3 := hxd 3
    fun_prop
  -- `Δ log |α| = (|α|² - 1) / 8` off the zeros of `α`.
  have hΔ : Δ (logModulus x) z = (t - 1) / 8 := by
    have hlog : ContDiffAt ℝ 2 (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z :=
      (hs.contDiffAt.log ht.ne').of_le (by norm_cast)
    have hfun : logModulus x = (2⁻¹ : ℝ) • fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) := by
      funext w
      simp [logModulus, div_eq_inv_mul]
    rw [hfun, InnerProductSpace.laplacian_smul _ hlog, laplacian_log_normSq_of_equation_eq_zero
      ((hxd 2).contDiffAt.of_le (by norm_cast)) ((hxd 3).contDiffAt.of_le (by norm_cast)) hα
      (.of_forall hsol), smul_eq_mul]
    ring
  have hexp : Real.exp (2 * logModulus x z) = t := by
    rw [logModulus, mul_div_cancel₀ _ two_ne_zero, Real.exp_log ht]
  rw [(InnerProductSpace.laplacian_congr_nhds heq).self_of_nhds, heq.self_of_nhds, hΔ, hexp,
    logModulus]
  ring

/-- **The nonlinearity lies in `H^(2n)` with `g`.** For a square integrable `g` with
`|g| ≤ 1 / 2`, the function `exp (2g) - 1 - 2g` lies in `H^(2n)` whenever `g` does: for `n = 0`
because `|exp (2g) - 1 - 2g| ≤ 4 g² ≤ 2 |g|`, and for `n ≥ 1` by the exponential on the Sobolev
algebra. -/
private theorem exp_two_mul_sub_one_sub_mem_realSobolevFunctions {g : ℂ → ℝ}
    (hL : MemLp g 2 volume) (hbd : ∀ z, |g z| ≤ 1 / 2) {n : ℕ}
    (hn : g ∈ realSobolevFunctions ℂ (2 * n) 2) :
    (fun z ↦ Real.exp (2 * g z) - 1 - 2 * g z) ∈ realSobolevFunctions ℂ (2 * n) 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [Nat.cast_zero, mul_zero, mem_realSobolevFunctions_zero_iff]
    have h2g := hL.aestronglyMeasurable.const_mul 2
    have hm : AEStronglyMeasurable (fun z ↦ Real.exp (2 * g z) - 1 - 2 * g z) volume :=
      ((Real.continuous_exp.comp_aestronglyMeasurable h2g).sub aestronglyMeasurable_const).sub h2g
    refine (hL.norm.const_mul 2).of_le hm (.of_forall fun z ↦ ?_)
    have h := Real.abs_exp_sub_one_sub_id_le (x := 2 * g z) (by
      rw [abs_mul, abs_two]
      linarith [hbd z])
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 2 * |g z|)]
    calc |Real.exp (2 * g z) - 1 - 2 * g z| ≤ (2 * g z) ^ 2 := h
      _ = 4 * |g z| * |g z| := by rw [mul_pow, ← sq_abs (g z)]; ring
      _ ≤ 2 * |g z| := by nlinarith [abs_nonneg (g z), hbd z]
  · have hs : Module.finrank ℝ ℂ < 2 * (2 * (n : ℝ)) := by
      refine finrank_real_complex_lt_two_mul ?_
      have : (1 : ℝ) ≤ n := by exact_mod_cast hpos
      linarith
    exact sub_mem (exp_mul_sub_one_mem_realSobolevFunctions hs hn 2)
      (Submodule.smul_mem _ (2 : ℝ) hn)

/-- **The cut-off logarithmic modulus lies in every Sobolev space.** It is square integrable,
since `g² ≤ 1 - |α|²`, and the elliptic regularity of `-Δ + 1 / 4` raises its order by two at
each step: the nonlinearity `exp (2g) - 1 - 2g` is square integrable because `g` is bounded, and
lies in `H^s`, `s > 1`, together with `g`. -/
private theorem cutoffLogModulus_mem_realSobolevFunctions (b : ContDiffBump (0 : ℂ))
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hb : ∀ z, b.rIn - 1 ≤ ‖z‖ → 1 / 2 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (s : ℝ) :
    cutoffLogModulus b x ∈ realSobolevFunctions ℂ s 2 := by
  have hxd (i : Fin 4) : ContDiff ℝ ∞ (fun w ↦ x w i) := contDiff_euclidean.1 hx i
  have hp := (hxd 2).of_le (m := 2) (by norm_cast)
  have hq := (hxd 3).of_le (m := 2) (by norm_cast)
  set g := cutoffLogModulus b x
  have hg : ContDiff ℝ ∞ g := contDiff_cutoffLogModulus b hx hb
  have hbd := abs_cutoffLogModulus_le b (normSq_le_one_of_tendsto hp hq hsol hlim) hb
  -- `g` is square integrable, since `g² ≤ 1 - |α|²`.
  have hL : MemLp g 2 volume := by
    refine (memLp_two_iff_integrable_sq hg.continuous.aestronglyMeasurable).2 <|
      (integrable_one_sub_normSq (μ := volume) hp hq hsol hlim).mono'
        (hg.continuous.pow 2).aestronglyMeasurable (.of_forall fun z ↦ ?_)
    obtain ⟨h₁, -⟩ := hbd z
    rw [Real.norm_eq_abs, abs_pow, sq_abs]
    nlinarith [abs_nonneg (g z), sq_abs (g z)]
  set G : ℂ → ℝ := fun z ↦ Real.exp (2 * g z) - 1 - 2 * g z
  -- The compactly supported remainder lies in every Sobolev space.
  have hk (s' : ℝ) : (fun z ↦ -Δ g z + g z / 4 + G z / 8) ∈ realSobolevFunctions ℂ s' 2 := by
    refine mem_realSobolevFunctions_of_hasCompactSupport ?_
      (hasCompactSupport_cutoffLogModulus_remainder b hx hsol hb) s'
    have hΔ : ContDiff ℝ ∞ (Δ g) := hg.laplacian (by simp)
    have hGc : ContDiff ℝ ∞ G :=
      ((Real.contDiff_exp.comp (contDiff_const.mul hg)).sub contDiff_const).sub
        (contDiff_const.mul hg)
    exact (hΔ.neg.add (hg.div_const 4)).add (hGc.div_const 8)
  -- Bootstrap: `-Δg + g / 4 = k - G / 8` raises the order by two.
  have hstep (n : ℕ) : g ∈ realSobolevFunctions ℂ (2 * n) 2 := by
    induction n with
    | zero => simpa using mem_realSobolevFunctions_zero_iff.2 hL
    | succ n ih =>
      have h := mem_realSobolevFunctions_add_two_of_neg_laplacian_add_smul (c := 1 / 4)
        (s := 2 * n) (by norm_num) (hg.of_le (by norm_cast)) hL ?_
      · convert h using 2
        push_cast
        ring
      · have hfun : (fun z ↦ -Δ g z + 1 / 4 * g z) =
            (fun z ↦ -Δ g z + g z / 4 + G z / 8) - (8⁻¹ : ℝ) • G := by
          funext z
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [hfun]
        exact sub_mem (hk _) (Submodule.smul_mem _ _
          (exp_two_mul_sub_one_sub_mem_realSobolevFunctions hL (fun z ↦ (hbd z).2) ih))
  obtain ⟨n, hn⟩ := exists_nat_ge (s / 2)
  exact realSobolevFunctions_mono (by norm_num) (by norm_num) (by linarith) (hstep n)

/-! ### The model field -/

private theorem contDiff_modelField (f : ContDiffBump (0 : ℝ)) (m : ℕ) {g : ℂ → ℝ}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (modelField f m g) := by
  have hdg (v : ℂ) : ContDiff ℝ ∞ (fun z ↦ fderiv ℝ g z v) :=
    (hg.fderiv_right le_rfl).clm_apply contDiff_const
  have href (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ referenceField f m z i) :=
    contDiff_euclidean.1 (contDiff_referenceField f m) i
  have hexp : ContDiff ℝ ∞ (fun z ↦ Real.exp (g z) - 1) :=
    (Real.contDiff_exp.comp hg).sub contDiff_const
  refine contDiff_euclidean.2 fun i ↦ ?_
  fin_cases i
  exacts [(hdg I).neg, hdg 1, hexp.mul (href 2), hexp.mul (href 3)]

/-- The model field of a smooth `g` lying in every Sobolev space lies in every Sobolev space: its
connection coordinates are derivatives of `g`, and its section coordinates are `exp g - 1` times
coordinates of the reference field, which have bounded derivatives of every order. -/
private theorem modelField_mem_sobolevFields (f : ContDiffBump (0 : ℝ)) (m : ℕ) {g : ℂ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgs : ∀ s, g ∈ realSobolevFunctions ℂ s 2) (k : ℕ) :
    modelField f m g ∈ sobolevFields k := by
  have hd (v : ℂ) : (fun z ↦ fderiv ℝ g z v) ∈ realSobolevFunctions ℂ k 2 :=
    fderiv_apply_mem_realSobolevFunctions (by norm_num) (by norm_num) (Nat.cast_nonneg k)
      (hg.of_le (by norm_cast)) (hgs (k + 1)) v
  have hexp : (fun z ↦ Real.exp (g z) - 1) ∈ realSobolevFunctions ℂ k 2 := by
    have h := exp_mul_sub_one_mem_realSobolevFunctions
      (finrank_real_complex_lt_two_mul (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]))
      (hgs (k + 2)) 1
    simp only [one_mul] at h
    exact realSobolevFunctions_mono (by norm_num) (by norm_num) (by linarith) h
  have hmul (i : Fin 4) :
      (fun z ↦ referenceField f m z i * (Real.exp (g z) - 1)) ∈ realSobolevFunctions ℂ k 2 :=
    mul_mem_realSobolevFunctions_of_bounded_derivatives (by norm_num) (by norm_num) k
      (contDiff_euclidean.1 (contDiff_referenceField f m) i)
      (fun j _ ↦ exists_norm_iteratedFDeriv_referenceField_apply_le f m i j) hexp
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · exact neg_mem (hd I)
  · exact hd 1
  · convert hmul 2 using 2
    simp [modelField, mul_comm]
  · convert hmul 3 using 2
    simp [modelField, mul_comm]

/-! ### Framed representatives in `A_m^s` -/

/-- **Every smooth framed vortex has a representative in every affine Sobolev space.** A smooth
solution of the plane vortex equations with the degree-`m` end framing `α (z / |z|)^(-m) → 1` is
carried by a smooth framed gauge into `A_m^s` for every `s` simultaneously. The gauge normalizes
the end phase, so that `α = |α| (z / |z|)^m` outside a compact set. -/
theorem exists_framedGaugeGroup_smul_mem_framedFieldSpace (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (f : ContDiffBump (0 : ℝ)) :
    ∃ u : framedGaugeGroup, ∀ s, u • x ∈ framedFieldSpace f m s := by
  obtain ⟨u, hu⟩ := exists_framedGaugeGroup_sectionValue_smul_eq hx hframe
  refine ⟨u, fun s ↦ ?_⟩
  set y := u • x
  have huc := ((mem_framedGaugeGroup _).1 u.property).1
  have hy : ContDiff ℝ ∞ y := contDiff_gaugeTransform huc hx
  have hsol' (z : ℂ) : equation y z = 0 :=
    (equation_gaugeTransform_eq_zero_iff ((huc.of_le (by norm_cast)).contDiffAt)
      fun i ↦ (contDiff_euclidean.1 hx i).differentiable (by simp) z).2 (hsol z)
  have hlim : Tendsto (fun z ↦ 4 * (y z 2 ^ 2 + y z 3 ^ 2)) (cocompact ℂ) (𝓝 1) := by
    refine (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe).congr fun z ↦ ?_
    rw [← sq_norm_sectionValue, ← sq_norm_sectionValue]
    simp only [y, framedGaugeGroup_smul, sectionValue_gaugeTransform, norm_mul, Circle.norm_coe,
      one_mul]
  -- Outside a disc of radius `R₁` the section has modulus at least `1 / √2` and the
  -- normalized end phase.
  obtain ⟨R₁, -, hR₁⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸
      (hlim.eventually (le_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1))).and hu)
  set R := max R₁ (max 1 f.rOut)
  have hR : 0 < R := lt_max_of_lt_right (lt_max_of_lt_left one_pos)
  let b : ContDiffBump (0 : ℂ) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  have hbIn : b.rIn = R + 1 := rfl
  have hbOut : b.rOut = R + 2 := rfl
  have hb (z : ℂ) (hz : b.rIn - 1 ≤ ‖z‖) : 1 / 2 ≤ 4 * (y z 2 ^ 2 + y z 3 ^ 2) := by
    rw [hbIn, add_sub_cancel_right] at hz
    exact (hR₁ ((le_max_left _ _).trans hz)).1
  set g := cutoffLogModulus b y
  have hg : ContDiff ℝ ∞ g := contDiff_cutoffLogModulus b hy hb
  have hgs := cutoffLogModulus_mem_realSobolevFunctions b hy hsol' hlim hb
  -- Outside the disc of radius `R + 2` the field is the model field.
  have hD : HasCompactSupport (y - referenceField f m - modelField f m g) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R + 2)) fun z hz ↦ ?_
    rw [mem_closedBall_zero_iff, not_le] at hz
    have hzR : R < ‖z‖ := by linarith
    have hnhds : ∀ᶠ w in 𝓝 z, R₁ ≤ ‖w‖ :=
      Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds
        ((le_max_left _ _).trans_lt hzR)) fun w hw ↦ le_of_lt hw
    have heq := cutoffLogModulus_eventuallyEq (x := y) b (hbOut ▸ hz)
    have h := sub_referenceField_eq f (rOut_le_norm_sq f ((le_max_right _ _).trans_lt hzR)) hy
      (hsol' z) (hnhds.mono fun w hw ↦ (hR₁ hw).2)
      (hnhds.mono fun w hw h0 ↦ by have := (hR₁ hw).1; rw [h0] at this; norm_num at this)
    rw [Pi.sub_apply, Pi.sub_apply, h]
    simp only [modelField, g, heq.fderiv_eq, heq.self_of_nhds, sub_self]
  have hsplit : y - referenceField f m =
      (y - referenceField f m - modelField f m g) + modelField f m g := by abel
  rw [mem_framedFieldSpace, hsplit]
  obtain ⟨k, hk⟩ := exists_nat_ge s
  exact add_mem (mem_sobolevFields_of_hasCompactSupport
      ((hy.sub (contDiff_referenceField f m)).sub (contDiff_modelField f m hg)) hD s)
    (sobolevFields_mono hk (modelField_mem_sobolevFields f m hg hgs k))

end TauCeti.Vortex

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EndFraming
public import TauCeti.Analysis.Complex.LogOneAddNormSq
public import TauCeti.Analysis.Polynomial.AtInfinity
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The background amplitude of the prescribed-zero vortex problem

Let `P` be a monic polynomial of degree `m`. A field of the form `amplitudeField u P.eval`, with
section `α = exp(u) P` and zero divisor `P`, is a vortex with the degree-`m` end framing exactly
when `u` solves the regularized scalar equation

`Δu = (exp(2u) |P|² - 1) / 8`,    `u + m log |z| → 0` at infinity

(`TauCeti.Vortex.equation_amplitudeField_eq_zero_iff`,
`TauCeti.Vortex.tendsto_sectionValue_amplitudeField_mul_inv_phase_iff_log`, for `C²` amplitudes
`u`). Bringing an arbitrary vortex with zero divisor `P` into this form is a gauge choice that is
not treated here. The solution `u` grows logarithmically, so it lies in no Sobolev space.
Following Taubes, this file subtracts an explicit smooth background with the same growth. Here the
background is

`u₀ = -log (1 + |P|²) / 2`    (`TauCeti.Vortex.backgroundAmplitude`),

which needs no choice of roots and no cutoff. For `m ≥ 1`, `u₀ + m log |z| → 0`. For a
correction `w`:

* if `w` is `C²` at `z`, then `u = u₀ + w` solves the scalar equation at `z` exactly when

  `Δw = (exp(2w) h - 1) / 8 + g`,    `h = |P|² / (1 + |P|²)`,    `g = 2 |P'|² / (1 + |P|²)²`;

  here `g = -Δu₀` and `h = exp(2u₀) |P|²` is the squared modulus of the background section;
* if `m ≥ 1`, then for every `w` the reconstructed section has the degree-`m` end framing
  exactly when `w → 0` at infinity.

So, for `m ≥ 1` and `C²` corrections `w`, the field `amplitudeField (u₀ + w) P.eval` is a vortex
with the degree-`m` end framing exactly when `w` solves the reduced equation and tends to zero at
infinity. The reduced equation has smooth coefficients with `0 ≤ h < 1`. The defect
`1 - h = (1 + |P|²)⁻¹` is square integrable (`Polynomial.memLp_inv_one_add_norm_eval_sq`) and the
source `g` is integrable; these are the integrability properties of the coefficients that a
variational treatment of the reduced equation on `H¹(ℂ)` uses. Existence of a solution of the
reduced equation is not proved here.

## Main results

* `TauCeti.Vortex.laplacian_backgroundAmplitude`: `Δu₀ = -2 |f'|² / (1 + |f|²)²` for holomorphic
  `f`.
* `TauCeti.Vortex.equation_amplitudeField_backgroundAmplitude_add_eq_zero_iff`: the field
  reconstructed from `u₀ + w` solves the vortex equation at `z` exactly when `w` solves the
  reduced equation at `z`.
* `TauCeti.Vortex.tendsto_backgroundAmplitude_add_natDegree_mul_log`: `u₀ + m log |z| → 0`.
* `TauCeti.Vortex.tendsto_sectionValue_amplitudeField_backgroundAmplitude_add_iff`: the end
  framing of the reconstructed section is equivalent to `w → 0`.
* `TauCeti.Vortex.integrable_laplacian_backgroundAmplitude`: the source term of the reduced
  equation is integrable.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Topology InnerProductSpace Laplacian MeasureTheory

variable {f : ℂ → ℂ} {z : ℂ}

/-- The background amplitude `u₀ = -log (1 + ‖f‖²) / 2`. For a polynomial `f` it is smooth on the
whole plane, and for a monic polynomial `f` of degree `m ≥ 1` it has the growth `-m log ‖z‖` of a
degree-`m` vortex amplitude at infinity. -/
def backgroundAmplitude (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  -Real.log (1 + ‖f z‖ ^ 2) / 2

/-- The defining formula of the background amplitude. -/
theorem backgroundAmplitude_apply (f : ℂ → ℂ) (z : ℂ) :
    backgroundAmplitude f z = -Real.log (1 + ‖f z‖ ^ 2) / 2 := (rfl)

/-- `exp (2 u₀) = (1 + ‖f‖²)⁻¹`. -/
@[simp]
theorem exp_two_mul_backgroundAmplitude (f : ℂ → ℂ) (z : ℂ) :
    Real.exp (2 * backgroundAmplitude f z) = (1 + ‖f z‖ ^ 2)⁻¹ := by
  rw [backgroundAmplitude_apply, mul_div_cancel₀ _ two_ne_zero, Real.exp_neg,
    Real.exp_log (by positivity)]

/-- The background amplitude is as smooth as `f`, including at the zeros of `f`. -/
theorem contDiff_backgroundAmplitude {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (backgroundAmplitude f) := by
  have h : ContDiff ℝ n fun z ↦ 1 + ‖f z‖ ^ 2 := contDiff_const.add (hf.norm_sq ℝ)
  exact (h.log fun z ↦ by positivity).neg.div_const 2

/-- The background amplitude is as smooth at `z` as `f`. -/
theorem contDiffAt_backgroundAmplitude {n : WithTop ℕ∞} (hf : ContDiffAt ℝ n f z) :
    ContDiffAt ℝ n (backgroundAmplitude f) z := by
  have h : ContDiffAt ℝ n (fun z ↦ 1 + ‖f z‖ ^ 2) z := contDiffAt_const.add (hf.norm_sq ℝ)
  exact (h.log (by positivity)).neg.div_const 2

/-- The Laplacian of the background amplitude of a holomorphic function:
`Δu₀ = -2 ‖f'‖² / (1 + ‖f‖²)²`. -/
theorem laplacian_backgroundAmplitude (hf : AnalyticAt ℂ f z) :
    Δ (backgroundAmplitude f) z = -(2 * ‖deriv f z‖ ^ 2 / (1 + ‖f z‖ ^ 2) ^ 2) := by
  have hlog : ContDiffAt ℝ 2 (fun w ↦ Real.log (1 + ‖f w‖ ^ 2)) z :=
    (contDiffAt_const.add ((hf.contDiffAt.restrict_scalars ℝ).norm_sq ℝ)).log (by positivity)
  have heq : backgroundAmplitude f = (-(1 / 2) : ℝ) • fun w ↦ Real.log (1 + ‖f w‖ ^ 2) := by
    funext w
    simp only [backgroundAmplitude_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq, laplacian_smul _ hlog, laplacian_log_one_add_norm_sq_of_analyticAt hf, smul_eq_mul]
  ring

/-- **Reduction of the scalar vortex equation to the background.** For a holomorphic `f`, the
amplitude `u₀ + w` solves the regularized scalar equation `Δu = (exp (2u) ‖f‖² - 1) / 8` at `z`
exactly when `w` solves the reduced equation
`Δw = (exp (2w) h - 1) / 8 + 2 ‖f'‖² / (1 + ‖f‖²)²` at `z`, where `h = ‖f‖² / (1 + ‖f‖²)`. -/
theorem laplacian_backgroundAmplitude_add_eq_iff {w : ℂ → ℝ} (hf : AnalyticAt ℂ f z)
    (hw : ContDiffAt ℝ 2 w z) :
    Δ (fun z ↦ backgroundAmplitude f z + w z) z =
        (Real.exp (2 * (backgroundAmplitude f z + w z)) * ‖f z‖ ^ 2 - 1) / 8 ↔
      Δ w z = (Real.exp (2 * w z) * (‖f z‖ ^ 2 / (1 + ‖f z‖ ^ 2)) - 1) / 8 +
        2 * ‖deriv f z‖ ^ 2 / (1 + ‖f z‖ ^ 2) ^ 2 := by
  have hbg : ContDiffAt ℝ 2 (backgroundAmplitude f) z :=
    contDiffAt_backgroundAmplitude (hf.contDiffAt.restrict_scalars ℝ)
  have hexp : Real.exp (2 * (backgroundAmplitude f z + w z)) * ‖f z‖ ^ 2 =
      Real.exp (2 * w z) * (‖f z‖ ^ 2 / (1 + ‖f z‖ ^ 2)) := by
    rw [mul_add, Real.exp_add, exp_two_mul_backgroundAmplitude]
    field_simp
  rw [← Pi.add_def, hbg.laplacian_add hw, laplacian_backgroundAmplitude hf, hexp]
  constructor <;> intro h <;> linarith

/-- The field reconstructed from the amplitude `u₀ + w` and a holomorphic `f` solves the vortex
equation at `z` exactly when `w` solves the reduced equation at `z`. -/
theorem equation_amplitudeField_backgroundAmplitude_add_eq_zero_iff {w : ℂ → ℝ}
    (hf : AnalyticAt ℂ f z) (hw : ContDiffAt ℝ 2 w z) :
    equation (amplitudeField (fun z ↦ backgroundAmplitude f z + w z) f) z = 0 ↔
      Δ w z = (Real.exp (2 * w z) * (‖f z‖ ^ 2 / (1 + ‖f z‖ ^ 2)) - 1) / 8 +
        2 * ‖deriv f z‖ ^ 2 / (1 + ‖f z‖ ^ 2) ^ 2 := by
  have hbg : ContDiffAt ℝ 2 (backgroundAmplitude f) z :=
    contDiffAt_backgroundAmplitude (hf.contDiffAt.restrict_scalars ℝ)
  rw [equation_amplitudeField_eq_zero_iff (hbg.add hw) hf.differentiableAt,
    laplacian_backgroundAmplitude_add_eq_iff hf hw]

/-- For a monic polynomial `P` of degree `m ≥ 1`, the background amplitude has the growth of a
degree-`m` vortex amplitude: `u₀ + m log ‖z‖ → 0` at infinity. -/
theorem tendsto_backgroundAmplitude_add_natDegree_mul_log {P : Polynomial ℂ} (hP : P.Monic)
    (hm : 0 < P.natDegree) :
    Tendsto (fun z ↦ backgroundAmplitude P.eval z + P.natDegree * Real.log ‖z‖)
      (cocompact ℂ) (𝓝 0) := by
  set m := P.natDegree
  have hz : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 :=
    (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
  have hq := hP.tendsto_eval_div_pow_natDegree_cocompact
  have hinv : Tendsto (fun z : ℂ ↦ (‖z‖ ^ (2 * m))⁻¹) (cocompact ℂ) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      ((tendsto_pow_atTop (by omega)).comp tendsto_norm_cocompact_atTop)
  -- `(1 + ‖P‖²) / ‖z‖ ^ (2m) = ‖z‖ ^ (-2m) + ‖P / z ^ m‖² → 1`.
  have hlim : Tendsto (fun z ↦ (‖z‖ ^ (2 * m))⁻¹ + ‖P.eval z / z ^ m‖ ^ 2) (cocompact ℂ)
      (𝓝 1) := by
    simpa using hinv.add ((hq.norm.pow 2).trans (by simp))
  have hlog := ((Real.continuousAt_log one_ne_zero).tendsto.comp hlim).div_const (-2)
  simp only [Real.log_one, zero_div] at hlog
  refine hlog.congr' ?_
  filter_upwards [hz] with z hz
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hsplit : (‖z‖ ^ (2 * m))⁻¹ + ‖P.eval z / z ^ m‖ ^ 2 =
      (1 + ‖P.eval z‖ ^ 2) / ‖z‖ ^ (2 * m) := by
    rw [norm_div, norm_pow, div_pow, ← pow_mul, mul_comm m 2]
    field_simp
  simp only [Function.comp_apply, hsplit, backgroundAmplitude_apply]
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
  push_cast
  ring

/-- The end framing of the section reconstructed from `u₀ + w` is equivalent to `w → 0` at
infinity. Thus the boundary condition of the prescribed-zero vortex problem becomes a decay
condition on the correction `w`. -/
theorem tendsto_sectionValue_amplitudeField_backgroundAmplitude_add_iff {P : Polynomial ℂ}
    (hP : P.Monic) (hm : 0 < P.natDegree) (w : ℂ → ℝ) :
    Tendsto (fun z ↦ sectionValue
        (amplitudeField (fun z ↦ backgroundAmplitude P.eval z + w z) P.eval) z *
          ((z / (‖z‖ : ℂ)) ^ P.natDegree)⁻¹) (cocompact ℂ) (𝓝 1) ↔
      Tendsto w (cocompact ℂ) (𝓝 0) := by
  rw [tendsto_sectionValue_amplitudeField_mul_inv_phase_iff_log hP]
  have h₀ := tendsto_backgroundAmplitude_add_natDegree_mul_log hP hm
  constructor
  · intro h
    simpa using h.sub h₀
  · intro h
    have h' := h.add h₀
    rw [add_zero] at h'
    exact h'.congr fun z ↦ by ring

/-! ### Integrability of the coefficients of the reduced equation -/

/-- For every complex polynomial `P`, the Laplacian of the background amplitude, the source term
`-g` of the reduced equation, is integrable on the plane. -/
theorem integrable_laplacian_backgroundAmplitude (P : Polynomial ℂ) :
    Integrable (Δ (backgroundAmplitude P.eval)) := by
  have hΔ : Δ (backgroundAmplitude P.eval) = fun z ↦
      -(2 * (‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2)) := by
    funext z
    rw [laplacian_backgroundAmplitude (P.differentiable.analyticAt z), Polynomial.deriv,
      mul_div_assoc]
  rw [hΔ]
  exact (P.integrable_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq.const_mul 2).neg

end TauCeti.Vortex

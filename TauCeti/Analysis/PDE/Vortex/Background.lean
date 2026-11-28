/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EndFraming
public import TauCeti.Analysis.Complex.LogOneAddNormSq
public import TauCeti.Analysis.Polynomial.AtInfinity
public import TauCeti.Analysis.Normed.Module.Ball.UnivUnitBall
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.SpecialFunctions.Exp.UniformConvergence

/-!
# The background amplitude of the prescribed-zero vortex problem

Let `P` be a monic polynomial of degree `m`. A field of the form `amplitudeField u P.eval`, with
section `α = exp(u) P` and zero divisor `P`, is a vortex with the degree-`m` end framing exactly
when `u` solves the regularized scalar equation

`Δu = (exp(2u) |P|² - 1) / 8`,    `u + m log |z| → 0` at infinity

(`TauCeti.Vortex.equation_amplitudeField_eq_zero_iff`,
`TauCeti.Vortex.tendsto_sectionValue_amplitudeField_mul_inv_phase_iff_log`, for `C²` amplitudes
`u`). Conversely, every smooth vortex with this end framing and zero divisor `P` is a framed gauge
transform of such an amplitude field
(`TauCeti.Vortex.exists_framedGaugeGroup_smul_amplitudeField_eq`, in
`TauCeti.Analysis.PDE.Vortex.AmplitudeForm`). For `m ≥ 1` the solution `u` grows like
`-m log |z|`, so it is not square integrable on `ℂ` and in particular does not lie in the
unweighted space `H¹(ℂ)`. Following Taubes, this file subtracts an explicit smooth background with
the same growth. Here the background is

`u₀ = -log (1 + |P|²) / 2`    (`TauCeti.Vortex.backgroundAmplitude`),

which needs no choice of roots and no cutoff. For `m ≥ 1`, `u₀ + m log |z| → 0`. For a
correction `w`:

* if `w` is `C²` at `z`, then `u = u₀ + w` solves the scalar equation at `z` exactly when

  `Δw = (exp(2w) h - 1) / 8 + g`,    `h = |P|² / (1 + |P|²)`,    `g = 2 |P'|² / (1 + |P|²)²`;

  here `g = -Δu₀` and `h = exp(2u₀) |P|²` (`TauCeti.Vortex.backgroundWeight`) is the squared
  modulus of the background section;
* if `m ≥ 1`, then for every `w` the reconstructed section has the degree-`m` end framing
  exactly when `w → 0` at infinity.

So, for `m ≥ 1` and `C²` corrections `w`, the field `amplitudeField (u₀ + w) P.eval` is a vortex
with the degree-`m` end framing exactly when `w` solves the reduced equation and tends to zero at
infinity. The reduced equation has smooth coefficients with `0 ≤ h < 1`. The defect
`1 - h = (1 + |P|²)⁻¹` is square integrable (`Polynomial.memLp_inv_one_add_norm_eval_sq`) and the
source `g` is integrable; these are the integrability properties of the coefficients that a
variational treatment of the reduced equation on `H¹(ℂ)` uses. Existence of a solution of the
reduced equation is not proved here.

**Dependence on the polynomial.** The background section is the image
`exp(u₀) P = (√(1 + ‖P‖²))⁻¹ • P` of `P` under the radial map
`OpenPartialHomeomorph.univUnitBall` onto the open unit disc, and the background connection is
`Du₀ = -⟪P, DP⟫ / (1 + ‖P‖²)`. Let the coefficients of polynomials `P i` converge to those of `Q`,
with eventually `deg P i ≤ deg Q`. Then `P i - Q` and its derivative are bounded by
`δ i (1 + ‖Q‖)` with `δ i → 0`, while `‖Q'‖ ≤ C (1 + ‖Q‖)`. The radial map turns errors of this
size into uniformly small ones (`OpenPartialHomeomorph.norm_univUnitBall_sub_le_of_norm_sub_le`),
so the background sections and the derivatives `Du₀` converge uniformly on the whole plane, not
only on compact sets; zeros of `P i` may collide in the limit. The fields reconstructed from
amplitudes `u₀ + w i` then converge uniformly whenever differentiable corrections `w i` converge
uniformly together with their first derivatives and the limit `w₀` is bounded above. This is the
background half of the continuity of the vortex field `amplitudeField (u₀ + w_P) P` in `P`, the
correction `w_P` entering through these hypotheses.

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
* `TauCeti.Vortex.exp_backgroundAmplitude_smul`, `TauCeti.Vortex.hasFDerivAt_backgroundAmplitude`:
  the background section is `univUnitBall ∘ f`, and `Du₀ = -⟪f, Df⟫ / (1 + ‖f‖²)`.
* `TauCeti.Vortex.exists_abs_fderiv_backgroundAmplitude_apply_le`: for a polynomial `P`, the
  derivative `Du₀` is bounded on the plane.
* `TauCeti.Vortex.tendstoUniformly_exp_backgroundAmplitude_smul`,
  `TauCeti.Vortex.tendstoUniformly_fderiv_backgroundAmplitude`: along polynomials whose
  coefficients converge, the background sections and the derivatives of the background amplitudes
  converge uniformly on the plane.
* `TauCeti.Vortex.continuous_ofFun_exp_backgroundAmplitude_smul`,
  `TauCeti.Vortex.continuous_ofFun_fderiv_backgroundAmplitude`: the same as continuity in the
  uniform topology for families of a fixed degree.
* `TauCeti.Vortex.tendstoUniformly_amplitudeField_backgroundAmplitude_add`: the reconstructed
  fields converge uniformly when the corrections and their derivatives do and the limit correction
  is bounded above.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Topology InnerProductSpace RealInnerProductSpace Laplacian MeasureTheory

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

/-- The coefficient `h = ‖f‖² / (1 + ‖f‖²)` of the reduced vortex equation, equal to
`exp (2u₀) ‖f‖²` for the background amplitude `u₀`. -/
def backgroundWeight (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  ‖f z‖ ^ 2 / (1 + ‖f z‖ ^ 2)

/-- The defining formula of `TauCeti.Vortex.backgroundWeight`. -/
theorem backgroundWeight_def (f : ℂ → ℂ) (z : ℂ) :
    backgroundWeight f z = ‖f z‖ ^ 2 / (1 + ‖f z‖ ^ 2) := (rfl)

/-- `h = exp (2u₀) ‖f‖²`: the coefficient `TauCeti.Vortex.backgroundWeight` is the squared modulus
of the background section. -/
theorem exp_two_mul_backgroundAmplitude_mul_sq_norm (f : ℂ → ℂ) (z : ℂ) :
    Real.exp (2 * backgroundAmplitude f z) * ‖f z‖ ^ 2 = backgroundWeight f z := by
  rw [exp_two_mul_backgroundAmplitude, backgroundWeight_def, inv_mul_eq_div]

theorem backgroundWeight_nonneg (f : ℂ → ℂ) (z : ℂ) : 0 ≤ backgroundWeight f z := by
  rw [backgroundWeight_def]
  positivity

/-- The coefficient `h = ‖f‖² / (1 + ‖f‖²)` is less than one: its defect `1 - h` is
`(1 + ‖f‖²)⁻¹`. -/
theorem backgroundWeight_lt_one (f : ℂ → ℂ) (z : ℂ) : backgroundWeight f z < 1 := by
  rw [backgroundWeight_def, div_lt_one (by positivity)]
  exact lt_one_add _

/-- The coefficient `h = ‖f‖² / (1 + ‖f‖²)` is `1` minus its defect `(1 + ‖f‖²)⁻¹`. -/
theorem backgroundWeight_eq_one_sub_inv (f : ℂ → ℂ) (z : ℂ) :
    backgroundWeight f z = 1 - (1 + ‖f z‖ ^ 2)⁻¹ := by
  rw [backgroundWeight_def]
  field_simp
  ring

theorem continuous_backgroundWeight (hf : Continuous f) : Continuous (backgroundWeight f) := by
  have hh : backgroundWeight f = fun z ↦ ‖f z‖ ^ 2 / (1 + ‖f z‖ ^ 2) :=
    funext (backgroundWeight_def f)
  rw [hh]
  exact (hf.norm.pow 2).div (continuous_const.add (hf.norm.pow 2)) fun z ↦ by positivity

/-- The coefficient `h = ‖f‖² / (1 + ‖f‖²)` is as smooth as `f`. -/
theorem contDiff_backgroundWeight {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (backgroundWeight f) := by
  have hh : backgroundWeight f = fun z ↦ ‖f z‖ ^ 2 / (1 + ‖f z‖ ^ 2) :=
    funext (backgroundWeight_def f)
  rw [hh]
  exact (hf.norm_sq ℝ).div (contDiff_const.add (hf.norm_sq ℝ)) fun z ↦ by positivity

/-- The background amplitudes of sections depending on a parameter are as smooth, jointly in the
parameter and the point, as the sections, including at their zeros. -/
theorem contDiff_parametric_backgroundAmplitude {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {f : P → ℂ → ℂ} {n : WithTop ℕ∞}
    (hf : ContDiff ℝ n fun p : P × ℂ ↦ f p.1 p.2) :
    ContDiff ℝ n fun p : P × ℂ ↦ backgroundAmplitude (f p.1) p.2 := by
  have h : ContDiff ℝ n fun p : P × ℂ ↦ 1 + ‖f p.1 p.2‖ ^ 2 := contDiff_const.add (hf.norm_sq ℝ)
  exact (h.log fun p ↦ by positivity).neg.div_const 2

/-- The background amplitude is as smooth as `f`, including at the zeros of `f`. -/
theorem contDiff_backgroundAmplitude {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (backgroundAmplitude f) :=
  (contDiff_parametric_backgroundAmplitude (P := Unit) (f := fun _ ↦ f)
    (hf.comp contDiff_snd)).comp ((contDiff_const (c := ())).prodMk contDiff_id)

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
`Δw = (exp (2w) h - 1) / 8 + 2 ‖f'‖² / (1 + ‖f‖²)²` at `z`, where `h = ‖f‖² / (1 + ‖f‖²)`
(`TauCeti.Vortex.backgroundWeight`). -/
theorem laplacian_backgroundAmplitude_add_eq_iff {w : ℂ → ℝ} (hf : AnalyticAt ℂ f z)
    (hw : ContDiffAt ℝ 2 w z) :
    Δ (fun z ↦ backgroundAmplitude f z + w z) z =
        (Real.exp (2 * (backgroundAmplitude f z + w z)) * ‖f z‖ ^ 2 - 1) / 8 ↔
      Δ w z = (Real.exp (2 * w z) * backgroundWeight f z - 1) / 8 +
        2 * ‖deriv f z‖ ^ 2 / (1 + ‖f z‖ ^ 2) ^ 2 := by
  have hbg : ContDiffAt ℝ 2 (backgroundAmplitude f) z :=
    contDiffAt_backgroundAmplitude (hf.contDiffAt.restrict_scalars ℝ)
  have hexp : Real.exp (2 * (backgroundAmplitude f z + w z)) * ‖f z‖ ^ 2 =
      Real.exp (2 * w z) * backgroundWeight f z := by
    rw [mul_add, Real.exp_add, mul_right_comm, exp_two_mul_backgroundAmplitude_mul_sq_norm,
      mul_comm]
  rw [← Pi.add_def, hbg.laplacian_add hw, laplacian_backgroundAmplitude hf, hexp]
  constructor <;> intro h <;> linarith

/-- The field reconstructed from the amplitude `u₀ + w` and a holomorphic `f` solves the vortex
equation at `z` exactly when `w` solves the reduced equation at `z`. -/
theorem equation_amplitudeField_backgroundAmplitude_add_eq_zero_iff {w : ℂ → ℝ}
    (hf : AnalyticAt ℂ f z) (hw : ContDiffAt ℝ 2 w z) :
    equation (amplitudeField (fun z ↦ backgroundAmplitude f z + w z) f) z = 0 ↔
      Δ w z = (Real.exp (2 * w z) * backgroundWeight f z - 1) / 8 +
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

/-! ### The background section and the derivative of the background amplitude -/

/-- `exp u₀ = (√(1 + ‖f‖²))⁻¹`. -/
@[simp]
theorem exp_backgroundAmplitude (f : ℂ → ℂ) (z : ℂ) :
    Real.exp (backgroundAmplitude f z) = (√(1 + ‖f z‖ ^ 2))⁻¹ := by
  rw [← Real.sqrt_inv, eq_comm, Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _),
    ← Real.exp_add, ← two_mul, exp_two_mul_backgroundAmplitude]

/-- The background section `exp(u₀) f` is the image of `f` under the radial map
`OpenPartialHomeomorph.univUnitBall : w ↦ (√(1 + ‖w‖²))⁻¹ • w` onto the open unit disc. -/
theorem exp_backgroundAmplitude_smul (f : ℂ → ℂ) (z : ℂ) :
    Real.exp (backgroundAmplitude f z) • f z = OpenPartialHomeomorph.univUnitBall (f z) := by
  rw [exp_backgroundAmplitude, OpenPartialHomeomorph.univUnitBall_apply]

/-- The derivative of the background amplitude `u₀ = -log (1 + ‖f‖²) / 2`:
`Du₀ = -⟪f, Df⟫ / (1 + ‖f‖²)`. -/
theorem hasFDerivAt_backgroundAmplitude {f' : ℂ →L[ℝ] ℂ} (hf : HasFDerivAt f f' z) :
    HasFDerivAt (backgroundAmplitude f) (-(1 + ‖f z‖ ^ 2)⁻¹ • (innerSL ℝ (f z)).comp f') z := by
  have h := ((hf.norm_sq.const_add 1).log (by positivity : 1 + ‖f z‖ ^ 2 ≠ 0)).const_mul
    (-(1 / 2) : ℝ)
  convert h using 1
  · funext x
    rw [backgroundAmplitude_apply]
    ring
  module

/-- The derivative of the background amplitude of a real-differentiable `f`. -/
theorem fderiv_backgroundAmplitude (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ (backgroundAmplitude f) z =
      -(1 + ‖f z‖ ^ 2)⁻¹ • (innerSL ℝ (f z)).comp (fderiv ℝ f z) :=
  (hasFDerivAt_backgroundAmplitude hf.hasFDerivAt).fderiv

/-- The derivative of the background amplitude of a complex-differentiable `f`, applied to a
vector `v`: `Du₀(v) = -⟪f, v f'⟫ / (1 + ‖f‖²)`. -/
theorem fderiv_backgroundAmplitude_apply (hf : DifferentiableAt ℂ f z) (v : ℂ) :
    fderiv ℝ (backgroundAmplitude f) z v = -((1 + ‖f z‖ ^ 2)⁻¹ * ⟪f z, v * deriv f z⟫_ℝ) := by
  rw [(hasFDerivAt_backgroundAmplitude (hf.hasDerivAt.hasFDerivAt.restrictScalars ℝ)).fderiv]
  simp [smul_eq_mul]

/-- The derivative of the background amplitude of a polynomial is bounded on unit vectors. -/
theorem exists_abs_fderiv_backgroundAmplitude_apply_le (P : Polynomial ℂ) :
    ∃ C, ∀ z v, ‖v‖ = 1 → |fderiv ℝ (backgroundAmplitude P.eval) z v| ≤ C := by
  obtain ⟨C, hC0, hC⟩ :=
    Polynomial.exists_norm_eval_le_mul_one_add_norm_eval (Polynomial.degree_derivative_le (p := P))
  refine ⟨2 * C, fun z v hv ↦ ?_⟩
  rw [fderiv_backgroundAmplitude_apply (P.differentiable z), Polynomial.deriv, abs_neg, abs_mul,
    abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 1 + ‖P.eval z‖ ^ 2)]
  have hin : |⟪P.eval z, v * P.derivative.eval z⟫_ℝ| ≤ ‖P.eval z‖ * (C * (1 + ‖P.eval z‖)) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_mul, hv, one_mul]
    exact mul_le_mul_of_nonneg_left (hC z) (norm_nonneg _)
  rw [inv_mul_le_iff₀ (by positivity)]
  refine hin.trans ?_
  have := norm_nonneg (P.eval z)
  nlinarith [sq_nonneg (‖P.eval z‖ - 1), mul_nonneg hC0 (sq_nonneg (‖P.eval z‖ - 1))]

/-! ### Uniform convergence along converging polynomials -/

variable {ι : Type*} {l : Filter ι} {P : ι → Polynomial ℂ} {Q : Polynomial ℂ}

/-- **Uniform convergence of the background sections.** If the coefficients of the polynomials
`P i` converge to those of `Q`, and eventually `deg P i ≤ deg Q`, then the background sections
`exp(u₀) P = P / √(1 + ‖P‖²)` converge uniformly on the whole plane. -/
theorem tendstoUniformly_exp_backgroundAmplitude_smul
    (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ Q.natDegree)
    (hcoeff : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (Q.coeff k))) :
    TendstoUniformly (fun i z ↦ Real.exp (backgroundAmplitude (P i).eval z) • (P i).eval z)
      (fun z ↦ Real.exp (backgroundAmplitude Q.eval z) • Q.eval z) l := by
  obtain ⟨δ, -, hδ, hev⟩ := Polynomial.exists_tendsto_eventually_norm_eval_sub_le hdeg hcoeff
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hev, hδ.eventually (gt_mem_nhds (by positivity : 0 < ε / 4))] with i hi hδi z
  rw [dist_comm, dist_eq_norm, exp_backgroundAmplitude_smul, exp_backgroundAmplitude_smul]
  linarith [OpenPartialHomeomorph.norm_univUnitBall_sub_le_of_norm_sub_le (hi z).1]

/-- **Uniform convergence of the derivatives of the background amplitudes.** If the coefficients of
the polynomials `P i` converge to those of `Q`, and eventually `deg P i ≤ deg Q`, then the
derivatives `Du₀ = -⟪P, D P⟫ / (1 + ‖P‖²)` of the background amplitudes converge uniformly on the
whole plane, in operator norm. -/
theorem tendstoUniformly_fderiv_backgroundAmplitude
    (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ Q.natDegree)
    (hcoeff : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (Q.coeff k))) :
    TendstoUniformly (fun i ↦ fderiv ℝ (backgroundAmplitude (P i).eval))
      (fderiv ℝ (backgroundAmplitude Q.eval)) l := by
  obtain ⟨δ, hδ0, hδ, hev⟩ := Polynomial.exists_tendsto_eventually_norm_eval_sub_le hdeg hcoeff
  -- `‖Q'‖ ≤ C (1 + ‖Q‖)`, since `deg Q' ≤ deg Q`.
  obtain ⟨C, hC, hQ'⟩ :=
    Polynomial.exists_norm_eval_le_mul_one_add_norm_eval (Polynomial.degree_derivative_le (p := Q))
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hK : 0 < 24 * C + 12 := by positivity
  filter_upwards [hev, hδ.eventually
    (gt_mem_nhds (by positivity : 0 < min (1 / 2) (ε / (2 * (24 * C + 12)))))] with i hi hδi z
  have hδ1 : δ i ≤ 1 / 2 := hδi.le.trans (min_le_left _ _)
  have hδε : δ i * (24 * C + 12) < ε := by
    have := hδi.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at this
    nlinarith
  rw [dist_comm, dist_eq_norm]
  refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_of_unit_norm (mul_nonneg hK.le (hδ0 i))
    fun v hv ↦ ?_)
    (by nlinarith : (24 * C + 12) * δ i < ε)
  rw [sub_apply, fderiv_backgroundAmplitude_apply ((P i).differentiable z),
    fderiv_backgroundAmplitude_apply (Q.differentiable z), Polynomial.deriv, Polynomial.deriv,
    Real.norm_eq_abs, neg_sub_neg, abs_sub_comm]
  -- Multiplying by a unit vector `v` preserves the hypotheses on the derivatives.
  refine TauCeti.abs_inv_one_add_norm_sq_mul_inner_sub_le hδ1 (hi z).1 ?_ ?_
  · rw [← mul_sub, norm_mul, hv, one_mul]
    exact (hi z).2
  · rw [norm_mul, hv, one_mul]
    exact hQ' z

/-- **Continuity of the background sections in the uniform topology.** For a family of
polynomials of a fixed degree whose coefficients depend continuously on a parameter, the background
sections `exp(u₀) P` depend continuously on the parameter in the topology of uniform convergence on
the plane. -/
theorem continuous_ofFun_exp_backgroundAmplitude_smul {X : Type*} [TopologicalSpace X]
    {P : X → Polynomial ℂ} {m : ℕ} (hdeg : ∀ x, (P x).natDegree = m)
    (hcoeff : ∀ k, Continuous fun x ↦ (P x).coeff k) :
    Continuous fun x ↦
      UniformFun.ofFun fun z ↦ Real.exp (backgroundAmplitude (P x).eval z) • (P x).eval z :=
  continuous_iff_continuousAt.2 fun x ↦ UniformFun.tendsto_iff_tendstoUniformly.2 <|
    tendstoUniformly_exp_backgroundAmplitude_smul
      (Eventually.of_forall fun y ↦ ((hdeg y).trans (hdeg x).symm).le)
      fun k ↦ (hcoeff k).continuousAt

/-- **Continuity of the derivatives of the background amplitudes in the uniform topology.** Under
the hypotheses of `TauCeti.Vortex.continuous_ofFun_exp_backgroundAmplitude_smul`, the derivatives
of the background amplitudes depend continuously on the parameter in the topology of uniform
convergence on the plane. -/
theorem continuous_ofFun_fderiv_backgroundAmplitude {X : Type*} [TopologicalSpace X]
    {P : X → Polynomial ℂ} {m : ℕ} (hdeg : ∀ x, (P x).natDegree = m)
    (hcoeff : ∀ k, Continuous fun x ↦ (P x).coeff k) :
    Continuous fun x ↦ UniformFun.ofFun (fderiv ℝ (backgroundAmplitude (P x).eval)) :=
  continuous_iff_continuousAt.2 fun x ↦ UniformFun.tendsto_iff_tendstoUniformly.2 <|
    tendstoUniformly_fderiv_backgroundAmplitude
      (Eventually.of_forall fun y ↦ ((hdeg y).trans (hdeg x).symm).le)
      fun k ↦ (hcoeff k).continuousAt

/-- The derivatives `D (u₀ + w i)` of the amplitudes converge uniformly when the corrections are
differentiable and their derivatives converge uniformly. -/
private theorem tendstoUniformly_fderiv_backgroundAmplitude_add {w : ι → ℂ → ℝ} {w₀ : ℂ → ℝ}
    (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ Q.natDegree)
    (hcoeff : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (Q.coeff k)))
    (hw : ∀ i, Differentiable ℝ (w i)) (hw₀ : Differentiable ℝ w₀)
    (hconv' : TendstoUniformly (fun i ↦ fderiv ℝ (w i)) (fderiv ℝ w₀) l) :
    TendstoUniformly
      (fun i z ↦ fderiv ℝ (fun z ↦ backgroundAmplitude (P i).eval z + w i z) z)
      (fun z ↦ fderiv ℝ (fun z ↦ backgroundAmplitude Q.eval z + w₀ z) z) l := by
  have hu₀ (R : Polynomial ℂ) : Differentiable ℝ (backgroundAmplitude R.eval) :=
    (contDiff_backgroundAmplitude ((R.differentiable.contDiff (n := 1)).restrict_scalars ℝ)
      ).differentiable one_ne_zero
  have e₁ : ∀ i z, fderiv ℝ (fun z ↦ backgroundAmplitude (P i).eval z + w i z) z =
      fderiv ℝ (backgroundAmplitude (P i).eval) z + fderiv ℝ (w i) z :=
    fun i z ↦ fderiv_add (hu₀ (P i) z) (hw i z)
  have e₂ : ∀ z, fderiv ℝ (fun z ↦ backgroundAmplitude Q.eval z + w₀ z) z =
      fderiv ℝ (backgroundAmplitude Q.eval) z + fderiv ℝ w₀ z :=
    fun z ↦ fderiv_add (hu₀ Q z) (hw₀ z)
  simp_rw [e₁, e₂]
  exact (tendstoUniformly_fderiv_backgroundAmplitude hdeg hcoeff).add hconv'

/-- The sections `exp (w i) • exp(u₀) P i` converge uniformly when `w i → w₀` uniformly and `w₀` is
bounded above: a uniformly convergent bounded real factor times a uniformly convergent factor
bounded by `1`. -/
private theorem tendstoUniformly_exp_smul_exp_backgroundAmplitude_smul {w : ι → ℂ → ℝ}
    {w₀ : ℂ → ℝ} (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ Q.natDegree)
    (hcoeff : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (Q.coeff k))) {M : ℝ}
    (hM : ∀ z, w₀ z ≤ M) (hconv : TendstoUniformly w w₀ l) :
    TendstoUniformly
      (fun i z ↦ Real.exp (w i z) • (Real.exp (backgroundAmplitude (P i).eval z) • (P i).eval z))
      (fun z ↦ Real.exp (w₀ z) • (Real.exp (backgroundAmplitude Q.eval z) • Q.eval z)) l := by
  have hE := hconv.rexp ⟨M, Set.forall_mem_range.2 hM⟩
  have hG := tendstoUniformly_exp_backgroundAmplitude_smul hdeg hcoeff
  rw [Metric.tendstoUniformly_iff] at hE hG ⊢
  intro ε hε
  filter_upwards [hE (ε / 2) (by positivity),
    hG (ε / (2 * Real.exp M)) (by positivity)] with i hiE hiG z
  have hE' := hiE z
  have hG' := hiG z
  simp only [exp_backgroundAmplitude_smul] at hG' ⊢
  rw [dist_eq_norm] at hE' hG' ⊢
  set F := OpenPartialHomeomorph.univUnitBall (E := ℂ)
  have hsplit : Real.exp (w₀ z) • F (Q.eval z) - Real.exp (w i z) • F ((P i).eval z) =
      (Real.exp (w₀ z) - Real.exp (w i z)) • F ((P i).eval z) +
        Real.exp (w₀ z) • (F (Q.eval z) - F ((P i).eval z)) := by
    module
  rw [hsplit]
  refine (norm_add_le _ _).trans_lt ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp]
  have h₁ := mul_le_mul_of_nonneg_left (OpenPartialHomeomorph.norm_univUnitBall_le ((P i).eval z))
    (abs_nonneg (Real.exp (w₀ z) - Real.exp (w i z)))
  have h₂ := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.exp M)).1 hG'
  have h₃ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (hM z))
    (norm_nonneg (F (Q.eval z) - F ((P i).eval z)))
  rw [Real.norm_eq_abs] at hE'
  nlinarith [Real.exp_pos M]

/-- The second section coordinate of the field reconstructed from `u + w` is
`(exp w • exp u • f).re / 2`. -/
private theorem amplitudeField_add_apply_two (u w : ℂ → ℝ) (f : ℂ → ℂ) (z : ℂ) :
    amplitudeField (fun z ↦ u z + w z) f z 2 =
      2⁻¹ * (Real.exp (w z) • Real.exp (u z) • f z).re := by
  rw [amplitudeField_apply_two, Real.exp_add, smul_re, smul_re, smul_eq_mul, smul_eq_mul]
  ring

/-- The third section coordinate of the field reconstructed from `u + w` is
`(exp w • exp u • f).im / 2`. -/
private theorem amplitudeField_add_apply_three (u w : ℂ → ℝ) (f : ℂ → ℂ) (z : ℂ) :
    amplitudeField (fun z ↦ u z + w z) f z 3 =
      2⁻¹ * (Real.exp (w z) • Real.exp (u z) • f z).im := by
  rw [amplitudeField_apply_three, Real.exp_add, smul_im, smul_im, smul_eq_mul, smul_eq_mul]
  ring

/-- **Uniform convergence of the reconstructed fields.** Let the coefficients of the polynomials
`P i` converge to those of `Q`, with eventually `deg P i ≤ deg Q`, and let `w i`, `w₀` be
differentiable corrections such that `w i → w₀` and `D (w i) → D w₀` uniformly on the plane, with
`w₀` bounded above. Then the fields `amplitudeField (u₀ + w i) (P i)` reconstructed from the
amplitudes `u₀ + w i`, `u₀` the background amplitude of `P i`, converge uniformly on the plane to
`amplitudeField (u₀ + w₀) Q`. -/
theorem tendstoUniformly_amplitudeField_backgroundAmplitude_add {w : ι → ℂ → ℝ} {w₀ : ℂ → ℝ}
    (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ Q.natDegree)
    (hcoeff : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (Q.coeff k)))
    (hw : ∀ i, Differentiable ℝ (w i)) (hw₀ : Differentiable ℝ w₀) {M : ℝ} (hM : ∀ z, w₀ z ≤ M)
    (hconv : TendstoUniformly w w₀ l)
    (hconv' : TendstoUniformly (fun i ↦ fderiv ℝ (w i)) (fderiv ℝ w₀) l) :
    TendstoUniformly
      (fun i ↦ amplitudeField (fun z ↦ backgroundAmplitude (P i).eval z + w i z) (P i).eval)
      (amplitudeField (fun z ↦ backgroundAmplitude Q.eval z + w₀ z) Q.eval) l := by
  have hD := tendstoUniformly_fderiv_backgroundAmplitude_add hdeg hcoeff hw hw₀ hconv'
  have hS := tendstoUniformly_exp_smul_exp_backgroundAmplitude_smul hdeg hcoeff hM hconv
  -- The connection coordinates are `-D(u₀ + w) i` and `D(u₀ + w) 1`, and the section
  -- coordinates are the halved real and imaginary parts of `exp w • exp(u₀) P`.
  rw [PiLp.tendstoUniformly_iff]
  intro k
  fin_cases k
  · convert (-ContinuousLinearMap.apply ℝ ℝ I).uniformContinuous.comp_tendstoUniformly hD using 1
    · funext i z
      simp
    · funext z
      simp
  · convert (ContinuousLinearMap.apply ℝ ℝ (1 : ℂ)).uniformContinuous.comp_tendstoUniformly hD
      using 1
    · funext i z
      simp
    · funext z
      simp
  · convert ((2⁻¹ : ℝ) • Complex.reCLM).uniformContinuous.comp_tendstoUniformly hS using 1
    · funext i z
      simp only [Function.comp_apply, smul_apply, Complex.reCLM_apply, Fin.reduceFinMk,
        smul_eq_mul, amplitudeField_add_apply_two]
    · funext z
      simp only [Function.comp_apply, smul_apply, Complex.reCLM_apply, Fin.reduceFinMk,
        smul_eq_mul, amplitudeField_add_apply_two]
  · convert ((2⁻¹ : ℝ) • Complex.imCLM).uniformContinuous.comp_tendstoUniformly hS using 1
    · funext i z
      simp only [Function.comp_apply, smul_apply, Complex.imCLM_apply, Fin.reduceFinMk,
        smul_eq_mul, amplitudeField_add_apply_three]
    · funext z
      simp only [Function.comp_apply, smul_apply, Complex.imCLM_apply, Fin.reduceFinMk,
        smul_eq_mul, amplitudeField_add_apply_three]

end TauCeti.Vortex

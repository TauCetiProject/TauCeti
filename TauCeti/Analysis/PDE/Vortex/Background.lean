/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EndFraming
public import TauCeti.Analysis.Complex.LogOneAddNormSq
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# The background amplitude of the prescribed-zero vortex problem

A plane vortex with zero divisor given by a monic polynomial `P` of degree `m` is reconstructed as
`amplitudeField u P.eval`, with section `α = exp(u) P`, from a solution `u` of the regularized
scalar equation

`Δu = (exp(2u) |P|² - 1) / 8`,    `u + m log |z| → 0` at infinity

(`TauCeti.Vortex.equation_amplitudeField_eq_zero_iff`,
`TauCeti.Vortex.tendsto_sectionValue_amplitudeField_mul_inv_phase_iff_log`). The solution grows
logarithmically, so it lies in no Sobolev space. Following Taubes, this file subtracts an explicit
smooth background with the same growth. Here the background is

`u₀ = -log (1 + |P|²) / 2`    (`TauCeti.Vortex.backgroundAmplitude`),

which needs no choice of roots and no cutoff. For `m ≥ 1`,
`u₀ + m log |z| → 0`, and for every function `w`:

* `u = u₀ + w` solves the scalar equation exactly when

  `Δw = (exp(2w) h - 1) / 8 + g`,    `h = |P|² / (1 + |P|²)`,    `g = 2 |P'|² / (1 + |P|²)²`;

  here `g = -Δu₀` and `h = exp(2u₀) |P|²` is the squared modulus of the background section;
* the reconstructed section has the degree-`m` end framing exactly when `w → 0` at infinity.

So a vortex with zero divisor `P` is the same as a solution of the reduced equation that tends to
zero at infinity, and the reduced equation has smooth coefficients with `0 ≤ h < 1`. The defect
`1 - h = (1 + |P|²)⁻¹` is square integrable and the source `g` is integrable; these are the
integrability properties of the coefficients that a variational treatment of the reduced
equation on `H¹(ℂ)` uses. Existence of a solution of the reduced equation is not proved here.

## Main results

* `TauCeti.Vortex.laplacian_backgroundAmplitude`: `Δu₀ = -2 |f'|² / (1 + |f|²)²` for holomorphic
  `f`.
* `TauCeti.Vortex.equation_amplitudeField_backgroundAmplitude_add_eq_zero_iff`: the field
  reconstructed from `u₀ + w` solves the vortex equation at `z` exactly when `w` solves the
  reduced equation at `z`.
* `TauCeti.Vortex.tendsto_backgroundAmplitude_add_natDegree_mul_log`: `u₀ + m log |z| → 0`.
* `TauCeti.Vortex.tendsto_sectionValue_amplitudeField_backgroundAmplitude_add_iff`: the end
  framing of the reconstructed section is equivalent to `w → 0`.
* `TauCeti.Vortex.integrable_laplacian_backgroundAmplitude`,
  `TauCeti.Vortex.memLp_inv_one_add_norm_eval_sq`: integrability of the coefficients of the
  reduced equation.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Topology InnerProductSpace Laplacian MeasureTheory Asymptotics

variable {f : ℂ → ℂ} {z : ℂ}

/-- The background amplitude `u₀ = -log (1 + ‖f‖²) / 2`. For a polynomial `f` of degree `m ≥ 1`
it is smooth on the whole plane and has the growth `-m log ‖z‖` of a degree-`m` vortex
amplitude at infinity. -/
def backgroundAmplitude (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  -Real.log (1 + ‖f z‖ ^ 2) / 2

/-- The defining formula of the background amplitude. -/
theorem backgroundAmplitude_apply (f : ℂ → ℂ) (z : ℂ) :
    backgroundAmplitude f z = -Real.log (1 + ‖f z‖ ^ 2) / 2 := (rfl)

/-- `exp (2 u₀) = (1 + ‖f‖²)⁻¹`. -/
@[simp]
theorem exp_two_mul_backgroundAmplitude (f : ℂ → ℂ) (z : ℂ) :
    Real.exp (2 * backgroundAmplitude f z) = (1 + ‖f z‖ ^ 2)⁻¹ := by
  rw [backgroundAmplitude_apply, show 2 * (-Real.log (1 + ‖f z‖ ^ 2) / 2) =
    -Real.log (1 + ‖f z‖ ^ 2) by ring, Real.exp_neg, Real.exp_log (by positivity)]

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
  rw [show (fun z ↦ backgroundAmplitude f z + w z) = backgroundAmplitude f + w from rfl,
    hbg.laplacian_add hw, laplacian_backgroundAmplitude hf, hexp]
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
  have hq : Tendsto (fun z ↦ P.eval z / z ^ m) (cocompact ℂ) (𝓝 1) := by
    have he := Polynomial.isEquivalent_cobounded_leading_monomial (P := P)
    simp only [hP.leadingCoeff, one_mul, Metric.cobounded_eq_cocompact] at he
    exact (isEquivalent_iff_tendsto_one (hz.mono fun z hz ↦ pow_ne_zero _ hz)).mp he
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

-- Polynomial growth bounds at infinity, in the form used below: `‖z‖ ^ m ≤ c ‖P z‖` gives
-- `(‖z‖ ^ m) ^ 4 ≤ c ^ 4 (1 + ‖P z‖²)²`, and `‖P' z‖ ≤ c ‖z‖ ^ (m - 1)` is squared.
private theorem exists_eventually_norm_bounds {P : Polynomial ℂ} (hm : 0 < P.natDegree) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ z : ℂ in cocompact ℂ, 1 ≤ ‖z‖ ∧ (1 + ‖z‖) ^ 4 ≤ 16 * ‖z‖ ^ 4 ∧
      (‖z‖ ^ P.natDegree) ^ 4 ≤ c ^ 4 * (1 + ‖P.eval z‖ ^ 2) ^ 2 ∧
      ‖P.derivative.eval z‖ ^ 2 ≤ c ^ 2 * ‖z‖ ^ (2 * (P.natDegree - 1)) := by
  have hP : P ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hm
  have hlow : (fun z : ℂ ↦ z ^ P.natDegree) =O[cocompact ℂ] P.eval := by
    have he := (Polynomial.isEquivalent_cobounded_leading_monomial (P := P)).symm.isBigO
    rw [Metric.cobounded_eq_cocompact] at he
    exact (isBigO_self_const_mul (Polynomial.leadingCoeff_ne_zero.mpr hP) _ _).trans he
  have hup : P.derivative.eval =O[cocompact ℂ] fun z : ℂ ↦ z ^ (P.natDegree - 1) := by
    have h := (Polynomial.isBigO_cobounded_pow_natDegree P.derivative).trans
      (isBigO_pow_pow_cobounded_of_le (Polynomial.natDegree_derivative_le P))
    rwa [Metric.cobounded_eq_cocompact] at h
  obtain ⟨c₁, hc₁⟩ := hlow.bound
  obtain ⟨c₂, hc₂⟩ := hup.bound
  set c := max (max c₁ c₂) 1
  refine ⟨c, by positivity, ?_⟩
  filter_upwards [hc₁, hc₂, tendsto_norm_cocompact_atTop.eventually_ge_atTop 1]
    with z h₁ h₂ h₃
  rw [norm_pow] at h₁ h₂
  have h₁' : ‖z‖ ^ P.natDegree ≤ c * ‖P.eval z‖ :=
    h₁.trans (by gcongr; exact (le_max_left _ _).trans (le_max_left _ _))
  have h₂' : ‖P.derivative.eval z‖ ≤ c * ‖z‖ ^ (P.natDegree - 1) :=
    h₂.trans (by gcongr; exact (le_max_right _ _).trans (le_max_left _ _))
  refine ⟨h₃, ?_, ?_, ?_⟩
  · calc (1 + ‖z‖) ^ 4 ≤ (2 * ‖z‖) ^ 4 := by gcongr; linarith
      _ = 16 * ‖z‖ ^ 4 := by ring
  · calc (‖z‖ ^ P.natDegree) ^ 4 ≤ (c * ‖P.eval z‖) ^ 4 := by gcongr
      _ = c ^ 4 * (‖P.eval z‖ ^ 2) ^ 2 := by ring
      _ ≤ c ^ 4 * (1 + ‖P.eval z‖ ^ 2) ^ 2 := by gcongr; linarith
  · calc ‖P.derivative.eval z‖ ^ 2 ≤ (c * ‖z‖ ^ (P.natDegree - 1)) ^ 2 := by gcongr
      _ = c ^ 2 * ‖z‖ ^ (2 * (P.natDegree - 1)) := by ring

-- A continuous function on the plane bounded at infinity by a multiple of `(1 + ‖z‖)⁻⁴` is
-- integrable.
private theorem integrable_of_eventually_le_div_one_add_norm_pow_four {F : ℂ → ℝ}
    (hF : Continuous F) {K : ℝ} (h : ∀ᶠ z in cocompact ℂ, ‖F z‖ ≤ K / (1 + ‖z‖) ^ 4) :
    Integrable F := by
  refine hF.locallyIntegrable.integrable_of_isBigO_cocompact
    (g := fun z : ℂ ↦ (1 + ‖z‖) ^ (-(4 : ℝ))) (IsBigO.of_bound K (h.mono fun z hz ↦ ?_))
    ((integrable_one_add_norm (r := 4) (by simp [Complex.finrank_real_complex]; norm_num)
      ).integrableAtFilter _)
  have hpos : 0 < 1 + ‖z‖ := by positivity
  rwa [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + ‖z‖) ^ (-(4 : ℝ))),
    Real.rpow_neg hpos.le, Real.rpow_ofNat, ← div_eq_mul_inv]

/-- For a polynomial `P` of degree `m ≥ 1`, the Laplacian of the background amplitude, the
source term `-g` of the reduced equation, is integrable on the plane. -/
theorem integrable_laplacian_backgroundAmplitude {P : Polynomial ℂ} (hm : 0 < P.natDegree) :
    Integrable (Δ (backgroundAmplitude P.eval)) := by
  have hΔ : Δ (backgroundAmplitude P.eval) = fun z ↦
      -(2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) := by
    funext z
    rw [laplacian_backgroundAmplitude (P.differentiable.analyticAt z), Polynomial.deriv]
  obtain ⟨c, hc, hb⟩ := exists_eventually_norm_bounds hm
  have hcont : Continuous (Δ (backgroundAmplitude P.eval)) :=
    (contDiff_backgroundAmplitude
      ((P.differentiable.contDiff (n := 2)).restrict_scalars ℝ)).continuous_laplacian
  refine integrable_of_eventually_le_div_one_add_norm_pow_four hcont (K := 32 * c ^ 6) ?_
  filter_upwards [hb] with z ⟨h₁, hr, ha, hd⟩
  obtain ⟨k, hk⟩ : ∃ k, P.natDegree = k + 1 := ⟨P.natDegree - 1, by omega⟩
  rw [hk] at ha hd
  rw [Nat.add_sub_cancel] at hd
  rw [hΔ, norm_neg, Real.norm_of_nonneg (by positivity), div_le_div_iff₀ (by positivity)
    (by positivity)]
  -- `‖P'‖² (1 + ‖z‖)⁴ ≲ ‖z‖ ^ (2m + 2) ≤ ‖z‖ ^ (4m) ≲ (1 + ‖P‖²)²`, using `m ≥ 1`.
  have hpow : ‖z‖ ^ (2 * k) * ‖z‖ ^ 4 ≤ (‖z‖ ^ (k + 1)) ^ 4 := by
    rw [← pow_add, ← pow_mul]
    exact pow_le_pow_right₀ h₁ (by omega)
  calc 2 * ‖P.derivative.eval z‖ ^ 2 * (1 + ‖z‖) ^ 4 ≤
        2 * (c ^ 2 * ‖z‖ ^ (2 * k)) * (16 * ‖z‖ ^ 4) := by gcongr
    _ = 32 * c ^ 2 * (‖z‖ ^ (2 * k) * ‖z‖ ^ 4) := by ring
    _ ≤ 32 * c ^ 2 * (c ^ 4 * (1 + ‖P.eval z‖ ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left (hpow.trans ha) (by positivity)
    _ = 32 * c ^ 6 * (1 + ‖P.eval z‖ ^ 2) ^ 2 := by ring

/-- For a polynomial `P` of degree `m ≥ 1`, the defect `1 - h = (1 + ‖P‖²)⁻¹` of the reduced
equation is square integrable on the plane. -/
theorem memLp_inv_one_add_norm_eval_sq {P : Polynomial ℂ} (hm : 0 < P.natDegree) :
    MemLp (fun z ↦ (1 + ‖P.eval z‖ ^ 2)⁻¹) 2 := by
  have hcont : Continuous fun z ↦ (1 + ‖P.eval z‖ ^ 2)⁻¹ :=
    (continuous_const.add (P.continuous.norm.pow 2)).inv₀ fun z ↦
      (by positivity : (0 : ℝ) < 1 + ‖P.eval z‖ ^ 2).ne'
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  obtain ⟨c, hc, hb⟩ := exists_eventually_norm_bounds hm
  refine integrable_of_eventually_le_div_one_add_norm_pow_four (hcont.pow 2)
    (K := 16 * c ^ 4) ?_
  filter_upwards [hb] with z ⟨h₁, hr, ha, _⟩
  rw [Real.norm_of_nonneg (by positivity), inv_pow, ← one_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have hpow : ‖z‖ ^ 4 ≤ (‖z‖ ^ P.natDegree) ^ 4 := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ h₁ (by omega)
  linarith [hpow.trans ha]

end TauCeti.Vortex

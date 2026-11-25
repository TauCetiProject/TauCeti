/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.SpecialFunctions.Airy.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Modulus and phase of the Airy functions

On the real line the Airy functions are written in modulus–phase form (DLMF §9.8),
`Ai(x) = M(x) sin θ(x)`, `Bi(x) = M(x) cos θ(x)`, `Ai′(x) = N(x) sin φ(x)`,
`Bi′(x) = N(x) cos φ(x)`. This file defines the moduli `M = (Ai² + Bi²)^{1/2}` (DLMF 9.8.3) and
`N = (Ai′² + Bi′²)^{1/2}` (DLMF 9.8.7), and the phases as the integrals of their derivatives
(DLMF 9.8.14), normalized by `θ(0) = π/6` and `φ(0) = −π/6`:

`θ(x) = π/6 − π⁻¹ ∫₀ˣ M(t)⁻² dt`,  `φ(x) = −π/6 + π⁻¹ ∫₀ˣ t N(t)⁻² dt`.

So `θ` and `φ` are continuous on all of `ℝ`, unlike the arctangents of `Ai/Bi` and `Ai′/Bi′`,
which jump at the zeros of `Bi` and `Bi′`. The Wronskian `Ai Bi′ − Ai′ Bi = 1/π` (DLMF 9.2.7)
gives Lagrange's identity `M² N² = (Ai Ai′ + Bi Bi′)² + π⁻²`, so `M > 0` and `N > 0`.

## Main definitions

* `Real.airyModulus`, `Real.airyDerivModulus`: the moduli `M` and `N` (DLMF 9.8.3, 9.8.7).
* `Real.airyPhase`, `Real.airyDerivPhase`: the phases `θ` and `φ` (DLMF 9.8.14).

## Main results

* `Real.airyModulus_sq_mul_airyDerivModulus_sq`: `M² N² = (Ai Ai′ + Bi Bi′)² + π⁻²`.
* `Real.airyModulus_pos`, `Real.airyDerivModulus_pos`: `M > 0` and `N > 0`.
* `Real.airyModulus_zero`, `Real.airyDerivModulus_zero`: `M(0) = 2 Ai(0)`, `N(0) = −2 Ai′(0)`.
* `Real.hasDerivAt_airyModulus`, `Real.hasDerivAt_airyDerivModulus`: `M′ = (Ai Ai′ + Bi Bi′)/M`
  and `N′ = x (Ai Ai′ + Bi Bi′)/N`.
* `TauCeti.airy_modulus_phase_deriv`: `θ′ = −1/(π M²)` and `φ′ = x/(π N²)` (DLMF 9.8.14), with
  `Real.airyModulus_sq_mul_deriv_airyPhase` (`M² θ′ = −1/π`),
  `Real.airyDerivModulus_sq_mul_deriv_airyDerivPhase` (`N² φ′ = x/π`) and
  `Real.airyDerivModulus_mul_deriv_airyDerivModulus` (`N N′ = x M M′`).
* `Real.strictAnti_airyPhase`: `θ` is strictly decreasing on `ℝ`;
  `Real.strictAntiOn_airyDerivPhase`, `Real.strictMonoOn_airyDerivPhase`: `φ` is strictly
  decreasing on `(−∞, 0]` and strictly increasing on `[0, ∞)`.

## References

* NIST Digital Library of Mathematical Functions, §9.8, <https://dlmf.nist.gov/9.8>.

The definitions and the derivative formulas are adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file `DLMF/Airy/Basic/ModulusPhase.lean`
(`airyModulus`, `airyDerivModulus`, `airyPhase`, `airyDerivPhase`, `airyModulus_pos`,
`hasDerivAt_airyModulus`, `hasDerivAt_airyDerivModulus`, `hasDerivAt_airyPhase`,
`hasDerivAt_airyDerivPhase`, `airy_lagrange`), and file
`DLMF/Airy/ModulusPhase/Representations.lean` (`airy_modulus_phase_derivatives`). Positivity of
`M` and `N` is derived here from Lagrange's identity; the values at `0` and the monotonicity of
the phases are new.
-/

public section

noncomputable section

open Set
open scoped Real

namespace TauCeti

/-! ### The moduli -/

/-- The modulus `M = (Ai² + Bi²)^{1/2}` of the Airy functions on the real line (DLMF 9.8.3). -/
def _root_.Real.airyModulus (x : ℝ) : ℝ := √(Real.airyAi x ^ 2 + Real.airyBi x ^ 2)

/-- The defining expression of `Real.airyModulus`. -/
theorem _root_.Real.airyModulus_def (x : ℝ) :
    Real.airyModulus x = √(Real.airyAi x ^ 2 + Real.airyBi x ^ 2) := (rfl)

/-- The modulus `N = (Ai′² + Bi′²)^{1/2}` of the Airy derivatives on the real line
(DLMF 9.8.7). -/
def _root_.Real.airyDerivModulus (x : ℝ) : ℝ :=
  √(deriv Real.airyAi x ^ 2 + deriv Real.airyBi x ^ 2)

/-- The defining expression of `Real.airyDerivModulus`. -/
theorem _root_.Real.airyDerivModulus_def (x : ℝ) :
    Real.airyDerivModulus x = √(deriv Real.airyAi x ^ 2 + deriv Real.airyBi x ^ 2) := (rfl)

/-- `M² = Ai² + Bi²`. -/
theorem _root_.Real.airyModulus_sq (x : ℝ) :
    Real.airyModulus x ^ 2 = Real.airyAi x ^ 2 + Real.airyBi x ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- `N² = Ai′² + Bi′²`. -/
theorem _root_.Real.airyDerivModulus_sq (x : ℝ) :
    Real.airyDerivModulus x ^ 2 = deriv Real.airyAi x ^ 2 + deriv Real.airyBi x ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- **Lagrange's identity** for the Airy moduli: `M² N² = (Ai Ai′ + Bi Bi′)² + π⁻²`, the
Wronskian `Ai Bi′ − Ai′ Bi = 1/π` supplying the second square. -/
theorem _root_.Real.airyModulus_sq_mul_airyDerivModulus_sq (x : ℝ) :
    Real.airyModulus x ^ 2 * Real.airyDerivModulus x ^ 2 =
      (Real.airyAi x * deriv Real.airyAi x + Real.airyBi x * deriv Real.airyBi x) ^ 2 +
        π⁻¹ ^ 2 := by
  have hW := Real.wronskian_airyAi_airyBi x
  rw [Real.airyModulus_sq, Real.airyDerivModulus_sq]
  linear_combination (Real.airyAi x * deriv Real.airyBi x - deriv Real.airyAi x * Real.airyBi x +
    π⁻¹) * hW

/-- `M(x) > 0`: `Ai` and `Bi` have no common real zero. -/
theorem _root_.Real.airyModulus_pos (x : ℝ) : 0 < Real.airyModulus x := by
  refine (Real.sqrt_nonneg _).lt_of_ne' fun h => ?_
  have hL := Real.airyModulus_sq_mul_airyDerivModulus_sq x
  rw [← Real.airyModulus_def] at h
  rw [h] at hL
  have : 0 < π⁻¹ ^ 2 := by positivity
  nlinarith

/-- `N(x) > 0`: `Ai′` and `Bi′` have no common real zero. -/
theorem _root_.Real.airyDerivModulus_pos (x : ℝ) : 0 < Real.airyDerivModulus x := by
  refine (Real.sqrt_nonneg _).lt_of_ne' fun h => ?_
  have hL := Real.airyModulus_sq_mul_airyDerivModulus_sq x
  rw [← Real.airyDerivModulus_def] at h
  rw [h] at hL
  have : 0 < π⁻¹ ^ 2 := by positivity
  nlinarith

/-- `M(0) = 2 Ai(0)`. -/
theorem _root_.Real.airyModulus_zero : Real.airyModulus 0 = 2 * Real.airyAi 0 := by
  -- `Bi(0)² = 3 Ai(0)²`, cast down from `TauCeti.airyBi_zero_sq`.
  have h : Real.airyBi 0 ^ 2 = 3 * Real.airyAi 0 ^ 2 := by
    have h := airyBi_zero_sq
    rw [← Complex.ofReal_zero, ← Real.ofReal_real_airyAi, ← Real.ofReal_real_airyBi] at h
    exact_mod_cast h
  rw [Real.airyModulus_def, h, ← Real.sqrt_sq (by linarith [Real.airyAi_zero_pos] :
    0 ≤ 2 * Real.airyAi 0)]
  congr 1
  ring

/-- `N(0) = −2 Ai′(0)`. -/
theorem _root_.Real.airyDerivModulus_zero :
    Real.airyDerivModulus 0 = -(2 * deriv Real.airyAi 0) := by
  -- `Bi′(0) = −√3 Ai′(0)`, cast down from
  -- `TauCeti.deriv_airyBi_zero_eq_neg_cpow_mul_deriv_airyAi_zero`.
  have h : deriv Real.airyBi 0 = -√3 * deriv Real.airyAi 0 := by
    have h := deriv_airyBi_zero_eq_neg_cpow_mul_deriv_airyAi_zero
    have h3 : (3 : ℂ) ^ (1 / 2 : ℂ) = ((√3 : ℝ) : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by norm_num)]
      norm_num
    rw [h3, ← Complex.ofReal_zero, ← Real.ofReal_deriv_real_airyAi,
      ← Real.ofReal_deriv_real_airyBi] at h
    exact_mod_cast h
  rw [Real.airyDerivModulus_def, h, ← Real.sqrt_sq (by linarith [Real.deriv_airyAi_zero_neg] :
    0 ≤ -(2 * deriv Real.airyAi 0))]
  congr 1
  rw [mul_pow, neg_sq, Real.sq_sqrt (by norm_num)]
  ring

/-- The derivative of `M` is `(Ai Ai′ + Bi Bi′)/M`. -/
theorem _root_.Real.hasDerivAt_airyModulus (x : ℝ) :
    HasDerivAt Real.airyModulus
      ((Real.airyAi x * deriv Real.airyAi x + Real.airyBi x * deriv Real.airyBi x) /
        Real.airyModulus x) x := by
  have h := (((Real.differentiable_airyAi x).hasDerivAt.pow 2).add
    ((Real.differentiable_airyBi x).hasDerivAt.pow 2)).sqrt
    (by
      simp only [Pi.add_apply, Pi.pow_apply]
      rw [← Real.airyModulus_sq]
      exact (pow_pos (Real.airyModulus_pos x) 2).ne')
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, Pi.pow_apply]
  rw [← Real.airyModulus_def]
  field_simp [(Real.airyModulus_pos x).ne']
  ring

/-- The derivative of `N` is `x (Ai Ai′ + Bi Bi′)/N`. -/
theorem _root_.Real.hasDerivAt_airyDerivModulus (x : ℝ) :
    HasDerivAt Real.airyDerivModulus
      (x * (Real.airyAi x * deriv Real.airyAi x + Real.airyBi x * deriv Real.airyBi x) /
        Real.airyDerivModulus x) x := by
  have h := (((Real.hasDerivAt_deriv_airyAi x).pow 2).add
    ((Real.hasDerivAt_deriv_airyBi x).pow 2)).sqrt
    (by
      simp only [Pi.add_apply, Pi.pow_apply]
      rw [← Real.airyDerivModulus_sq]
      exact (pow_pos (Real.airyDerivModulus_pos x) 2).ne')
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, Pi.pow_apply]
  rw [← Real.airyDerivModulus_def]
  field_simp [(Real.airyDerivModulus_pos x).ne']
  ring

/-- `M` is differentiable. -/
theorem _root_.Real.differentiable_airyModulus : Differentiable ℝ Real.airyModulus := fun x =>
  (Real.hasDerivAt_airyModulus x).differentiableAt

/-- `N` is differentiable. -/
theorem _root_.Real.differentiable_airyDerivModulus :
    Differentiable ℝ Real.airyDerivModulus := fun x =>
  (Real.hasDerivAt_airyDerivModulus x).differentiableAt

/-- `N N′ = x M M′` (DLMF 9.8.14). -/
theorem _root_.Real.airyDerivModulus_mul_deriv_airyDerivModulus (x : ℝ) :
    Real.airyDerivModulus x * deriv Real.airyDerivModulus x =
      x * (Real.airyModulus x * deriv Real.airyModulus x) := by
  rw [(Real.hasDerivAt_airyModulus x).deriv, (Real.hasDerivAt_airyDerivModulus x).deriv]
  field_simp [(Real.airyModulus_pos x).ne', (Real.airyDerivModulus_pos x).ne']

/-! ### The phases -/

/-- The phase `θ` of the Airy functions on the real line, the continuous function with
`θ(0) = π/6` and `M² θ′ = −1/π` (DLMF 9.8.14). -/
def _root_.Real.airyPhase (x : ℝ) : ℝ :=
  π / 6 - π⁻¹ * ∫ t in (0 : ℝ)..x, (Real.airyModulus t ^ 2)⁻¹

/-- The defining expression of `Real.airyPhase`. -/
theorem _root_.Real.airyPhase_def (x : ℝ) :
    Real.airyPhase x = π / 6 - π⁻¹ * ∫ t in (0 : ℝ)..x, (Real.airyModulus t ^ 2)⁻¹ := (rfl)

/-- The phase `φ` of the Airy derivatives on the real line, the continuous function with
`φ(0) = −π/6` and `N² φ′ = x/π` (DLMF 9.8.14). -/
def _root_.Real.airyDerivPhase (x : ℝ) : ℝ :=
  -(π / 6) + π⁻¹ * ∫ t in (0 : ℝ)..x, t / Real.airyDerivModulus t ^ 2

/-- The defining expression of `Real.airyDerivPhase`. -/
theorem _root_.Real.airyDerivPhase_def (x : ℝ) :
    Real.airyDerivPhase x =
      -(π / 6) + π⁻¹ * ∫ t in (0 : ℝ)..x, t / Real.airyDerivModulus t ^ 2 := (rfl)

/-- `θ(0) = π/6`. -/
@[simp]
theorem _root_.Real.airyPhase_zero : Real.airyPhase 0 = π / 6 := by
  simp [Real.airyPhase_def]

/-- `φ(0) = −π/6`. -/
@[simp]
theorem _root_.Real.airyDerivPhase_zero : Real.airyDerivPhase 0 = -(π / 6) := by
  simp [Real.airyDerivPhase_def]

/-- `θ′ = −1/(π M²)` (DLMF 9.8.14). -/
theorem _root_.Real.hasDerivAt_airyPhase (x : ℝ) :
    HasDerivAt Real.airyPhase (-(π * Real.airyModulus x ^ 2)⁻¹) x := by
  have hc : Continuous fun t => (Real.airyModulus t ^ 2)⁻¹ :=
    (Real.differentiable_airyModulus.continuous.pow 2).inv₀ fun t =>
      (pow_pos (Real.airyModulus_pos t) 2).ne'
  have h := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).const_mul π⁻¹
  refine (h.const_sub (π / 6)).congr_deriv ?_
  rw [mul_inv]

/-- `φ′ = x/(π N²)` (DLMF 9.8.14). -/
theorem _root_.Real.hasDerivAt_airyDerivPhase (x : ℝ) :
    HasDerivAt Real.airyDerivPhase (x / (π * Real.airyDerivModulus x ^ 2)) x := by
  have hc : Continuous fun t => t / Real.airyDerivModulus t ^ 2 :=
    continuous_id.div (Real.differentiable_airyDerivModulus.continuous.pow 2) fun t =>
      (pow_pos (Real.airyDerivModulus_pos t) 2).ne'
  have h := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).const_mul π⁻¹
  refine (h.const_add (-(π / 6))).congr_deriv ?_
  ring

/-- **DLMF 9.8.14**: `θ′ = −1/(π M²)` and `φ′ = x/(π N²)`. -/
theorem airy_modulus_phase_deriv (x : ℝ) :
    HasDerivAt Real.airyPhase (-(π * Real.airyModulus x ^ 2)⁻¹) x ∧
      HasDerivAt Real.airyDerivPhase (x / (π * Real.airyDerivModulus x ^ 2)) x :=
  ⟨Real.hasDerivAt_airyPhase x, Real.hasDerivAt_airyDerivPhase x⟩

/-- `θ` is differentiable. -/
theorem _root_.Real.differentiable_airyPhase : Differentiable ℝ Real.airyPhase := fun x =>
  (Real.hasDerivAt_airyPhase x).differentiableAt

/-- `φ` is differentiable. -/
theorem _root_.Real.differentiable_airyDerivPhase : Differentiable ℝ Real.airyDerivPhase :=
  fun x => (Real.hasDerivAt_airyDerivPhase x).differentiableAt

/-- `M² θ′ = −1/π` (DLMF 9.8.14). -/
theorem _root_.Real.airyModulus_sq_mul_deriv_airyPhase (x : ℝ) :
    Real.airyModulus x ^ 2 * deriv Real.airyPhase x = -π⁻¹ := by
  rw [(Real.hasDerivAt_airyPhase x).deriv]
  field_simp [(Real.airyModulus_pos x).ne']

/-- `N² φ′ = x/π` (DLMF 9.8.14). -/
theorem _root_.Real.airyDerivModulus_sq_mul_deriv_airyDerivPhase (x : ℝ) :
    Real.airyDerivModulus x ^ 2 * deriv Real.airyDerivPhase x = x / π := by
  rw [(Real.hasDerivAt_airyDerivPhase x).deriv]
  field_simp [(Real.airyDerivModulus_pos x).ne']

/-- `θ` is strictly decreasing on `ℝ`. -/
theorem _root_.Real.strictAnti_airyPhase : StrictAnti Real.airyPhase :=
  strictAnti_of_deriv_neg fun x => by
    rw [(Real.hasDerivAt_airyPhase x).deriv, neg_lt_zero, inv_pos]
    exact mul_pos Real.pi_pos (pow_pos (Real.airyModulus_pos x) 2)

/-- `φ` is strictly decreasing on `(−∞, 0]`. -/
theorem _root_.Real.strictAntiOn_airyDerivPhase : StrictAntiOn Real.airyDerivPhase (Iic 0) :=
  strictAntiOn_of_deriv_neg (convex_Iic 0)
    Real.differentiable_airyDerivPhase.continuous.continuousOn fun x hx => by
      rw [interior_Iic, mem_Iio] at hx
      rw [(Real.hasDerivAt_airyDerivPhase x).deriv]
      exact div_neg_of_neg_of_pos hx
        (mul_pos Real.pi_pos (pow_pos (Real.airyDerivModulus_pos x) 2))

/-- `φ` is strictly increasing on `[0, ∞)`. -/
theorem _root_.Real.strictMonoOn_airyDerivPhase : StrictMonoOn Real.airyDerivPhase (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici 0)
    Real.differentiable_airyDerivPhase.continuous.continuousOn fun x hx => by
      rw [interior_Ici, mem_Ioi] at hx
      rw [(Real.hasDerivAt_airyDerivPhase x).deriv]
      exact div_pos hx (mul_pos Real.pi_pos (pow_pos (Real.airyDerivModulus_pos x) 2))

end TauCeti

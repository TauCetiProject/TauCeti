/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Airy.Real
import Mathlib.Algebra.Ring.Identities
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Modulus and phase of the Airy functions

On the real line the Airy functions are written in modulus–phase form (DLMF §9.8),
`Ai(x) = M(x) sin θ(x)`, `Bi(x) = M(x) cos θ(x)`, `Ai′(x) = N(x) sin φ(x)`,
`Bi′(x) = N(x) cos φ(x)`. These four representations are the motivation only: this file does not
prove them. It defines the moduli `M = (Ai² + Bi²)^{1/2}` (DLMF 9.8.3) and
`N = (Ai′² + Bi′²)^{1/2}` (DLMF 9.8.7), and the phases as the integrals of their derivatives
(DLMF 9.8.14), normalized by `θ(0) = π/6` and `φ(0) = −π/6`:

`θ(x) = π/6 − π⁻¹ ∫₀ˣ M(t)⁻² dt`,  `φ(x) = −π/6 + π⁻¹ ∫₀ˣ t N(t)⁻² dt`,

and proves the derivative formulas of the moduli and the phases. So `θ` and `φ` are continuous on
all of `ℝ`, unlike the arctangents of `Ai/Bi` and `Ai′/Bi′`, which jump at the zeros of `Bi` and
`Bi′`. The Wronskian `Ai Bi′ − Ai′ Bi = 1/π` (DLMF 9.2.7) gives Lagrange's identity
`M² N² = (Ai Ai′ + Bi Bi′)² + π⁻²`, so `M > 0` and `N > 0`.

## Main definitions

* `Real.airyModulus`, `Real.airyDerivModulus`: the moduli `M` and `N` (DLMF 9.8.3, 9.8.7).
* `Real.airyPhase`, `Real.airyDerivPhase`: the phases `θ` and `φ` (DLMF 9.8.14).

## Main results

* `Real.airyModulus_sq_mul_airyDerivModulus_sq`: `M² N² = (Ai Ai′ + Bi Bi′)² + π⁻²`, hence
  `Real.airyModulus_sq_mul_airyDerivModulus_sq_pos` (`M² N² > 0`).
* `Real.airyModulus_pos`, `Real.airyDerivModulus_pos`: `M > 0` and `N > 0`.
* `TauCeti.airyModulus_zero`, `TauCeti.airyDerivModulus_zero`: `M(0) = 2 Ai(0)`,
  `N(0) = −2 Ai′(0)`.
* `Real.hasDerivAt_airyModulus`, `Real.hasDerivAt_airyDerivModulus`: `M′ = (Ai Ai′ + Bi Bi′)/M`
  and `N′ = x (Ai Ai′ + Bi Bi′)/N`.
* `TauCeti.airy_modulus_phase_deriv`: `θ′ = −1/(π M²)` and `φ′ = x/(π N²)` (DLMF 9.8.14), with
  `Real.airyModulus_sq_mul_deriv_airyPhase` (`M² θ′ = −1/π`),
  `Real.airyDerivModulus_sq_mul_deriv_airyDerivPhase` (`N² φ′ = x/π`) and
  `Real.airyDerivModulus_mul_deriv_airyDerivModulus` (`N N′ = x M M′`).
* `TauCeti.eq_airyPhase_of_hasDerivAt`, `TauCeti.eq_airyDerivPhase_of_hasDerivAt`: a function
  with the value at `0` and the derivative of `θ` (of `φ`) is `θ` (is `φ`).
* `TauCeti.strictAnti_airyPhase`: `θ` is strictly decreasing on `ℝ`;
  `TauCeti.strictAntiOn_airyDerivPhase`, `TauCeti.strictMonoOn_airyDerivPhase`: `φ` is strictly
  decreasing on `(−∞, 0]` and strictly increasing on `[0, ∞)`.

## References

* NIST Digital Library of Mathematical Functions, §9.8, <https://dlmf.nist.gov/9.8>.

The definitions and the derivative formulas are adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file `DLMF/Airy/Basic/ModulusPhase.lean`
(`airyModulus`, `airyDerivModulus`, `airyPhase`, `airyDerivPhase`, `airyModulus_pos`,
`hasDerivAt_airyModulus`, `hasDerivAt_airyDerivModulus`, `hasDerivAt_airyPhase`,
`hasDerivAt_airyDerivPhase`, `airy_lagrange`), and file
`DLMF/Airy/ModulusPhase/Representations.lean` (`airy_modulus_phase_derivatives`). Positivity of
`M` and `N` is derived here from Lagrange's identity; the values at `0`, the uniqueness of the
phases and their monotonicity are new.
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
    Real.airyModulus x ^ 2 = Real.airyAi x ^ 2 + Real.airyBi x ^ 2 := by
  rw [Real.airyModulus_def]
  exact Real.sq_sqrt (by positivity)

/-- `N² = Ai′² + Bi′²`. -/
theorem _root_.Real.airyDerivModulus_sq (x : ℝ) :
    Real.airyDerivModulus x ^ 2 = deriv Real.airyAi x ^ 2 + deriv Real.airyBi x ^ 2 := by
  rw [Real.airyDerivModulus_def]
  exact Real.sq_sqrt (by positivity)

/-- **Lagrange's identity** for the Airy moduli: `M² N² = (Ai Ai′ + Bi Bi′)² + π⁻²`, the
Wronskian `Ai Bi′ − Ai′ Bi = 1/π` supplying the second square. -/
theorem _root_.Real.airyModulus_sq_mul_airyDerivModulus_sq (x : ℝ) :
    Real.airyModulus x ^ 2 * Real.airyDerivModulus x ^ 2 =
      (Real.airyAi x * deriv Real.airyAi x + Real.airyBi x * deriv Real.airyBi x) ^ 2 +
        π⁻¹ ^ 2 := by
  -- The two-square identity for `(Ai, −Bi)` and `(Ai′, Bi′)`; its second square is the
  -- Wronskian.
  rw [Real.airyModulus_sq, Real.airyDerivModulus_sq, ← neg_sq (Real.airyBi x),
    sq_add_sq_mul_sq_add_sq, ← Real.wronskian_airyAi_airyBi x]
  ring

/-- `M² N² > 0`, by Lagrange's identity. -/
theorem _root_.Real.airyModulus_sq_mul_airyDerivModulus_sq_pos (x : ℝ) :
    0 < Real.airyModulus x ^ 2 * Real.airyDerivModulus x ^ 2 := by
  rw [Real.airyModulus_sq_mul_airyDerivModulus_sq]
  positivity

/-- `M(x) > 0`: `Ai` and `Bi` have no common real zero. -/
theorem _root_.Real.airyModulus_pos (x : ℝ) : 0 < Real.airyModulus x := by
  rw [Real.airyModulus_def, Real.sqrt_pos, ← Real.airyModulus_sq]
  exact pos_of_mul_pos_left (Real.airyModulus_sq_mul_airyDerivModulus_sq_pos x) (sq_nonneg _)

/-- `N(x) > 0`: `Ai′` and `Bi′` have no common real zero. -/
theorem _root_.Real.airyDerivModulus_pos (x : ℝ) : 0 < Real.airyDerivModulus x := by
  rw [Real.airyDerivModulus_def, Real.sqrt_pos, ← Real.airyDerivModulus_sq]
  exact pos_of_mul_pos_right (Real.airyModulus_sq_mul_airyDerivModulus_sq_pos x) (sq_nonneg _)

/-- `M(0) = 2 Ai(0)`. -/
@[simp]
theorem airyModulus_zero : Real.airyModulus 0 = 2 * Real.airyAi 0 := by
  -- `Ai(0)² + Bi(0)² = (2 Ai(0))²`, cast down from `TauCeti.airyAi_zero_sq_add_airyBi_zero_sq`.
  have h : Real.airyAi 0 ^ 2 + Real.airyBi 0 ^ 2 = (2 * Real.airyAi 0) ^ 2 := by
    have h := airyAi_zero_sq_add_airyBi_zero_sq
    rw [← Complex.ofReal_zero, ← Real.ofReal_real_airyAi, ← Real.ofReal_real_airyBi] at h
    rw [mul_pow]
    exact_mod_cast h
  rw [Real.airyModulus_def, h, Real.sqrt_sq (by linarith [realAiryAi_zero_pos])]

/-- `N(0) = −2 Ai′(0)`. -/
@[simp]
theorem airyDerivModulus_zero : Real.airyDerivModulus 0 = -(2 * deriv Real.airyAi 0) := by
  rw [Real.airyDerivModulus_def, deriv_realAiryBi_zero,
    ← Real.sqrt_sq (by linarith [deriv_realAiryAi_zero_neg] : 0 ≤ -(2 * deriv Real.airyAi 0))]
  congr 1
  rw [mul_pow, neg_sq, Real.sq_sqrt (by norm_num)]
  ring

/-- The derivative of `t ↦ √(f(t)² + g(t)²)` at a point where `f(x)² + g(x)² ≠ 0`. -/
private theorem hasDerivAt_sqrt_sq_add_sq {f g : ℝ → ℝ} {f' g' x : ℝ} (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) (h : f x ^ 2 + g x ^ 2 ≠ 0) :
    HasDerivAt (fun t => √(f t ^ 2 + g t ^ 2))
      ((f x * f' + g x * g') / √(f x ^ 2 + g x ^ 2)) x := by
  have hs : √(f x ^ 2 + g x ^ 2) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (by positivity) h.symm)
  refine (((hf.pow 2).add (hg.pow 2)).sqrt h).congr_deriv ?_
  simp only [Pi.add_apply, Pi.pow_apply]
  field_simp
  ring

/-- The derivative of `M` is `(Ai Ai′ + Bi Bi′)/M`. -/
theorem _root_.Real.hasDerivAt_airyModulus (x : ℝ) :
    HasDerivAt Real.airyModulus
      ((Real.airyAi x * deriv Real.airyAi x + Real.airyBi x * deriv Real.airyBi x) /
        Real.airyModulus x) x := by
  have h : Real.airyAi x ^ 2 + Real.airyBi x ^ 2 ≠ 0 := by
    rw [← Real.airyModulus_sq]
    exact (pow_pos (Real.airyModulus_pos x) 2).ne'
  rw [funext Real.airyModulus_def]
  exact hasDerivAt_sqrt_sq_add_sq (Real.differentiable_airyAi x).hasDerivAt
    (Real.differentiable_airyBi x).hasDerivAt h

/-- The derivative of `N` is `x (Ai Ai′ + Bi Bi′)/N`. -/
theorem _root_.Real.hasDerivAt_airyDerivModulus (x : ℝ) :
    HasDerivAt Real.airyDerivModulus
      (x * (Real.airyAi x * deriv Real.airyAi x + Real.airyBi x * deriv Real.airyBi x) /
        Real.airyDerivModulus x) x := by
  have h : deriv Real.airyAi x ^ 2 + deriv Real.airyBi x ^ 2 ≠ 0 := by
    rw [← Real.airyDerivModulus_sq]
    exact (pow_pos (Real.airyDerivModulus_pos x) 2).ne'
  rw [funext Real.airyDerivModulus_def]
  exact (hasDerivAt_sqrt_sq_add_sq (Real.hasDerivAt_deriv_airyAi x)
    (Real.hasDerivAt_deriv_airyBi x) h).congr_deriv (by ring)

/-- `M` is differentiable. -/
theorem differentiable_airyModulus : Differentiable ℝ Real.airyModulus := fun x =>
  (Real.hasDerivAt_airyModulus x).differentiableAt

/-- `N` is differentiable. -/
theorem differentiable_airyDerivModulus : Differentiable ℝ Real.airyDerivModulus := fun x =>
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
theorem airyPhase_zero : Real.airyPhase 0 = π / 6 := by
  simp [Real.airyPhase_def]

/-- `φ(0) = −π/6`. -/
@[simp]
theorem airyDerivPhase_zero : Real.airyDerivPhase 0 = -(π / 6) := by
  simp [Real.airyDerivPhase_def]

/-- `θ′ = −1/(π M²)` (DLMF 9.8.14). -/
theorem _root_.Real.hasDerivAt_airyPhase (x : ℝ) :
    HasDerivAt Real.airyPhase (-(π * Real.airyModulus x ^ 2)⁻¹) x := by
  have hc : Continuous fun t => (Real.airyModulus t ^ 2)⁻¹ :=
    (differentiable_airyModulus.continuous.pow 2).inv₀ fun t =>
      (pow_pos (Real.airyModulus_pos t) 2).ne'
  rw [funext Real.airyPhase_def]
  refine (((hc.integral_hasStrictDerivAt 0 x).hasDerivAt.const_mul π⁻¹).const_sub
    (π / 6)).congr_deriv ?_
  rw [mul_inv]

/-- `φ′ = x/(π N²)` (DLMF 9.8.14). -/
theorem _root_.Real.hasDerivAt_airyDerivPhase (x : ℝ) :
    HasDerivAt Real.airyDerivPhase (x / (π * Real.airyDerivModulus x ^ 2)) x := by
  have hc : Continuous fun t => t / Real.airyDerivModulus t ^ 2 :=
    continuous_id.div (differentiable_airyDerivModulus.continuous.pow 2) fun t =>
      (pow_pos (Real.airyDerivModulus_pos t) 2).ne'
  rw [funext Real.airyDerivPhase_def]
  refine (((hc.integral_hasStrictDerivAt 0 x).hasDerivAt.const_mul π⁻¹).const_add
    (-(π / 6))).congr_deriv ?_
  ring

/-- **DLMF 9.8.14**: `θ′ = −1/(π M²)` and `φ′ = x/(π N²)`. -/
theorem airy_modulus_phase_deriv (x : ℝ) :
    HasDerivAt Real.airyPhase (-(π * Real.airyModulus x ^ 2)⁻¹) x ∧
      HasDerivAt Real.airyDerivPhase (x / (π * Real.airyDerivModulus x ^ 2)) x :=
  ⟨Real.hasDerivAt_airyPhase x, Real.hasDerivAt_airyDerivPhase x⟩

/-- `θ` is differentiable. -/
theorem differentiable_airyPhase : Differentiable ℝ Real.airyPhase := fun x =>
  (Real.hasDerivAt_airyPhase x).differentiableAt

/-- `φ` is differentiable. -/
theorem differentiable_airyDerivPhase : Differentiable ℝ Real.airyDerivPhase := fun x =>
  (Real.hasDerivAt_airyDerivPhase x).differentiableAt

/-- **Uniqueness of `θ`**: a function `f` with `f(0) = π/6` and `f′ = −1/(π M²)` on `ℝ` is the
phase `θ`. -/
theorem eq_airyPhase_of_hasDerivAt {f : ℝ → ℝ} (h0 : f 0 = π / 6)
    (hf : ∀ x, HasDerivAt f (-(π * Real.airyModulus x ^ 2)⁻¹) x) : f = Real.airyPhase :=
  eq_of_fderiv_eq (fun x => (hf x).differentiableAt) differentiable_airyPhase
    (fun x => by rw [(hf x).hasFDerivAt.fderiv, (Real.hasDerivAt_airyPhase x).hasFDerivAt.fderiv])
    0 (by rw [h0, airyPhase_zero])

/-- **Uniqueness of `φ`**: a function `f` with `f(0) = −π/6` and `f′ = x/(π N²)` on `ℝ` is the
phase `φ`. -/
theorem eq_airyDerivPhase_of_hasDerivAt {f : ℝ → ℝ} (h0 : f 0 = -(π / 6))
    (hf : ∀ x, HasDerivAt f (x / (π * Real.airyDerivModulus x ^ 2)) x) :
    f = Real.airyDerivPhase :=
  eq_of_fderiv_eq (fun x => (hf x).differentiableAt) differentiable_airyDerivPhase
    (fun x => by
      rw [(hf x).hasFDerivAt.fderiv, (Real.hasDerivAt_airyDerivPhase x).hasFDerivAt.fderiv])
    0 (by rw [h0, airyDerivPhase_zero])

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
theorem strictAnti_airyPhase : StrictAnti Real.airyPhase :=
  strictAnti_of_deriv_neg fun x => by
    rw [(Real.hasDerivAt_airyPhase x).deriv, neg_lt_zero, inv_pos]
    exact mul_pos Real.pi_pos (pow_pos (Real.airyModulus_pos x) 2)

/-- `φ` is strictly decreasing on `(−∞, 0]`. -/
theorem strictAntiOn_airyDerivPhase : StrictAntiOn Real.airyDerivPhase (Iic 0) :=
  strictAntiOn_of_deriv_neg (convex_Iic 0) differentiable_airyDerivPhase.continuous.continuousOn
    fun x hx => by
      rw [interior_Iic, mem_Iio] at hx
      rw [(Real.hasDerivAt_airyDerivPhase x).deriv]
      exact div_neg_of_neg_of_pos hx
        (mul_pos Real.pi_pos (pow_pos (Real.airyDerivModulus_pos x) 2))

/-- `φ` is strictly increasing on `[0, ∞)`. -/
theorem strictMonoOn_airyDerivPhase : StrictMonoOn Real.airyDerivPhase (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici 0) differentiable_airyDerivPhase.continuous.continuousOn
    fun x hx => by
      rw [interior_Ici, mem_Ioi] at hx
      rw [(Real.hasDerivAt_airyDerivPhase x).deriv]
      exact div_pos hx (mul_pos Real.pi_pos (pow_pos (Real.airyDerivModulus_pos x) 2))

end TauCeti

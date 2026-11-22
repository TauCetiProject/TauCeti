/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.Contiguous
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.EulerIntegral
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.Transformation

/-!
# The Whittaker function `M_{κ,μ}`

The Whittaker function of the first kind (DLMF 13.14.2) is

`M_{κ,μ}(z) = Γ(1 + 2μ) e^{-z/2} z^{1/2 + μ} 𝐌(1/2 + μ - κ, 1 + 2μ, z)`,

where `𝐌(a, b, z) = Complex.regularizedHGFun {a} {b} z` is Olver's regularized Kummer function
and `z^{1/2 + μ}` is the principal complex power. When `1 + 2μ` is not a nonpositive integer,
`Γ(1 + 2μ) 𝐌(a, 1 + 2μ, z)` is Kummer's function `M(a, 1 + 2μ, z)`, so this is DLMF's
`M_{κ,μ}`. At the poles of `Γ(1 + 2μ)` Mathlib's convention `Γ(-n) = 0` makes the value zero; this
totalization is not the analytic continuation in `μ`, which does not exist there in general.

The function `M_{κ,μ}` solves Whittaker's equation
`w'' + (-1/4 + κ / z + (1/4 - μ²) / z²) w = 0` on the slit plane: writing
`w = e^{-z/2} z^{1/2 + μ} f`, Whittaker's equation for `w` becomes Kummer's equation
`z f'' + (1 + 2μ - z) f' - (1/2 + μ - κ) f = 0` for `f`. When `0 < re (1/2 + μ ± κ)`, Kummer's
integral gives the Euler-type integral representation (DLMF 13.16.1, after `t ↦ (1 - t) / 2`)

`M_{κ,μ}(z) = Γ(1 + 2μ) / (Γ(1/2 + μ + κ) Γ(1/2 + μ - κ)) e^{z/2} z^{1/2 + μ}
  ∫₀¹ t^{μ + κ - 1/2} (1 - t)^{μ - κ - 1/2} e^{-z t} dt`.

Near the origin, `M_{κ,μ}(z) = z^{1/2 + μ} (1 + O(z))` when `Γ(1 + 2μ)` has no pole. Whittaker
functions of real positive argument appear as the radial parts of Fourier coefficients of Maass
forms and of non-holomorphic Poincaré series on the upper half-plane.

## Main declarations

* `Complex.whittakerM` — the Whittaker function `M_{κ,μ}(z)`.
* `Complex.whittakerM_sub_half` — `M_{κ,s - 1/2}(z) = e^{-z/2} z^s Γ(2s) 𝐌(s - κ, 2s, z)`.
* `Complex.isBigO_whittakerM_sub_half_sub_cpow` — `M_{κ,s - 1/2}(z) = z^s (1 + O(z))` near `0`.
* `Complex.whittakerM_eq_integral` — the Euler-type integral representation (DLMF 13.16.1).
* `Complex.hasDerivAt_whittakerM` — the derivative of `M_{κ,μ}` on the slit plane.
* `Complex.whittakerM_ode` — Whittaker's equation (DLMF 13.14.1).
* `Complex.whittakerM_zero_half`, `Complex.whittakerM_one_half` — the elementary values
  `M_{0,1/2}(z) = 2 sinh (z / 2)` and `M_{1,1/2}(z) = z e^{-z/2}`.

## References

* *NIST Digital Library of Mathematical Functions*, [§13.14](https://dlmf.nist.gov/13.14) and
  [§13.16](https://dlmf.nist.gov/13.16).
* W. Duke, Ö. Imamoglu and Á. Tóth, *Cycle integrals of the j-function and mock modular forms*,
  Ann. of Math. 173 (2011), Appendix A.
-/

public section

noncomputable section

open Filter Set
open scoped Topology

namespace Complex

/-- The **Whittaker function**
`M_{κ,μ}(z) = Γ(1 + 2μ) e^{-z/2} z^{1/2 + μ} 𝐌(1/2 + μ - κ, 1 + 2μ, z)` (DLMF 13.14.2), with the
principal complex power and Olver's regularized Kummer function `𝐌`.
At the poles of `Γ(1 + 2μ)` the value is the totalized `0`. -/
def whittakerM (κ μ z : ℂ) : ℂ :=
  Gamma (1 + 2 * μ) * exp (-(z / 2)) * z ^ (1 / 2 + μ) *
    regularizedHGFun {1 / 2 + μ - κ} {1 + 2 * μ} z

/-- The defining formula of `whittakerM`. -/
theorem whittakerM_def (κ μ z : ℂ) :
    whittakerM κ μ z = Gamma (1 + 2 * μ) * exp (-(z / 2)) * z ^ (1 / 2 + μ) *
      regularizedHGFun {1 / 2 + μ - κ} {1 + 2 * μ} z := (rfl)

/-- In terms of the shifted order `s = μ + 1/2`,
`M_{κ,s - 1/2}(z) = e^{-z/2} z^s Γ(2s) 𝐌(s - κ, 2s, z)`. -/
theorem whittakerM_sub_half (κ s z : ℂ) :
    whittakerM κ (s - 1 / 2) z =
      exp (-(z / 2)) * z ^ s * Gamma (2 * s) * regularizedHGFun {s - κ} {2 * s} z := by
  have hb : 1 + 2 * (s - 1 / 2) = 2 * s := by ring
  have hp : (1 / 2 + (s - 1 / 2) : ℂ) = s := by ring
  have ha : (1 / 2 + (s - 1 / 2) - κ : ℂ) = s - κ := by ring
  rw [whittakerM_def, hb, ha, hp]
  ring

/-- Near the origin, `M_{κ,s - 1/2}(z) = z^s (1 + O(z))` whenever `Γ(2s)` has no pole, in
particular for `0 < re s`. -/
theorem isBigO_whittakerM_sub_half_sub_cpow (κ : ℂ) {s : ℂ} (hs : ∀ n : ℕ, 2 * s ≠ -n) :
    (fun z => whittakerM κ (s - 1 / 2) z - z ^ s) =O[𝓝 0] fun z => z ^ s * z := by
  let E : ℂ → ℂ := fun z => exp (-(z / 2)) * Gamma (2 * s) * regularizedHGFun {s - κ} {2 * s} z
  have hE : DifferentiableAt ℂ E 0 :=
    (((differentiable_exp.comp (differentiable_id.div_const 2).neg) 0).mul_const _).mul
      (differentiable_regularizedHGFun_of_card_le (by simp) 0)
  have hE0 : E 0 = 1 := by
    simp only [E, regularizedHGFun_zero, regularizedHGFunCoeff_singleton_zero, zero_div, neg_zero,
      exp_zero, one_mul]
    exact mul_inv_cancel₀ (Gamma_ne_zero hs)
  have h := (Asymptotics.isBigO_refl (fun z : ℂ => z ^ s) (𝓝 0)).mul hE.isBigO_sub
  rw [hE0] at h
  refine (h.congr_left fun z => ?_).congr_right fun z => by rw [sub_zero]
  rw [whittakerM_sub_half]
  ring

/-- The **Euler-type integral** for the Whittaker function (DLMF 13.16.1, after the substitution
`t ↦ (1 - t) / 2`): when `0 < re (1/2 + μ + κ)` and `0 < re (1/2 + μ - κ)`,
`M_{κ,μ}(z) = Γ(1 + 2μ) / (Γ(1/2 + μ + κ) Γ(1/2 + μ - κ)) e^{z/2} z^{1/2 + μ}
  ∫₀¹ t^{μ + κ - 1/2} (1 - t)^{μ - κ - 1/2} e^{-z t} dt` for every `z : ℂ`. -/
theorem whittakerM_eq_integral {κ μ : ℂ} (h₁ : 0 < (1 / 2 + μ + κ).re)
    (h₂ : 0 < (1 / 2 + μ - κ).re) (z : ℂ) :
    whittakerM κ μ z =
      Gamma (1 + 2 * μ) / (Gamma (1 / 2 + μ + κ) * Gamma (1 / 2 + μ - κ)) * exp (z / 2) *
        z ^ (1 / 2 + μ) * ∫ t : ℝ in 0..1,
          (t : ℂ) ^ (μ + κ - 1 / 2) * (1 - (t : ℂ)) ^ (μ - κ - 1 / 2) * exp (-(z * t)) := by
  have hba : 1 + 2 * μ - (1 / 2 + μ - κ) = 1 / 2 + μ + κ := by ring
  have hab : (1 / 2 + μ - κ).re < (1 + 2 * μ).re := by
    rw [← sub_pos, ← sub_re, hba]
    exact h₁
  -- Reflect `t ↦ 1 - t` to pass from Kummer's integrand to the Whittaker integrand.
  have hreflect : (∫ t : ℝ in 0..1,
      (t : ℂ) ^ (μ + κ - 1 / 2) * (1 - (t : ℂ)) ^ (μ - κ - 1 / 2) * exp (-(z * t))) =
      exp (-z) * ∫ t : ℝ in 0..1, (t : ℂ) ^ (1 / 2 + μ - κ - 1) *
        (1 - (t : ℂ)) ^ (1 + 2 * μ - (1 / 2 + μ - κ) - 1) * exp (z * t) := by
    have hsub := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
      (fun t : ℝ => (t : ℂ) ^ (μ + κ - 1 / 2) * (1 - (t : ℂ)) ^ (μ - κ - 1 / 2) *
        exp (-(z * t))) 1
    rw [sub_self, sub_zero] at hsub
    rw [← hsub, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have he : exp (-(z * (1 - (t : ℂ)))) = exp (-z) * exp (z * t) := by
      rw [← exp_add]
      ring_nf
    have h1 : μ - κ - 1 / 2 = 1 / 2 + μ - κ - 1 := by ring
    have h2 : μ + κ - 1 / 2 = 1 + 2 * μ - (1 / 2 + μ - κ) - 1 := by ring
    simp only [ofReal_sub, ofReal_one, sub_sub_cancel]
    rw [he, h1, h2]
    ring
  rw [hreflect, whittakerM_def, regularizedHGFun_singleton_eq_integral h₂ hab, hba]
  have hexp : exp (z / 2) * exp (-z) = exp (-(z / 2)) := by
    rw [← exp_add]
    ring_nf
  rw [← hexp]
  field_simp

/-- The derivative of `e^{-w/2} w^p f(w)` at a point of the slit plane. -/
private theorem hasDerivAt_exp_mul_cpow_mul {f : ℂ → ℂ} {f' p z : ℂ} (hf : HasDerivAt f f' z)
    (hz : z ∈ slitPlane) :
    HasDerivAt (fun w => exp (-(w / 2)) * w ^ p * f w)
      (exp (-(z / 2)) * z ^ p * ((p / z - 1 / 2) * f z + f')) z := by
  have hz0 := slitPlane_ne_zero hz
  have he : HasDerivAt (fun w : ℂ => exp (-(w / 2))) (exp (-(z / 2)) * -(1 / 2)) z := by
    simpa using ((hasDerivAt_id z).div_const 2).neg.cexp
  have hc : HasDerivAt (fun w : ℂ => w ^ p) (p * z ^ (p - 1) * 1) z :=
    (hasDerivAt_id z).cpow_const hz
  convert (he.mul hc).mul hf using 1
  simp only [Pi.mul_apply]
  rw [cpow_sub _ _ hz0, cpow_one]
  field_simp
  ring

/-- The derivative of the Whittaker function on the slit plane:
`M_{κ,μ}'(z) = ((1/2 + μ) / z - 1/2) M_{κ,μ}(z)
  + Γ(1 + 2μ) e^{-z/2} z^{1/2 + μ} (1/2 + μ - κ) 𝐌(3/2 + μ - κ, 2 + 2μ, z)`. -/
theorem hasDerivAt_whittakerM (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (whittakerM κ μ)
      (((1 / 2 + μ) / z - 1 / 2) * whittakerM κ μ z +
        Gamma (1 + 2 * μ) * exp (-(z / 2)) * z ^ (1 / 2 + μ) *
          ((1 / 2 + μ - κ) * regularizedHGFun {1 / 2 + μ - κ + 1} {1 + 2 * μ + 1} z)) z := by
  have h := (hasDerivAt_exp_mul_cpow_mul (p := 1 / 2 + μ)
    (hasDerivAt_regularizedHGFun_singleton (1 / 2 + μ - κ) (1 + 2 * μ) z) hz).const_mul
    (Gamma (1 + 2 * μ))
  convert h using 1
  · funext w
    rw [whittakerM_def]
    ring
  · rw [whittakerM_def]
    ring

/-- The Whittaker function is complex differentiable on the slit plane. -/
theorem differentiableAt_whittakerM (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    DifferentiableAt ℂ (whittakerM κ μ) z :=
  (hasDerivAt_whittakerM κ μ hz).differentiableAt

/-- **Whittaker's equation** (DLMF 13.14.1): on the slit plane, `w = M_{κ,μ}` satisfies
`w'' + (-1/4 + κ / z + (1/4 - μ²) / z²) w = 0`, for all complex `κ` and `μ`. -/
theorem whittakerM_ode (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    deriv^[2] (whittakerM κ μ) z +
      (-1 / 4 + κ / z + (1 / 4 - μ ^ 2) / z ^ 2) * whittakerM κ μ z = 0 := by
  have hz0 := slitPlane_ne_zero hz
  set F := regularizedHGFun {1 / 2 + μ - κ} {1 + 2 * μ} with hFdef
  have hF : Differentiable ℂ F := differentiable_regularizedHGFun_of_card_le (by simp)
  have hF' : Differentiable ℂ (deriv F) := by
    rw [hFdef, deriv_regularizedHGFun_singleton]
    exact (differentiable_regularizedHGFun_of_card_le (by simp)).const_mul _
  have hM : whittakerM κ μ =
      fun w => Gamma (1 + 2 * μ) * (exp (-(w / 2)) * w ^ (1 / 2 + μ) * F w) := by
    funext w
    rw [whittakerM_def]
    ring
  -- `M = Γ(1 + 2μ) e^{-w/2} w^{1/2 + μ} H₀` and `M' = Γ(1 + 2μ) e^{-w/2} w^{1/2 + μ} H₁`.
  have hD : deriv (whittakerM κ μ) =ᶠ[𝓝 z] fun w => Gamma (1 + 2 * μ) *
      (exp (-(w / 2)) * w ^ (1 / 2 + μ) * (((1 / 2 + μ) / w - 1 / 2) * F w + deriv F w)) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    rw [hM]
    exact ((hasDerivAt_exp_mul_cpow_mul (hF w).hasDerivAt hw).const_mul _).deriv
  have hH : HasDerivAt (fun w => ((1 / 2 + μ) / w - 1 / 2) * F w + deriv F w)
      (-((1 / 2 + μ) / z ^ 2) * F z + ((1 / 2 + μ) / z - 1 / 2) * deriv F z +
        deriv (deriv F) z) z := by
    have hinv : HasDerivAt (fun w : ℂ => (1 / 2 + μ) / w - 1 / 2) (-((1 / 2 + μ) / z ^ 2)) z := by
      simpa [div_eq_mul_inv] using ((hasDerivAt_inv hz0).const_mul (1 / 2 + μ)).sub_const (1 / 2)
    exact (hinv.mul (hF z).hasDerivAt).add (hF' z).hasDerivAt
  have h2 : deriv^[2] (whittakerM κ μ) z = Gamma (1 + 2 * μ) *
      (exp (-(z / 2)) * z ^ (1 / 2 + μ) *
        (((1 / 2 + μ) / z - 1 / 2) * (((1 / 2 + μ) / z - 1 / 2) * F z + deriv F z) +
          (-((1 / 2 + μ) / z ^ 2) * F z + ((1 / 2 + μ) / z - 1 / 2) * deriv F z +
            deriv (deriv F) z))) := by
    rw [Function.iterate_succ_apply', Function.iterate_one, hD.deriv_eq]
    exact ((hasDerivAt_exp_mul_cpow_mul hH hz).const_mul _).deriv
  -- Whittaker's equation for `M` is `Γ(1 + 2μ) e^{-z/2} z^{1/2 + μ} / z` times Kummer's equation.
  have hK := regularizedHGFun_singleton_ode (1 / 2 + μ - κ) (1 + 2 * μ) z
  rw [Function.iterate_succ_apply', Function.iterate_one, ← hFdef] at hK
  rw [h2]
  simp only [hM]
  linear_combination (Gamma (1 + 2 * μ) * exp (-(z / 2)) * z ^ (1 / 2 + μ) * z⁻¹) * hK +
    Gamma (1 + 2 * μ) * exp (-(z / 2)) * z ^ (1 / 2 + μ) * (deriv F z - deriv (deriv F) z) *
      mul_inv_cancel₀ hz0

/-- `M_{0,1/2}(z) = 2 sinh (z / 2)` for every `z : ℂ`. -/
theorem whittakerM_zero_half (z : ℂ) : whittakerM 0 (1 / 2) z = 2 * sinh (z / 2) := by
  have hb : (1 + 2 * (1 / 2) : ℂ) = 1 + 1 := by norm_num
  have ha : (1 / 2 + 1 / 2 - 0 : ℂ) = 1 := by norm_num
  have hp : (1 / 2 + 1 / 2 : ℂ) = 1 := by norm_num
  -- `z 𝐌(1, 2, z) = 𝐌(1, 1, z) - 1 = e^z - 1`.
  have h11 : regularizedHGFun {1} {1} z = exp z := by
    rw [regularizedHGFun_singleton_eq_exp_mul, sub_self,
      regularizedHGFun_of_zero_mem (Multiset.mem_singleton_self 0)]
    simp
  have h12 := regularizedHGFun_one_singleton_eq_inv_Gamma_add_mul 1 z
  rw [h11, Gamma_one, inv_one] at h12
  have hexp : exp (z / 2) = exp (-(z / 2)) * exp z := by
    rw [← exp_add]
    ring_nf
  rw [whittakerM_def, hb, ha, hp, cpow_one, two_sinh, Gamma_add_one _ one_ne_zero, Gamma_one,
    hexp]
  linear_combination (-exp (-(z / 2))) * h12

/-- `M_{1,1/2}(z) = z e^{-z/2}` for every `z : ℂ`: the Kummer series terminates. -/
theorem whittakerM_one_half (z : ℂ) : whittakerM 1 (1 / 2) z = z * exp (-(z / 2)) := by
  have hb : (1 + 2 * (1 / 2) : ℂ) = 1 + 1 := by norm_num
  have ha : (1 / 2 + 1 / 2 - 1 : ℂ) = 0 := by norm_num
  have hp : (1 / 2 + 1 / 2 : ℂ) = 1 := by norm_num
  rw [whittakerM_def, hb, ha, hp, cpow_one,
    regularizedHGFun_of_zero_mem (Multiset.mem_singleton_self 0)]
  simp only [Multiset.map_singleton, Multiset.prod_singleton, Gamma_add_one _ one_ne_zero,
    Gamma_one]
  ring

end Complex

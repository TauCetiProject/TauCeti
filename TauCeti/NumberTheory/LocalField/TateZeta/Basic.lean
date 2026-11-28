/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import TauCeti.Analysis.Complex.ParametricIntegralHolomorphy

/-!
# The local Tate zeta integral

Let `F` be a field, `ν` a measure on `Fˣ`, `a : F → ℝ` an absolute value (in the arithmetic
applications the normalized absolute value of a local field), `χ : Fˣ → ℂˣ` a continuous
quasi-character and `f : F → ℂ` a test function. The **local Tate zeta integral** is

`z(s, χ; f) = ∫_{Fˣ} f(x) χ(x) a(x) ^ s dν(x)`,

Tate's `ζ(f, χ |·|^s)`. This file defines it with no hypothesis on `F`, `ν`, `a` or `χ`, as
Mathlib's totalized Bochner integral, and proves the identities that only use the shape of the
integrand:

* it is linear in the test function;
* it is holomorphic in `s` on every half-plane `α < re s` on which `‖f χ‖ a ^ σ` is integrable
  for all `σ > α`;
* rescaling the measure by `c` rescales the integral by `c`;
* twisting `χ` by the norm power `a ^ t` translates `s` by `t`: `z(s, χ a^t; f) = z(s + t, χ; f)`;
* for a left-invariant `ν` and a multiplicative positive `a`, translating the test function by
  `b ∈ Fˣ` multiplies the integral by `(χ a^s)(b)⁻¹`:
  `z(s, χ; f(b ·)) = χ(b)⁻¹ a(b)^(-s) z(s, χ; f)`.

The last identity says that `f ↦ z(s, χ; f)` is an eigendistribution for the scalar action of
`Fˣ` with eigencharacter `χ a^s`; in particular it vanishes on test functions invariant under
some `b` with `(χ a^s)(b) ≠ 1`. The convergence and the explicit values over a nonarchimedean
local field are in `TauCeti.NumberTheory.LocalField.TateZeta.Nonarchimedean`.

## Main definitions

* `TauCeti.TateZeta.localZetaIntegral ν a χ f s`: the integral `∫ f(x) χ(x) a(x) ^ s dν(x)`.

## Main results

* `TauCeti.TateZeta.localZetaIntegral_add`, `TauCeti.TateZeta.localZetaIntegral_const_mul`:
  linearity in the test function.
* `TauCeti.TateZeta.differentiableOn_localZetaIntegral_of_integrable`: holomorphy on a
  half-plane of absolute convergence.
* `TauCeti.TateZeta.localZetaIntegral_smul_measure`: `z_{c ν} = c z_ν`.
* `TauCeti.TateZeta.localZetaIntegral_of_twist`: `z(s, χ a^t; f) = z(s + t, χ; f)`.
* `TauCeti.TateZeta.localZetaIntegral_comp_mul_left`:
  `z(s, χ; f(b ·)) = χ(b)⁻¹ a(b)^(-s) z(s, χ; f)`.
* `TauCeti.TateZeta.localZetaIntegral_eq_zero_of_comp_mul_left`: if `f(b ·) = c f` and
  `c χ(b) a(b) ^ s ≠ 1`, then `z(s, χ; f) = 0`.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels
  and A. Fröhlich, eds., *Algebraic Number Theory*, §2.4.
* S. S. Kudla, *Tate's thesis*, in J. Bernstein and S. Gelbart, eds., *An Introduction to the
  Langlands Program*, §3, (3.4).
* The definition follows `localIdelicZetaIntegral` in `RiemannMasullo/Ch03_IdelicZeta/Sec3.lean`
  of the Riemann–Masullo formalization (https://github.com/mccorvie/riemann-masullo), which
  integrates `f(x) c(x)` against a quasi-character `c` that already contains the power `a ^ s`.
-/

public section
noncomputable section

open MeasureTheory Complex

namespace TauCeti.TateZeta

variable {F : Type*} [Field F] [TopologicalSpace F] [MeasurableSpace F]

/-- The **local Tate zeta integral** `z(s, χ; f) = ∫_{Fˣ} f(x) χ(x) a(x) ^ s dν(x)` of a test
function `f`, a quasi-character `χ` and an exponent `s`, for a measure `ν` on `Fˣ` and an
absolute value `a`. It is Mathlib's totalized Bochner integral: its value is `0` when the
integrand is not integrable. With `ν` the multiplicative Haar measure and `a` the normalized
absolute value of a local field, it is Tate's local zeta integral `ζ(f, χ |·|^s)`. -/
def localZetaIntegral (ν : Measure Fˣ) (a : F → ℝ) (χ : Fˣ →ₜ* ℂˣ) (f : F → ℂ) (s : ℂ) : ℂ :=
  ∫ x : Fˣ, f x * (χ x : ℂ) * (a x : ℂ) ^ s ∂ν

variable (ν : Measure Fˣ) (a : F → ℝ) (χ : Fˣ →ₜ* ℂˣ)

theorem localZetaIntegral_def (f : F → ℂ) (s : ℂ) :
    localZetaIntegral ν a χ f s = ∫ x : Fˣ, f x * (χ x : ℂ) * (a x : ℂ) ^ s ∂ν :=
  (rfl)

/-- The local zeta integral is additive in the test function, for integrable integrands. -/
theorem localZetaIntegral_add {f g : F → ℂ} {s : ℂ}
    (hf : Integrable (fun x : Fˣ ↦ f x * (χ x : ℂ) * (a x : ℂ) ^ s) ν)
    (hg : Integrable (fun x : Fˣ ↦ g x * (χ x : ℂ) * (a x : ℂ) ^ s) ν) :
    localZetaIntegral ν a χ (f + g) s =
      localZetaIntegral ν a χ f s + localZetaIntegral ν a χ g s := by
  rw [localZetaIntegral_def, localZetaIntegral_def, localZetaIntegral_def, ← integral_add hf hg]
  congr 1
  ext x
  simp only [Pi.add_apply]
  ring

/-- The local zeta integral is homogeneous in the test function. -/
theorem localZetaIntegral_const_mul (c : ℂ) (f : F → ℂ) (s : ℂ) :
    localZetaIntegral ν a χ (fun x ↦ c * f x) s = c * localZetaIntegral ν a χ f s := by
  rw [localZetaIntegral_def, localZetaIntegral_def, ← integral_const_mul]
  simp only [mul_assoc]

/-- **Holomorphy on a half-plane of absolute convergence.** If `a` is positive and measurable
on `Fˣ`, `f χ` is almost everywhere strongly measurable and `‖f(x) χ(x)‖ a(x) ^ σ` is integrable
for every `σ > α`, then `s ↦ z(s, χ; f)` is holomorphic on the half-plane `α < re s`. -/
theorem differentiableOn_localZetaIntegral_of_integrable {f : F → ℂ} (ha : ∀ x : Fˣ, 0 < a x)
    (ham : Measurable fun x : Fˣ ↦ a x)
    (hf : AEStronglyMeasurable (fun x : Fˣ ↦ f x * (χ x : ℂ)) ν) {α : ℝ}
    (hint : ∀ σ : ℝ, α < σ → Integrable (fun x : Fˣ ↦ ‖f x * (χ x : ℂ)‖ * a x ^ σ) ν) :
    DifferentiableOn ℂ (localZetaIntegral ν a χ f) {s | α < s.re} :=
  differentiableOn_integral_mul_cpow ν ha hf ham hint

/-- Rescaling the multiplicative measure by `c` rescales the local zeta integral by `c`. -/
theorem localZetaIntegral_smul_measure (c : ENNReal) (f : F → ℂ) (s : ℂ) :
    localZetaIntegral (c • ν) a χ f s = c.toReal • localZetaIntegral ν a χ f s := by
  rw [localZetaIntegral_def, localZetaIntegral_def, integral_smul_measure]

/-- **Twisting by a norm power translates the exponent**: if `χ' = χ a ^ t` on `Fˣ`, then
`z(s, χ'; f) = z(s + t, χ; f)`. -/
theorem localZetaIntegral_of_twist {χ' : Fˣ →ₜ* ℂˣ} {t : ℂ}
    (hχ' : ∀ x : Fˣ, (χ' x : ℂ) = χ x * (a x : ℂ) ^ t) (f : F → ℂ) (s : ℂ) :
    localZetaIntegral ν a χ' f s = localZetaIntegral ν a χ f (s + t) := by
  rw [localZetaIntegral_def, localZetaIntegral_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rcases eq_or_ne t 0 with rfl | ht
  · rw [hχ' x, cpow_zero, mul_one, add_zero]
  -- For `t ≠ 0`, `a x ≠ 0`, since otherwise `χ' x = χ x * 0 ^ t = 0`.
  have ha : (a x : ℂ) ≠ 0 := fun h ↦ (χ' x).ne_zero (by rw [hχ' x, h, zero_cpow ht, mul_zero])
  rw [hχ' x, add_comm s t, cpow_add _ _ ha]
  ring

/-- **The local zeta integral is an eigendistribution**: for a left-invariant measure and a
positive multiplicative `a`, translating the test function by `b ∈ Fˣ` multiplies the integral
by `(χ a ^ s)(b)⁻¹`, that is `z(s, χ; f(b ·)) = χ(b)⁻¹ a(b) ^ (-s) z(s, χ; f)`. -/
theorem localZetaIntegral_comp_mul_left [MeasurableMul Fˣ] [ν.IsMulLeftInvariant]
    (ha : ∀ x : Fˣ, 0 < a x) (hmul : ∀ x y : Fˣ, a ((x * y : Fˣ) : F) = a x * a y)
    (f : F → ℂ) (b : Fˣ) (s : ℂ) :
    localZetaIntegral ν a χ (fun x ↦ f (b * x)) s =
      (χ b : ℂ)⁻¹ * (a b : ℂ) ^ (-s) * localZetaIntegral ν a χ f s := by
  have h1 : a ((1 : Fˣ) : F) = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    nlinarith [ha 1]
  have hinv : a ((b⁻¹ : Fˣ) : F) = (a b)⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by rw [← hmul, inv_mul_cancel, h1])
  -- Substitute `y = b * x` in the integral of `y ↦ f y χ(b⁻¹ y) a(b⁻¹ y) ^ s`.
  have key := integral_mul_left_eq_self (μ := ν)
    (fun y : Fˣ ↦ f y * (χ (b⁻¹ * y) : ℂ) * (a ((b⁻¹ * y : Fˣ) : F) : ℂ) ^ s) b
  simp only [inv_mul_cancel_left, Units.val_mul] at key
  rw [localZetaIntegral_def, localZetaIntegral_def, key, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  dsimp only
  rw [map_mul, Units.val_mul, map_inv, Units.val_inv_eq_inv_val, ← Units.val_mul, hmul,
    hinv, Complex.ofReal_mul,
    Complex.ofReal_mul_cpow (inv_nonneg.2 (ha b).le), Complex.ofReal_inv, Complex.inv_cpow,
    Complex.cpow_neg]
  · ring
  · rw [Complex.arg_ofReal_of_nonneg (ha b).le]
    exact Real.pi_ne_zero.symm

/-- **Vanishing by an eigenfunction**: for a left-invariant measure and a positive multiplicative
`a`, if translating the test function by `b ∈ Fˣ` multiplies it by `c`, that is `f(b ·) = c f`,
and `c (χ a ^ s)(b) ≠ 1`, then `z(s, χ; f) = 0`. The invariant case is `c = 1`. -/
theorem localZetaIntegral_eq_zero_of_comp_mul_left [MeasurableMul Fˣ] [ν.IsMulLeftInvariant]
    (ha : ∀ x : Fˣ, 0 < a x) (hmul : ∀ x y : Fˣ, a ((x * y : Fˣ) : F) = a x * a y)
    {f : F → ℂ} {b : Fˣ} {c : ℂ} (hb : ∀ x, f (b * x) = c * f x) {s : ℂ}
    (hχ : c * (χ b : ℂ) * (a b : ℂ) ^ s ≠ 1) :
    localZetaIntegral ν a χ f s = 0 := by
  have h := localZetaIntegral_comp_mul_left ν a χ ha hmul f b s
  simp only [hb, localZetaIntegral_const_mul] at h
  have hs : (a b : ℂ) ^ s ≠ 0 := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.2 (ha b).ne')]
    exact exp_ne_zero _
  have h1 : (χ b : ℂ) * (a b : ℂ) ^ s * ((χ b : ℂ)⁻¹ * (a b : ℂ) ^ (-s)) = 1 := by
    have := (χ b).ne_zero
    rw [cpow_neg]
    field_simp
  -- `(c (χ a ^ s)(b) - 1) z = (χ a ^ s)(b) (c z - (χ a ^ s)(b)⁻¹ z)`.
  have h0 : (c * (χ b : ℂ) * (a b : ℂ) ^ s - 1) * localZetaIntegral ν a χ f s = 0 := by
    linear_combination ((χ b : ℂ) * (a b : ℂ) ^ s) * h + localZetaIntegral ν a χ f s * h1
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hχ)

end TauCeti.TateZeta

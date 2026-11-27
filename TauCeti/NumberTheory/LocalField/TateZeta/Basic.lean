/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

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
* rescaling the measure by `c` rescales the integral by `c`;
* twisting `χ` by the norm power `a ^ t` translates `s` by `t`: `z(s, χ a^t; f) = z(s + t, χ; f)`;
* for a left-invariant `ν` and a multiplicative positive `a`, translating the test function by
  `b ∈ Fˣ` multiplies the integral by `(χ a^s)(b)⁻¹`:
  `z(s, χ; f(b ·)) = χ(b)⁻¹ a(b)^(-s) z(s, χ; f)`.

The last identity says that `f ↦ z(s, χ; f)` is an eigendistribution for the scalar action of
`Fˣ` with eigencharacter `χ a^s`. The convergence and the explicit values over a nonarchimedean
local field are in `TauCeti.NumberTheory.LocalField.TateZeta.Nonarchimedean`.

## Main definitions

* `TauCeti.TateZeta.localZetaIntegral ν a χ f s`: the integral `∫ f(x) χ(x) a(x) ^ s dν(x)`.

## Main results

* `TauCeti.TateZeta.localZetaIntegral_add`, `TauCeti.TateZeta.localZetaIntegral_const_mul`:
  linearity in the test function.
* `TauCeti.TateZeta.localZetaIntegral_smul_measure`: `z_{c ν} = c z_ν`.
* `TauCeti.TateZeta.localZetaIntegral_of_twist`: `z(s, χ a^t; f) = z(s + t, χ; f)`.
* `TauCeti.TateZeta.localZetaIntegral_comp_mul_left`:
  `z(s, χ; f(b ·)) = χ(b)⁻¹ a(b)^(-s) z(s, χ; f)`.

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
@[expose]
def localZetaIntegral (ν : Measure Fˣ) (a : F → ℝ) (χ : Fˣ →ₜ* ℂˣ) (f : F → ℂ) (s : ℂ) : ℂ :=
  ∫ x : Fˣ, f x * (χ x : ℂ) * (a x : ℂ) ^ s ∂ν

variable (ν : Measure Fˣ) (a : F → ℝ) (χ : Fˣ →ₜ* ℂˣ)

/-- The local zeta integral is additive in the test function, for integrable integrands. -/
theorem localZetaIntegral_add {f g : F → ℂ} {s : ℂ}
    (hf : Integrable (fun x : Fˣ ↦ f x * (χ x : ℂ) * (a x : ℂ) ^ s) ν)
    (hg : Integrable (fun x : Fˣ ↦ g x * (χ x : ℂ) * (a x : ℂ) ^ s) ν) :
    localZetaIntegral ν a χ (f + g) s =
      localZetaIntegral ν a χ f s + localZetaIntegral ν a χ g s := by
  rw [localZetaIntegral, localZetaIntegral, localZetaIntegral, ← integral_add hf hg]
  congr 1
  ext x
  simp only [Pi.add_apply]
  ring

/-- The local zeta integral is homogeneous in the test function. -/
theorem localZetaIntegral_const_mul (c : ℂ) (f : F → ℂ) (s : ℂ) :
    localZetaIntegral ν a χ (fun x ↦ c * f x) s = c * localZetaIntegral ν a χ f s := by
  rw [localZetaIntegral, localZetaIntegral, ← integral_const_mul]
  simp only [mul_assoc]

/-- Rescaling the multiplicative measure by `c` rescales the local zeta integral by `c`. -/
theorem localZetaIntegral_smul_measure (c : ENNReal) (f : F → ℂ) (s : ℂ) :
    localZetaIntegral (c • ν) a χ f s = c.toReal • localZetaIntegral ν a χ f s :=
  integral_smul_measure _ c

/-- **Twisting by a norm power translates the exponent**: if `χ' = χ a ^ t` on `Fˣ`, then
`z(s, χ'; f) = z(s + t, χ; f)`. -/
theorem localZetaIntegral_of_twist {χ' : Fˣ →ₜ* ℂˣ} {t : ℂ}
    (hχ' : ∀ x : Fˣ, (χ' x : ℂ) = χ x * (a x : ℂ) ^ t) (f : F → ℂ) (s : ℂ) :
    localZetaIntegral ν a χ' f s = localZetaIntegral ν a χ f (s + t) := by
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
  rw [localZetaIntegral, localZetaIntegral, key, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  dsimp only
  rw [map_mul, Units.val_mul, map_inv, Units.val_inv_eq_inv_val, ← Units.val_mul, hmul,
    hinv, Complex.ofReal_mul,
    Complex.ofReal_mul_cpow (inv_nonneg.2 (ha b).le), Complex.ofReal_inv, Complex.inv_cpow,
    Complex.cpow_neg]
  · ring
  · rw [Complex.arg_ofReal_of_nonneg (ha b).le]
    exact Real.pi_ne_zero.symm

end TauCeti.TateZeta

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.CompMul
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv
import TauCeti.Analysis.SpecialFunctions.Log.Deriv

/-!
# Second derivatives of functions of one variable

Computations of the second derivative `deriv (deriv f)` of a function of one variable.

The `n`-th iterated derivative of `fun x ↦ f (c * x)` is `c ^ n` times the `n`-th iterated
derivative of `f` at `c * x`; in particular its second derivative is `c ^ 2` times the second
derivative of `f` at `c * x`. As for `deriv_comp_mul_left`, no differentiability of `f` is needed,
since Mathlib's derivative is `0` wherever it is undefined. Mathlib's
`iteratedDeriv_comp_const_smul` states the same formula under a `ContDiff` hypothesis.

The second derivative of a quadratic polynomial `a + b s + c s ^ 2` is the constant `2 c`, and
the affine line `t ↦ a + t • b` has constant derivative `b` and vanishing second derivative.

The second derivative of the square root of a quadratic polynomial `Q s = a + b s + c s ^ 2` is
computed where `Q` is positive. Since `2 Q Q'' - Q' ^ 2` is the constant `4 a c - b ^ 2`, it is
`(4 a c - b ^ 2) / (4 Q √Q)`; at `0` this is `(4 a c - b ^ 2) / (4 a √a)`.

Under the change of variables `x = e^y` the operators `x d/dx` and `x² d²/dx²` become `d/dy` and
`d²/dy² - d/dy`: for `v` twice differentiable at `log x`, `x (v ∘ log)'(x) = v'(log x)` and
`x² (v ∘ log)''(x) = v''(log x) - v'(log x)`, and conversely
`(f ∘ exp)''(y) = e^y f'(e^y) + e^{2y} f''(e^y)`. These turn equations of Euler type, whose
coefficients `x` and `x²` degenerate at `0`, into equations with constant coefficients.

If `f′ = f ℓ` near a point `z` and `ℓ` has derivative `ℓ′` at `z`, then `f′` has derivative
`f(z) (ℓ(z) ^ 2 + ℓ′)` at `z`.

For `p` and `φ` differentiable near `z` and `F` differentiable near `φ z`, the product and chain
rules give `(p · (F ∘ φ))′ = p′ · (F ∘ φ) + p · (F′ ∘ φ) · φ′` on a neighbourhood of `z`; if also
`p′`, `φ′` are differentiable at `z` and `F′` at `φ z`, then

`(p · (F ∘ φ))′′ = p′′ · (F ∘ φ) + 2 p′ · (F′ ∘ φ) · φ′ + p · ((F′′ ∘ φ) · φ′ ^ 2 + (F′ ∘ φ) · φ′′)`

at `z`. These formulas transform a linear second-order differential equation under a change of
dependent variable `w = p · u` combined with a change of independent variable `ζ = φ(z)`. Over a
complete field they hold in particular when `p`, `φ` are analytic at `z` and `F` at `φ z`.

## Main results

* `TauCeti.iteratedDeriv_comp_mul_left`: the iterated derivatives of `fun x ↦ f (c * x)`, and
  `TauCeti.deriv_deriv_comp_mul_left` its second derivative.
* `TauCeti.deriv_deriv_fun_add`, `TauCeti.deriv_deriv_fun_sub`: the second derivative of a sum and
  of a difference of functions that are `C²` at the point.
* `TauCeti.deriv_deriv_quadratic`: the second derivative of `s ↦ a + b s + c s ^ 2`.
* `TauCeti.deriv_const_add_smul`, `TauCeti.iteratedDeriv_two_const_add_smul`: the first and
  second derivatives of the affine line `t ↦ a + t • b`.
* `TauCeti.deriv_deriv_sqrt_quadratic`: the second derivative of `s ↦ √(a + b s + c s ^ 2)`, and
  `TauCeti.deriv_deriv_sqrt_quadratic_zero` its value at `0`.
* `TauCeti.sq_mul_deriv_deriv_comp_log`, `TauCeti.deriv_deriv_comp_exp`: the second derivatives
  under the change of variables `x = e^y`.
* `TauCeti.hasDerivAt_deriv_of_eventually_hasDerivAt_mul`: the second derivative of `f` from a
  logarithmic derivative `ℓ` of `f`.
* `TauCeti.deriv_mul_comp_eventuallyEq`, `TauCeti.hasDerivAt_deriv_mul_comp`: the first
  derivative of `p · (F ∘ φ)` near a point and its second derivative at the point, with the
  analytic special cases `AnalyticAt.deriv_mul_comp_eventuallyEq`,
  `AnalyticAt.hasDerivAt_deriv_mul_comp`.

The derivatives of `p · (F ∘ φ)` are adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/Hypergeometric/FurtherTransformations/Quadratic.lean`.
-/

public section

open Filter Real Topology

namespace TauCeti

section CompMul

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The `n`-th iterated derivative of `fun x ↦ f (c * x)` is
`fun x ↦ c ^ n • iteratedDeriv n f (c * x)`, with no differentiability assumption on `f`. -/
theorem iteratedDeriv_comp_mul_left (n : ℕ) (c : 𝕜) (f : 𝕜 → F) :
    iteratedDeriv n (f <| c * ·) = fun x ↦ c ^ n • iteratedDeriv n f (c * x) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_smul]
  | succ n ih =>
    funext x
    rw [iteratedDeriv_succ, ih, deriv_fun_const_smul_field, deriv_comp_mul_left,
      iteratedDeriv_succ, smul_smul, pow_succ]

/-- The second derivative of `fun x ↦ f (c * x)` at `x` is `c ^ 2 • deriv (deriv f) (c * x)`,
with no differentiability assumption on `f`. -/
theorem deriv_deriv_comp_mul_left (c : 𝕜) (f : 𝕜 → F) (x : 𝕜) :
    deriv (deriv (f <| c * ·)) x = c ^ 2 • deriv (deriv f) (c * x) := by
  simpa only [iteratedDeriv_succ (n := 1), iteratedDeriv_one] using
    congrFun (iteratedDeriv_comp_mul_left 2 c f) x

end CompMul

section AddSub

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f g : 𝕜 → F} {x : 𝕜}

/-- The second derivative of a sum of functions that are `C²` at `x`: Mathlib's
`iteratedDeriv_fun_add` at order two, written with `deriv`. -/
theorem deriv_deriv_fun_add (hf : ContDiffAt 𝕜 2 f x) (hg : ContDiffAt 𝕜 2 g x) :
    deriv (deriv fun y ↦ f y + g y) x = deriv (deriv f) x + deriv (deriv g) x := by
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using iteratedDeriv_fun_add hf hg

/-- The second derivative of a difference of functions that are `C²` at `x`: Mathlib's
`iteratedDeriv_fun_sub` at order two, written with `deriv`. -/
theorem deriv_deriv_fun_sub (hf : ContDiffAt 𝕜 2 f x) (hg : ContDiffAt 𝕜 2 g x) :
    deriv (deriv fun y ↦ f y - g y) x = deriv (deriv f) x - deriv (deriv g) x := by
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using iteratedDeriv_fun_sub hf hg

end AddSub

section Quadratic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The derivative of a quadratic polynomial `a + b * s + c * s ^ 2` at `t` is `b + 2 * c * t`. -/
theorem hasDerivAt_quadratic (a b c t : 𝕜) :
    HasDerivAt (fun s ↦ a + b * s + c * s ^ 2) (b + 2 * c * t) t := by
  have h := HasDerivAt.add (HasDerivAt.const_add a (HasDerivAt.const_mul b (hasDerivAt_id t)))
    (HasDerivAt.const_mul c (hasDerivAt_pow 2 t))
  convert h using 1
  · ext u
    simp only [id, Pi.add_apply]
  · simp only [mul_one, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring

/-- The second derivative of a quadratic polynomial `a + b * s + c * s ^ 2` is `2 * c`. -/
theorem deriv_deriv_quadratic (a b c t : 𝕜) :
    deriv (deriv fun s ↦ a + b * s + c * s ^ 2) t = 2 * c := by
  have h : deriv (fun s ↦ a + b * s + c * s ^ 2) = fun s ↦ b + 2 * c * s :=
    funext fun s ↦ (hasDerivAt_quadratic a b c s).deriv
  rw [h]
  simp

/-- Subtracting a quadratic subtracts its exact second derivative. -/
theorem _root_.ContDiffAt.deriv_deriv_sub_quadratic {B : 𝕜 → 𝕜} {t : 𝕜}
    (hB : ContDiffAt 𝕜 2 B t) (a b c : 𝕜) :
    deriv (deriv (fun s ↦ B s - (a + b * s + c * s ^ 2))) t =
      deriv (deriv B) t - 2 * c := by
  have hpoly : ContDiffAt 𝕜 2 (fun s ↦ a + b * s + c * s ^ 2) t := by fun_prop
  have h := iteratedDeriv_sub hB hpoly
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero, deriv_deriv_quadratic, Pi.sub_def] using h

end Quadratic

section AffineLine

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of the affine line `t ↦ a + t • b` is constantly `b`. -/
theorem deriv_const_add_smul (a b : F) : deriv (fun t : 𝕜 ↦ a + t • b) = fun _ ↦ b :=
  funext fun t ↦ by simpa using (((hasDerivAt_id t).smul_const b).const_add a).deriv

/-- The second derivative of the affine line `t ↦ a + t • b` vanishes. -/
@[simp]
theorem iteratedDeriv_two_const_add_smul (a b : F) :
    iteratedDeriv 2 (fun t : 𝕜 ↦ a + t • b) = 0 := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, deriv_const_add_smul, deriv_const',
    Pi.zero_def]

end AffineLine

section LogDeriv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- If `f′ = f · ℓ` near `z`, so that `ℓ` is a logarithmic derivative of `f` there, and `ℓ` has
derivative `ℓ′` at `z`, then `f′` has derivative `f(z) (ℓ(z) ^ 2 + ℓ′)` at `z`. -/
theorem hasDerivAt_deriv_of_eventually_hasDerivAt_mul {f ℓ : 𝕜 → 𝕜} {ℓ' z : 𝕜}
    (hf : ∀ᶠ w in 𝓝 z, HasDerivAt f (f w * ℓ w) w) (hℓ : HasDerivAt ℓ ℓ' z) :
    HasDerivAt (deriv f) (f z * (ℓ z ^ 2 + ℓ')) z := by
  have hev : deriv f =ᶠ[𝓝 z] fun w ↦ f w * ℓ w := hf.mono fun w hw ↦ hw.deriv
  refine ((hf.self_of_nhds.mul hℓ).congr_of_eventuallyEq hev).congr_deriv ?_
  ring

end LogDeriv

section MulComp

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {p φ F : 𝕜 → 𝕜} {z : 𝕜}

/-- The derivative of `p · (F ∘ φ)` near a point `z` near which `p` and `φ` are differentiable
and `F` is differentiable at the values of `φ`: it agrees on a neighbourhood of `z` with
`p′ · (F ∘ φ) + p · (F′ ∘ φ) · φ′`. -/
theorem deriv_mul_comp_eventuallyEq (hp : ∀ᶠ w in 𝓝 z, DifferentiableAt 𝕜 p w)
    (hφ : ∀ᶠ w in 𝓝 z, DifferentiableAt 𝕜 φ w) (hF : ∀ᶠ w in 𝓝 z, DifferentiableAt 𝕜 F (φ w)) :
    deriv (fun w ↦ p w * F (φ w)) =ᶠ[𝓝 z]
      fun w ↦ deriv p w * F (φ w) + p w * (deriv F (φ w) * deriv φ w) := by
  filter_upwards [hp, hφ, hF] with w h1 h2 h3
  exact (h1.hasDerivAt.mul (h3.hasDerivAt.comp w h2.hasDerivAt)).deriv

/-- The derivative of `p · (F ∘ φ)`, as a function, has derivative
`p′′ · F(φ) + 2 p′ · F′(φ) · φ′ + p · (F′′(φ) · φ′ ^ 2 + F′(φ) · φ′′)` at a point `z`, when `p`,
`φ` are differentiable near `z`, `F` is differentiable at the values of `φ` near `z`, and `p′`,
`φ′` are differentiable at `z` and `F′` at `φ z`. -/
theorem hasDerivAt_deriv_mul_comp (hp : ∀ᶠ w in 𝓝 z, DifferentiableAt 𝕜 p w)
    (hφ : ∀ᶠ w in 𝓝 z, DifferentiableAt 𝕜 φ w) (hF : ∀ᶠ w in 𝓝 z, DifferentiableAt 𝕜 F (φ w))
    (hp' : DifferentiableAt 𝕜 (deriv p) z) (hφ' : DifferentiableAt 𝕜 (deriv φ) z)
    (hF' : DifferentiableAt 𝕜 (deriv F) (φ z)) :
    HasDerivAt (deriv fun w ↦ p w * F (φ w))
      (deriv (deriv p) z * F (φ z) + 2 * deriv p z * (deriv F (φ z) * deriv φ z) +
        p z * (deriv (deriv F) (φ z) * deriv φ z ^ 2 + deriv F (φ z) * deriv (deriv φ) z)) z := by
  -- Differentiate the first-derivative formula once more, term by term.
  have hφz := hφ.self_of_nhds.hasDerivAt
  have hFφ := hF.self_of_nhds.hasDerivAt.comp z hφz
  have hF'φ := hF'.hasDerivAt.comp z hφz
  have h : HasDerivAt (fun w ↦ deriv p w * F (φ w) + p w * (deriv F (φ w) * deriv φ w)) _ z :=
    (hp'.hasDerivAt.mul hFφ).add (hp.self_of_nhds.hasDerivAt.mul (hF'φ.mul hφ'.hasDerivAt))
  refine (h.congr_of_eventuallyEq (deriv_mul_comp_eventuallyEq hp hφ hF)).congr_deriv ?_
  simp only [Function.comp_apply]
  ring

end MulComp

/-- The second derivative of the square root of a quadratic polynomial
`Q s = a + b * s + c * s ^ 2` at a point `t` where `Q` is positive is
`(4 * a * c - b ^ 2) / (4 * Q t * √(Q t))`. -/
theorem deriv_deriv_sqrt_quadratic {a b c t : ℝ} (ht : 0 < a + b * t + c * t ^ 2) :
    deriv (deriv fun s ↦ √(a + b * s + c * s ^ 2)) t =
      (4 * a * c - b ^ 2) / (4 * (a + b * t + c * t ^ 2) * √(a + b * t + c * t ^ 2)) := by
  have hQ (s : ℝ) := hasDerivAt_quadratic a b c s
  have hpos : ∀ᶠ s in 𝓝 t, 0 < a + b * s + c * s ^ 2 :=
    continuousAt_const.eventually_lt (HasDerivAt.continuousAt (hQ t)) ht
  have hderiv : deriv (fun s ↦ √(a + b * s + c * s ^ 2)) =ᶠ[𝓝 t]
      fun s ↦ (b + 2 * c * s) / (2 * √(a + b * s + c * s ^ 2)) :=
    hpos.mono fun s hs ↦ (HasDerivAt.sqrt (hQ s) hs.ne').deriv
  have hnum : HasDerivAt (fun s ↦ b + 2 * c * s) (2 * c) t := by
    simpa using HasDerivAt.const_add b (HasDerivAt.const_mul (2 * c) (hasDerivAt_id t))
  have hden : HasDerivAt (fun s ↦ 2 * √(a + b * s + c * s ^ 2))
      (2 * ((b + 2 * c * t) / (2 * √(a + b * t + c * t ^ 2)))) t :=
    HasDerivAt.const_mul 2 (HasDerivAt.sqrt (hQ t) ht.ne')
  rw [hderiv.deriv_eq, (HasDerivAt.fun_div hnum hden (by positivity)).deriv]
  have hsq := Real.sq_sqrt ht.le
  field_simp
  rw [hsq]
  ring

/-- The second derivative at `0` of the square root of a quadratic polynomial
`a + b * s + c * s ^ 2` with `0 < a` is `(4 * a * c - b ^ 2) / (4 * a * √a)`. -/
theorem deriv_deriv_sqrt_quadratic_zero {a b c : ℝ} (ha : 0 < a) :
    deriv (deriv fun s ↦ √(a + b * s + c * s ^ 2)) 0 = (4 * a * c - b ^ 2) / (4 * a * √a) := by
  simpa using deriv_deriv_sqrt_quadratic (b := b) (c := c) (t := 0) (by simpa using ha)

section LogExp

variable {f v : ℝ → ℝ} {x y : ℝ}

/-- Under the change of variables `x = e^y` the operator `x² d²/dx²` is `d²/dy² - d/dy`:
`x² (v ∘ log)''(x) = v''(log x) - v'(log x)` for `x ≠ 0`. -/
theorem sq_mul_deriv_deriv_comp_log (hv' : DifferentiableAt ℝ (deriv v) (log x)) (hx : x ≠ 0) :
    x ^ 2 * deriv (deriv fun x ↦ v (log x)) x = deriv (deriv v) (log x) - deriv v (log x) := by
  have hev : deriv (fun x ↦ v (log x)) =ᶠ[𝓝 x] fun x ↦ deriv v (log x) / x := by
    filter_upwards [eventually_ne_nhds hx] with z hz0
    rw [← mul_deriv_comp_log hz0]
    field_simp
  have h : HasDerivAt (fun x ↦ deriv v (log x) / x)
      ((deriv (deriv v) (log x) * x⁻¹ * x - deriv v (log x) * 1) / x ^ 2) x :=
    (hv'.hasDerivAt.comp x (hasDerivAt_log hx)).div (hasDerivAt_id x) hx
  rw [hev.deriv_eq, h.deriv]
  field_simp

/-- The second derivative of `f ∘ exp`: `(f ∘ exp)''(y) = e^y f'(e^y) + e^{2y} f''(e^y)`. -/
theorem deriv_deriv_comp_exp (hf' : DifferentiableAt ℝ (deriv f) (exp y)) :
    deriv (deriv fun y ↦ f (exp y)) y =
      exp y * deriv f (exp y) + exp y ^ 2 * deriv (deriv f) (exp y) := by
  have hd : deriv (fun y ↦ f (exp y)) = fun y ↦ exp y * deriv f (exp y) :=
    funext fun _ ↦ deriv_comp_exp
  have h : HasDerivAt (fun y ↦ exp y * deriv f (exp y))
      (exp y * deriv f (exp y) + exp y * (deriv (deriv f) (exp y) * exp y)) y :=
    (hasDerivAt_exp y).mul (hf'.hasDerivAt.comp y (hasDerivAt_exp y))
  rw [hd, h.deriv]
  ring

end LogExp

end TauCeti

namespace AnalyticAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {p φ F : 𝕜 → 𝕜} {z : 𝕜}

/-- The derivative of `p · (F ∘ φ)` near a point `z` where `p` and `φ` are analytic and `F` is
analytic at `φ z`: it agrees on a neighbourhood of `z` with `p′ · (F ∘ φ) + p · (F′ ∘ φ) · φ′`. -/
theorem deriv_mul_comp_eventuallyEq (hp : AnalyticAt 𝕜 p z) (hφ : AnalyticAt 𝕜 φ z)
    (hF : AnalyticAt 𝕜 F (φ z)) :
    deriv (fun w ↦ p w * F (φ w)) =ᶠ[𝓝 z]
      fun w ↦ deriv p w * F (φ w) + p w * (deriv F (φ w) * deriv φ w) :=
  TauCeti.deriv_mul_comp_eventuallyEq (hp.eventually_analyticAt.mono fun _ h ↦ h.differentiableAt)
    (hφ.eventually_analyticAt.mono fun _ h ↦ h.differentiableAt)
    (hφ.continuousAt.eventually (hF.eventually_analyticAt.mono fun _ h ↦ h.differentiableAt))

/-- The derivative of `p · (F ∘ φ)`, as a function, has derivative
`p′′ · F(φ) + 2 p′ · F′(φ) · φ′ + p · (F′′(φ) · φ′ ^ 2 + F′(φ) · φ′′)` at a point `z` where `p`
and `φ` are analytic and `F` is analytic at `φ z`. -/
theorem hasDerivAt_deriv_mul_comp (hp : AnalyticAt 𝕜 p z) (hφ : AnalyticAt 𝕜 φ z)
    (hF : AnalyticAt 𝕜 F (φ z)) :
    HasDerivAt (deriv fun w ↦ p w * F (φ w))
      (deriv (deriv p) z * F (φ z) + 2 * deriv p z * (deriv F (φ z) * deriv φ z) +
        p z * (deriv (deriv F) (φ z) * deriv φ z ^ 2 + deriv F (φ z) * deriv (deriv φ) z)) z :=
  TauCeti.hasDerivAt_deriv_mul_comp (hp.eventually_analyticAt.mono fun _ h ↦ h.differentiableAt)
    (hφ.eventually_analyticAt.mono fun _ h ↦ h.differentiableAt)
    (hφ.continuousAt.eventually (hF.eventually_analyticAt.mono fun _ h ↦ h.differentiableAt))
    hp.deriv.differentiableAt hφ.deriv.differentiableAt hF.deriv.differentiableAt

end AnalyticAt

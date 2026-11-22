/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.CompMul
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
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

For the second-order linear differential operator `L(w) = w'' + f w' + g w`, pointwise linearity
`L(ψ + c' Φ) = L(ψ) + c' L(Φ)` holds under local differentiability hypotheses, and on the complex
slit plane `z - z₀ ∈ Complex.slitPlane` the product `w(z) * Complex.log (z - z₀)` satisfies the
operator identity
`L(w * log(· - z₀)) z - log(z - z₀) * L(w) z =`
`((z - z₀) ^ 2)⁻¹ * (2 (z - z₀) w'(z) + ((z - z₀) f(z) - 1) w(z))`.

## Main results

* `TauCeti.iteratedDeriv_comp_mul_left`: the iterated derivatives of `fun x ↦ f (c * x)`, and
  `TauCeti.deriv_deriv_comp_mul_left` its second derivative.
* `TauCeti.deriv_deriv_quadratic`: the second derivative of `s ↦ a + b s + c s ^ 2`.
* `TauCeti.deriv_const_add_smul`, `TauCeti.iteratedDeriv_two_const_add_smul`: the first and
  second derivatives of the affine line `t ↦ a + t • b`.
* `TauCeti.deriv_deriv_sqrt_quadratic`: the second derivative of `s ↦ √(a + b s + c s ^ 2)`, and
  `TauCeti.deriv_deriv_sqrt_quadratic_zero` its value at `0`.
* `TauCeti.sq_mul_deriv_deriv_comp_log`, `TauCeti.deriv_deriv_comp_exp`: the second derivatives
  under the change of variables `x = e^y`.
* `TauCeti.secondOrder_operator_add_const_mul`: pointwise linearity of `w'' + f w' + g w`.
* `HasDerivAt.mul_log_sub`, `TauCeti.deriv_deriv_add_mul_deriv_add_mul_mul_log_sub`: first
  derivative and second-order operator identity for `w(z) * Complex.log (z - z₀)`.
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

section SecondOrderOperator

/-- Pointwise linearity `L(ψ + c' Φ) = L(ψ) + c' L(Φ)` for the second-order linear differential
operator `L(w) = w'' + f w' + g w` under local differentiability assumptions near `z`. -/
theorem secondOrder_operator_add_const_mul {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {f g ψ Φ : 𝕜 → 𝕜} {c' z : 𝕜}
    (hψ₁ : ∀ᶠ w in 𝓝 z, DifferentiableAt 𝕜 ψ w)
    (hΦ₁ : ∀ᶠ w in 𝓝 z, DifferentiableAt 𝕜 Φ w)
    (hψ₂ : DifferentiableAt 𝕜 (deriv ψ) z)
    (hΦ₂ : DifferentiableAt 𝕜 (deriv Φ) z) :
    (deriv (deriv fun w ↦ ψ w + c' * Φ w) z + f z * deriv (fun w ↦ ψ w + c' * Φ w) z +
        g z * (ψ z + c' * Φ z)) =
      (deriv (deriv ψ) z + f z * deriv ψ z + g z * ψ z) +
        c' * (deriv (deriv Φ) z + f z * deriv Φ z + g z * Φ z) := by
  have hd1_ev : deriv (fun w ↦ ψ w + c' * Φ w) =ᶠ[𝓝 z] fun w ↦ deriv ψ w + c' * deriv Φ w := by
    filter_upwards [hψ₁, hΦ₁] with w hwψ hwΦ
    exact ((hwψ.hasDerivAt).add ((hwΦ.hasDerivAt).const_mul c')).deriv
  have hd2 : deriv (deriv fun w ↦ ψ w + c' * Φ w) z =
      deriv (deriv ψ) z + c' * deriv (deriv Φ) z :=
    (((hψ₂.hasDerivAt).add ((hΦ₂.hasDerivAt).const_mul c')).congr_of_eventuallyEq hd1_ev).deriv
  rw [hd1_ev.self_of_nhds, hd2]
  ring

/-- Pointwise first derivative of `u ↦ w u * Complex.log (u - z₀)` at a point `z` with
`z - z₀ ∈ Complex.slitPlane`. -/
theorem _root_.HasDerivAt.mul_log_sub {w : ℂ → ℂ} {w' z₀ z : ℂ}
    (hw : HasDerivAt w w' z) (hzs : z - z₀ ∈ Complex.slitPlane) :
    HasDerivAt (fun u ↦ w u * Complex.log (u - z₀))
      (w' * Complex.log (z - z₀) + (z - z₀)⁻¹ * w z) z :=
  (hw.mul (((hasDerivAt_id z).sub_const z₀).clog hzs)).congr_deriv
    (by dsimp only [id]; rw [one_div]; ring)

/-- Pointwise logarithmic-product identity for the second-order linear operator
`L(w) = w'' + f w' + g w` on the logarithm branch `z - z₀ ∈ Complex.slitPlane`: if `w` is
differentiable near `z` and `deriv w` is differentiable at `z`, then
`L(w * log(· - z₀)) z - log(z - z₀) * L(w) z` equals
`((z - z₀) ^ 2)⁻¹ * (2 * (z - z₀) * deriv w z + ((z - z₀) * f z - 1) * w z)`. -/
theorem deriv_deriv_add_mul_deriv_add_mul_mul_log_sub
    {z₀ z : ℂ} (hzs : z - z₀ ∈ Complex.slitPlane) {f g w : ℂ → ℂ}
    (hw : ∀ᶠ u in 𝓝 z, DifferentiableAt ℂ w u) (hdw : DifferentiableAt ℂ (deriv w) z) :
    let Φ : ℂ → ℂ := fun u ↦ w u * Complex.log (u - z₀)
    (deriv (deriv Φ) z + f z * deriv Φ z + g z * Φ z) -
        Complex.log (z - z₀) * (deriv (deriv w) z + f z * deriv w z + g z * w z) =
      ((z - z₀) ^ 2)⁻¹ * (2 * (z - z₀) * deriv w z + ((z - z₀) * f z - 1) * w z) := by
  intro Φ
  have hzu0 : z - z₀ ≠ 0 := Complex.slitPlane_ne_zero hzs
  have hsub : HasDerivAt (fun u : ℂ ↦ u - z₀) 1 z := (hasDerivAt_id z).sub_const z₀
  have hU_log : ∀ᶠ u in 𝓝 z, u - z₀ ∈ Complex.slitPlane :=
    (Complex.isOpen_slitPlane.preimage (continuous_id.sub continuous_const)).mem_nhds hzs
  have hderiv1 : ∀ᶠ u in 𝓝 z,
      HasDerivAt Φ (deriv w u * Complex.log (u - z₀) + (u - z₀)⁻¹ * w u) u := by
    filter_upwards [hw, hU_log] with u hu hsu
    exact hu.hasDerivAt.mul_log_sub hsu
  have hd1 : deriv Φ z = deriv w z * Complex.log (z - z₀) + (z - z₀)⁻¹ * w z :=
    hderiv1.self_of_nhds.deriv
  have hev : deriv Φ =ᶠ[𝓝 z]
      (deriv w * (fun u : ℂ ↦ Complex.log (u - z₀)) + (fun u : ℂ ↦ (u - z₀)⁻¹) * w) :=
    hderiv1.mono fun _ hu ↦ hu.deriv
  have hd2 : deriv (deriv Φ) z = deriv (deriv w) z * Complex.log (z - z₀) +
      2 * (z - z₀)⁻¹ * deriv w z - ((z - z₀) ^ 2)⁻¹ * w z := by
    rw [(((hdw.hasDerivAt.mul (hsub.clog hzs)).add
      ((hsub.inv hzu0).mul hw.self_of_nhds.hasDerivAt)).congr_of_eventuallyEq hev).deriv]
    simp only [Pi.inv_apply]; field_simp [hzu0]; ring
  rw [hd1, hd2]
  dsimp only [Φ]
  field_simp [hzu0]
  ring

end SecondOrderOperator

end TauCeti
